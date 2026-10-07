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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.ENat.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Volume 2, Chapter 5 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discrete MDPs and Q-factors

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.1 (pp. 105–108).

* A sup-norm contraction of `ℝ^G` with `G` finite is globally stable for the product topology.
* §3.2.1.1: the finite MDP ADP is regular, globally stable and finite, so Corollary 3.1.3 and
  Theorem 2.2.6 give optimality, convergence of VFI, OPI and HPI, and finite termination of HPI.
* **Exercise 3.2.1**: the MDP with countable state space, finite feasible sets and bounded
  rewards, as an ADP on `bX`, via Theorems 3.1.5 and 3.1.2.
* The Q-factor model (3.6) on `ℝ^G`: **Exercise 3.2.2** (it is an ADP), **Exercise 3.2.3**
  (greedy policies), **Exercise 3.2.4** (the Bellman operator (3.7)), **Exercise 3.2.5**
  (contraction) and **Exercise 3.2.6** (optimality, convergence, HPI in finitely many steps).
* The "only if" half of Exercise 3.2.3 needs every state to be reachable and `β > 0`:
  `exercise_3_2_3_converse_fails` is a two-state counterexample.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- On a finite index set, a `β`-contraction of `ℝ^G` for the supremum distance is globally stable
for the product topology. -/
theorem globallyStable_of_supContraction {G : Type*} [Finite G] {T : (G → ℝ) → G → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hT : IsSupContraction univ T β) : GloballyStable T := by
  have hbdd : ∀ v ∈ (univ : Set (G → ℝ)), IsBdd v := fun v _ => FiniteMDP.isBdd_of_finite v
  obtain ⟨u, -, hu, huniq, hlim⟩ := hT.globallyStable hβ0 hβ1 hbdd
    (fun _ _ _ _ => trivial) (mapsTo_univ _ _) univ_nonempty
  exact ⟨u, hu, fun w hw => huniq w trivial hw, fun v =>
    tendsto_pi_nhds.2 fun x => (hlim v trivial).tendsto_at x⟩

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- Each MDP policy operator is globally stable on `ℝ^X` (Exercise 1.2.1). -/
theorem adp_isGloballyStable : M.adp.IsGloballyStable := fun σ =>
  globallyStable_of_supContraction M.β_nonneg M.β_lt_one fun _ _ _ _ _ h x =>
    M.abs_Q_sub_le (σ.2 x) h

/-- §3.2.1.1 (p. 106): via Corollary 3.1.3 and Theorem 2.2.6, the finite MDP ADP satisfies the
fundamental optimality properties, VFI, OPI and HPI all converge, and HPI converges in finitely
many steps. -/
theorem section_3_2_1_1 :
    M.adp.FundamentalOptimality M.adp_isGloballyStable.wellPosed ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isGloballyStable.wellPosed g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.adp_isGloballyStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h2⟩ := ADP.corollary_3_1_3 M.adp_regular M.adp_isGloballyStable (finite_range _)
  exact ⟨h1, h2, (ADP.fundamentalOptimality_of_finite M.adp_isGloballyStable.isOrderStable
    M.adp_regular (finite_range _)).2⟩

/-! ### The Q-factor model -/

/-- The feasible state-action pairs `G`. -/
def G : Type _ := {p : X × A // p.2 ∈ M.Γ p.1}

theorem finite_G : Finite M.G := by
  have h : {p : X × A | p.2 ∈ M.Γ p.1} = ⋃ x, ({x} : Set X) ×ˢ (M.Γ x : Set A) := by
    ext ⟨x, a⟩
    simp
  have hfin : {p : X × A | p.2 ∈ M.Γ p.1}.Finite := by
    rw [h]
    exact finite_iUnion fun x => (finite_singleton x).prod (M.Γ x).finite_toSet
  exact hfin.to_subtype

/-- `(x', σ(x'))` as a feasible pair. -/
def pairOf (σ : M.Policy) (x : X) : M.G := ⟨(x, σ.1 x), σ.2 x⟩

/-- The Q-factor policy operator (3.6):
`(S_σ q)(x, a) = r(x, a) + β ∑_{x'} q(x', σ(x'))P(x, a, x')`. -/
def Sσ (σ : M.Policy) (q : M.G → ℝ) (p : M.G) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * ∑ x', q (M.pairOf σ x') * M.P p.1.1 p.1.2 x'

theorem Sσ_mono (σ : M.Policy) : Monotone (M.Sσ σ) := fun _ _ h p =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (h _) (M.P_nonneg _ _ p.2 x')) M.β_nonneg)

/-- **Exercise 3.2.2** (p. 107): `(ℝ^G, 𝕊)` is an ADP. -/
def qadp : ADP (M.G → ℝ) M.Policy where
  T := M.Sσ
  mono := M.Sσ_mono
  nonempty := M.nonempty_policy

/-- **Exercise 3.2.3** (p. 107), "if": a policy choosing `σ(x) ∈ argmax_{a ∈ Γ(x)} q(x, a)` at
every state is `q`-greedy. -/
theorem exercise_3_2_3 (q : M.G → ℝ) (σ : M.Policy)
    (h : ∀ x, ∀ a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤ q (M.pairOf σ x)) : M.qadp.IsGreedy q σ :=
  fun τ p => add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (h x' (τ.1 x') (τ.2 x')) (M.P_nonneg _ _ p.2 x')) M.β_nonneg)

/-- **Exercise 3.2.3** (p. 107), "only if", at the states it can see: if `β > 0` and `σ` is
`q`-greedy, then `σ(x')` maximizes `q(x', ·)` at every state `x'` reachable from a feasible pair. -/
theorem exercise_3_2_3_converse (hβ : 0 < M.β) (q : M.G → ℝ) (σ : M.Policy)
    (hσ : M.qadp.IsGreedy q σ) {x' : X} (hreach : ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x') :
    ∀ a (ha : a ∈ M.Γ x'), q ⟨(x', a), ha⟩ ≤ q (M.pairOf σ x') := by
  classical
  intro a ha
  obtain ⟨p, hp⟩ := hreach
  by_contra hlt
  rw [not_le] at hlt
  let τ : M.Policy := ⟨fun y => if y = x' then a else σ.1 y, fun y => by
    change (if y = x' then a else σ.1 y) ∈ M.Γ y
    split_ifs with hy
    · rw [hy]
      exact ha
    · exact σ.2 y⟩
  have hτx : M.pairOf τ x' = ⟨(x', a), ha⟩ := Subtype.ext (by simp [pairOf, τ])
  have hτy : ∀ y, y ≠ x' → M.pairOf τ y = M.pairOf σ y := fun y hy =>
    Subtype.ext (by simp [pairOf, τ, hy])
  have h := hσ τ p
  simp only [qadp, Sσ, add_le_add_iff_left] at h
  have hlt' : ∑ y, q (M.pairOf σ y) * M.P p.1.1 p.1.2 y <
      ∑ y, q (M.pairOf τ y) * M.P p.1.1 p.1.2 y := by
    refine Finset.sum_lt_sum (fun y _ => ?_) ⟨x', Finset.mem_univ _, ?_⟩
    · rcases eq_or_ne y x' with rfl | hy
      · rw [hτx]
        exact mul_le_mul_of_nonneg_right hlt.le (M.P_nonneg _ _ p.2 y)
      · rw [hτy y hy]
    · rw [hτx]
      exact mul_lt_mul_of_pos_right hlt hp
  linarith [mul_lt_mul_of_pos_left hlt' hβ]

/-- The Q-factor `q`-greedy policy: `σ(x) ∈ argmax_{a ∈ Γ(x)} q(x, a)`. -/
theorem exists_qgreedy (q : M.G → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤ q (M.pairOf σ x) := by
  classical
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x)
    (fun a => if ha : a ∈ M.Γ x then q ⟨(x, a), ha⟩ else 0) (M.Γ_nonempty x)
  refine ⟨⟨f, hf⟩, fun x a ha => ?_⟩
  have := hmax x a ha
  simp only [ha, hf x, ↓reduceDIte] at this
  exact this

/-- The Q-factor ADP is regular. -/
theorem qadp_regular : M.qadp.Regular := fun q => by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy q
  exact ⟨σ, M.exercise_3_2_3 q σ hσ⟩

/-- **Exercise 3.2.4** (p. 107): the Bellman operator of `(ℝ^G, 𝕊)` is (3.7),
`(Sq)(x, a) = r(x, a) + β ∑_{x'} max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')`. -/
theorem exercise_3_2_4 (q : M.G → ℝ) (p : M.G) :
    M.qadp.bellman q p = M.r p.1.1 p.1.2 + M.β * ∑ x',
      (M.Γ x').attach.sup' ((M.Γ_nonempty x').attach)
        (fun a => q ⟨(x', a.1), a.2⟩) * M.P p.1.1 p.1.2 x' := by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy q
  have hlub := M.qadp.isBellmanValue_bellman (M.qadp_regular q)
  have hgr : IsLUB (range fun τ => M.qadp.T τ q) (M.qadp.T σ q) :=
    ⟨by rintro _ ⟨τ, rfl⟩; exact M.exercise_3_2_3 q σ hσ τ, fun w hw => hw ⟨σ, rfl⟩⟩
  rw [hlub.unique hgr]
  simp only [qadp, Sσ]
  congr 2
  refine Finset.sum_congr rfl fun x' _ => ?_
  congr 1
  refine le_antisymm (Finset.le_sup' (fun a : M.Γ x' => q ⟨(x', a.1), a.2⟩)
    (Finset.mem_attach _ ⟨σ.1 x', σ.2 x'⟩)) (Finset.sup'_le _ _ fun a _ => hσ x' a.1 a.2)

/-- **Exercise 3.2.5** (p. 108): each `S_σ` is a contraction of modulus `β` for the supremum
norm on `ℝ^G`. -/
theorem exercise_3_2_5 (σ : M.Policy) : IsSupContraction univ (M.Sσ σ) M.β :=
  fun q _ q' _ c h p => by
    simp only [Sσ, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
    exact M.abs_sum_sub_le p.2 (v := fun x' => q (M.pairOf σ x'))
      (w := fun x' => q' (M.pairOf σ x')) fun y => h _

/-- The Q-factor ADP is globally stable. -/
theorem qadp_isGloballyStable : M.qadp.IsGloballyStable := fun σ => by
  have := M.finite_G
  exact globallyStable_of_supContraction M.β_nonneg M.β_lt_one (M.exercise_3_2_5 σ)

/-- **Exercise 3.2.6** (p. 108): the Q-factor ADP satisfies the fundamental optimality
properties, VFI, OPI and HPI all converge, and HPI converges in finitely many steps. -/
theorem exercise_3_2_6 :
    M.qadp.FundamentalOptimality M.qadp_isGloballyStable.wellPosed ∧
      (∃ vstar, M.qadp.IsValueFunction vstar ∧ M.qadp.VFIConverges vstar ∧
        ∀ g, M.qadp.IsSelector g → M.qadp.OPIConverges g vstar ∧
          M.qadp.HPIConverges M.qadp_isGloballyStable.wellPosed g vstar) ∧
      ∀ g, M.qadp.IsSelector g → ∀ v ∈ M.qadp.VU,
        ∃ n, M.qadp.IsValueFunction
          ((M.qadp.howard M.qadp_isGloballyStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h2⟩ := ADP.corollary_3_1_3 M.qadp_regular M.qadp_isGloballyStable (finite_range _)
  exact ⟨h1, h2, (ADP.fundamentalOptimality_of_finite M.qadp_isGloballyStable.isOrderStable
    M.qadp_regular (finite_range _)).2⟩

end FiniteMDP

/-- **The converse in Exercise 3.2.3 fails at unreachable states.** Two states `x ∈ Bool`, two
actions, `β = 1/2`, `r = 0`, and every transition goes to state `false`. With
`q(true, true) = 1` and `q(x, a) = 0` otherwise, the policy choosing `false` everywhere is
`q`-greedy, yet at the state `true` it does not maximize `q(true, ·)`. -/
theorem exercise_3_2_3_converse_fails :
    ∃ (M : FiniteMDP Bool Bool) (q : M.G → ℝ) (σ : M.Policy), M.qadp.IsGreedy q σ ∧
      ∃ x a, ∃ ha : a ∈ M.Γ x, q (M.pairOf σ x) < q ⟨(x, a), ha⟩ := by
  let M : FiniteMDP Bool Bool :=
    { Γ := fun _ => Finset.univ
      Γ_nonempty := fun _ => Finset.univ_nonempty
      r := fun _ _ => 0
      β := 1 / 2
      β_nonneg := by norm_num
      β_lt_one := by norm_num
      P := fun _ _ x' => if x' = false then 1 else 0
      P_nonneg := fun _ _ _ _ => by split_ifs <;> norm_num
      P_sum := fun _ _ _ => by simp }
  let q : M.G → ℝ := fun p => if p.1 = (true, true) then 1 else 0
  let σ : M.Policy := ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
  refine ⟨M, q, σ, fun τ p => ?_, true, true, Finset.mem_univ _, ?_⟩
  · simp [FiniteMDP.qadp, FiniteMDP.Sσ, FiniteMDP.pairOf, M, q, σ]
  · simp [FiniteMDP.pairOf, q, σ]

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Structural estimation

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.3.1, §4.2.3.3 and §4.2.3.4
(pp. 140–146).

Post-action value functions `g ∈ bG`, `G = X × A`, with `A` finite. For a certainty equivalent
operator `M : bX → bG` (order preserving, `M(v + κ𝟙) = Mv + κ𝟙`) the policy operators are
`T̂_σ g = M H_σ g` with `(H_σ g)(x') = r(x', σ(x')) + βg(x', σ(x'))`.

* **Exercise 4.2.4**: a Borel `σ` with `σ(x) ∈ argmax_a [r(x, a) + βg(x, a)]` (4.22), the least
  maximizer for a fixed order on `A`; such `σ` is `g`-greedy, so the ADP is regular.
* **Proposition 4.2.6** (§4.2.3.3): optimality, VFI, OPI and HPI for every certainty equivalent
  `M`, by Theorem 4.1.3 and (4.28); the Bellman operator is `T̂g = MHg` (4.26).
* §4.2.3.1: `M` the expectation under a stochastic kernel `P` from `G` to `X`, giving (4.21), the
  Bellman equation (4.20), **Exercise 4.2.5** (contraction of modulus `β`) and
  **Proposition 4.2.4**.
* §4.2.3.4: the risk-sensitive certainty equivalent `Mf = −γ⁻¹ ln ∫ exp(−γf) dP`, `γ ≠ 0`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Exercise 4.2.4: measurable greedy policies -/

/-- The maximizers of `a ↦ h(x, a)`. -/
noncomputable def argmaxSet [Fintype A] (h : X → A → ℝ) (x : X) : Finset A :=
  Finset.univ.filter fun a => ∀ a', h x a' ≤ h x a

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem argmaxSet_nonempty [Fintype A] [Nonempty A] (h : X → A → ℝ) (x : X) :
    (argmaxSet h x).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (h x) Finset.univ_nonempty
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a' => ha a' (Finset.mem_univ _)⟩⟩

/-- The least maximizer of `a ↦ h(x, a)`. -/
noncomputable def argmaxSel [Fintype A] [Nonempty A] [LinearOrder A] (h : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet h x).min' (argmaxSet_nonempty h x)

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem argmaxSel_max [Fintype A] [Nonempty A] [LinearOrder A] (h : X → A → ℝ) (x : X) (a : A) :
    h x a ≤ h x (argmaxSel h x) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (argmaxSet_nonempty h x))).2 a

/-- **Exercise 4.2.4** (p. 142): if `x ↦ h(x, a)` is measurable for each `a`, the least maximizer
is a Borel measurable selection from `argmax_a h(x, a)`. -/
theorem measurable_argmaxSel [Fintype A] [Nonempty A] [LinearOrder A] {h : X → A → ℝ}
    (hm : ∀ a, Measurable fun x => h x a) : Measurable (argmaxSel h) := by
  classical
  refine measurable_to_countable' fun a => ?_
  have hset : argmaxSel h ⁻¹' {a} =
      {x | ∀ a', h x a' ≤ h x a} ∩ ⋂ a', ({x | ∀ a'', h x a'' ≤ h x a'}ᶜ ∪ {_x | a ≤ a'}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨argmaxSel_max h x, fun a' => ?_⟩
      by_cases ha' : ∀ a'', h x a'' ≤ h x a'
      · exact Or.inr (Finset.min'_le (argmaxSet h x) a'
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha'⟩))
      · exact Or.inl ha'
    · rintro ⟨hmax, hmin⟩
      refine le_antisymm (Finset.min'_le (argmaxSet h x) a
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax⟩))
        (Finset.le_min' (argmaxSet h x) (argmaxSet_nonempty h x) a fun a' ha' => ?_)
      rcases hmin a' with h1 | h1
      · exact absurd (Finset.mem_filter.1 ha').2 h1
      · exact h1
  rw [hset]
  have hmeas : ∀ b, MeasurableSet {x | ∀ a', h x a' ≤ h x b} := fun b => by
    have : {x | ∀ a', h x a' ≤ h x b} = ⋂ a', {x | h x a' ≤ h x b} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iInter fun a' => measurableSet_le (hm a') (hm b)
  refine (hmeas a).inter (MeasurableSet.iInter fun a' => (hmeas a').compl.union ?_)
  by_cases h' : a ≤ a'
  · simp [h']
  · simp [h']

/-! ### The post-action ADP with a certainty equivalent operator -/

/-- Policies: Borel maps `X → A`. -/
def SEPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] : Type _ :=
  {σ : X → A // Measurable σ}

/-- A certainty equivalent operator from `bX` to `bG` (§4.2.3.3). -/
def IsCEOperator (M : BM X → BM (X × A)) : Prop :=
  Monotone M ∧ ∀ v (κ : ℝ), 0 ≤ κ → M (v + κ • BM.const 1) = M v + κ • BM.const 1

/-- The structural estimation model: a reward `r ∈ bG`, a discount factor `β ∈ [0, 1)` and a
certainty equivalent operator `M`. -/
structure PostAction (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the reward -/
  r : BM (X × A)
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the certainty equivalent operator -/
  M : BM X → BM (X × A)

namespace PostAction

variable (S : PostAction X A)

/-- `(H_σ g)(x') = r(x', σ(x')) + βg(x', σ(x'))`. -/
noncomputable def H (σ : SEPolicy X A) (g : BM (X × A)) : BM X :=
  ⟨fun x => S.r.toFun (x, σ.1 x) + S.β * g.toFun (x, σ.1 x),
    (S.r.measurable'.comp (measurable_id.prodMk σ.2)).add
      (measurable_const.mul (g.measurable'.comp (measurable_id.prodMk σ.2))),
    ⟨‖S.r‖ + |S.β| * ‖g‖, fun _ => (abs_add_le _ _).trans (add_le_add (BM.abs_le_norm _ _)
      ((abs_mul S.β _).trans_le (mul_le_mul_of_nonneg_left (BM.abs_le_norm _ _)
        (abs_nonneg _))))⟩⟩

theorem H_mono (σ : SEPolicy X A) : Monotone (S.H σ) := fun _ _ h _ =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (h _) S.β_nonneg)

theorem H_shift (σ : SEPolicy X A) (g : BM (X × A)) (κ : ℝ) :
    S.H σ (g + κ • BM.const 1) = S.H σ g + (S.β * κ) • BM.const 1 :=
  BM.ext fun x => by
    simp only [H, BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
    ring

/-- The policy operators `T̂_σ g = M H_σ g`. -/
noncomputable def adp [Nonempty A] (hM : IsCEOperator S.M) : ADP (BM (X × A)) (SEPolicy X A) where
  T σ g := S.M (S.H σ g)
  mono σ _ _ h := hM.1 (S.H_mono σ h)
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

/-- (4.28): Blackwell's condition with `e = 𝟙`, `λ = β`. -/
theorem blackwell [Nonempty A] (hM : IsCEOperator S.M) (σ : SEPolicy X A) (g : BM (X × A))
    (κ : ℝ) (hκ : 0 ≤ κ) :
    (S.adp hM).T σ (g + κ • BM.const 1) ≤ (S.adp hM).T σ g + (S.β * κ) • BM.const 1 := by
  change S.M (S.H σ (g + κ • BM.const 1)) ≤ _
  rw [S.H_shift, hM.2 _ _ (mul_nonneg S.β_nonneg hκ)]
  exact le_rfl

/-- The `g`-greedy policy (4.27): the least maximizer of `r(x, ·) + βg(x, ·)`. -/
noncomputable def greedySE [Fintype A] [Nonempty A] [LinearOrder A] (g : BM (X × A)) :
    SEPolicy X A :=
  ⟨argmaxSel fun x a => S.r.toFun (x, a) + S.β * g.toFun (x, a), measurable_argmaxSel fun _ =>
    (S.r.measurable'.comp (measurable_id.prodMk measurable_const)).add
      (measurable_const.mul (g.measurable'.comp (measurable_id.prodMk measurable_const)))⟩

/-- `H_τ g ≤ H_σ g` for the greedy `σ`, with `H_σ g = Hg = max_a [r + βg]`. -/
theorem H_le_greedy [Fintype A] [Nonempty A] [LinearOrder A] (g : BM (X × A))
    (τ : SEPolicy X A) : S.H τ g ≤ S.H (S.greedySE g) g :=
  fun x => argmaxSel_max (fun x a => S.r.toFun (x, a) + S.β * g.toFun (x, a)) x (τ.1 x)

/-- (4.27): the greedy policy is `g`-greedy for `(bG, 𝕋̂_SE)`. -/
theorem greedySE_isGreedy [Fintype A] [Nonempty A] [LinearOrder A] (hM : IsCEOperator S.M)
    (g : BM (X × A)) : (S.adp hM).IsGreedy g (S.greedySE g) := fun τ => hM.1 (S.H_le_greedy g τ)

/-- **Exercise 4.2.4** (p. 142): a measurable `g`-greedy policy exists, so `(bG, 𝕋̂_SE)` is
regular. -/
theorem adp_regular [Finite A] [Nonempty A] (hM : IsCEOperator S.M) : (S.adp hM).Regular :=
  fun g => by
    have := Fintype.ofFinite A
    let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
    exact ⟨_, S.greedySE_isGreedy hM g⟩

/-- (4.26): the Bellman operator is `T̂g = MHg`, `(Hg)(x') = max_{a'} [r(x', a') + βg(x', a')]`. -/
theorem adp_bellman [Fintype A] [Nonempty A] [LinearOrder A] (hM : IsCEOperator S.M)
    (g : BM (X × A)) : (S.adp hM).bellman g = S.M (S.H (S.greedySE g) g) :=
  le_antisymm (S.greedySE_isGreedy hM g _) ((S.adp hM).isGreedy_greedy (S.adp_regular hM g) _)

/-- **Proposition 4.2.6** (p. 145): for every certainty equivalent operator `M`, the fundamental
optimality properties hold for `(bG, 𝕋̂_SE)`, VFI converges (geometrically), and OPI and HPI
converge. -/
theorem proposition_4_2_6 [Nonempty X] [Finite A] [Nonempty A] (hM : IsCEOperator S.M) :
    ∃ hw : (S.adp hM).WellPosed, (S.adp hM).FundamentalOptimality hw ∧ ∃ gstar,
      (S.adp hM).VFIGeometric univ gstar ∧ (S.adp hM).VFIConverges gstar ∧
        ∀ g, (S.adp hM).IsSelector g → (S.adp hM).OPIConverges g gstar ∧
          (S.adp hM).HPIConverges hw g gstar := by
  have hsr : (S.adp hM).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => S.adp_regular hM v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, gstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one (S.adp hM) S.β_nonneg S.β_lt_one (S.blackwell hM) hsr
    univ_nonempty
  have hT : ∀ σ v w, dist ((S.adp hM).T σ v) ((S.adp hM).T σ w) ≤ S.β * dist v w :=
    fun σ v w => by
      rw [dist_eq_norm, dist_eq_norm]
      exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one ((S.adp hM).mono σ)
        S.β_nonneg (S.blackwell hM σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg S.β_lt_one hT
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 (S.adp_regular hM) hgs
    (((S.adp hM).solvesBellman_iff hwG).1 hwb)
  obtain rfl : gstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, gstar, hgeo, hvfi, hconv (S.adp_regular hM)⟩

end PostAction

/-! ### Expected utility: §4.2.3.1 -/

/-- The expectation operator `(Mv)(x, a) = ∫ v(x')P(x, a, dx')` of a stochastic kernel from
`G = X × A` to `X`. -/
noncomputable def expectOp (P : Kernel (X × A) X) [IsMarkovKernel P] (v : BM X) : BM (X × A) :=
  ⟨fun p => ∫ x', v.toFun x' ∂(P p),
    (v.measurable'.stronglyMeasurable.integral_kernel (κ := P)).measurable,
    ⟨‖v‖, fun p => by
      have := norm_integral_le_of_norm_le_const (μ := P p) (f := v.toFun) (C := ‖v‖)
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)
      simpa using this⟩⟩

theorem integrable_BM (μ : Measure X) [IsProbabilityMeasure μ] (v : BM X) : Integrable v.toFun μ :=
  Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)

/-- The expectation operator is a certainty equivalent operator. -/
theorem isCEOperator_expectOp (P : Kernel (X × A) X) [IsMarkovKernel P] :
    IsCEOperator (A := A) (expectOp P) := by
  refine ⟨fun v w h p => integral_mono (integrable_BM _ v) (integrable_BM _ w) h,
    fun v κ _ => BM.ext fun p => ?_⟩
  change ∫ x', (v + κ • BM.const 1).toFun x' ∂(P p) = ∫ x', v.toFun x' ∂(P p) + κ * 1
  simp only [BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
  rw [integral_add (integrable_BM _ v) (integrable_const κ), integral_const, probReal_univ,
    one_smul]

/-- (4.21): the expected-utility post-action model. -/
noncomputable def postActionEU (r : BM (X × A)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] : PostAction X A :=
  ⟨r, β, hβ0, hβ1, expectOp P⟩

/-- **Exercise 4.2.5** (p. 142): each `T̂_σ` is a contraction of modulus `β` on `bG`. -/
theorem exercise_4_2_5 [Nonempty X] [Nonempty A] (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (σ : SEPolicy X A) (g g' : BM (X × A)) :
    ‖((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).T σ g -
      ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).T σ g'‖ ≤ β * ‖g - g'‖ :=
  BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one
    (((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).mono σ) hβ0
    ((postActionEU r β hβ0 hβ1 P).blackwell (isCEOperator_expectOp P) σ) g g'

/-- (4.20): the Bellman operator of the expected-utility model is
`(T̂g)(x, a) = ∫ max_{a'} [r(x', a') + βg(x', a')] P(x, a, dx')`. -/
theorem bellman_EU [Fintype A] [Nonempty A] (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (g : BM (X × A)) (p : X × A) :
    (((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).bellman g).toFun p =
      ∫ x', (Finset.univ.sup' Finset.univ_nonempty fun a' =>
        r.toFun (x', a') + β * g.toFun (x', a')) ∂(P p) := by
  let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
  rw [(postActionEU r β hβ0 hβ1 P).adp_bellman (isCEOperator_expectOp P)]
  refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
  refine le_antisymm (Finset.le_sup' (fun a' => r.toFun (x', a') + β * g.toFun (x', a'))
    (Finset.mem_univ _)) (Finset.sup'_le _ _ fun a' _ => ?_)
  exact argmaxSel_max (fun x a => r.toFun (x, a) + β * g.toFun (x, a)) x' a'

/-- **Proposition 4.2.4** (p. 143): for the structural estimation ADP `(bG, 𝕋̂_SE)` the
fundamental optimality properties hold, and VFI, OPI and HPI all converge. -/
theorem proposition_4_2_4 [Nonempty X] [Finite A] [Nonempty A] (r : BM (X × A)) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X) [IsMarkovKernel P] :
    ∃ hw : ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).WellPosed,
      ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).FundamentalOptimality hw ∧
        ∃ gstar, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).VFIGeometric
          univ gstar ∧
          ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).VFIConverges gstar ∧
          ∀ g, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsSelector g →
            ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).OPIConverges g gstar ∧
            ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).HPIConverges hw g
              gstar :=
  (postActionEU r β hβ0 hβ1 P).proposition_4_2_6 (isCEOperator_expectOp P)

/-! ### The risk-sensitive case: §4.2.3.4 -/

/-- The risk-sensitive certainty equivalent `(Mf)(x, a) = −γ⁻¹ ln ∫ exp(−γf(x')) P(x, a, dx')`. -/
noncomputable def riskSensitive (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ} (hγ : γ ≠ 0)
    (f : BM X) : BM (X × A) :=
  ⟨fun p => -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)),
    measurable_const.mul (Real.measurable_log.comp
      (((measurable_const.mul f.measurable').exp).stronglyMeasurable.integral_kernel
        (κ := P)).measurable),
    ⟨‖f‖, fun p => by
      have hb : ∀ x', Real.exp (-|γ| * ‖f‖) ≤ Real.exp (-γ * f.toFun x') ∧
          Real.exp (-γ * f.toFun x') ≤ Real.exp (|γ| * ‖f‖) := fun x' => by
        have h1 := BM.abs_le_norm f x'
        have h2 : |γ * f.toFun x'| ≤ |γ| * ‖f‖ := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        rw [abs_le] at h2
        constructor <;> (apply Real.exp_le_exp.2; linarith)
      have hint : Integrable (fun x' => Real.exp (-γ * f.toFun x')) (P p) :=
        Integrable.of_bound ((measurable_const.mul f.measurable').exp.aestronglyMeasurable)
          (Real.exp (|γ| * ‖f‖)) (Eventually.of_forall fun x' => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x').2)
      have hlo : Real.exp (-|γ| * ‖f‖) ≤ ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) := by
        have := integral_mono (integrable_const (Real.exp (-|γ| * ‖f‖))) hint fun x' => (hb x').1
        simpa using this
      have hhi : ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) ≤ Real.exp (|γ| * ‖f‖) := by
        have := integral_mono hint (integrable_const (Real.exp (|γ| * ‖f‖))) fun x' => (hb x').2
        simpa using this
      have hpos := (Real.exp_pos _).trans_le hlo
      have hlog : |Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p))| ≤ |γ| * ‖f‖ := by
        rw [abs_le]
        constructor
        · have := Real.log_le_log (Real.exp_pos _) hlo
          rw [Real.log_exp] at this
          linarith
        · have := Real.log_le_log hpos hhi
          rwa [Real.log_exp] at this
      rw [abs_mul, abs_neg, abs_inv]
      have hγ' : 0 < |γ| := abs_pos.2 hγ
      rw [inv_mul_le_iff₀ hγ']
      exact hlog⟩⟩

/-- §4.2.3.4: the risk-sensitive operator is a certainty equivalent operator, for any `γ ≠ 0`. -/
theorem isCEOperator_riskSensitive (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ}
    (hγ : γ ≠ 0) : IsCEOperator (A := A) (riskSensitive P hγ) := by
  have hint : ∀ (f : BM X) p, Integrable (fun x' => Real.exp (-γ * f.toFun x')) (P p) :=
    fun f p => Integrable.of_bound ((measurable_const.mul f.measurable').exp.aestronglyMeasurable)
      (Real.exp (|γ| * ‖f‖)) (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have := (abs_le.1 ((abs_mul γ (f.toFun x')).trans_le
          (mul_le_mul_of_nonneg_left (BM.abs_le_norm f x') (abs_nonneg γ)))).1
        linarith)
  have hpos : ∀ (f : BM X) p, 0 < ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) := fun f p =>
    integral_exp_pos (hint f p)
  refine ⟨fun f g hfg p => ?_, fun f κ _ => BM.ext fun p => ?_⟩
  · change -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)) ≤
      -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * g.toFun x') ∂(P p))
    rcases lt_or_gt_of_ne hγ with hneg | hpos'
    · have hle : ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) ≤
          ∫ x', Real.exp (-γ * g.toFun x') ∂(P p) :=
        integral_mono (hint f p) (hint g p) fun x' => Real.exp_le_exp.2 (by nlinarith [hfg x'])
      have := Real.log_le_log (hpos f p) hle
      have hc : 0 < -γ⁻¹ := neg_pos.2 (inv_lt_zero.2 hneg)
      nlinarith
    · have hle : ∫ x', Real.exp (-γ * g.toFun x') ∂(P p) ≤
          ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) :=
        integral_mono (hint g p) (hint f p) fun x' => Real.exp_le_exp.2 (by nlinarith [hfg x'])
      have := Real.log_le_log (hpos g p) hle
      have hc : -γ⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hpos')
      nlinarith
  · change -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * (f + κ • BM.const 1).toFun x') ∂(P p)) =
      -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)) + κ * 1
    have hshift : (fun x' => Real.exp (-γ * (f + κ • BM.const 1).toFun x')) =
        fun x' => Real.exp (-γ * κ) * Real.exp (-γ * f.toFun x') := by
      funext x'
      simp only [BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
      rw [← Real.exp_add]
      ring_nf
    rw [hshift, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (hpos f p).ne',
      Real.log_exp]
    field_simp
    ring

/-- §4.2.3.4 (p. 146): with the risk-sensitive certainty equivalent, Proposition 4.2.6 applies: a
unique solution `g*` of the functional equation exists in `bG`, policies are optimal iff they
choose `σ(x) ∈ argmax_a [r(x, a) + βg*(x, a)]`, and VFI, OPI and HPI converge. -/
theorem riskSensitive_optimality [Nonempty X] [Finite A] [Nonempty A] (r : BM (X × A)) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ hw : ((⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).adp
      (isCEOperator_riskSensitive P hγ)).WellPosed,
      ((⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).adp
        (isCEOperator_riskSensitive P hγ)).FundamentalOptimality hw := by
  obtain ⟨hw, hFO, -⟩ := (⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).proposition_4_2_6
    (isCEOperator_riskSensitive P hγ)
  exact ⟨hw, hFO⟩

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Isomorphic and anti-isomorphic ADPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.2 (pp. 151–157).

* Isomorphic ADPs (§5.1.2.1): the same policy set and `F ∘ T_σ = T̂_σ ∘ F` (5.1) for an order
  isomorphism `F`. **Example 5.1.4** (the exponential transformation of the savings problem) and
  **Lemma 5.1.4** / **Exercise 5.1.4** (an equivalence relation).
* §5.1.2.2: **Theorem 5.1.5** (greedy policies, regularity, well-posedness, order stability and
  optimal policies transfer), **Theorem 5.1.6** (Bellman operators are conjugate, `v̂* = Fv*`,
  the fundamental optimality properties transfer) and **Theorem 5.1.7** / **Exercise 5.1.5**
  ((5.5), (5.6) and convergence of VFI, OPI and HPI transfer).
* §5.1.2.3: anti-isomorphic ADPs. **Exercise 5.1.6** (anti-isomorphic iff isomorphic to the
  dual), **Theorem 5.1.8**, **Theorem 5.1.9** / **Exercise 5.1.7** and **Theorem 5.1.10** /
  **Exercise 5.1.8**: maximization in one ADP is minimization in the other.

OPI and HPI are run with a greedy *selector* `g`; a selector `g` of `(V, 𝕋)` corresponds to the
selector `g ∘ F⁻¹` of `(V̂, 𝕋̂)`.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace ADP

variable {V W U P : Type*} [PartialOrder V] [PartialOrder W] [PartialOrder U]

/-- `(V, 𝕋)` and `(V̂, 𝕋̂)` are isomorphic under the order isomorphism `F` (§5.1.2.1): they share
the policy set and `F ∘ T_σ = T̂_σ ∘ F` for every `σ` (5.1). -/
def IsIsomorphic (A : ADP V P) (B : ADP W P) (F : V ≃o W) : Prop :=
  ∀ σ, IsOrderConjugate F (A.T σ) (B.T σ)

/-- **Lemma 5.1.4** (p. 152) and **Exercise 5.1.4**: isomorphism is reflexive, … -/
theorem IsIsomorphic.refl (A : ADP V P) : A.IsIsomorphic A (OrderIso.refl V) := fun _ _ => rfl

/-- … symmetric, … -/
theorem IsIsomorphic.symm {A : ADP V P} {B : ADP W P} {F : V ≃o W} (h : A.IsIsomorphic B F) :
    B.IsIsomorphic A F.symm := fun σ => (h σ).symm

/-- … and transitive. -/
theorem IsIsomorphic.trans {A : ADP V P} {B : ADP W P} {C : ADP U P} {F : V ≃o W} {G : W ≃o U}
    (h : A.IsIsomorphic B F) (h' : B.IsIsomorphic C G) : A.IsIsomorphic C (F.trans G) :=
  fun σ => (h σ).trans (h' σ)

namespace IsIsomorphic

variable {A : ADP V P} {B : ADP W P} {F : V ≃o W}

theorem T_apply (h : A.IsIsomorphic B F) (σ : P) (v : V) : F (A.T σ v) = B.T σ (F v) := h σ v

theorem range_T (h : A.IsIsomorphic B F) (v : V) :
    range (fun σ => B.T σ (F v)) = F '' range fun σ => A.T σ v := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun σ => (h σ v).symm)

theorem isBellmanValue_iff (h : A.IsIsomorphic B F) (v w : V) :
    A.IsBellmanValue v w ↔ B.IsBellmanValue (F v) (F w) := by
  unfold IsBellmanValue
  rw [h.range_T]
  exact (F.isLUB_image' (s := range fun σ => A.T σ v)).symm

theorem solvesBellman_iff (h : A.IsIsomorphic B F) (v : V) :
    A.SolvesBellman v ↔ B.SolvesBellman (F v) :=
  h.isBellmanValue_iff v v

/-- **Theorem 5.1.5 (i)** (p. 153): `σ` is `v`-greedy for `(V, 𝕋)` iff it is `Fv`-greedy for
`(V̂, 𝕋̂)`. -/
theorem isGreedy_iff (h : A.IsIsomorphic B F) (v : V) (σ : P) :
    A.IsGreedy v σ ↔ B.IsGreedy (F v) σ := by
  refine forall_congr' fun τ => ?_
  rw [← h.T_apply, ← h.T_apply]
  exact F.le_iff_le.symm

theorem mem_VG_iff (h : A.IsIsomorphic B F) (v : V) : v ∈ A.VG ↔ F v ∈ B.VG :=
  exists_congr fun σ => h.isGreedy_iff v σ

/-- **Theorem 5.1.5 (ii)**: `(V, 𝕋)` is regular iff `(V̂, 𝕋̂)` is. -/
theorem regular_iff (h : A.IsIsomorphic B F) : A.Regular ↔ B.Regular := by
  refine ⟨fun hr w => ?_, fun hr v => (h.mem_VG_iff v).2 (hr (F v))⟩
  rw [← F.apply_symm_apply w]
  exact (h.mem_VG_iff _).1 (hr _)

/-- **Theorem 5.1.5 (iii)**: `(V, 𝕋)` is well-posed iff `(V̂, 𝕋̂)` is. -/
theorem wellPosed_iff (h : A.IsIsomorphic B F) : A.WellPosed ↔ B.WellPosed := by
  refine forall_congr' fun σ => ?_
  have hc : IsConjugate F.toEquiv (A.T σ) (B.T σ) := h σ
  constructor
  · rintro ⟨v, hv, huniq⟩
    refine ⟨F v, (hc.fixed_iff v).1 hv, fun w hw => ?_⟩
    rw [← huniq _ ((hc.fixed_iff_symm w).1 hw)]
    exact (F.apply_symm_apply w).symm
  · rintro ⟨w, hw, huniq⟩
    refine ⟨F.symm w, (hc.fixed_iff_symm w).1 hw, fun v hv => ?_⟩
    rw [← huniq _ ((hc.fixed_iff v).1 hv)]
    exact (F.symm_apply_apply v).symm

/-- The `σ`-value functions are linked by `F v_σ = v̂_σ`. -/
theorem vσ_eq (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (σ : P) :
    F (A.vσ hw σ) = B.vσ hw' σ :=
  eq_vσ hw' (by rw [← h.T_apply, T_vσ])

theorem VSig_eq (h : A.IsIsomorphic B F) : B.VSig = F '' A.VSig := by
  ext w
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨F.symm w, ⟨σ, ?_⟩, F.apply_symm_apply w⟩
    apply F.injective
    rw [h.T_apply, F.apply_symm_apply, hσ]
  · rintro ⟨v, ⟨σ, hσ⟩, rfl⟩
    exact ⟨σ, by rw [← h.T_apply, hσ]⟩

/-- **Theorem 5.1.6 (ii)** (p. 154): `v̂* = Fv*`. -/
theorem isValueFunction_iff (h : A.IsIsomorphic B F) (v : V) :
    A.IsValueFunction v ↔ B.IsValueFunction (F v) := by
  unfold IsValueFunction
  rw [h.VSig_eq]
  exact (F.isLUB_image' (s := A.VSig)).symm

/-- **Theorem 5.1.5 (v)**: `σ` is optimal for `(V, 𝕋)` iff it is optimal for `(V̂, 𝕋̂)`. -/
theorem isOptimal_iff (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (σ : P) :
    A.IsOptimal hw σ ↔ B.IsOptimal hw' σ := by
  unfold IsOptimal
  rw [← h.vσ_eq hw hw' σ, h.VSig_eq]
  constructor
  · rintro ⟨ha, hup⟩
    exact ⟨⟨_, ha, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact F.monotone (hup hx)⟩
  · rintro ⟨⟨b, hb, hba⟩, hup⟩
    exact ⟨F.injective hba ▸ hb, fun x hx => F.le_iff_le.1 (hup ⟨x, hx, rfl⟩)⟩

theorem orderStable_iff (h : A.IsIsomorphic B F) : A.IsOrderStable ↔ B.IsOrderStable :=
  forall_congr' fun σ => (IsOrderConjugate.lemma_5_1_3 (h σ)).1

theorem stronglyOrderStable_iff (h : A.IsIsomorphic B F) :
    A.IsStronglyOrderStable ↔ B.IsStronglyOrderStable :=
  forall_congr' fun σ => (IsOrderConjugate.lemma_5_1_3 (h σ)).2

/-- **Theorem 5.1.6 (i)** (5.4): `F ∘ T = T̂ ∘ F` at every `v ∈ V_G`. -/
theorem bellman_eq (h : A.IsIsomorphic B F) {v : V} (hv : v ∈ A.VG) :
    F (A.bellman v) = B.bellman (F v) := by
  have hg := A.isGreedy_greedy hv
  have hg' := (h.isGreedy_iff v _).1 hg
  rw [← (B.isGreedy_iff ((h.mem_VG_iff v).1 hv) _).1 hg']
  exact h.T_apply _ v

theorem bellmanPrinciple (h : A.IsIsomorphic B F) {hw : A.WellPosed} {hw' : B.WellPosed}
    (hb : A.BellmanPrinciple hw) : B.BellmanPrinciple hw' := by
  intro σ
  rw [← h.isOptimal_iff hw hw' σ, hb σ]
  constructor
  · rintro ⟨v, hv, hg⟩
    exact ⟨F v, (h.isValueFunction_iff v).1 hv, (h.isGreedy_iff v σ).1 hg⟩
  · rintro ⟨w, hv, hg⟩
    refine ⟨F.symm w, (h.isValueFunction_iff _).2 ?_, (h.isGreedy_iff _ σ).2 ?_⟩
    · rwa [F.apply_symm_apply]
    · rwa [F.apply_symm_apply]

theorem fundamentalOptimality (h : A.IsIsomorphic B F) {hw : A.WellPosed} {hw' : B.WellPosed}
    (hfo : A.FundamentalOptimality hw) : B.FundamentalOptimality hw' := by
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, hvG, hb, huniq⟩, hbp⟩ := hfo
  refine ⟨⟨σ, (h.isOptimal_iff hw hw' σ).1 hσ⟩, ⟨F v, (h.isValueFunction_iff v).1 hv,
    (h.mem_VG_iff v).1 hvG, (h.solvesBellman_iff v).1 hb, fun w hwG hwb => ?_⟩,
    h.bellmanPrinciple hbp⟩
  rw [← F.apply_symm_apply w]
  refine congrArg F (huniq _ ?_ ?_)
  · rw [h.mem_VG_iff, F.apply_symm_apply]; exact hwG
  · rw [h.solvesBellman_iff, F.apply_symm_apply]; exact hwb

/-- **Theorem 5.1.6 (iii)**: the fundamental optimality properties hold for `(V, 𝕋)` iff they hold
for `(V̂, 𝕋̂)`. -/
theorem fundamentalOptimality_iff (h : A.IsIsomorphic B F) (hw : A.WellPosed)
    (hw' : B.WellPosed) : A.FundamentalOptimality hw ↔ B.FundamentalOptimality hw' :=
  ⟨h.fundamentalOptimality, h.symm.fundamentalOptimality⟩

theorem mem_VU_iff (h : A.IsIsomorphic B F) (v : V) : v ∈ A.VU ↔ F v ∈ B.VU := by
  constructor
  · rintro ⟨hvG, hle⟩
    refine ⟨(h.mem_VG_iff v).1 hvG, ?_⟩
    rw [← h.bellman_eq hvG]
    exact F.monotone hle
  · rintro ⟨hvG, hle⟩
    have hvG' := (h.mem_VG_iff v).2 hvG
    refine ⟨hvG', ?_⟩
    rw [← h.bellman_eq hvG'] at hle
    exact F.le_iff_le.1 hle

theorem isSelector_iff (h : A.IsIsomorphic B F) (g : V → P) :
    A.IsSelector g ↔ B.IsSelector (g ∘ F.symm) := by
  refine ⟨fun hg w => ?_, fun hg v => ?_⟩
  · have := (h.isGreedy_iff (F.symm w) (g (F.symm w))).1 (hg _)
    rwa [F.apply_symm_apply] at this
  · have := hg (F v)
    simp only [Function.comp_apply, F.symm_apply_apply] at this
    exact (h.isGreedy_iff v _).2 this

/-- **Theorem 5.1.7 (i)** (5.5): `F ∘ W = Ŵ ∘ F`, with the selector `g` of `(V, 𝕋)` read as the
selector `g ∘ F⁻¹` of `(V̂, 𝕋̂)`. -/
theorem opt_eq (h : A.IsIsomorphic B F) (m : ℕ) (g : V → P) :
    Semiconj F (A.opt m g) (B.opt m (g ∘ F.symm)) := fun v => by
  change F ((A.T (g v))^[m] v) = (B.T (g (F.symm (F v))))^[m] (F v)
  rw [F.symm_apply_apply]
  exact (Semiconj.iterate_right (h (g v)) m) v

/-- **Theorem 5.1.7 (ii)** (5.6): `F ∘ H = Ĥ ∘ F`. -/
theorem howard_eq (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (g : V → P) :
    Semiconj F (A.howard hw g) (B.howard hw' (g ∘ F.symm)) := fun v => by
  change F (A.vσ hw (g v)) = B.vσ hw' (g (F.symm (F v)))
  rw [F.symm_apply_apply]
  exact h.vσ_eq hw hw' _

theorem bellman_semiconj (h : A.IsIsomorphic B F) (hr : A.Regular) :
    Semiconj F A.bellman B.bellman := fun v => h.bellman_eq (hr v)

theorem vfiConverges (h : A.IsIsomorphic B F) (hr : A.Regular) {vstar : V}
    (hv : A.VFIConverges vstar) : B.VFIConverges (F vstar) := by
  intro w hw
  have hw' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hw
  have := orderIso_increasesTo F (hv _ hw')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.bellman_semiconj hr) n) (F.symm w), F.apply_symm_apply]

theorem opiConverges (h : A.IsIsomorphic B F) {vstar : V}
    (hv : ∀ g, A.IsSelector g → A.OPIConverges g vstar) :
    ∀ g, B.IsSelector g → B.OPIConverges g (F vstar) := by
  intro g' hg' m hm w hw
  have hg : A.IsSelector (g' ∘ F) := by
    rw [h.isSelector_iff]
    convert hg' using 1
    funext w; simp
  have hw' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hw
  have := orderIso_increasesTo F (hv _ hg m hm _ hw')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.opt_eq m _) n) (F.symm w), F.apply_symm_apply]
  congr 2
  funext w; simp

theorem hpiConverges (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) {vstar : V}
    (hv : ∀ g, A.IsSelector g → A.HPIConverges hw g vstar) :
    ∀ g, B.IsSelector g → B.HPIConverges hw' g (F vstar) := by
  intro g' hg' w hwU
  have hg : A.IsSelector (g' ∘ F) := by
    rw [h.isSelector_iff]
    convert hg' using 1
    funext w; simp
  have hwU' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hwU
  have := orderIso_increasesTo F (hv _ hg _ hwU')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.howard_eq hw hw' _) n) (F.symm w), F.apply_symm_apply]
  congr 2
  funext w; simp

end IsIsomorphic

variable {A : ADP V P} {B : ADP W P} {F : V ≃o W}

/-- **Theorem 5.1.5** (p. 153): if `(V, 𝕋)` and `(V̂, 𝕋̂)` are isomorphic under `F`, then (i) `σ`
is `v`-greedy iff it is `Fv`-greedy, (ii) regularity, (iii) well-posedness and (iv) order
stability transfer, and (v) the optimal policies coincide. -/
theorem theorem_5_1_5 (h : A.IsIsomorphic B F) :
    (∀ v σ, A.IsGreedy v σ ↔ B.IsGreedy (F v) σ) ∧ (A.Regular ↔ B.Regular) ∧
      (A.WellPosed ↔ B.WellPosed) ∧ (A.IsOrderStable ↔ B.IsOrderStable) ∧
      ∀ (hw : A.WellPosed) (hw' : B.WellPosed) σ, A.IsOptimal hw σ ↔ B.IsOptimal hw' σ :=
  ⟨h.isGreedy_iff, h.regular_iff, h.wellPosed_iff, h.orderStable_iff, h.isOptimal_iff⟩

/-- **Theorem 5.1.6** (p. 153): for regular, well-posed isomorphic ADPs, (i) `F ∘ T = T̂ ∘ F`
(5.4), (ii) `v̂* = Fv*` and (iii) the fundamental optimality properties transfer. -/
theorem theorem_5_1_6 (h : A.IsIsomorphic B F) (hr : A.Regular) (hw : A.WellPosed)
    (hw' : B.WellPosed) :
    Semiconj F A.bellman B.bellman ∧ (∀ v, A.IsValueFunction v → B.IsValueFunction (F v)) ∧
      (A.FundamentalOptimality hw ↔ B.FundamentalOptimality hw') :=
  ⟨h.bellman_semiconj hr, fun v => (h.isValueFunction_iff v).1, h.fundamentalOptimality_iff hw hw'⟩

/-- **Theorem 5.1.7** (p. 154) and **Exercise 5.1.5**: for regular, well-posed isomorphic ADPs,
(i) `F ∘ W = Ŵ ∘ F` (5.5), (ii) `F ∘ H = Ĥ ∘ F` (5.6), and (iii) VFI, (iv) OPI and (v) HPI
converge for `(V, 𝕋)` iff they converge for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_7 (h : A.IsIsomorphic B F) (hr : A.Regular) (hw : A.WellPosed)
    (hw' : B.WellPosed) (vstar : V) :
    (∀ m g, Semiconj F (A.opt m g) (B.opt m (g ∘ F.symm))) ∧
      (∀ g, Semiconj F (A.howard hw g) (B.howard hw' (g ∘ F.symm))) ∧
      (A.VFIConverges vstar ↔ B.VFIConverges (F vstar)) ∧
      ((∀ g, A.IsSelector g → A.OPIConverges g vstar) ↔
        ∀ g, B.IsSelector g → B.OPIConverges g (F vstar)) ∧
      ((∀ g, A.IsSelector g → A.HPIConverges hw g vstar) ↔
        ∀ g, B.IsSelector g → B.HPIConverges hw' g (F vstar)) := by
  have hr' := h.regular_iff.1 hr
  refine ⟨h.opt_eq, h.howard_eq hw hw', ⟨h.vfiConverges hr, fun hv => ?_⟩,
    ⟨h.opiConverges, fun hv => ?_⟩, ⟨h.hpiConverges hw hw', fun hv => ?_⟩⟩
  · simpa using h.symm.vfiConverges hr' hv
  · simpa using h.symm.opiConverges hv
  · simpa using h.symm.hpiConverges hw' hw hv

/-! ### Example 5.1.4 -/

/-- The additive savings ADP (5.2), `(T_σ v)(w) = u(σ(w)) + βv(w − σ(w))`, on `ℝ^ℝ`. -/
def savingsAdd (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) : ADP (ℝ → ℝ) (ℝ → ℝ) where
  T σ v w := u (σ w) + β * v (w - σ w)
  mono _ _ _ h _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (h _) hβ)
  nonempty := ⟨id⟩

/-- The multiplicative savings ADP (5.3), `(T̂_σ v̂)(w) = û(σ(w)) v̂(w − σ(w))^β` with
`û = exp ∘ u`, on positive functions. -/
noncomputable def savingsMul (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    ADP (ℝ → Ioi (0 : ℝ)) (ℝ → ℝ) where
  T σ v w := ⟨Real.exp (u (σ w)) * (v (w - σ w) : ℝ) ^ β,
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (v (w - σ w)).2 β)⟩
  mono _ _ _ h _ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_of_lt (Subtype.prop _)) (h _) hβ) (Real.exp_pos _).le
  nonempty := ⟨id⟩

/-- `v ↦ exp ∘ v`, an order isomorphism from `ℝ^Z` onto the positive functions
(Exercise A.1.10). -/
noncomputable def expPi (Z : Type*) : (Z → ℝ) ≃o (Z → Ioi (0 : ℝ)) where
  toEquiv := Equiv.piCongrRight fun _ => Real.expOrderIso.toEquiv
  map_rel_iff' {v w} := by
    change (∀ z, Real.expOrderIso (v z) ≤ Real.expOrderIso (w z)) ↔ ∀ z, v z ≤ w z
    exact forall_congr' fun z => Real.expOrderIso.le_iff_le

/-- **Example 5.1.4** (p. 152): `F v = exp ∘ v` makes the additive and multiplicative savings
ADPs isomorphic. -/
theorem example_5_1_4 (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    (savingsAdd u hβ).IsIsomorphic (savingsMul u hβ)
      (expPi ℝ) := fun σ v => by
  funext w
  apply Subtype.ext
  change Real.exp (u (σ w) + β * v (w - σ w)) = Real.exp (u (σ w)) * Real.exp (v (w - σ w)) ^ β
  rw [Real.exp_add, ← Real.exp_mul, mul_comm β]

/-! ### Anti-isomorphic ADPs -/

/-- `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F` (§5.1.2.3): `F` is an order
anti-isomorphism (an order isomorphism onto `V̂^∂`) and `F ∘ T_σ = T̂_σ ∘ F` (5.1). -/
def IsAntiIsomorphic (A : ADP V P) (B : ADP W P) (F : V ≃o Wᵒᵈ) : Prop :=
  ∀ σ v, OrderDual.ofDual (F (A.T σ v)) = B.T σ (OrderDual.ofDual (F v))

/-- **Exercise 5.1.6** (p. 155): `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F` iff `(V, 𝕋)`
and `(V̂, 𝕋̂)^∂` are isomorphic under `F`. -/
theorem exercise_5_1_6 (F : V ≃o Wᵒᵈ) : A.IsAntiIsomorphic B F ↔ A.IsIsomorphic B.dual F :=
  ⟨fun h σ v => congrArg OrderDual.toDual (h σ v), fun h σ v => congrArg OrderDual.ofDual (h σ v)⟩

namespace IsAntiIsomorphic

variable {F : V ≃o Wᵒᵈ}

theorem iso (h : A.IsAntiIsomorphic B F) : A.IsIsomorphic B.dual F := (exercise_5_1_6 F).1 h

theorem orderStable_iff (h : A.IsAntiIsomorphic B F) : A.IsOrderStable ↔ B.IsOrderStable :=
  h.iso.orderStable_iff.trans (forall_congr' fun σ => orderStable_dual_iff (B.T σ))

theorem minSelector_iff (h : A.IsAntiIsomorphic B F) (g : V → P) :
    A.IsSelector g ↔ B.IsMinSelector (g ∘ F.symm ∘ OrderDual.toDual) := by
  rw [h.iso.isSelector_iff, B.isMinSelector_iff]
  rfl

end IsAntiIsomorphic

/-- **Theorem 5.1.8** (p. 155): if `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F`, then (i)
`σ` is `v`-max-greedy iff it is `Fv`-min-greedy, (ii) max-regularity of `(V, 𝕋)` is
min-regularity of `(V̂, 𝕋̂)`, (iii) well-posedness and (iv) order stability transfer, and (v)
max-optimal policies of `(V, 𝕋)` are the min-optimal policies of `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_8 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) :
    (∀ v σ, A.IsGreedy v σ ↔ B.IsMinGreedy (OrderDual.ofDual (F v)) σ) ∧
      (A.Regular ↔ B.MinRegular) ∧ (A.WellPosed ↔ B.WellPosed) ∧
      (A.IsOrderStable ↔ B.IsOrderStable) ∧
      ∀ (hw : A.WellPosed) (hw' : B.WellPosed) σ, A.IsOptimal hw σ ↔ B.IsMinOptimal hw' σ :=
  ⟨fun v σ => (h.iso.isGreedy_iff v σ).trans (B.isMinGreedy_iff _ σ).symm,
    h.iso.regular_iff.trans (B.minRegular_iff).symm, h.iso.wellPosed_iff, h.orderStable_iff,
    fun hw hw' σ => (h.iso.isOptimal_iff hw hw'.dual σ).trans (B.isMinOptimal_iff hw' σ).symm⟩

/-- **Theorem 5.1.9** (p. 156) and **Exercise 5.1.7**: for anti-isomorphic, well-posed ADPs with
`(V, 𝕋)` max-regular, (i) `F ∘ T = T̂▿ ∘ F` (5.7), the min-Bellman operator `T̂▿` being the
Bellman operator of `(V̂, 𝕋̂)^∂`, (ii) `v̂▿* = Fv*`, and (iii) the fundamental max-optimality
properties hold for `(V, 𝕋)` iff the fundamental min-optimality properties hold for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_9 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) (hr : A.Regular)
    (hw : A.WellPosed) (hw' : B.WellPosed) :
    Semiconj F A.bellman B.dual.bellman ∧
      (∀ v, A.IsValueFunction v → B.IsMinValueFunction (OrderDual.ofDual (F v))) ∧
      (A.FundamentalOptimality hw ↔ B.MinFundamentalOptimality hw') :=
  ⟨h.iso.bellman_semiconj hr, fun v hv => (h.iso.isValueFunction_iff v).1 hv,
    (h.iso.fundamentalOptimality_iff hw hw'.dual).trans (B.minFundamentalOptimality_iff hw').symm⟩

/-- **Theorem 5.1.10** (p. 156) and **Exercise 5.1.8**: for anti-isomorphic, well-posed ADPs with
`(V, 𝕋)` max-regular, (i) `F ∘ W = Ŵ▿ ∘ F` (5.8), (ii) `F ∘ H = Ĥ▿ ∘ F` (5.9), and (iii)
max-VFI, (iv) max-OPI and (v) max-HPI converge for `(V, 𝕋)` iff min-VFI, min-OPI and min-HPI
converge for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_10 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) (hr : A.Regular)
    (hw : A.WellPosed) (hw' : B.WellPosed) (vstar : V) :
    (∀ m g, Semiconj F (A.opt m g) (B.dual.opt m (g ∘ F.symm))) ∧
      (∀ g, Semiconj F (A.howard hw g) (B.dual.howard hw'.dual (g ∘ F.symm))) ∧
      (A.VFIConverges vstar ↔ B.MinVFIConverges (OrderDual.ofDual (F vstar))) ∧
      ((∀ g, A.IsSelector g → A.OPIConverges g vstar) ↔
        ∀ g, B.IsMinSelector g → B.MinOPIConverges g (OrderDual.ofDual (F vstar))) ∧
      ((∀ g, A.IsSelector g → A.HPIConverges hw g vstar) ↔
        ∀ g, B.IsMinSelector g → B.MinHPIConverges hw' g (OrderDual.ofDual (F vstar))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_5_1_7 h.iso hr hw hw'.dual vstar
  refine ⟨h1, h2, h3.trans (B.minVFIConverges_iff _).symm, h4.trans ?_, h5.trans ?_⟩
  · constructor
    · intro hv g hg
      exact (B.minOPIConverges_iff g _).2 (hv _ ((B.isMinSelector_iff g).1 hg))
    · intro hv g hg
      have := (B.minOPIConverges_iff (g ∘ OrderDual.toDual) _).1
        (hv _ ((B.isMinSelector_iff _).2 hg))
      exact this
  · constructor
    · intro hv g hg
      exact (B.minHPIConverges_iff hw' g _).2 (hv _ ((B.isMinSelector_iff g).1 hg))
    · intro hv g hg
      have := (B.minHPIConverges_iff hw' (g ∘ OrderDual.toDual) _).1
        (hv _ ((B.isMinSelector_iff _).2 hg))
      exact this

end ADP

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

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

namespace SargentStachurski.ADPTransformations

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

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Q-factors as a factored dynamic program

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.1 (pp. 174–176).

With `(Fv)(x, a) = r(x, a) + β ∑_{x'} v(x')P(x, a, x')` (5.27) and `(G_σ f)(x) = f(x, σ(x))`,
the finite MDP and its Q-factor model are the primary and subordinate ADPs of one
order-preserving FDP (`qfdp_primary`, `qfdp_sub`).

* **Proposition 5.3.1**: `v*(x) = max_{a ∈ Γ(x)} q*(x, a)` and `q* = r + βPv*`; MDP-optimal
  policies are Q-optimal; `σ` is MDP-optimal when it maximizes `q*(x, ·)` at every state.
* **Proposition 5.3.2**: if no state is isolated under `P` and `β > 0`, Q-optimal policies are
  MDP-optimal. The book allows `β ∈ [0, 1)` for MDPs; at `β = 0` the claim fails
  (`proposition_5_3_2_needs_beta_pos`).
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- The Q-factor FDP `(ℝ^X, F, ℝ^G, 𝔾)` of a finite MDP (§5.3.1). -/
def qfdp : FDP (X → ℝ) (M.G → ℝ) M.Policy where
  F v p := M.Q v p.1.1 p.1.2
  G σ f x := f (M.pairOf σ x)
  greatest f := by
    obtain ⟨σ, hσ⟩ := M.exists_qgreedy f
    exact ⟨σ, fun τ x => hσ x (τ.1 x) (τ.2 x)⟩
  nonempty := M.nonempty_policy

theorem qfdp_isOrderPreserving : M.qfdp.IsOrderPreserving :=
  ⟨fun _ _ h p => M.Q_mono p.2 h, fun _ _ _ h _ => h _⟩

theorem qfdp_monotonic : M.qfdp.Monotonic := Or.inl M.qfdp_isOrderPreserving

/-- The primary ADP of the Q-factor FDP is the MDP ADP. -/
theorem qfdp_primary : M.qfdp.primary M.qfdp_monotonic = M.adp := rfl

/-- The subordinate ADP of the Q-factor FDP is the Q-factor ADP (3.6). -/
theorem qfdp_sub : M.qfdp.sub M.qfdp_monotonic = M.qadp := rfl

/-- `Gq` picks the maximum of `q(x, ·)` over `Γ(x)`. -/
theorem le_Gsup (q : M.G → ℝ) (x : X) (a : A) (ha : a ∈ M.Γ x) :
    q ⟨(x, a), ha⟩ ≤ M.qfdp.Gsup q x := by
  classical
  let σ₀ := M.qfdp.gsel q
  let τ : M.Policy := ⟨Function.update σ₀.1 x a, fun y => by
    rcases eq_or_ne y x with rfl | hy
    · rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne hy]; exact σ₀.2 y⟩
  have h := M.qfdp.G_le_Gsup τ q x
  have hτ : M.pairOf τ x = ⟨(x, a), ha⟩ := Subtype.ext (by simp [pairOf, τ])
  change q (M.pairOf τ x) ≤ _ at h
  rwa [hτ] at h

theorem Gsup_eq_sup (q : M.G → ℝ) (x : X) :
    M.qfdp.Gsup q x = (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach)
      (fun a => q ⟨(x, a.1), a.2⟩) := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun a _ => M.le_Gsup q x a.1 a.2)
  exact Finset.le_sup' (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩)
    (Finset.mem_attach _ ⟨(M.qfdp.gsel q).1 x, (M.qfdp.gsel q).2 x⟩)

/-- **Proposition 5.3.1** (p. 175): for the MDP and its Q-factor model, (i)
`v*(x) = max_{a ∈ Γ(x)} q*(x, a)` and `q*(x, a) = r(x, a) + β ∑_{x'} v*(x')P(x, a, x')`, (ii)
MDP-optimal policies are Q-optimal, and (iii) `σ` is MDP-optimal whenever
`q*(x, σ(x)) = max_{a ∈ Γ(x)} q*(x, a)` at every `x`. -/
theorem proposition_5_3_1 :
    (∀ v q, M.adp.IsValueFunction v → M.qadp.IsValueFunction q →
      (∀ x, v x = (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach) (fun a => q ⟨(x, a.1), a.2⟩)) ∧
      ∀ x a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ = M.r x a + M.β * ∑ x', v x' * M.P x a x') ∧
    (∀ σ, M.adp.IsOptimal M.adp_wellPosed σ →
      M.qadp.IsOptimal M.qadp_isGloballyStable.wellPosed σ) ∧
    ∀ q σ, M.qadp.IsValueFunction q → (∀ x a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤
      q (M.pairOf σ x)) → M.adp.IsOptimal M.adp_wellPosed σ := by
  have hfo : M.adp.FundamentalOptimality M.adp_wellPosed := M.section_3_2_1_1.1
  obtain ⟨hi, hii, hiii⟩ := (FDP.theorem_5_2_13 M.qfdp_monotonic M.qfdp_isOrderPreserving
    M.adp_wellPosed M.qadp_isGloballyStable.wellPosed).2 hfo
  refine ⟨fun v q hv hq => ?_, hiii, fun q σ hq hσ => hii q σ hq ?_⟩
  · obtain ⟨e1, e2⟩ := hi v q hv hq
    refine ⟨fun x => ?_, fun x a ha => ?_⟩
    · rw [e1, ← M.Gsup_eq_sup]
    · rw [e2]
      rfl
  · funext x
    exact le_antisymm (M.qfdp.G_le_Gsup σ q x) (by
      rw [M.Gsup_eq_sup]
      exact Finset.sup'_le _ _ fun a _ => hσ x a.1 a.2)

/-- With `β > 0` and no isolated state, `F` in (5.27) is strictly order preserving
(Example A.1.12). -/
theorem qfdp_F_strictMono (hβ : 0 < M.β) (hiso : ∀ x', ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x') :
    StrictMono M.qfdp.F := by
  intro u v huv
  refine lt_of_le_of_ne (M.qfdp_isOrderPreserving.1 huv.le) fun heq => ?_
  obtain ⟨x', hx'⟩ : ∃ x', u x' < v x' := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact huv.ne (le_antisymm huv.le hcon)
  obtain ⟨p, hp⟩ := hiso x'
  have h := congrFun heq p
  change M.Q u p.1.1 p.1.2 = M.Q v p.1.1 p.1.2 at h
  have hlt : ∑ y, u y * M.P p.1.1 p.1.2 y < ∑ y, v y * M.P p.1.1 p.1.2 y :=
    Finset.sum_lt_sum (fun y _ => mul_le_mul_of_nonneg_right (huv.le y) (M.P_nonneg _ _ p.2 y))
      ⟨x', Finset.mem_univ _, mul_lt_mul_of_pos_right hx' hp⟩
  simp only [Q] at h
  linarith [mul_lt_mul_of_pos_left hlt hβ]

/-- **Proposition 5.3.2** (p. 176): if `β > 0` and no state is isolated under `P` (every `x'` has
`P(x, a, x') > 0` for some feasible `(x, a)`), every Q-optimal policy is MDP-optimal. -/
theorem proposition_5_3_2 (hβ : 0 < M.β) (hiso : ∀ x', ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x')
    (σ : M.Policy) (hσ : M.qadp.IsOptimal M.qadp_isGloballyStable.wellPosed σ) :
    M.adp.IsOptimal M.adp_wellPosed σ :=
  (FDP.proposition_5_2_14 M.qfdp_monotonic M.qfdp_isOrderPreserving
    (M.qfdp_F_strictMono hβ hiso) M.adp_wellPosed M.qadp_isGloballyStable.wellPosed
    M.exercise_3_2_6.1).2 σ hσ

end FiniteMDP

/-- A one-state MDP with actions `Bool`, `r(·, b) = 1` if `b` else `0`, `β = 0`. -/
def zeroDiscountMDP : FiniteMDP Unit Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  r _ b := if b then 1 else 0
  β := 0
  β_nonneg := le_rfl
  β_lt_one := zero_lt_one
  P _ _ _ := 1
  P_nonneg _ _ _ _ := zero_le_one
  P_sum _ _ _ := by simp

/-- **Proposition 5.3.2 needs `β > 0`.** For `zeroDiscountMDP` (`β = 0`, no isolated state), the
policy choosing `false` is optimal for the Q-factor model, since `S_σ q = r` for every `σ`, but
not for the MDP, whose `true` policy earns `1 > 0`. -/
theorem proposition_5_3_2_needs_beta_pos :
    (∀ x', ∃ p : zeroDiscountMDP.G, 0 < zeroDiscountMDP.P p.1.1 p.1.2 x') ∧
      zeroDiscountMDP.qadp.IsOptimal zeroDiscountMDP.qadp_isGloballyStable.wellPosed
        ⟨fun _ => false, fun _ => Finset.mem_univ _⟩ ∧
      ¬ zeroDiscountMDP.adp.IsOptimal zeroDiscountMDP.adp_wellPosed
        ⟨fun _ => false, fun _ => Finset.mem_univ _⟩ := by
  have hrq : ∀ σ : zeroDiscountMDP.Policy,
      zeroDiscountMDP.qadp.vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed σ =
        fun p => zeroDiscountMDP.r p.1.1 p.1.2 := fun σ => by
    refine (ADP.eq_vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed (funext fun p => ?_)).symm
    simp [FiniteMDP.qadp, FiniteMDP.Sσ, zeroDiscountMDP]
  have hrv : ∀ σ : zeroDiscountMDP.Policy, zeroDiscountMDP.adp.vσ zeroDiscountMDP.adp_wellPosed σ =
      fun x => zeroDiscountMDP.r x (σ.1 x) := fun σ => by
    refine (ADP.eq_vσ zeroDiscountMDP.adp_wellPosed (funext fun x => ?_)).symm
    simp [FiniteMDP.adp, FiniteMDP.Tσ, FiniteMDP.Q, zeroDiscountMDP]
  refine ⟨fun _ => ⟨⟨((), true), Finset.mem_univ _⟩, by simp [zeroDiscountMDP]⟩, ?_, ?_⟩
  · refine ⟨⟨_, ADP.T_vσ _ _⟩, ?_⟩
    rintro _ ⟨τ, hτ⟩
    rw [ADP.eq_vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed hτ]
    exact le_of_eq ((hrq τ).trans (hrq _).symm)
  · rintro ⟨-, hup⟩
    have h := hup ⟨⟨fun _ => true, fun _ => Finset.mem_univ _⟩,
      ADP.T_vσ zeroDiscountMDP.adp_wellPosed _⟩
    have e1 := hrv ⟨fun _ => true, fun _ => Finset.mem_univ _⟩
    have e2 := hrv ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
    have h2 := (le_of_eq e1.symm).trans (h.trans (le_of_eq e2))
    have := h2 ()
    simp only [zeroDiscountMDP, ite_true] at this
    norm_num at this

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Structural estimation via transforms

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.2 (pp. 176–178).

With `(Fv)(x, a) = ∫ v(x')P(x, a, dx')` (5.28) and `(G_σ g)(x) = r(x, σ(x)) + βg(x, σ(x))`
(5.29), `(bX, F, bG, 𝔾)` is an order-preserving FDP (`seFDP`): a measurable greatest `G_σ g`
exists by Exercise 4.2.4. Its subordinate ADP is the post-action model (4.20) of §4.2.3
(`seFDP_sub`); its primary ADP is the discrete choice model
`(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`, whose Bellman operator is
`(Tv)(x) = max_a {r(x, a) + β ∫ v(x')P(x, a, dx')}` (`seFDP_primary_bellman`).

`section_5_3_2`: by Proposition 4.2.4 and Theorem 5.2.13 the fundamental optimality properties
hold for the discrete choice model, its optimal policies are optimal for the post-action model,
and a policy is optimal as soon as `σ(x) ∈ argmax_a {r(x, a) + βg*(x, a)}`, `g*` the post-action
value function.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Finite A] [Nonempty A]

/-- The FDP `(bX, F, bG, 𝔾)` of §5.3.2. -/
noncomputable def seFDP (r : BM (X × A)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] : FDP (BM X) (BM (X × A)) (SEPolicy X A) where
  F := expectOp P
  G := (postActionEU r β hβ0 hβ1 P).H
  greatest g := by
    have := Fintype.ofFinite A
    let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
    exact ⟨_, (postActionEU r β hβ0 hβ1 P).H_le_greedy g⟩
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

variable (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X)
  [IsMarkovKernel P]

theorem seFDP_isOrderPreserving : (seFDP r β hβ0 hβ1 P).IsOrderPreserving :=
  ⟨(isCEOperator_expectOp P).1, (postActionEU r β hβ0 hβ1 P).H_mono⟩

theorem seFDP_monotonic : (seFDP r β hβ0 hβ1 P).Monotonic :=
  Or.inl (seFDP_isOrderPreserving r hβ0 hβ1 P)

/-- The subordinate ADP of `(bX, F, bG, 𝔾)` is the post-action model `(bG, 𝕋̂_SE)` (4.20). -/
theorem seFDP_sub : (seFDP r β hβ0 hβ1 P).sub (seFDP_monotonic r hβ0 hβ1 P) =
    (postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P) := rfl

/-- The primary ADP is the discrete choice model
`(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`. -/
theorem seFDP_primary_T (σ : SEPolicy X A) (v : BM X) (x : X) :
    (((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).T σ v).toFun x =
      r.toFun (x, σ.1 x) + β * ∫ x', v.toFun x' ∂(P (x, σ.1 x)) := rfl

/-- The Bellman operator of the discrete choice model:
`(Tv)(x) = max_a {r(x, a) + β ∫ v(x')P(x, a, dx')}`. -/
theorem seFDP_primary_bellman [Fintype A] (v : BM X) (x : X) :
    (((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).bellman v).toFun x =
      Finset.univ.sup' Finset.univ_nonempty fun a =>
        r.toFun (x, a) + β * ∫ x', v.toFun x' ∂(P (x, a)) := by
  rw [FDP.primary_bellman]
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun a _ => ?_)
  · exact Finset.le_sup' (fun a => r.toFun (x, a) + β * ∫ x', v.toFun x' ∂(P (x, a)))
      (Finset.mem_univ (((seFDP r β hβ0 hβ1 P).gsel (expectOp P v)).1 x))
  · exact (seFDP r β hβ0 hβ1 P).G_le_Gsup ⟨fun _ => a, measurable_const⟩ (expectOp P v) x

/-- §5.3.2 (p. 177): for the discrete choice model `(bX, 𝕋_SE)`, the fundamental optimality
properties hold; its optimal policies are optimal for the post-action model `(bG, 𝕋̂_SE)`; and if
`g*` is the post-action value function, any measurable `σ` with
`σ(x) ∈ argmax_a {r(x, a) + βg*(x, a)}` at every `x` is optimal. -/
theorem section_5_3_2 [Nonempty X] :
    ∃ (hw : ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).WellPosed)
      (hw' : ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).WellPosed),
      ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).FundamentalOptimality hw ∧
      (∀ σ, ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).IsOptimal hw σ →
        ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsOptimal hw' σ) ∧
      ∀ gstar σ, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsValueFunction
          gstar →
        (∀ x a, r.toFun (x, a) + β * gstar.toFun (x, a) ≤
          r.toFun (x, σ.1 x) + β * gstar.toFun (x, σ.1 x)) →
        ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).IsOptimal hw σ := by
  obtain ⟨hw', hfo', -⟩ := proposition_4_2_4 r hβ0 hβ1 P
  have h := seFDP_monotonic r hβ0 hβ1 P
  have hP := seFDP_isOrderPreserving r hβ0 hβ1 P
  have hw : ((seFDP r β hβ0 hβ1 P).primary h).WellPosed := (FDP.lemma_5_2_12 h).1.1 hw'
  have key := FDP.theorem_5_2_13 h hP hw hw'
  have hfo := key.1.2 hfo'
  obtain ⟨-, hii, hiii⟩ := key.2 hfo
  refine ⟨hw, hw', hfo, hiii, fun gstar σ hg hσ => hii gstar σ hg ?_⟩
  refine le_antisymm ((seFDP r β hβ0 hβ1 P).G_le_Gsup σ gstar) fun x => ?_
  exact hσ x _

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Epstein–Zin aggregator in one variable

Sargent and Stachurski, *Dynamic Programming*, Volume 2, solution to Exercise 5.1.10 (p. 405).

For `c > 0`, `0 ≤ β < 1` and `θ ≠ 0`, let `f(t) = ((1 − β)c + βt^{1/θ})^θ` on `t > 0`.

* `f` is order preserving, and `f(d^θ) = ((1 − β)c + βd)^θ`.
* `f'(t) = β((1 − β)c t^{−1/θ} + β)^{θ−1}`, so `f` is convex when `0 < θ ≤ 1` and concave when
  `θ < 0` or `1 ≤ θ`.
-/

open Set Filter Topology

namespace SargentStachurski.ADPTransformations

namespace EZ

/-- `f(t) = ((1 − β)c + βt^{1/θ})^θ`. -/
noncomputable def f (β θ c t : ℝ) : ℝ := ((1 - β) * c + β * t ^ θ⁻¹) ^ θ

/-- The inner aggregate `(1 − β)c + βt^{1/θ}`. -/
noncomputable def g (β θ c t : ℝ) : ℝ := (1 - β) * c + β * t ^ θ⁻¹

/-- The derivative `β((1 − β)c t^{−1/θ} + β)^{θ−1}`. -/
noncomputable def f' (β θ c t : ℝ) : ℝ := β * ((1 - β) * c * t ^ (-θ⁻¹) + β) ^ (θ - 1)

variable {β θ c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc : 0 < c)
include hβ0 hβ1 hc

theorem g_pos {t : ℝ} (ht : 0 ≤ t) : 0 < g β θ c t :=
  add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 hβ1) hc)
    (mul_nonneg hβ0 (Real.rpow_nonneg ht _))

/-- `f` is order preserving on `(0, ∞)`. -/
theorem f_monotoneOn (hθ : θ ≠ 0) : MonotoneOn (f β θ c) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  have hgs := g_pos hβ0 hβ1 hc (θ := θ) hs'.le
  have hgt := g_pos hβ0 hβ1 hc (θ := θ) ht'.le
  change g β θ c s ^ θ ≤ g β θ c t ^ θ
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hinv : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    have h1 : t ^ θ⁻¹ ≤ s ^ θ⁻¹ := Real.rpow_le_rpow_of_nonpos hs' hst hinv.le
    have h2 : g β θ c t ≤ g β θ c s :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hβ0)
    exact Real.rpow_le_rpow_of_nonpos hgt h2 hneg.le
  · have h1 : s ^ θ⁻¹ ≤ t ^ θ⁻¹ := Real.rpow_le_rpow hs'.le hst (inv_nonneg.2 hpos.le)
    have h2 : g β θ c s ≤ g β θ c t :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hβ0)
    exact Real.rpow_le_rpow hgs.le h2 hpos.le

omit hβ0 hβ1 hc in
/-- `f(d^θ) = ((1 − β)c + βd)^θ`. -/
theorem f_rpow (hθ : θ ≠ 0) {d : ℝ} (hd : 0 < d) :
    f β θ c (d ^ θ) = ((1 - β) * c + β * d) ^ θ := by
  rw [f, Real.rpow_rpow_inv hd.le hθ]

/-- `f'(t) = β((1 − β)c t^{−1/θ} + β)^{θ−1}`. -/
theorem hasDerivAt_f (hθ : θ ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (f β θ c) (f' β θ c t) t := by
  have hg : HasDerivAt (g β θ c) (β * (θ⁻¹ * t ^ (θ⁻¹ - 1))) t :=
    ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul β).const_add ((1 - β) * c)
  have hgt := g_pos hβ0 hβ1 hc (θ := θ) ht.le
  have hf := hg.rpow_const (p := θ) (Or.inl hgt.ne')
  have hfg : f β θ c = fun y => g β θ c y ^ θ := rfl
  rw [hfg]
  convert hf using 1
  -- `β((1−β)c t^{−1/θ} + β)^{θ−1} = βθ⁻¹t^{θ⁻¹−1} · θ · g(t)^{θ−1}`
  have hsplit : (1 - β) * c * t ^ (-θ⁻¹) + β = g β θ c t * t ^ (-θ⁻¹) := by
    rw [g, add_mul, mul_assoc β, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  have hpow : (t ^ (-θ⁻¹)) ^ (θ - 1) = t ^ (θ⁻¹ - 1) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    field_simp
    ring
  unfold f'
  rw [hsplit, Real.mul_rpow hgt.le (Real.rpow_nonneg ht.le _), hpow]
  field_simp

theorem deriv_f (hθ : θ ≠ 0) {t : ℝ} (ht : 0 < t) : deriv (f β θ c) t = f' β θ c t :=
  (hasDerivAt_f hβ0 hβ1 hc hθ ht).deriv

theorem f'_inner_pos {t : ℝ} (ht : 0 < t) : 0 < (1 - β) * c * t ^ (-θ⁻¹) + β :=
  add_pos_of_pos_of_nonneg (mul_pos (mul_pos (sub_pos.2 hβ1) hc) (Real.rpow_pos_of_pos ht _)) hβ0

theorem continuousOn_f (hθ : θ ≠ 0) : ContinuousOn (f β θ c) (Ioi 0) := fun _ ht =>
  (hasDerivAt_f hβ0 hβ1 hc hθ ht).continuousAt.continuousWithinAt

theorem differentiableOn_f (hθ : θ ≠ 0) : DifferentiableOn ℝ (f β θ c) (interior (Ioi 0)) := by
  rw [interior_Ioi]
  exact fun _ ht => (hasDerivAt_f hβ0 hβ1 hc hθ ht).differentiableAt.differentiableWithinAt

/-- **Exercise 5.1.10 (i)**, scalar form: if `0 < θ ≤ 1`, `f` is convex on `(0, ∞)`. -/
theorem convexOn_f (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : ConvexOn ℝ (Ioi 0) (f β θ c) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (continuousOn_f hβ0 hβ1 hc hθ0.ne')
    (differentiableOn_f hβ0 hβ1 hc hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  rw [deriv_f hβ0 hβ1 hc hθ0.ne' hs', deriv_f hβ0 hβ1 hc hθ0.ne' ht]
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hs' hst (neg_nonpos.2 (inv_nonneg.2 hθ0.le))
  have h2 : (1 - β) * c * t ^ (-θ⁻¹) + β ≤ (1 - β) * c * s ^ (-θ⁻¹) + β :=
    add_le_add (mul_le_mul_of_nonneg_left h1 (mul_pos (sub_pos.2 hβ1) hc).le) le_rfl
  exact Real.rpow_le_rpow_of_nonpos (f'_inner_pos hβ0 hβ1 hc ht) h2 (by linarith)

/-- **Exercise 5.1.10 (ii)**, scalar form: if `θ < 0` or `1 ≤ θ`, `f` is concave on `(0, ∞)`. -/
theorem concaveOn_f (hθ : θ < 0 ∨ 1 ≤ θ) : ConcaveOn ℝ (Ioi 0) (f β θ c) := by
  have hθ0 : θ ≠ 0 := by
    rcases hθ with h | h
    · exact h.ne
    · exact (by linarith : (0 : ℝ) < θ).ne'
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) (continuousOn_f hβ0 hβ1 hc hθ0)
    (differentiableOn_f hβ0 hβ1 hc hθ0) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [deriv_f hβ0 hβ1 hc hθ0 hs', deriv_f hβ0 hβ1 hc hθ0 ht']
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  have hk : 0 ≤ (1 - β) * c := (mul_pos (sub_pos.2 hβ1) hc).le
  rcases hθ with hneg | hge
  · -- `t ↦ t^{−1/θ}` is increasing, the exponent `θ − 1` is negative
    have h1 : s ^ (-θ⁻¹) ≤ t ^ (-θ⁻¹) :=
      Real.rpow_le_rpow hs'.le hst (neg_nonneg.2 (inv_lt_zero.2 hneg).le)
    have h2 : (1 - β) * c * s ^ (-θ⁻¹) + β ≤ (1 - β) * c * t ^ (-θ⁻¹) + β :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hk) le_rfl
    exact Real.rpow_le_rpow_of_nonpos (f'_inner_pos hβ0 hβ1 hc hs') h2 (by linarith)
  · -- `t ↦ t^{−1/θ}` is decreasing, the exponent `θ − 1` is nonnegative
    have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
      Real.rpow_le_rpow_of_nonpos hs' hst (neg_nonpos.2 (inv_nonneg.2 (by linarith)))
    have h2 : (1 - β) * c * t ^ (-θ⁻¹) + β ≤ (1 - β) * c * s ^ (-θ⁻¹) + β :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hk) le_rfl
    exact Real.rpow_le_rpow (f'_inner_pos hβ0 hβ1 hc ht').le h2 (by linarith)

end EZ

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Du's theorem for minimization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, proof of Lemma 5.1.11 (ii) (p. 159).

The book obtains the min-results from the max-results "by Exercise 2.2.6". Exercise 2.2.6 turns
min-statements for `(V, 𝕋)` into max-statements for the dual `(V^∂, 𝕋)`, and `V^∂` is not an order
interval of a Banach lattice, so Theorem 4.1.11 does not apply to it directly. Here the reflection
`w ↦ −w` carries the order interval `[−b, −a]` onto `[a, b]^∂`:

* `ADP.reflect` is the ADP `T̃_σ w = −T_σ(−w)` on `[−b, −a]`, anti-isomorphic to `(V, 𝕋)`.
* It satisfies Du's conditions whenever `(V, 𝕋)` does, with concave and convex swapped.
* `theorem_4_1_11_min`: a min-regular ADP on `[a, b]` whose policy operators satisfy Du's
  conditions, with `𝕋` finite, satisfies the fundamental min-optimality properties, and min-VFI,
  min-OPI and min-HPI all converge (Theorems 4.1.11, 5.1.9 and 5.1.10).
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_neg {a b : E} (v : Icc a b) : -(v : E) ∈ Icc (-b) (-a) :=
  neg_mem_Icc_iff'.1 (by rw [neg_neg]; exact v.2)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_of_neg {a b : E} (w : Icc (-b) (-a)) : -(w : E) ∈ Icc a b :=
  neg_mem_Icc_iff'.2 w.2

/-- `w ↦ −w`, an order anti-isomorphism from `[−b, −a]` onto `[a, b]`. -/
def negIcc (a b : E) : Icc (-b) (-a) ≃o (Icc a b)ᵒᵈ where
  toFun w := OrderDual.toDual ⟨-(w : E), neg_mem_Icc_of_neg w⟩
  invFun v := ⟨-((OrderDual.ofDual v : Icc a b) : E), neg_mem_Icc_neg (OrderDual.ofDual v)⟩
  left_inv w := Subtype.ext (neg_neg (w : E))
  right_inv v := by
    change OrderDual.toDual (⟨-(-((OrderDual.ofDual v : Icc a b) : E)), _⟩ : Icc a b) = v
    exact congrArg OrderDual.toDual (Subtype.ext (neg_neg _))
  map_rel_iff' {w w'} := by
    change ((⟨-(w' : E), _⟩ : Icc a b) ≤ ⟨-(w : E), _⟩) ↔ w ≤ w'
    exact neg_le_neg_iff

end BanachLattice

namespace ADP

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] {a b : E}
  {P : Type*}

/-- The reflected ADP `T̃_σ w = −T_σ(−w)` on `[−b, −a]`. -/
def reflect (A : ADP (Icc a b) P) : ADP (Icc (-b) (-a)) P where
  T σ w := ⟨-(A.T σ ⟨-(w : E), BanachLattice.neg_mem_Icc_of_neg w⟩ : E),
    BanachLattice.neg_mem_Icc_neg _⟩
  mono σ _ _ h := neg_le_neg (A.mono σ (show (⟨_, _⟩ : Icc a b) ≤ ⟨_, _⟩ from neg_le_neg h))
  nonempty := A.nonempty

end ADP

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]

variable {a b : E} {P : Type*}

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
/-- The reflection is anti-isomorphic to the original ADP under `w ↦ −w`. -/
theorem reflect_isAntiIsomorphic (A : ADP (Icc a b) P) :
    A.reflect.IsAntiIsomorphic A (negIcc a b) := fun _ _ =>
  Subtype.ext (neg_neg _)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem reflect_isFinite {A : ADP (Icc a b) P} (h : A.IsFinite) : A.reflect.IsFinite := by
  have : range A.reflect.T = (fun S : Icc a b → Icc a b => fun w : Icc (-b) (-a) =>
      (⟨-(S ⟨-(w : E), neg_mem_Icc_of_neg w⟩ : E), neg_mem_Icc_neg _⟩ : Icc (-b) (-a))) ''
        range A.T := by
    rw [← Set.range_comp]
    rfl
  change (range A.reflect.T).Finite
  rw [this]
  exact h.image _

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem extendIcc_reflect (A : ADP (Icc a b) P) (σ : P) (w : Icc (-b) (-a)) :
    extendIcc (A.reflect.T σ) w = -extendIcc (A.T σ) (-(w : E)) := by
  rw [extendIcc_apply,
    show -(w : E) = ((⟨-(w : E), neg_mem_Icc_of_neg w⟩ : Icc a b) : E) from rfl, extendIcc_apply]
  rfl

omit [HasSolidNorm E] [CompleteSpace E] in
/-- Du's conditions pass to the reflection, with concave and convex swapped. -/
theorem duConditions_reflect (hab : a ≤ b) {A : ADP (Icc a b) P} {σ : P}
    (h : DuConditions a b (extendIcc (A.T σ))) :
    DuConditions (-b) (-a) (extendIcc (A.reflect.T σ)) := by
  set F := extendIcc (A.T σ)
  have hF : ∀ w ∈ Icc (-b) (-a), extendIcc (A.reflect.T σ) w = -F (-w) := fun w hw =>
    extendIcc_reflect A σ ⟨w, hw⟩
  have hsub : (-a) - (-b) = b - a := by abel
  have ha : -a ∈ Icc (-b) (-a) := ⟨neg_le_neg hab, le_rfl⟩
  have hb : -b ∈ Icc (-b) (-a) := ⟨le_rfl, neg_le_neg hab⟩
  rcases h with ⟨hconc, ε, hε0, hε1, hε⟩ | ⟨hconv, ε, hε0, hε1, hε⟩
  · refine Or.inr ⟨⟨convex_Icc _ _, fun x hx y hy s t hs ht hst => ?_⟩, ε, hε0, hε1, ?_⟩
    · have hxy : s • x + t • y ∈ Icc (-b) (-a) := convex_Icc _ _ hx hy hs ht hst
      have key := hconc.2 (neg_mem_Icc_iff'.2 hx) (neg_mem_Icc_iff'.2 hy) hs ht hst
      rw [hF _ hxy, hF x hx, hF y hy]
      have he : -(s • x + t • y) = s • -x + t • -y := by rw [smul_neg, smul_neg, neg_add]
      calc -F (-(s • x + t • y)) = -F (s • -x + t • -y) := by rw [he]
        _ ≤ -(s • F (-x) + t • F (-y)) := neg_le_neg key
        _ = s • -F (-x) + t • -F (-y) := by rw [smul_neg, smul_neg, neg_add]
    · rw [hF _ ha, neg_neg, hsub]
      calc -F a ≤ -(a + ε • (b - a)) := neg_le_neg hε
        _ = -a - ε • (b - a) := by abel
  · refine Or.inl ⟨⟨convex_Icc _ _, fun x hx y hy s t hs ht hst => ?_⟩, ε, hε0, hε1, ?_⟩
    · have hxy : s • x + t • y ∈ Icc (-b) (-a) := convex_Icc _ _ hx hy hs ht hst
      have key := hconv.2 (neg_mem_Icc_iff'.2 hx) (neg_mem_Icc_iff'.2 hy) hs ht hst
      rw [hF _ hxy, hF x hx, hF y hy]
      have he : -(s • x + t • y) = s • -x + t • -y := by rw [smul_neg, smul_neg, neg_add]
      calc s • -F (-x) + t • -F (-y) = -(s • F (-x) + t • F (-y)) := by
            rw [smul_neg, smul_neg, neg_add]
        _ ≤ -F (s • -x + t • -y) := neg_le_neg key
        _ = -F (-(s • x + t • y)) := by rw [he]
    · rw [hF _ hb, neg_neg, hsub]
      calc -b + ε • (b - a) = -(b - ε • (b - a)) := by abel
        _ ≤ -F b := neg_le_neg hε

/-- **Du's theorem for minimization**: a min-regular ADP on `[a, b]` whose policy operators
satisfy Du's conditions, with `𝕋` finite, satisfies the fundamental min-optimality properties,
and min-VFI, min-OPI and min-HPI all converge. -/
theorem theorem_4_1_11_min (hab : a ≤ b) (A : ADP (Icc a b) P) (hr : A.MinRegular)
    (hdu : ∀ σ, DuConditions a b (extendIcc (A.T σ))) (hfin : A.IsFinite) :
    ∃ hw : A.WellPosed, A.MinFundamentalOptimality hw ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧ A.MinHPIConverges hw g vstar := by
  have hanti := reflect_isAntiIsomorphic A
  have h8 := ADP.theorem_5_1_8 hanti
  have hrR : A.reflect.Regular := h8.2.1.2 hr
  obtain ⟨hwR, hFO, vstar, hv, hvfi, hconv⟩ := theorem_4_1_11 (neg_le_neg hab) A.reflect hrR
    (fun σ => duConditions_reflect hab (hdu σ)) (Or.inr (Or.inl (reflect_isFinite hfin)))
  have hw : A.WellPosed := h8.2.2.1.1 hwR
  have h9 := ADP.theorem_5_1_9 hanti hrR hwR hw
  have h10 := ADP.theorem_5_1_10 hanti hrR hwR hw vstar
  refine ⟨hw, h9.2.2.1 hFO, _, h9.2.1 vstar hv, h10.2.2.1.1 hvfi, fun g hg => ⟨?_, ?_⟩⟩
  · exact h10.2.2.2.1.1 (fun g' hg' => (hconv g' hg').1) g hg
  · exact h10.2.2.2.2.1 (fun g' hg' => (hconv g' hg').2) g hg

end BanachLattice

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.3 (pp. 157–160).

The finite-state Epstein–Zin model (5.10) has policy operators (5.11),
`T_σ v = {(1 − β)r_σ^α + β(L_σ v)^α}^{1/α}` with
`(L_σ v)(x) = (∑_{x'} v(x')^ν P(x, σ(x), x'))^{1/ν}`, for nonzero `α, ν`. With `θ = ν/α`, the
auxiliary ADP (5.13) on `V̂ = [v₁, v₂]` is
`T̂_σ v = {(1 − β)r_σ^α + β(P_σ v)^{1/θ}}^θ`, and `Fv = v^ν` links the two (5.12).

* **Exercise 5.1.9**: `v₁ ≪ T̂_σ v₁` and `T̂_σ v₂ ≪ v₂`.
* **Exercise 5.1.10**: `T̂_σ` is convex on `V̂` if `0 < θ ≤ 1` and concave if `θ < 0` or `1 ≤ θ`.
* **Lemma 5.1.11**: the fundamental max- and min-optimality properties hold for `(V̂, 𝕋̂_EZ)`,
  with VFI, OPI and HPI converging in both senses (Theorem 4.1.11 and its reflection).
* **Exercise 5.1.11**: `F ∘ T_σ = T̂_σ ∘ F` on `V`.
* **Lemma 5.1.12**: `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are isomorphic if `ν > 0` and anti-isomorphic if
  `ν < 0`.
* **Proposition 5.1.13**: the fundamental optimality properties hold for `(V, 𝕋_EZ)`, and VFI,
  OPI and HPI all converge, without irreducibility of `P_σ`.

The book takes `v₁ = m₁ ∧ m₂`, `v₂ = m₁ ∨ m₂` with `m₁ = (min r^α − ε)^θ` and
`m₂ = (max r^α + ε)^θ`; here `m₁ = c₁^θ`, `m₂ = c₂^θ` for any `0 < c₁ < r^α < c₂` on the feasible
pairs, which includes that choice.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

/-- On a finite set, a positive function has a positive lower bound: some `ε ∈ (0, 1)` has
`εd ≤ u(x)` for all `x`. -/
theorem exists_eps_mul_le {X : Type*} [Finite X] (u : X → ℝ) (hu : ∀ x, 0 < u x) {d : ℝ}
    (hd : 0 < d) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x, ε * d ≤ u x := by
  have := Fintype.ofFinite X
  obtain ⟨δ, hδ, hδu⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ u x := by
    rcases (Finset.univ : Finset X).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x =>
        absurd (Finset.mem_univ x) (by rw [he]; exact Finset.notMem_empty x)⟩
    · exact ⟨Finset.univ.inf' hne u, (Finset.lt_inf'_iff hne).2 fun x _ => hu x,
        fun x => Finset.inf'_le u (Finset.mem_univ x)⟩
  refine ⟨min (1 / 2) (δ / d), lt_min (by norm_num) (div_pos hδ hd),
    (min_le_left _ _).trans_lt (by norm_num), fun x => ?_⟩
  calc min (1 / 2) (δ / d) * d ≤ δ / d * d := mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le
    _ = δ := div_mul_cancel₀ δ hd.ne'
    _ ≤ u x := hδu x

/-- The finite-state Epstein–Zin model (5.10), with bounds `c₁ < r^α < c₂` on the feasible
pairs. -/
structure EZModel (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the (strictly positive) reward -/
  r : X → A → ℝ
  r_pos : ∀ x a, 0 < r x a
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_sum : ∀ x a, ∑ x', P x a x' = 1
  /-- `α = 1 − 1/ψ` -/
  α : ℝ
  /-- `ν = 1 − γ` -/
  ν : ℝ
  α_ne : α ≠ 0
  ν_ne : ν ≠ 0
  /-- a lower bound for `r^α` -/
  c₁ : ℝ
  /-- an upper bound for `r^α` -/
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₁_lt : ∀ x, ∀ a ∈ Γ x, c₁ < r x a ^ α
  lt_c₂ : ∀ x, ∀ a ∈ Γ x, r x a ^ α < c₂

namespace EZModel

variable {X A : Type*} [Fintype X] (M : EZModel X A)

/-- `θ = ν/α`. -/
noncomputable def θ : ℝ := M.ν / M.α

theorem θ_ne : M.θ ≠ 0 := div_ne_zero M.ν_ne M.α_ne

/-- Feasible policies. -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

theorem nonempty_policy : Nonempty M.Policy :=
  ⟨⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩⟩

theorem finite_policy : Finite M.Policy := by
  classical
  refine Finite.of_injective (fun σ : M.Policy => fun x => (⟨σ.1 x, σ.2 x⟩ : M.Γ x)) ?_
  intro σ τ h
  apply Subtype.ext
  funext x
  have := congrFun h x
  simpa using congrArg Subtype.val this

theorem c₂_pos : 0 < M.c₂ := M.c₁_pos.trans M.c₁_lt_c₂

/-- `v₁ = m₁ ∧ m₂`, with `m₁ = c₁^θ`, `m₂ = c₂^θ`. -/
noncomputable def lo : ℝ := if 0 < M.θ then M.c₁ ^ M.θ else M.c₂ ^ M.θ

/-- `v₂ = m₁ ∨ m₂`. -/
noncomputable def hi : ℝ := if 0 < M.θ then M.c₂ ^ M.θ else M.c₁ ^ M.θ

theorem lo_pos : 0 < M.lo := by
  unfold lo; split_ifs
  · exact Real.rpow_pos_of_pos M.c₁_pos _
  · exact Real.rpow_pos_of_pos M.c₂_pos _

theorem hi_pos : 0 < M.hi := by
  unfold hi; split_ifs
  · exact Real.rpow_pos_of_pos M.c₂_pos _
  · exact Real.rpow_pos_of_pos M.c₁_pos _

theorem lo_lt_hi : M.lo < M.hi := by
  unfold lo hi; split_ifs with h
  · exact Real.rpow_lt_rpow M.c₁_pos.le M.c₁_lt_c₂ h
  · exact Real.rpow_lt_rpow_of_neg M.c₁_pos M.c₁_lt_c₂
      (lt_of_le_of_ne (not_lt.1 h) M.θ_ne)

/-- The constant function `v₁`. -/
noncomputable def a : X → ℝ := fun _ => M.lo

/-- The constant function `v₂`. -/
noncomputable def b : X → ℝ := fun _ => M.hi

theorem a_le_b : M.a ≤ M.b := fun _ => M.lo_lt_hi.le

/-- `(P_σ v)(x) = ∑_{x'} v(x')P(x, σ(x), x')`. -/
def Pσ (σ : M.Policy) (v : X → ℝ) (x : X) : ℝ := ∑ x', v x' * M.P x (σ.1 x) x'

theorem Pσ_const (σ : M.Policy) (c : ℝ) (x : X) : M.Pσ σ (fun _ => c) x = c := by
  rw [Pσ, ← Finset.mul_sum, M.P_sum, mul_one]

theorem Pσ_mono (σ : M.Policy) {v w : X → ℝ} (h : v ≤ w) (x : X) : M.Pσ σ v x ≤ M.Pσ σ w x :=
  Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg _ _ _)

theorem Pσ_combo (σ : M.Policy) (v w : X → ℝ) (s t : ℝ) (x : X) :
    M.Pσ σ (s • v + t • w) x = s * M.Pσ σ v x + t * M.Pσ σ w x := by
  simp only [Pσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x' _ => by ring

theorem Pσ_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) (x : X) :
    M.lo ≤ M.Pσ σ v x ∧ M.Pσ σ v x ≤ M.hi :=
  ⟨(M.Pσ_const σ M.lo x).symm.le.trans (M.Pσ_mono σ hv.1 x),
    (M.Pσ_mono σ hv.2 x).trans (M.Pσ_const σ M.hi x).le⟩

theorem Pσ_pos (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) (x : X) : 0 < M.Pσ σ v x :=
  M.lo_pos.trans_le (M.Pσ_mem σ hv x).1

/-- The auxiliary policy operator (5.13), `T̂_σ v = {(1 − β)r_σ^α + β(P_σ v)^{1/θ}}^θ`. -/
noncomputable def That (σ : M.Policy) (v : X → ℝ) : X → ℝ :=
  fun x => EZ.f M.β M.θ (M.r x (σ.1 x) ^ M.α) (M.Pσ σ v x)

theorem rα_pos (x : X) (a : A) : 0 < M.r x a ^ M.α := Real.rpow_pos_of_pos (M.r_pos x a) _

theorem That_le (σ : M.Policy) {v w : X → ℝ} (hv : v ∈ Icc M.a M.b) (hw : w ∈ Icc M.a M.b)
    (h : v ≤ w) : M.That σ v ≤ M.That σ w := fun x =>
  EZ.f_monotoneOn M.β_nonneg M.β_lt_one (M.rα_pos x _) M.θ_ne (M.Pσ_pos σ hv x)
    (M.Pσ_pos σ hw x) (M.Pσ_mono σ h x)

/-- `v₁ < f(v₁)` and `f(v₂) < v₂` for `f(t) = ((1 − β)c + βt^{1/θ})^θ` with `c₁ < c < c₂`. -/
theorem lo_lt_f_hi {c : ℝ} (hc1 : M.c₁ < c) (hc2 : c < M.c₂) :
    M.lo < EZ.f M.β M.θ c M.lo ∧ EZ.f M.β M.θ c M.hi < M.hi := by
  have hβ1 := sub_pos.2 M.β_lt_one
  have hA : M.c₁ < (1 - M.β) * c + M.β * M.c₁ := by nlinarith [M.β_nonneg]
  have hB : (1 - M.β) * c + M.β * M.c₂ < M.c₂ := by nlinarith [M.β_nonneg]
  have hApos : 0 < (1 - M.β) * c + M.β * M.c₁ := M.c₁_pos.trans hA
  have hBpos : 0 < (1 - M.β) * c + M.β * M.c₂ :=
    add_pos_of_pos_of_nonneg (mul_pos hβ1 (M.c₁_pos.trans hc1)) (mul_nonneg M.β_nonneg M.c₂_pos.le)
  unfold lo hi
  split_ifs with hθ
  · rw [EZ.f_rpow M.θ_ne M.c₁_pos, EZ.f_rpow M.θ_ne M.c₂_pos]
    exact ⟨Real.rpow_lt_rpow M.c₁_pos.le hA hθ, Real.rpow_lt_rpow hBpos.le hB hθ⟩
  · have hneg : M.θ < 0 := lt_of_le_of_ne (not_lt.1 hθ) M.θ_ne
    rw [EZ.f_rpow M.θ_ne M.c₂_pos, EZ.f_rpow M.θ_ne M.c₁_pos]
    exact ⟨Real.rpow_lt_rpow_of_neg hBpos hB hneg, Real.rpow_lt_rpow_of_neg M.c₁_pos hA hneg⟩

/-- **Exercise 5.1.9** (p. 158): `v₁ ≪ T̂_σ v₁` and `T̂_σ v₂ ≪ v₂`. -/
theorem exercise_5_1_9 (σ : M.Policy) :
    (∀ x, M.a x < M.That σ M.a x) ∧ ∀ x, M.That σ M.b x < M.b x := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change M.lo < EZ.f M.β M.θ _ (M.Pσ σ (fun _ => M.lo) x)
    rw [M.Pσ_const]
    exact (M.lo_lt_f_hi (M.c₁_lt x _ (σ.2 x)) (M.lt_c₂ x _ (σ.2 x))).1
  · change EZ.f M.β M.θ _ (M.Pσ σ (fun _ => M.hi) x) < M.hi
    rw [M.Pσ_const]
    exact (M.lo_lt_f_hi (M.c₁_lt x _ (σ.2 x)) (M.lt_c₂ x _ (σ.2 x))).2

theorem That_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) : M.That σ v ∈ Icc M.a M.b :=
  have ha : M.a ∈ Icc M.a M.b := Set.left_mem_Icc.2 M.a_le_b
  have hb : M.b ∈ Icc M.a M.b := Set.right_mem_Icc.2 M.a_le_b
  ⟨fun x => ((M.exercise_5_1_9 σ).1 x).le.trans (M.That_le σ ha hv hv.1 x),
    fun x => (M.That_le σ hv hb hv.2 x).trans ((M.exercise_5_1_9 σ).2 x).le⟩

/-- The auxiliary ADP `(V̂, 𝕋̂_EZ)` on `V̂ = [v₁, v₂]`. -/
noncomputable def adpHat : ADP (Icc M.a M.b) M.Policy where
  T σ v := ⟨M.That σ v, M.That_mem σ v.2⟩
  mono σ v w h := M.That_le σ v.2 w.2 h
  nonempty := M.nonempty_policy

/-- **Exercise 5.1.10** (p. 158): (i) if `0 < θ ≤ 1`, `T̂_σ` is convex on `V̂`; (ii) if `θ < 0` or
`1 ≤ θ`, `T̂_σ` is concave on `V̂`. -/
theorem exercise_5_1_10 (σ : M.Policy) :
    (0 < M.θ → M.θ ≤ 1 → ConvexOn ℝ (Icc M.a M.b) (M.That σ)) ∧
      (M.θ < 0 ∨ 1 ≤ M.θ → ConcaveOn ℝ (Icc M.a M.b) (M.That σ)) := by
  refine ⟨fun h0 h1 => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst x => ?_⟩,
    fun hθ => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst x => ?_⟩⟩
  · change EZ.f M.β M.θ _ (M.Pσ σ (s • v + t • w) x) ≤ s * M.That σ v x + t * M.That σ w x
    rw [M.Pσ_combo]
    exact (EZ.convexOn_f M.β_nonneg M.β_lt_one (M.rα_pos x _) h0 h1).2 (M.Pσ_pos σ hv x)
      (M.Pσ_pos σ hw x) hs ht hst
  · change s * M.That σ v x + t * M.That σ w x ≤ EZ.f M.β M.θ _ (M.Pσ σ (s • v + t • w) x)
    rw [M.Pσ_combo]
    exact (EZ.concaveOn_f M.β_nonneg M.β_lt_one (M.rα_pos x _) hθ).2 (M.Pσ_pos σ hv x)
      (M.Pσ_pos σ hw x) hs ht hst

theorem adpHat_isFinite : M.adpHat.IsFinite := by
  have := M.finite_policy
  exact Set.finite_range _

/-- A policy maximizing (`max := true`) or minimizing `T̂_τ v (x)` over `Γ(x)` at every `x`. -/
theorem exists_extremal (v : Icc M.a M.b) (max : Bool) :
    ∃ σ : M.Policy, ∀ τ : M.Policy, if max then M.That τ v ≤ M.That σ v
      else M.That σ v ≤ M.That τ v := by
  let h : X → A → ℝ := fun x a' => EZ.f M.β M.θ (M.r x a' ^ M.α) (∑ x', v.1 x' * M.P x a' x')
  cases max with
  | true =>
    choose σ hσ hmax using fun x => Finset.exists_max_image (M.Γ x) (h x) (M.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmax x (τ.1 x) (τ.2 x)⟩
  | false =>
    choose σ hσ hmin using fun x => Finset.exists_min_image (M.Γ x) (h x) (M.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmin x (τ.1 x) (τ.2 x)⟩

theorem adpHat_regular : M.adpHat.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_extremal v true
  exact ⟨σ, fun τ => hσ τ⟩

theorem adpHat_minRegular : M.adpHat.MinRegular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_extremal v false
  exact ⟨σ, fun τ => hσ τ⟩

/-- Every `T̂_σ` satisfies Du's conditions on `[v₁, v₂]` (proof of Lemma 5.1.11). -/
theorem duConditions (σ : M.Policy) :
    BanachLattice.DuConditions M.a M.b (BanachLattice.extendIcc (M.adpHat.T σ)) := by
  have heq : EqOn (M.That σ) (BanachLattice.extendIcc (M.adpHat.T σ)) (Icc M.a M.b) :=
    fun v hv => (BanachLattice.extendIcc_apply (M.adpHat.T σ) ⟨v, hv⟩).symm
  have ha : M.a ∈ Icc M.a M.b := Set.left_mem_Icc.2 M.a_le_b
  have hb : M.b ∈ Icc M.a M.b := Set.right_mem_Icc.2 M.a_le_b
  have hd : 0 < M.hi - M.lo := sub_pos.2 M.lo_lt_hi
  by_cases hθ : M.θ < 0 ∨ 1 ≤ M.θ
  · obtain ⟨ε, hε0, hε1, hε⟩ := exists_eps_mul_le (fun x => M.That σ M.a x - M.lo)
      (fun x => sub_pos.2 ((M.exercise_5_1_9 σ).1 x)) hd
    refine Or.inl ⟨((M.exercise_5_1_10 σ).2 hθ).congr heq, ε, hε0, hε1, ?_⟩
    rw [← heq ha]
    intro x
    change M.lo + ε * (M.hi - M.lo) ≤ M.That σ M.a x
    linarith [hε x]
  · have h0 : 0 < M.θ := lt_of_le_of_ne (not_lt.1 fun h => hθ (Or.inl h)) M.θ_ne.symm
    have h1 : M.θ ≤ 1 := (not_le.1 fun h => hθ (Or.inr h)).le
    obtain ⟨ε, hε0, hε1, hε⟩ := exists_eps_mul_le (fun x => M.hi - M.That σ M.b x)
      (fun x => sub_pos.2 ((M.exercise_5_1_9 σ).2 x)) hd
    refine Or.inr ⟨((M.exercise_5_1_10 σ).1 h0 h1).congr heq, ε, hε0, hε1, ?_⟩
    rw [← heq hb]
    intro x
    change M.That σ M.b x ≤ M.hi - ε * (M.hi - M.lo)
    linarith [hε x]

/-- Each `T̂_σ` is globally stable on `[v₁, v₂]` (Theorem 4.1.10), so `(V̂, 𝕋̂_EZ)` is order
stable. -/
theorem adpHat_isOrderStable : M.adpHat.IsOrderStable :=
  ADP.IsGloballyStable.isOrderStable fun σ =>
    BanachLattice.theorem_4_1_10_subtype M.a_le_b (M.adpHat.mono σ) (M.duConditions σ)

/-- **Lemma 5.1.11** (p. 158): (i) the fundamental max-optimality properties hold for
`(V̂, 𝕋̂_EZ)` and max-VFI, max-OPI and max-HPI all converge; (ii) the fundamental min-optimality
properties hold and min-VFI, min-OPI and min-HPI all converge. -/
theorem lemma_5_1_11 :
    (∃ hw : M.adpHat.WellPosed, M.adpHat.FundamentalOptimality hw ∧
      ∃ vstar, M.adpHat.IsValueFunction vstar ∧ M.adpHat.VFIConverges vstar ∧
        ∀ g, M.adpHat.IsSelector g → M.adpHat.OPIConverges g vstar ∧
          M.adpHat.HPIConverges hw g vstar) ∧
    (∃ hw : M.adpHat.WellPosed, M.adpHat.MinFundamentalOptimality hw ∧
      ∃ vstar, M.adpHat.IsMinValueFunction vstar ∧ M.adpHat.MinVFIConverges vstar ∧
        ∀ g, M.adpHat.IsMinSelector g → M.adpHat.MinOPIConverges g vstar ∧
          M.adpHat.MinHPIConverges hw g vstar) :=
  ⟨BanachLattice.theorem_4_1_11 M.a_le_b M.adpHat M.adpHat_regular M.duConditions
      (Or.inr (Or.inl M.adpHat_isFinite)),
    BanachLattice.theorem_4_1_11_min M.a_le_b M.adpHat M.adpHat_minRegular M.duConditions
      M.adpHat_isFinite⟩

/-! ### The Epstein–Zin ADP `(V, 𝕋_EZ)` -/

/-- `V = F⁻¹V̂ = {v ∈ (0, ∞)^X : v₁ ≤ v^ν ≤ v₂}` (5.12). -/
def V : Set (X → ℝ) := {v | (∀ x, 0 < v x) ∧ (fun x => v x ^ M.ν) ∈ Icc M.a M.b}

/-- `(L_σ v)(x) = (∑_{x'} v(x')^ν P(x, σ(x), x'))^{1/ν}`. -/
noncomputable def Lσ (σ : M.Policy) (v : X → ℝ) (x : X) : ℝ :=
  M.Pσ σ (fun x' => v x' ^ M.ν) x ^ M.ν⁻¹

/-- The Epstein–Zin policy operator (5.11), `T_σ v = {(1 − β)r_σ^α + β(L_σ v)^α}^{1/α}`. -/
noncomputable def Tσ (σ : M.Policy) (v : X → ℝ) : X → ℝ :=
  fun x => ((1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * M.Lσ σ v x ^ M.α) ^ M.α⁻¹

/-- **Exercise 5.1.11** (p. 159): `F ∘ T_σ = T̂_σ ∘ F` on `V`, with `Fv = v^ν`. -/
theorem exercise_5_1_11 (σ : M.Policy) {v : X → ℝ} (hv : v ∈ M.V) :
    (fun x => M.Tσ σ v x ^ M.ν) = M.That σ fun x => v x ^ M.ν := by
  funext x
  have hS := M.Pσ_pos σ hv.2 x
  have hL : M.Lσ σ v x ^ M.α = M.Pσ σ (fun x' => v x' ^ M.ν) x ^ M.θ⁻¹ := by
    rw [Lσ, ← Real.rpow_mul hS.le, θ, inv_div, div_eq_inv_mul]
  have hA : 0 < (1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * M.Lσ σ v x ^ M.α :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 M.β_lt_one) (M.rα_pos x _))
      (mul_nonneg M.β_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hS.le _) _))
  rw [Tσ, ← Real.rpow_mul hA.le, hL]
  change _ = ((1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * _ ^ M.θ⁻¹) ^ M.θ
  rw [θ, div_eq_inv_mul]

theorem Tσ_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ M.V) : M.Tσ σ v ∈ M.V := by
  refine ⟨fun x => ?_, ?_⟩
  · have hS := M.Pσ_pos σ hv.2 x
    exact Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 M.β_lt_one)
      (M.rα_pos x _)) (mul_nonneg M.β_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hS.le _) _))) _
  · rw [M.exercise_5_1_11 σ hv]
    exact M.That_mem σ hv.2

/-- `F v = v^ν` as a map `V → V̂`. -/
noncomputable def Φ (v : M.V) : Icc M.a M.b := ⟨fun x => v.1 x ^ M.ν, v.2.2⟩

/-- The inverse `v̂ ↦ v̂^{1/ν}`. -/
noncomputable def Ψ (w : Icc M.a M.b) : M.V :=
  ⟨fun x => w.1 x ^ M.ν⁻¹, fun x => Real.rpow_pos_of_pos (M.lo_pos.trans_le (w.2.1 x)) _, by
    have : (fun x => (w.1 x ^ M.ν⁻¹) ^ M.ν) = w.1 := funext fun x =>
      Real.rpow_inv_rpow (M.lo_pos.trans_le (w.2.1 x)).le M.ν_ne
    rw [this]
    exact w.2⟩

theorem Φ_Ψ (w : Icc M.a M.b) : M.Φ (M.Ψ w) = w :=
  Subtype.ext (funext fun x => Real.rpow_inv_rpow (M.lo_pos.trans_le (w.2.1 x)).le M.ν_ne)

theorem Ψ_Φ (v : M.V) : M.Ψ (M.Φ v) = v :=
  Subtype.ext (funext fun x => Real.rpow_rpow_inv (v.2.1 x).le M.ν_ne)

/-- For `ν > 0`, `F` is an order isomorphism `V → V̂`. -/
noncomputable def isoPos (hν : 0 < M.ν) : M.V ≃o Icc M.a M.b where
  toFun := M.Φ
  invFun := M.Ψ
  left_inv := M.Ψ_Φ
  right_inv := M.Φ_Ψ
  map_rel_iff' {v w} := by
    change (∀ x, v.1 x ^ M.ν ≤ w.1 x ^ M.ν) ↔ ∀ x, v.1 x ≤ w.1 x
    exact forall_congr' fun x => Real.rpow_le_rpow_iff (v.2.1 x).le (w.2.1 x).le hν

/-- For `ν < 0`, `F` is an order anti-isomorphism `V → V̂`. -/
noncomputable def isoNeg (hν : M.ν < 0) : M.V ≃o (Icc M.a M.b)ᵒᵈ where
  toFun v := OrderDual.toDual (M.Φ v)
  invFun w := M.Ψ (OrderDual.ofDual w)
  left_inv := M.Ψ_Φ
  right_inv w := congrArg OrderDual.toDual (M.Φ_Ψ (OrderDual.ofDual w))
  map_rel_iff' {v w} := by
    change (∀ x, w.1 x ^ M.ν ≤ v.1 x ^ M.ν) ↔ ∀ x, v.1 x ≤ w.1 x
    exact forall_congr' fun x => Real.rpow_le_rpow_iff_of_neg (w.2.1 x) (v.2.1 x) hν

theorem Φ_T (σ : M.Policy) (v : M.V) :
    M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩ = M.adpHat.T σ (M.Φ v) :=
  Subtype.ext (M.exercise_5_1_11 σ v.2)

/-- The Epstein–Zin ADP `(V, 𝕋_EZ)`. -/
noncomputable def adp : ADP M.V M.Policy where
  T σ v := ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩
  mono σ v w h := by
    rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
    · refine (M.isoNeg hneg).le_iff_le.1 ?_
      change M.Φ ⟨M.Tσ σ w.1, M.Tσ_mem σ w.2⟩ ≤ M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩
      rw [M.Φ_T, M.Φ_T]
      exact M.adpHat.mono σ ((M.isoNeg hneg).le_iff_le.2 h)
    · refine (M.isoPos hpos).le_iff_le.1 ?_
      change M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩ ≤ M.Φ ⟨M.Tσ σ w.1, M.Tσ_mem σ w.2⟩
      rw [M.Φ_T, M.Φ_T]
      exact M.adpHat.mono σ ((M.isoPos hpos).le_iff_le.2 h)
  nonempty := M.nonempty_policy

/-- **Lemma 5.1.12 (i)** (p. 159): if `ν > 0`, `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are isomorphic. -/
theorem lemma_5_1_12_i (hν : 0 < M.ν) : M.adp.IsIsomorphic M.adpHat (M.isoPos hν) :=
  fun σ v => M.Φ_T σ v

/-- **Lemma 5.1.12 (ii)**: if `ν < 0`, `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are anti-isomorphic. -/
theorem lemma_5_1_12_ii (hν : M.ν < 0) : M.adp.IsAntiIsomorphic M.adpHat (M.isoNeg hν) :=
  fun σ v => M.Φ_T σ v

/-- `(V, 𝕋_EZ)` is order stable. -/
theorem adp_isOrderStable : M.adp.IsOrderStable := by
  rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
  · exact (ADP.theorem_5_1_8 (M.lemma_5_1_12_ii hneg)).2.2.2.1.2 M.adpHat_isOrderStable
  · exact (M.lemma_5_1_12_i hpos).orderStable_iff.2 M.adpHat_isOrderStable

/-- **Proposition 5.1.13** (p. 159): the fundamental max-optimality properties hold for
`(V, 𝕋_EZ)`, and max-VFI, max-OPI and max-HPI all converge. -/
theorem proposition_5_1_13 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
  · have h := M.lemma_5_1_12_ii hneg
    obtain ⟨hw', hFO', w, hw₀, hvfi, hconv⟩ := M.lemma_5_1_11.2
    have h8 := ADP.theorem_5_1_8 h
    have hr : M.adp.Regular := h8.2.1.2 M.adpHat_minRegular
    have hw : M.adp.WellPosed := h8.2.2.1.2 hw'
    set vstar := (M.isoNeg hneg).symm (OrderDual.toDual w)
    have hF : OrderDual.ofDual (M.isoNeg hneg vstar) = w := by simp [vstar]
    have h10 := ADP.theorem_5_1_10 h hr hw hw' vstar
    rw [hF] at h10
    refine ⟨hw, ((ADP.theorem_5_1_9 h hr hw hw').2.2).2 hFO', vstar, ?_, h10.2.2.1.2 hvfi,
      fun g hg => ⟨h10.2.2.2.1.2 (fun g' hg' => (hconv g' hg').1) g hg,
        h10.2.2.2.2.2 (fun g' hg' => (hconv g' hg').2) g hg⟩⟩
    refine (h.iso.isValueFunction_iff vstar).2 ?_
    have hv : M.isoNeg hneg vstar = OrderDual.toDual w := by simp [vstar]
    rw [hv]
    exact (M.adpHat.isMinValueFunction_iff w).1 hw₀
  · have h := M.lemma_5_1_12_i hpos
    obtain ⟨hw', hFO', w, hw₀, hvfi, hconv⟩ := M.lemma_5_1_11.1
    have hr : M.adp.Regular := h.regular_iff.2 M.adpHat_regular
    have hw : M.adp.WellPosed := h.wellPosed_iff.2 hw'
    set vstar := (M.isoPos hpos).symm w
    have hF : M.isoPos hpos vstar = w := by simp [vstar]
    have h7 := ADP.theorem_5_1_7 h hr hw hw' vstar
    rw [hF] at h7
    refine ⟨hw, (h.fundamentalOptimality_iff hw hw').2 hFO', vstar, ?_, h7.2.2.1.2 hvfi,
      fun g hg => ⟨h7.2.2.2.1.2 (fun g' hg' => (hconv g' hg').1) g hg,
        h7.2.2.2.2.2 (fun g' hg' => (hconv g' hg').2) g hg⟩⟩
    rw [h.isValueFunction_iff, hF]
    exact hw₀

end EZModel

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin savings with iid endowments

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.3 (pp. 178–181).

Wealth `w ∈ W` and endowment `e ∈ E` are finite, the endowment is iid with distribution `φ`, and
the Bellman equation is (5.31). It is the Epstein–Zin model of §5.1.3 on `X = W × E`, `A = W`
(`toEZ`). The FDP `(V, F, V̂, 𝔾)` has `(Fv)(w) = {∑_e v(w, e)^ν φ(e)}^{1/ν}`, `V̂ = F(V)`, and
`(G_σ h)(w, e) = {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{1/α}` (5.32).

* The FDP is order preserving (`fdp_isOrderPreserving`); a greatest `G_σ h` is the pointwise
  maximizer (5.33).
* **Exercise 5.3.1**: the primary ADP has the policy operators (5.34), those of the Epstein–Zin
  model, so it is isomorphic to `(V, 𝕋_EZ)` under the identity.
* **Exercise 5.3.2**: the subordinate ADP has the policy operators (5.35), acting on functions of
  `w` alone.
* `section_5_3_3`: the fundamental optimality properties hold for both ADPs (Proposition 5.1.13
  and Theorem 5.2.13); a policy satisfying (5.33) at `h = v̂*` is optimal for (5.31); and HPI on
  the subordinate ADP reaches `v̂*` in finitely many steps, which is Algorithm 5.1.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- Power means are order preserving: for weights `φ` summing to one and `p ≠ 0`,
`u ≤ u'` implies `(∑ u^p φ)^{1/p} ≤ (∑ u'^p φ)^{1/p}` on positive vectors. -/
theorem powerSum_pos {ι : Type*} [Fintype ι] {φ : ι → ℝ} (hφ0 : ∀ i, 0 ≤ φ i)
    (hφ1 : ∑ i, φ i = 1) {p : ℝ} {u : ι → ℝ} (hu : ∀ i, 0 < u i) : 0 < ∑ i, u i ^ p * φ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < φ j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ i, φ i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hφ0 i)
    rw [hφ1] at this
    exact one_ne_zero this
  exact Finset.sum_pos' (fun i _ => mul_nonneg (Real.rpow_pos_of_pos (hu i) _).le (hφ0 i))
    ⟨j, Finset.mem_univ _, mul_pos (Real.rpow_pos_of_pos (hu j) _) hj⟩

theorem powerMean_mono {ι : Type*} [Fintype ι] {φ : ι → ℝ} (hφ0 : ∀ i, 0 ≤ φ i)
    (hφ1 : ∑ i, φ i = 1) {p : ℝ} (hp : p ≠ 0) {u u' : ι → ℝ} (hu : ∀ i, 0 < u i) (hle : u ≤ u') :
    (∑ i, u i ^ p * φ i) ^ p⁻¹ ≤ (∑ i, u' i ^ p * φ i) ^ p⁻¹ := by
  have hu' : ∀ i, 0 < u' i := fun i => (hu i).trans_le (hle i)
  have hS := powerSum_pos hφ0 hφ1 (p := p) hu
  have hS' := powerSum_pos hφ0 hφ1 (p := p) hu'
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have h1 : ∑ i, u' i ^ p * φ i ≤ ∑ i, u i ^ p * φ i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (hu i) (hle i) hneg.le) (hφ0 i)
    exact Real.rpow_le_rpow_of_nonpos hS' h1 (inv_lt_zero.2 hneg).le
  · have h1 : ∑ i, u i ^ p * φ i ≤ ∑ i, u' i ^ p * φ i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hu i).le (hle i) hpos.le) (hφ0 i)
    exact Real.rpow_le_rpow hS.le h1 (inv_nonneg.2 hpos.le)

/-- `t ↦ {(1 − β)c + βt^α}^{1/α}` is order preserving on `(0, ∞)`. -/
theorem aggr_mono {β c α : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc : 0 < c) (hα : α ≠ 0) {t t' : ℝ}
    (ht : 0 < t) (hle : t ≤ t') :
    ((1 - β) * c + β * t ^ α) ^ α⁻¹ ≤ ((1 - β) * c + β * t' ^ α) ^ α⁻¹ := by
  have hk : 0 < (1 - β) * c := mul_pos (sub_pos.2 hβ1) hc
  have hpos : ∀ s : ℝ, 0 < s → 0 < (1 - β) * c + β * s ^ α := fun s hs =>
    add_pos_of_pos_of_nonneg hk (mul_nonneg hβ0 (Real.rpow_pos_of_pos hs _).le)
  rcases lt_or_gt_of_ne hα with hneg | hposα
  · have h1 : (1 - β) * c + β * t' ^ α ≤ (1 - β) * c + β * t ^ α :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht hle hneg.le) hβ0)
    exact Real.rpow_le_rpow_of_nonpos (hpos t' (ht.trans_le hle)) h1 (inv_lt_zero.2 hneg).le
  · have h1 : (1 - β) * c + β * t ^ α ≤ (1 - β) * c + β * t' ^ α :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le hle hposα.le) hβ0)
    exact Real.rpow_le_rpow (hpos t ht).le h1 (inv_nonneg.2 hposα.le)

/-- The Epstein–Zin savings model (5.31): wealth `W`, endowments `E` drawn iid from `φ`,
feasible next-period wealth `Γ(w, e)` and reward `r(w, w', e) > 0`. -/
structure EZSavings (W E : Type*) [Fintype W] [Fintype E] where
  /-- the feasible next-period wealth levels -/
  Γ : W × E → Finset W
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward `r(w, w', e)` -/
  r : W → W → E → ℝ
  r_pos : ∀ w w' e, 0 < r w w' e
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the endowment distribution -/
  φ : E → ℝ
  φ_nonneg : ∀ e, 0 ≤ φ e
  φ_sum : ∑ e, φ e = 1
  α : ℝ
  ν : ℝ
  α_ne : α ≠ 0
  ν_ne : ν ≠ 0
  c₁ : ℝ
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₁_lt : ∀ x, ∀ w' ∈ Γ x, c₁ < r x.1 w' x.2 ^ α
  lt_c₂ : ∀ x, ∀ w' ∈ Γ x, r x.1 w' x.2 ^ α < c₂

namespace EZSavings

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W] (S : EZSavings W E)

/-- The model as an Epstein–Zin model (5.10) on `X = W × E`, `A = W`, with
`P((w, e), w', (w'', e')) = 𝟙{w'' = w'}φ(e')`. -/
noncomputable def toEZ : EZModel (W × E) W where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  r x w' := S.r x.1 w' x.2
  r_pos x w' := S.r_pos x.1 w' x.2
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  P _ w' x' := if x'.1 = w' then S.φ x'.2 else 0
  P_nonneg _ _ x' := by
    split_ifs
    · exact S.φ_nonneg _
    · exact le_rfl
  P_sum _ w' := by
    rw [Fintype.sum_prod_type_right]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact S.φ_sum
  α := S.α
  ν := S.ν
  α_ne := S.α_ne
  ν_ne := S.ν_ne
  c₁ := S.c₁
  c₂ := S.c₂
  c₁_pos := S.c₁_pos
  c₁_lt_c₂ := S.c₁_lt_c₂
  c₁_lt := S.c₁_lt
  lt_c₂ := S.lt_c₂

/-- `(Fv)(w) = {∑_e v(w, e)^ν φ(e)}^{1/ν}`. -/
noncomputable def Fraw (v : W × E → ℝ) (w : W) : ℝ := (∑ e, v (w, e) ^ S.ν * S.φ e) ^ S.ν⁻¹

/-- `(G_σ h)(w, e) = {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{1/α}` (5.32). -/
noncomputable def Graw (σ : S.toEZ.Policy) (h : W → ℝ) (x : W × E) : ℝ :=
  ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * h (σ.1 x) ^ S.α) ^ S.α⁻¹

theorem Pσ_eq (σ : S.toEZ.Policy) (v : W × E → ℝ) (x : W × E) :
    S.toEZ.Pσ σ (fun x' => v x' ^ S.ν) x = ∑ e, v (σ.1 x, e) ^ S.ν * S.φ e := by
  change ∑ x', v x' ^ S.ν * (if x'.1 = σ.1 x then S.φ x'.2 else 0) = _
  rw [Fintype.sum_prod_type_right]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Exercise 5.3.1** (p. 179): `G_σ ∘ F = T_σ`, the Epstein–Zin policy operator (5.34). -/
theorem exercise_5_3_1 (σ : S.toEZ.Policy) (v : W × E → ℝ) :
    S.Graw σ (S.Fraw v) = S.toEZ.Tσ σ v := by
  funext x
  have h := S.Pσ_eq σ v x
  change ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * S.Fraw v (σ.1 x) ^ S.α) ^ S.α⁻¹ =
    ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α +
      S.β * (S.toEZ.Pσ σ (fun x' => v x' ^ S.ν) x ^ S.ν⁻¹) ^ S.α) ^ S.α⁻¹
  rw [h]
  rfl

/-- `V̂ = F(V)`. -/
def Vhat : Set (W → ℝ) := {h | ∃ v ∈ S.toEZ.V, S.Fraw v = h}

theorem Fraw_pos {v : W × E → ℝ} (hv : v ∈ S.toEZ.V) (w : W) : 0 < S.Fraw v w :=
  Real.rpow_pos_of_pos (powerSum_pos S.φ_nonneg S.φ_sum (u := fun e => v (w, e))
    fun e => hv.1 (w, e)) _

theorem Graw_mem (σ : S.toEZ.Policy) {h : W → ℝ} (hh : h ∈ S.Vhat) : S.Graw σ h ∈ S.toEZ.V := by
  obtain ⟨v, hv, rfl⟩ := hh
  rw [S.exercise_5_3_1]
  exact S.toEZ.Tσ_mem σ hv

/-- The FDP `(V, F, V̂, 𝔾)` of §5.3.3. -/
noncomputable def fdp : FDP S.toEZ.V S.Vhat S.toEZ.Policy where
  F v := ⟨S.Fraw v.1, v.1, v.2, rfl⟩
  G σ h := ⟨S.Graw σ h.1, S.Graw_mem σ h.2⟩
  greatest h := by
    choose σ hσ hmax using fun x => Finset.exists_max_image (S.Γ x)
      (fun w' => ((1 - S.β) * S.r x.1 w' x.2 ^ S.α + S.β * h.1 w' ^ S.α) ^ S.α⁻¹)
      (S.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmax x (τ.1 x) (τ.2 x)⟩
  nonempty := S.toEZ.nonempty_policy

theorem Vhat_pos {h : W → ℝ} (hh : h ∈ S.Vhat) (w : W) : 0 < h w := by
  obtain ⟨v, hv, rfl⟩ := hh
  exact S.Fraw_pos hv w

/-- The FDP of §5.3.3 is order preserving. -/
theorem fdp_isOrderPreserving : S.fdp.IsOrderPreserving := by
  refine ⟨fun v v' hle w => ?_, fun σ h h' hle x => ?_⟩
  · exact powerMean_mono S.φ_nonneg S.φ_sum S.ν_ne (fun e => v.2.1 (w, e)) fun e => hle (w, e)
  · exact aggr_mono S.β_nonneg S.β_lt_one (Real.rpow_pos_of_pos (S.r_pos _ _ _) _) S.α_ne
      (S.Vhat_pos h.2 _) (hle _)

theorem fdp_monotonic : S.fdp.Monotonic := Or.inl S.fdp_isOrderPreserving

/-- The primary ADP coincides with the Epstein–Zin ADP `(V, 𝕋_EZ)`: they are isomorphic under the
identity (Exercise 5.3.1). -/
theorem primary_isIsomorphic :
    (S.fdp.primary S.fdp_monotonic).IsIsomorphic S.toEZ.adp (OrderIso.refl _) := fun σ v =>
  Subtype.ext (S.exercise_5_3_1 σ v.1)

/-- **Exercise 5.3.2** (p. 180): the subordinate policy operators (5.35),
`(T̂_σ h)(w) = {∑_e {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{ν/α} φ(e)}^{1/ν}`. -/
theorem exercise_5_3_2 (σ : S.toEZ.Policy) (h : S.Vhat) (w : W) :
    ((S.fdp.sub S.fdp_monotonic).T σ h).1 w =
      (∑ e, ((1 - S.β) * S.r w (σ.1 (w, e)) e ^ S.α + S.β * h.1 (σ.1 (w, e)) ^ S.α) ^
        (S.ν / S.α) * S.φ e) ^ S.ν⁻¹ := by
  change (∑ e, S.Graw σ h.1 (w, e) ^ S.ν * S.φ e) ^ S.ν⁻¹ = _
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Graw, ← Real.rpow_mul, div_eq_inv_mul]
  exact add_nonneg (mul_nonneg (sub_pos.2 S.β_lt_one).le
    (Real.rpow_pos_of_pos (S.r_pos _ _ _) _).le)
    (mul_nonneg S.β_nonneg (Real.rpow_pos_of_pos (S.Vhat_pos h.2 _) _).le)

/-- §5.3.3 (pp. 180–181): the fundamental optimality properties hold for the Epstein–Zin savings
model and for its subordinate ADP; any `σ` satisfying (5.33) at `h = v̂*` is optimal; and HPI on
the subordinate ADP reaches `v̂*` in finitely many steps from every `ĥ ∈ V̂_U` (Algorithm 5.1). -/
theorem section_5_3_3 :
    ∃ (hw : S.toEZ.adp.WellPosed) (hw' : (S.fdp.sub S.fdp_monotonic).WellPosed),
      S.toEZ.adp.FundamentalOptimality hw ∧
      (S.fdp.sub S.fdp_monotonic).FundamentalOptimality hw' ∧
      (∀ hstar σ, (S.fdp.sub S.fdp_monotonic).IsValueFunction hstar →
        (∀ x, ∀ w' ∈ S.Γ x, ((1 - S.β) * S.r x.1 w' x.2 ^ S.α + S.β * hstar.1 w' ^ S.α) ^ S.α⁻¹ ≤
          ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * hstar.1 (σ.1 x) ^ S.α) ^ S.α⁻¹) →
        S.toEZ.adp.IsOptimal hw σ) ∧
      ∀ g, (S.fdp.sub S.fdp_monotonic).IsSelector g → ∀ h ∈ (S.fdp.sub S.fdp_monotonic).VU,
        ∃ n, (S.fdp.sub S.fdp_monotonic).IsValueFunction
          (((S.fdp.sub S.fdp_monotonic).howard hw' g)^[n] h) := by
  have hm := S.fdp_monotonic
  have hP := S.fdp_isOrderPreserving
  have hiso := S.primary_isIsomorphic
  obtain ⟨hw, hFO, -⟩ := S.toEZ.proposition_5_1_13
  have hwp : (S.fdp.primary hm).WellPosed := hiso.wellPosed_iff.2 hw
  have hosP : (S.fdp.primary hm).IsOrderStable := hiso.orderStable_iff.2 S.toEZ.adp_isOrderStable
  have hosS : (S.fdp.sub hm).IsOrderStable := (FDP.lemma_5_2_12 hm).2.1.2 hosP
  have hw' : (S.fdp.sub hm).WellPosed := hosS.wellPosed
  have hFOp : (S.fdp.primary hm).FundamentalOptimality hwp :=
    (hiso.fundamentalOptimality_iff hwp hw).2 hFO
  have key := FDP.theorem_5_2_13 hm hP hwp hw'
  have hFOs := key.1.1 hFOp
  have hfin : (S.fdp.sub hm).IsFinite := by
    have := S.toEZ.finite_policy
    exact Set.finite_range _
  have hreg : (S.fdp.sub hm).Regular := FDP.sub_regular hm hP.1
  refine ⟨hw, hw', hFO, hFOs, fun hstar σ hv hσ => ?_, fun g hg h hh => ?_⟩
  · have hopt := (key.2 hFOp).2.1 hstar σ hv (le_antisymm (S.fdp.G_le_Gsup σ hstar)
      fun x => ?_)
    · exact (hiso.isOptimal_iff hwp hw σ).1 hopt
    · exact hσ x _ ((S.fdp.gsel hstar).2 x)
  · obtain ⟨-, hn⟩ := ADP.fundamentalOptimality_of_finite hosS hreg hfin
    exact hn g hg h hh

end EZSavings

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firm entry

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.1.3 (pp. 163–166).

Firm value solves (5.18), `v(z, f) = max{s(z) − f, β(z) ∫∫ v(z', f')φ(df')Q(z, dz')}`, with an
exogenous state `z` (kernel `Q`), an iid fixed cost `f ≥ 0` (distribution `φ`) and a state-dependent
discount factor `β(z) ≥ 0`. Here the cost is a nonnegative measurable function `c` of a draw from
`φ` on any measurable space.

* `S = G ∘ F` on `bX` and `T = F ∘ G` on `bZ`, with `(Fv)(z) = ∫ v(z, f)φ(df)` and
  `(Gw)(z, f) = max{s(z) − f, β(z) ∫ w(z')Q(z, dz')}`: **Lemma 5.2.6**.
* **Lemma 5.2.5**: under Assumption 5.2.1, `T` is strongly order stable on `bZ`. Condition (iii),
  `sup_z 𝔼_z ∏_{t<n} β(Z_t) < 1`, is stated as `sup_z (Kⁿ𝟙)(z) < 1` for the discount operator
  `(Kh)(z) = β(z) ∫ h(z')Q(z, dz')` (the two agree by Lemma 6.1.4); then `T` is an order contraction
  of modulus `K` (Theorem 4.1.4).
* **Lemma 5.2.8**: `G` preserves increasing and decreasing limits (dominated convergence; the
  book proves the increasing case).
* **Proposition 5.2.7**: (5.18) has a unique solution `v̄ ∈ bX`, and `w ≼ Tw ⟹ GTⁿw ↑ v̄`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace BM

variable {X : Type*} [MeasurableSpace X]

/-- **Lemma A.1.3** in `bX`: `fₙ ↑ w` gives pointwise convergence. -/
theorem tendsto_of_isLUB {f : ℕ → BM X} {w : BM X} (hf : Monotone f) (hl : IsLUB (range f) w)
    (x : X) : Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x)) := by
  have hbdd : ∀ y, BddAbove (range fun n => (f n).toFun y) := fun y =>
    ⟨w.toFun y, by rintro _ ⟨n, rfl⟩; exact hl.1 ⟨n, rfl⟩ y⟩
  let g : BM X := ⟨fun y => ⨆ n, (f n).toFun y, Measurable.iSup fun n => (f n).measurable',
    ⟨‖f 0‖ + ‖w‖, fun y => abs_le.2 ⟨by
      have h1 := le_ciSup (hbdd y) 0
      have h2 := abs_le.1 (abs_le_norm (f 0) y)
      have h3 := norm_nonneg w
      linarith, by
      have h1 : (⨆ n, (f n).toFun y) ≤ w.toFun y := ciSup_le fun n => hl.1 ⟨n, rfl⟩ y
      have h2 := abs_le.1 (abs_le_norm w y)
      have h3 := norm_nonneg (f 0)
      linarith⟩⟩⟩
  have hgw : g = w := le_antisymm (fun y => ciSup_le fun n => hl.1 ⟨n, rfl⟩ y)
    (hl.2 (by rintro _ ⟨n, rfl⟩; exact fun y => le_ciSup (hbdd y) n))
  have hx : w.toFun x = ⨆ n, (f n).toFun x := by rw [← hgw]
  rw [hx]
  exact tendsto_atTop_ciSup (fun a b h => hf h x) (hbdd x)

/-- **Lemma A.1.3** in `bX`: `fₙ ↓ w` gives pointwise convergence. -/
theorem tendsto_of_isGLB {f : ℕ → BM X} {w : BM X} (hf : Antitone f) (hl : IsGLB (range f) w)
    (x : X) : Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x)) := by
  have hbdd : ∀ y, BddBelow (range fun n => (f n).toFun y) := fun y =>
    ⟨w.toFun y, by rintro _ ⟨n, rfl⟩; exact hl.1 ⟨n, rfl⟩ y⟩
  let g : BM X := ⟨fun y => ⨅ n, (f n).toFun y, Measurable.iInf fun n => (f n).measurable',
    ⟨‖f 0‖ + ‖w‖, fun y => abs_le.2 ⟨by
      have h1 : w.toFun y ≤ ⨅ n, (f n).toFun y := le_ciInf fun n => hl.1 ⟨n, rfl⟩ y
      have h2 := abs_le.1 (abs_le_norm w y)
      have h3 := norm_nonneg (f 0)
      linarith, by
      have h1 := ciInf_le (hbdd y) 0
      have h2 := abs_le.1 (abs_le_norm (f 0) y)
      have h3 := norm_nonneg w
      linarith⟩⟩⟩
  have hgw : g = w := le_antisymm
    (hl.2 (by rintro _ ⟨n, rfl⟩; exact fun y => ciInf_le (hbdd y) n))
    (fun y => le_ciInf fun n => hl.1 ⟨n, rfl⟩ y)
  have hx : w.toFun x = ⨅ n, (f n).toFun x := by rw [← hgw]
  rw [hx]
  exact tendsto_atTop_ciInf (fun a b h => hf h x) (hbdd x)

/-- Pointwise increasing convergence is `↑` in `bX`. -/
theorem isLUB_of_tendsto {f : ℕ → BM X} {w : BM X} (hf : Monotone f)
    (h : ∀ x, Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x))) : IsLUB (range f) w :=
  ⟨by rintro _ ⟨n, rfl⟩ x; exact Monotone.ge_of_tendsto (fun a b hab => hf hab x) (h x) n,
    fun _ hu x => le_of_tendsto' (h x) fun n => hu ⟨n, rfl⟩ x⟩

/-- Pointwise decreasing convergence is `↓` in `bX`. -/
theorem isGLB_of_tendsto {f : ℕ → BM X} {w : BM X} (hf : Antitone f)
    (h : ∀ x, Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x))) : IsGLB (range f) w :=
  ⟨by rintro _ ⟨n, rfl⟩ x; exact Antitone.le_of_tendsto (fun a b hab => hf hab x) (h x) n,
    fun _ hu x => ge_of_tendsto' (h x) fun n => hu ⟨n, rfl⟩ x⟩

/-- Integrals against a Markov kernel commute with `↑` and `↓` limits (dominated convergence). -/
theorem tendsto_markov {P : Kernel X X} [IsMarkovKernel P] {f : ℕ → BM X} {w : BM X} {B : ℝ}
    (hB : ∀ n y, |(f n).toFun y| ≤ B)
    (h : ∀ y, Tendsto (fun n => (f n).toFun y) atTop (𝓝 (w.toFun y))) (x : X) :
    Tendsto (fun n => (markovCLM P (f n)).toFun x) atTop (𝓝 ((markovCLM P w).toFun x)) := by
  simp only [markovCLM_apply, markovOp]
  exact tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (f n).measurable'.aestronglyMeasurable) (integrable_const B)
    (fun n => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB n y)
    (Eventually.of_forall h)

end BM

/-- The firm entry model of §5.2.1.3. -/
structure FirmEntry (Z Ef : Type*) [MeasurableSpace Z] [MeasurableSpace Ef] where
  /-- the exogenous kernel -/
  Q : Kernel Z Z
  [Q_markov : IsMarkovKernel Q]
  /-- the distribution of the fixed-cost draw -/
  φ : Measure Ef
  [φ_prob : IsProbabilityMeasure φ]
  /-- the fixed cost -/
  c : Ef → ℝ
  c_meas : Measurable c
  c_nonneg : ∀ f, 0 ≤ c f
  /-- the entry profit `s` -/
  s : BM Z
  /-- the discount factor `β(z) ≥ 0` -/
  β : BM Z
  β_nonneg : 0 ≤ β

namespace FirmEntry

attribute [local instance] FirmEntry.Q_markov FirmEntry.φ_prob

variable {Z Ef : Type*} [MeasurableSpace Z] [MeasurableSpace Ef] (M : FirmEntry Z Ef)

theorem integrable_section (v : BM (Z × Ef)) (z : Z) :
    Integrable (fun f => v.toFun (z, f)) M.φ :=
  Integrable.of_bound (v.measurable'.comp measurable_prodMk_left).aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

/-- `(Fv)(z) = ∫ v(z, f)φ(df)`. -/
noncomputable def F (v : BM (Z × Ef)) : BM Z :=
  ⟨fun z => ∫ f, v.toFun (z, f) ∂M.φ,
    (v.measurable'.stronglyMeasurable.integral_prod_right' (ν := M.φ)).measurable,
    ⟨‖v‖, fun z => by
      have := norm_integral_le_of_norm_le_const (μ := M.φ) (f := fun f => v.toFun (z, f))
        (C := ‖v‖) (Eventually.of_forall fun f => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
      simpa using this⟩⟩

/-- `(Gw)(z, f) = max{s(z) − c(f), β(z) ∫ w(z')Q(z, dz')}`. -/
noncomputable def G (w : BM Z) : BM (Z × Ef) :=
  ⟨fun x => max (M.s.toFun x.1 - M.c x.2) (M.β.toFun x.1 * (BM.markovCLM M.Q w).toFun x.1),
    ((M.s.measurable'.comp measurable_fst).sub (M.c_meas.comp measurable_snd)).max
      ((M.β.measurable'.comp measurable_fst).mul
        ((BM.markovCLM M.Q w).measurable'.comp measurable_fst)),
    ⟨‖M.s‖ + ‖M.β‖ * ‖w‖, fun x => by
      have hb : |M.β.toFun x.1 * (BM.markovCLM M.Q w).toFun x.1| ≤ ‖M.β‖ * ‖w‖ := by
        rw [abs_mul, BM.markovCLM_apply]
        exact mul_le_mul (BM.abs_le_norm _ _) (abs_markovOp_le M.Q (BM.abs_le_norm w) _)
          (abs_nonneg _) (norm_nonneg _)
      have hs := abs_le.1 (BM.abs_le_norm M.s x.1)
      have hc := M.c_nonneg x.2
      have hb' := abs_le.1 hb
      have hn := norm_nonneg M.s
      refine abs_le.2 ⟨?_, max_le (by linarith) (by linarith)⟩
      exact (by linarith : -(‖M.s‖ + ‖M.β‖ * ‖w‖) ≤ _).trans (le_max_right _ _)⟩⟩

/-- The firm value operator `S = G ∘ F` on `bX`. -/
noncomputable def S (v : BM (Z × Ef)) : BM (Z × Ef) := M.G (M.F v)

/-- The low-dimensional operator `T = F ∘ G` on `bZ`. -/
noncomputable def T (w : BM Z) : BM Z := M.F (M.G w)

/-- `S` is the operator of (5.18):
`(Sv)(z, f) = max{s(z) − c(f), β(z) ∫∫ v(z', f')φ(df')Q(z, dz')}`. -/
theorem S_apply (v : BM (Z × Ef)) (x : Z × Ef) :
    (M.S v).toFun x = max (M.s.toFun x.1 - M.c x.2)
      (M.β.toFun x.1 * ∫ z', (∫ f', v.toFun (z', f') ∂M.φ) ∂(M.Q x.1)) := rfl

/-- `(Tw)(z) = ∫ max{s(z) − c(f), β(z) ∫ w(z')Q(z, dz')} φ(df)`. -/
theorem T_apply (w : BM Z) (z : Z) :
    (M.T w).toFun z = ∫ f, max (M.s.toFun z - M.c f)
      (M.β.toFun z * ∫ z', w.toFun z' ∂(M.Q z)) ∂M.φ := rfl

theorem F_mono : Monotone M.F := fun _ _ h z =>
  integral_mono (M.integrable_section _ z) (M.integrable_section _ z) fun f => h (z, f)

theorem G_mono : Monotone M.G := fun _ _ h x =>
  max_le_max le_rfl (mul_le_mul_of_nonneg_left (BM.markovCLM_isPositive M.Q |>.mono h x.1)
    (M.β_nonneg x.1))

/-- **Lemma 5.2.6** (p. 165): `(bX, S)` and `(bZ, T)` are strongly semiconjugate under the order
preserving maps `F, G`. -/
theorem lemma_5_2_6 : IsStronglySemiconj M.S M.T M.F M.G ∧ Monotone M.F ∧ Monotone M.G :=
  ⟨⟨fun _ => rfl, fun _ => rfl⟩, M.F_mono, M.G_mono⟩

/-- The discount operator `(Kh)(z) = β(z) ∫ h(z')Q(z, dz')` of (6.10). -/
noncomputable def K : BM Z →L[ℝ] BM Z := (BM.mulCLM M.β).comp (BM.markovCLM M.Q)

theorem K_isPositive : BanachLattice.IsPositiveOp M.K := fun h hh =>
  BM.mulCLM_isPositive M.β_nonneg _ (BM.markovCLM_isPositive M.Q h hh)

/-- `|Tw₁ − Tw₂| ≤ K|w₁ − w₂|` (proof of Lemma 5.2.5). -/
theorem abs_T_sub_le (w₁ w₂ : BM Z) : |M.T w₁ - M.T w₂| ≤ M.K |w₁ - w₂| := fun z => by
  have hpt : ∀ f, |(M.G w₁).toFun (z, f) - (M.G w₂).toFun (z, f)| ≤ (M.K |w₁ - w₂|).toFun z :=
    fun f => by
      refine (abs_max_sub_max_le _ _ _).trans ?_
      change |M.β.toFun z * _ - M.β.toFun z * _| ≤
        M.β.toFun z * (BM.markovCLM M.Q |w₁ - w₂|).toFun z
      rw [← mul_sub, abs_mul, abs_of_nonneg (M.β_nonneg z)]
      refine mul_le_mul_of_nonneg_left ?_ (M.β_nonneg z)
      have h1 := (BM.markovCLM_isPositive M.Q).abs_le (w₁ - w₂) z
      rw [map_sub] at h1
      exact h1
  change |∫ f, (M.G w₁).toFun (z, f) ∂M.φ - ∫ f, (M.G w₂).toFun (z, f) ∂M.φ| ≤ _
  rw [← integral_sub (M.integrable_section _ z) (M.integrable_section _ z)]
  have := norm_integral_le_of_norm_le_const (μ := M.φ)
    (f := fun f => (M.G w₁).toFun (z, f) - (M.G w₂).toFun (z, f))
    (C := (M.K |w₁ - w₂|).toFun z) (Eventually.of_forall fun f => by
      rw [Real.norm_eq_abs]; exact hpt f)
  simpa using this

/-- Assumption 5.2.1 (iii), in operator form: `sup_z (Kⁿ𝟙)(z) ≤ λ < 1` for some `n ≥ 1`. -/
def DiscountCondition : Prop :=
  ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ z, ((M.K ^ n) (BM.const 1)).toFun z ≤ lam

theorem K_isDiscountOperator (hA : M.DiscountCondition) : BanachLattice.IsDiscountOperator M.K := by
  obtain ⟨n, hn, lam, hlam0, hlam1, hK⟩ := hA
  refine ⟨map_zero _, fun h hh => M.K_isPositive h hh, fun u hu v _ huv => M.K_isPositive.mono huv,
    n, hn, lam, hlam0, hlam1, fun u _ v _ => ?_⟩
  rw [← FunLike.coe_pow_eq_iterate, ← map_sub]
  refine BM.norm_le (mul_nonneg hlam0 (norm_nonneg _)) fun z => ?_
  have hpos := M.K_isPositive.iterate n
  have h1 := hpos.abs_le (u - v) z
  have h2 : |u - v| ≤ ‖u - v‖ • BM.const 1 := fun y => by
    simp only [BM.abs_apply, BM.smul_apply, BM.const_apply, mul_one]
    exact BM.abs_le_norm _ y
  have h3 := hpos.mono h2 z
  rw [map_smul] at h3
  simp only [BM.abs_apply, BM.smul_apply] at h1 h3
  calc |((M.K ^ n) (u - v)).toFun z| ≤ ((M.K ^ n) |u - v|).toFun z := h1
    _ ≤ ‖u - v‖ * ((M.K ^ n) (BM.const 1)).toFun z := h3
    _ ≤ ‖u - v‖ * lam := mul_le_mul_of_nonneg_left (hK z) (norm_nonneg _)
    _ = lam * ‖u - v‖ := mul_comm _ _

/-- **Lemma 5.2.5** (p. 165): under Assumption 5.2.1, `T` is strongly order stable on `bZ`. -/
theorem lemma_5_2_5 (hA : M.DiscountCondition) : StronglyOrderStable M.T := by
  have : Nonempty (BM Z) := ⟨0⟩
  have hι : BanachLattice.IsIsoOrderEmbedding (id : BM Z → BM Z) :=
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩
  have hgs := (BanachLattice.theorem_4_1_4 hι ⟨M.K_isDiscountOperator hA,
    fun v w => M.abs_T_sub_le v w⟩).1
  exact stronglyOrderStable_of_globallyStable (M.F_mono.comp M.G_mono) hgs

theorem tendsto_G {f : ℕ → BM Z} {w : BM Z} {B : ℝ} (hB : ∀ n y, |(f n).toFun y| ≤ B)
    (h : ∀ y, Tendsto (fun n => (f n).toFun y) atTop (𝓝 (w.toFun y))) (x : Z × Ef) :
    Tendsto (fun n => (M.G (f n)).toFun x) atTop (𝓝 ((M.G w).toFun x)) :=
  tendsto_const_nhds.max ((BM.tendsto_markov hB h x.1).const_mul _)

/-- **Lemma 5.2.8** (p. 166): `G` is order continuous, and it also preserves decreasing
limits. -/
theorem lemma_5_2_8 : OrderContinuous M.G ∧ OrderContinuousDown M.G := by
  refine ⟨fun f w hf hl => ?_, fun f w hf hl => ?_⟩
  · have hpt := BM.tendsto_of_isLUB hf hl
    have hB : ∀ n y, |(f n).toFun y| ≤ ‖f 0‖ + ‖w‖ := fun n y => abs_le.2
      ⟨by linarith [abs_le.1 (BM.abs_le_norm (f 0) y), hf (Nat.zero_le n) y, norm_nonneg w],
        by linarith [abs_le.1 (BM.abs_le_norm w y), hl.1 ⟨n, rfl⟩ y, norm_nonneg (f 0)]⟩
    exact BM.isLUB_of_tendsto (M.G_mono.comp hf) (M.tendsto_G hB hpt)
  · have hpt := BM.tendsto_of_isGLB hf hl
    have hB : ∀ n y, |(f n).toFun y| ≤ ‖f 0‖ + ‖w‖ := fun n y => abs_le.2
      ⟨by linarith [abs_le.1 (BM.abs_le_norm w y), hl.1 ⟨n, rfl⟩ y, norm_nonneg (f 0)],
        by linarith [abs_le.1 (BM.abs_le_norm (f 0) y), hf (Nat.zero_le n) y, norm_nonneg w]⟩
    exact BM.isGLB_of_tendsto (M.G_mono.comp_antitone hf) (M.tendsto_G hB hpt)

/-- **Proposition 5.2.7** (p. 166): under Assumption 5.2.1, the firm valuation equation (5.18) has
a unique solution `v̄` in `bX`, and `w ≼ Tw ⟹ GTⁿw ↑ v̄` for `w ∈ bZ`. -/
theorem proposition_5_2_7 (hA : M.DiscountCondition) :
    ∃ vbar, M.S vbar = vbar ∧ (∀ v, M.S v = v → v = vbar) ∧
      ∀ w, w ≤ M.T w → IncreasesTo (fun n => M.G (M.T^[n] w)) vbar := by
  have hT := M.lemma_5_2_5 hA
  obtain ⟨wbar, hwbar, -, -, -⟩ := id hT
  obtain ⟨h, hF, hG⟩ := M.lemma_5_2_6
  obtain ⟨hGu, hGd⟩ := M.lemma_5_2_8
  obtain ⟨hS, hfix, hconv⟩ := h.theorem_5_2_3 hF hG hGu hGd hT hwbar
  obtain ⟨u, hu, huniq, -, -⟩ := hS
  refine ⟨M.G wbar, hfix, fun v hv => (huniq v hv).trans (huniq _ hfix).symm, hconv⟩

end FirmEntry

end SargentStachurski.ADPTransformations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Strong order stability does not transfer under one-sided order continuity

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Lemma 5.2.2 (ii), Theorem 5.2.3 and
Theorem 5.2.4 (pp. 162–163).

The book's order continuity (§A.5.1.3) asks only that `vₙ ↑ v` imply `Svₙ ↑ Sv`. With that
reading the three results fail:

* `Fork` is a chain `a₀ > a₁ > a₂ > ⋯` above two incomparable minimal points `⊥₁, ⊥₂`, and
  `Chain = ℕ∞ᵒᵈ` is `0 > 1 > 2 > ⋯ > ⊤`. In both, every increasing sequence is eventually
  constant, so every order preserving map out of them is order continuous.
* `S(aₙ) = aₙ₊₁`, `S(⊥ᵢ) = ⊥₁` on `Fork` and `Ŝc = c + 1` on `Chain` are strongly semiconjugate
  under order preserving, order continuous maps `F, G`. `Ŝ` is strongly order stable, but
  `Sⁿa₀ = aₙ` decreases without an infimum (`⊥₁` and `⊥₂` are both maximal lower bounds), so `S`
  is not (`theorem_5_2_3_fails`): this contradicts Lemma 5.2.2 (ii) and Theorem 5.2.3.
* Reversing the order of `Chain` gives order-reversing `F, G` satisfying the hypothesis of
  Theorem 5.2.4 with the same conclusion failing (`theorem_5_2_4_fails`).

The proofs of the corrected statements in `Semiconjugacy` also use decreasing limits.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- If every increasing sequence in `V` is eventually constant, every order preserving map out of
`V` is order continuous. -/
theorem orderContinuous_of_stabilizes {V W : Type*} [PartialOrder V] [PartialOrder W]
    (hV : ∀ f : ℕ → V, Monotone f → ∃ n, ∀ m, n ≤ m → f m = f n) {S : V → W} (hS : Monotone S) :
    OrderContinuous S := by
  intro f v hf hl
  obtain ⟨n, hn⟩ := hV f hf
  have hv : v = f n := le_antisymm (hl.2 fun _ ⟨m, hm⟩ => hm ▸ (by
    rcases le_total m n with h | h
    · exact hf h
    · exact (hn m h).le)) (hl.1 ⟨n, rfl⟩)
  subst hv
  refine ⟨fun _ ⟨m, hm⟩ => hm ▸ (by
    rcases le_total m n with h | h
    · exact hS (hf h)
    · exact (congrArg S (hn m h)).le), fun b hb => hb ⟨n, rfl⟩⟩

namespace SemiconjCounterexample

/-- A decreasing chain `a₀ > a₁ > ⋯` above two incomparable minimal points `⊥₁` and `⊥₂`:
`inl n` is `aₙ`, `inr false` is `⊥₁` and `inr true` is `⊥₂`. -/
def Fork : Type := ℕ ⊕ Bool

/-- `aₙ`. -/
def Fork.a (n : ℕ) : Fork := Sum.inl n

/-- `⊥₁`. -/
def Fork.bot₁ : Fork := Sum.inr false

/-- `⊥₂`. -/
def Fork.bot₂ : Fork := Sum.inr true

/-- The order of `Fork`. -/
def Fork.le : Fork → Fork → Prop
  | Sum.inl m, Sum.inl n => n ≤ m
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr b, Sum.inr b' => b = b'
  | Sum.inl _, Sum.inr _ => False

theorem Fork.le_refl' : ∀ x : Fork, Fork.le x x
  | Sum.inl _ => le_rfl
  | Sum.inr _ => rfl

theorem Fork.le_trans' : ∀ x y z : Fork, Fork.le x y → Fork.le y z → Fork.le x z
  | Sum.inl _, Sum.inl _, Sum.inl _, h1, h2 => le_trans h2 h1
  | Sum.inr _, Sum.inl _, Sum.inl _, _, _ => trivial
  | Sum.inr _, Sum.inr _, Sum.inl _, _, _ => trivial
  | Sum.inr _, Sum.inr _, Sum.inr _, h1, h2 => h1.trans h2
  | Sum.inl _, Sum.inr _, _, h, _ => False.elim h
  | _, Sum.inl _, Sum.inr _, _, h => False.elim h

theorem Fork.le_antisymm' : ∀ x y : Fork, Fork.le x y → Fork.le y x → x = y
  | Sum.inl _, Sum.inl _, h1, h2 => congrArg Sum.inl (le_antisymm h2 h1)
  | Sum.inr _, Sum.inr _, h, _ => congrArg Sum.inr h
  | Sum.inl _, Sum.inr _, h, _ => False.elim h
  | Sum.inr _, Sum.inl _, _, h => False.elim h

/-- `Fork` as a partial order. -/
abbrev forkOrder : PartialOrder Fork where
  le := Fork.le
  le_refl := Fork.le_refl'
  le_trans := Fork.le_trans'
  le_antisymm := Fork.le_antisymm'

attribute [local instance] forkOrder

/-- `ℕ∞` with the reversed order: `0 > 1 > 2 > ⋯ > ⊤`. -/
abbrev Chain : Type := ℕ∞ᵒᵈ

/-- `Ŝc = c + 1` on `Chain`. -/
def shift (c : Chain) : Chain := OrderDual.toDual (OrderDual.ofDual c + 1)

/-- `F : Fork → Chain`, `aₙ ↦ n + 1`, `⊥ᵢ ↦ ⊤`. -/
def Fmap : Fork → Chain
  | Sum.inl n => OrderDual.toDual ((n : ℕ∞) + 1)
  | Sum.inr _ => OrderDual.toDual ⊤

/-- `G : Chain → Fork`, `n ↦ aₙ`, `⊤ ↦ ⊥₁`. -/
noncomputable def Gmap (c : Chain) : Fork :=
  if OrderDual.ofDual c = ⊤ then Fork.bot₁ else Fork.a (OrderDual.ofDual c).toNat

/-- `S : Fork → Fork`, `aₙ ↦ aₙ₊₁`, `⊥ᵢ ↦ ⊥₁`. -/
def Smap : Fork → Fork
  | Sum.inl n => Fork.a (n + 1)
  | Sum.inr _ => Fork.bot₁

theorem le_a_iff {m n : ℕ} : Fork.a m ≤ Fork.a n ↔ n ≤ m := Iff.rfl

theorem isStronglySemiconj : IsStronglySemiconj Smap shift Fmap Gmap := by
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rcases x with n | b
    · have h : ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
      simp only [Smap, Fmap, Gmap, OrderDual.ofDual_toDual, h, ENat.natCast_ne_top, ite_false,
        ENat.toNat_natCast]
    · simp [Smap, Fmap, Gmap]
  · induction c using OrderDual.rec with
    | toDual e =>
      cases e using ENat.recTopCoe with
      | top => simp [shift, Fmap, Gmap, Fork.bot₁]
      | coe k => simp [shift, Fmap, Gmap, Fork.a]

theorem Fmap_mono : Monotone Fmap := by
  intro x y hxy
  rcases x with m | b <;> rcases y with n | b'
  all_goals first
    | exact (OrderDual.toDual_le_toDual.2 (by exact_mod_cast Nat.add_le_add_right hxy 1))
    | exact OrderDual.toDual_le_toDual.2 le_top
    | exact le_rfl
    | exact absurd hxy id

theorem Gmap_mono : Monotone Gmap := by
  intro c c' hcc'
  induction c using OrderDual.rec with
  | toDual e =>
  induction c' using OrderDual.rec with
  | toDual e' =>
  have h : e' ≤ e := OrderDual.toDual_le_toDual.1 hcc'
  cases e using ENat.recTopCoe with
  | top =>
    cases e' using ENat.recTopCoe with
    | top => exact le_rfl
    | coe j =>
      simp only [Gmap, OrderDual.ofDual_toDual, ENat.natCast_ne_top, ite_false, ite_true]
      exact trivial
  | coe k =>
    cases e' using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe j =>
      simp only [Gmap, OrderDual.ofDual_toDual, ENat.natCast_ne_top, ite_false,
        ENat.toNat_natCast]
      exact le_a_iff.2 (by exact_mod_cast h)

/-- Every increasing sequence in `Chain` is eventually constant. -/
theorem chain_stabilizes (f : ℕ → Chain) (hf : Monotone f) : ∃ n, ∀ m, n ≤ m → f m = f n := by
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition (α := Chain) ⟨f, hf⟩
  exact ⟨n, fun m hm => (hn m hm).symm⟩

/-- The rank of a point of `Fork` in `Chain`. -/
def rank : Fork → Chain
  | Sum.inl n => OrderDual.toDual (n : ℕ∞)
  | Sum.inr _ => OrderDual.toDual ⊤

theorem rank_strictMono : StrictMono rank := by
  intro x y hxy
  have hle : x ≤ y := hxy.le
  have hne : x ≠ y := hxy.ne
  rcases x with m | b <;> rcases y with n | b'
  · have h1 : n ≤ m := hle
    have h2 : n ≠ m := fun h => hne (by rw [h])
    exact OrderDual.toDual_lt_toDual.2 (by exact_mod_cast lt_of_le_of_ne h1 h2)
  · exact False.elim hle
  · exact OrderDual.toDual_lt_toDual.2 (ENat.natCast_lt_top _)
  · exact absurd (congrArg Sum.inr hle) hne

/-- Every increasing sequence in `Fork` is eventually constant. -/
theorem fork_stabilizes (f : ℕ → Fork) (hf : Monotone f) : ∃ n, ∀ m, n ≤ m → f m = f n := by
  obtain ⟨n, hn⟩ := chain_stabilizes (rank ∘ f) (rank_strictMono.monotone.comp hf)
  refine ⟨n, fun m hm => ?_⟩
  by_contra hne
  exact (rank_strictMono (lt_of_le_of_ne (hf hm) (Ne.symm hne))).ne (hn m hm).symm

theorem iterate_shift (c : Chain) (n : ℕ) :
    shift^[n] c = OrderDual.toDual (OrderDual.ofDual c + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [shift, OrderDual.ofDual_toDual, Nat.cast_succ, add_assoc]

theorem shift_stronglyOrderStable : StronglyOrderStable shift := by
  have htop : ∀ e : ℕ∞, e + 1 ≤ e → e = ⊤ := fun e he => by
    cases e using ENat.recTopCoe with
    | top => rfl
    | coe k => exact absurd (by exact_mod_cast he : k + 1 ≤ k) (by omega)
  refine ⟨OrderDual.toDual ⊤, by simp [shift], fun w hw => ?_, fun v hv => ?_, fun v _ => ?_⟩
  · change OrderDual.toDual (OrderDual.ofDual w + 1) = w at hw
    exact congrArg OrderDual.toDual (htop _ (le_of_eq (congrArg OrderDual.ofDual hw)))
  · have hv' : OrderDual.ofDual v = ⊤ := htop _ hv
    have hc : ∀ n, shift^[n] v = OrderDual.toDual ⊤ := fun n => by
      rw [iterate_shift, hv', top_add]
    refine ⟨fun a b _ => by dsimp only; rw [hc, hc], ?_⟩
    rw [show (fun n => shift^[n] v) = fun _ => OrderDual.toDual ⊤ from funext hc, Set.range_const]
    exact isLUB_singleton
  · refine ⟨fun a b hab => ?_, ?_⟩
    · dsimp only
      rw [iterate_shift, iterate_shift]
      exact OrderDual.toDual_le_toDual.2 (add_le_add le_rfl (by exact_mod_cast hab))
    · refine ⟨fun x _ => show OrderDual.ofDual x ≤ ⊤ from le_top, fun b hb => ?_⟩
      induction b using OrderDual.rec with
      | toDual e =>
      change ⊤ ≤ e
      cases e using ENat.recTopCoe with
      | top => exact le_rfl
      | coe k =>
        exfalso
        have := hb ⟨k + 1, rfl⟩
        dsimp only at this
        rw [iterate_shift] at this
        have h1 : OrderDual.ofDual v + ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) :=
          OrderDual.toDual_le_toDual.1 this
        have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ k := le_trans le_add_self h1
        exact absurd (by exact_mod_cast h2 : k + 1 ≤ k) (by omega)

theorem iterate_Smap (n : ℕ) : Smap^[n] (.a 0) = .a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ih]; rfl

theorem Smap_not_stronglyOrderStable : ¬ StronglyOrderStable Smap := by
  rintro ⟨u, -, huniq, -, hdown⟩
  have hu : Fork.bot₁ = u := huniq .bot₁ rfl
  subst hu
  obtain ⟨-, hglb⟩ := hdown (.a 0) (show Fork.a 1 ≤ Fork.a 0 from le_a_iff.2 (Nat.zero_le 1))
  have hlb : Fork.bot₂ ∈ lowerBounds (range fun n => Smap^[n] (Fork.a 0)) := by
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [iterate_Smap]
    trivial
  have h := hglb.2 hlb
  change (true : Bool) = false at h
  exact Bool.noConfusion h

/-- **Lemma 5.2.2 (ii) and Theorem 5.2.3 fail with the book's order continuity**: `(Fork, S)` and
`(Chain, Ŝ)` are strongly semiconjugate under order preserving, order continuous `F` and `G`,
and `Ŝ` is strongly order stable, but `S` is not. -/
theorem theorem_5_2_3_fails :
    IsStronglySemiconj Smap shift Fmap Gmap ∧ Monotone Fmap ∧ Monotone Gmap ∧
      OrderContinuous Fmap ∧ OrderContinuous Gmap ∧ StronglyOrderStable shift ∧
      ¬ StronglyOrderStable Smap :=
  ⟨isStronglySemiconj, Fmap_mono, Gmap_mono,
    orderContinuous_of_stabilizes fork_stabilizes Fmap_mono,
    orderContinuous_of_stabilizes chain_stabilizes Gmap_mono, shift_stronglyOrderStable,
    Smap_not_stronglyOrderStable⟩

/-- **Theorem 5.2.4 fails with its stated hypothesis on `G`**: reversing the order of `Chain`
gives order-reversing `F, G` with `wₙ ↓ w ⟹ Gwₙ ↑ Gw`, and `Ŝ` strongly order stable, but `S` is
not strongly order stable. -/
theorem theorem_5_2_4_fails :
    IsStronglySemiconj Smap (dualMap shift) (OrderDual.toDual ∘ Fmap) (Gmap ∘ OrderDual.ofDual) ∧
      Antitone (OrderDual.toDual ∘ Fmap) ∧ Antitone (Gmap ∘ OrderDual.ofDual) ∧
      AntiContinuousDown (Gmap ∘ OrderDual.ofDual) ∧ StronglyOrderStable (dualMap shift) ∧
      ¬ StronglyOrderStable Smap := by
  refine ⟨⟨isStronglySemiconj.1, fun c => congrArg OrderDual.toDual (isStronglySemiconj.2 _)⟩,
    fun _ _ h => Fmap_mono h, fun _ _ h => Gmap_mono h, fun f w hf hw => ?_,
    (stronglyOrderStable_dual_iff shift).2 shift_stronglyOrderStable,
    Smap_not_stronglyOrderStable⟩
  exact orderContinuous_of_stabilizes chain_stabilizes Gmap_mono (OrderDual.ofDual ∘ f)
    (OrderDual.ofDual w) (fun _ _ h => hf h) hw

end SemiconjCounterexample

end SargentStachurski.ADPTransformations

set_option linter.style.longLine false
#print axioms SargentStachurski.ADPTransformations.IsMarkov
#print axioms SargentStachurski.ADPTransformations.IsMarkov.mk
#print axioms SargentStachurski.ADPTransformations.IsMarkov.nonneg
#print axioms SargentStachurski.ADPTransformations.IsMarkov.rowsum
#print axioms SargentStachurski.ADPTransformations.IsDistribution
#print axioms SargentStachurski.ADPTransformations.IsDistribution.mk
#print axioms SargentStachurski.ADPTransformations.IsDistribution.nonneg
#print axioms SargentStachurski.ADPTransformations.IsDistribution.sum_eq_one
#print axioms SargentStachurski.ADPTransformations.mulVec_apply_eq
#print axioms SargentStachurski.ADPTransformations.IsMarkov.mul
#print axioms SargentStachurski.ADPTransformations.IsMarkov.pow
#print axioms SargentStachurski.ADPTransformations.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.ADPTransformations.IsMarkov.mulVec_const
#print axioms SargentStachurski.ADPTransformations.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.ADPTransformations.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.ADPTransformations.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.ADPTransformations.GloballyStable
#print axioms SargentStachurski.ADPTransformations.IsContractionOn
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.mk
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.mapsTo
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.nonneg
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.lt_one
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.iterate_mem
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.ADPTransformations.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.ADPTransformations.fixedPt_le_of_le
#print axioms SargentStachurski.ADPTransformations.le_fixedPt_of_le_apply
#print axioms SargentStachurski.ADPTransformations.isContractionOn_of_blackwell
#print axioms SargentStachurski.ADPTransformations.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.ADPTransformations.IsBdd
#print axioms SargentStachurski.ADPTransformations.IsSupContraction
#print axioms SargentStachurski.ADPTransformations.IsUniformlyClosed
#print axioms SargentStachurski.ADPTransformations.isBdd_const
#print axioms SargentStachurski.ADPTransformations.IsBdd.sub
#print axioms SargentStachurski.ADPTransformations.IsBdd.add
#print axioms SargentStachurski.ADPTransformations.IsBdd.nonneg_bound
#print axioms SargentStachurski.ADPTransformations.IsBdd.exists_dist
#print axioms SargentStachurski.ADPTransformations.IsSupContraction.iterate
#print axioms SargentStachurski.ADPTransformations.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.ADPTransformations.IsSupContraction.exists_limit
#print axioms SargentStachurski.ADPTransformations.IsSupContraction.globallyStable
#print axioms SargentStachurski.ADPTransformations.le_of_le_map_of_tendsto
#print axioms SargentStachurski.ADPTransformations.le_of_map_le_of_tendsto
#print axioms SargentStachurski.ADPTransformations.bX
#print axioms SargentStachurski.ADPTransformations.isUniformlyClosed_bX
#print axioms SargentStachurski.ADPTransformations.const_mem_bX
#print axioms SargentStachurski.ADPTransformations.abs_max_sub_max_le
#print axioms SargentStachurski.ADPTransformations.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.ADPTransformations.ContractingDP
#print axioms SargentStachurski.ADPTransformations.ContractingDP.mk
#print axioms SargentStachurski.ADPTransformations.ContractingDP.V
#print axioms SargentStachurski.ADPTransformations.ContractingDP.T
#print axioms SargentStachurski.ADPTransformations.ContractingDP.β
#print axioms SargentStachurski.ADPTransformations.ContractingDP.β_nonneg
#print axioms SargentStachurski.ADPTransformations.ContractingDP.β_lt_one
#print axioms SargentStachurski.ADPTransformations.ContractingDP.nonempty
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bdd
#print axioms SargentStachurski.ADPTransformations.ContractingDP.closed
#print axioms SargentStachurski.ADPTransformations.ContractingDP.mapsTo
#print axioms SargentStachurski.ADPTransformations.ContractingDP.mono
#print axioms SargentStachurski.ADPTransformations.ContractingDP.contraction
#print axioms SargentStachurski.ADPTransformations.ContractingDP.exists_greedy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.globallyStable
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_mem
#print axioms SargentStachurski.ADPTransformations.ContractingDP.T_vσ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.eq_vσ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.le_vσ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_le
#print axioms SargentStachurski.ADPTransformations.ContractingDP.IsGreedy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.nonempty_policy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.greedy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.ADPTransformations.ContractingDP.T_le_bellman
#print axioms SargentStachurski.ADPTransformations.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_mono
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_contraction
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vstar
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vstar_mem
#print axioms SargentStachurski.ADPTransformations.ContractingDP.bellman_vstar
#print axioms SargentStachurski.ADPTransformations.ContractingDP.eq_vstar
#print axioms SargentStachurski.ADPTransformations.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.ADPTransformations.ContractingDP.IsOptimal
#print axioms SargentStachurski.ADPTransformations.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.ADPTransformations.ContractingDP.optimality
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.ADPTransformations.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.ADPTransformations.ContractingDP.hpiPolicy
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.ADPTransformations.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.ADPTransformations.ContractingDP.hpi_terminates
#print axioms SargentStachurski.ADPTransformations.ContractingDP.opi
#print axioms SargentStachurski.ADPTransformations.ContractingDP.opi_step
#print axioms SargentStachurski.ADPTransformations.ContractingDP.tendsto_opi
#print axioms SargentStachurski.ADPTransformations.markovOp
#print axioms SargentStachurski.ADPTransformations.integrable_of_mem_bX
#print axioms SargentStachurski.ADPTransformations.measurable_markovOp
#print axioms SargentStachurski.ADPTransformations.abs_markovOp_le
#print axioms SargentStachurski.ADPTransformations.markovOp_mem_bX
#print axioms SargentStachurski.ADPTransformations.markovOp_mono
#print axioms SargentStachurski.ADPTransformations.markovOp_const
#print axioms SargentStachurski.ADPTransformations.markovOp_add
#print axioms SargentStachurski.ADPTransformations.markovOp_sub
#print axioms SargentStachurski.ADPTransformations.markovOp_smul
#print axioms SargentStachurski.ADPTransformations.markovOp_sub_const
#print axioms SargentStachurski.ADPTransformations.abs_markovOp_sub_le
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.mk
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.mapsTo
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.add
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.smul
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.mono
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.abs_le
#print axioms SargentStachurski.ADPTransformations.isMarkovLike_markovOp
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.sub
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.abs_sub_le
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.iterate_mem
#print axioms SargentStachurski.ADPTransformations.IsMarkovLike.abs_iterate_le
#print axioms SargentStachurski.ADPTransformations.affineOp
#print axioms SargentStachurski.ADPTransformations.affineOp_mapsTo
#print axioms SargentStachurski.ADPTransformations.affineOp_mono
#print axioms SargentStachurski.ADPTransformations.affineOp_contraction
#print axioms SargentStachurski.ADPTransformations.affineOp_globallyStable
#print axioms SargentStachurski.ADPTransformations.affineOp_iterate_zero
#print axioms SargentStachurski.ADPTransformations.affineOp_hasSum
#print axioms SargentStachurski.ADPTransformations.FiniteMDP
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.mk
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Γ
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Γ_nonempty
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.r
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.β
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.β_nonneg
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.β_lt_one
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.P
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.P_nonneg
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.P_sum
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Policy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Q
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Tσ
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.isBdd_of_finite
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.abs_sum_sub_le
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Q_mono
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.abs_Q_sub_le
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Q_sub_const
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exists_greedy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.toDP
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.IsGreedy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.isGreedy_iff
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.bellman_eq
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.bellman_contraction
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Pσ
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.rσ
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Tσ_eq_mulVec
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.abs_Pσ_mulVec_le
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.vσ_eq_inv
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.vσ_hasSum
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.abs_vσ_le
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.finite_policy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.theorem_1_2_1
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.theorem_1_2_2
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.vstar_le
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.IsLPFeasible
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.lp_solution
#print axioms SargentStachurski.ADPTransformations.OrderStable
#print axioms SargentStachurski.ADPTransformations.IncreasesTo
#print axioms SargentStachurski.ADPTransformations.DecreasesTo
#print axioms SargentStachurski.ADPTransformations.StronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.orderStable_of_up_down
#print axioms SargentStachurski.ADPTransformations.StronglyOrderStable.orderStable
#print axioms SargentStachurski.ADPTransformations.dualMap
#print axioms SargentStachurski.ADPTransformations.orderStable_dual_iff
#print axioms SargentStachurski.ADPTransformations.dualMap_iterate
#print axioms SargentStachurski.ADPTransformations.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.ADPTransformations.ChainComplete
#print axioms SargentStachurski.ADPTransformations.ChainComplete.exists_least
#print axioms SargentStachurski.ADPTransformations.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.ADPTransformations.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.ADPTransformations.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.ADPTransformations.ChainComplete.orderStable
#print axioms SargentStachurski.ADPTransformations.chainComplete_Icc
#print axioms SargentStachurski.ADPTransformations.CountablyDedekindComplete
#print axioms SargentStachurski.ADPTransformations.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.ADPTransformations.CountablyDedekindComplete.dual
#print axioms SargentStachurski.ADPTransformations.OrderContinuous
#print axioms SargentStachurski.ADPTransformations.OrderContinuous.monotone
#print axioms SargentStachurski.ADPTransformations.isLUB_range_succ_iff
#print axioms SargentStachurski.ADPTransformations.tarski_kantorovich
#print axioms SargentStachurski.ADPTransformations.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.ADPTransformations.ADP
#print axioms SargentStachurski.ADPTransformations.ADP.mk
#print axioms SargentStachurski.ADPTransformations.ADP.T
#print axioms SargentStachurski.ADPTransformations.ADP.mono
#print axioms SargentStachurski.ADPTransformations.ADP.nonempty
#print axioms SargentStachurski.ADPTransformations.ADP.IsGreedy
#print axioms SargentStachurski.ADPTransformations.ADP.VG
#print axioms SargentStachurski.ADPTransformations.ADP.WellPosed
#print axioms SargentStachurski.ADPTransformations.ADP.IsFinite
#print axioms SargentStachurski.ADPTransformations.ADP.Regular
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.IsBellmanValue
#print axioms SargentStachurski.ADPTransformations.ADP.SolvesBellman
#print axioms SargentStachurski.ADPTransformations.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.ADPTransformations.ADP.regular_iff
#print axioms SargentStachurski.ADPTransformations.ADP.greedy
#print axioms SargentStachurski.ADPTransformations.ADP.isGreedy_greedy
#print axioms SargentStachurski.ADPTransformations.ADP.bellman
#print axioms SargentStachurski.ADPTransformations.ADP.T_le_bellman
#print axioms SargentStachurski.ADPTransformations.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.ADPTransformations.ADP.isGreedy_iff
#print axioms SargentStachurski.ADPTransformations.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.ADPTransformations.ADP.solvesBellman_iff
#print axioms SargentStachurski.ADPTransformations.ADP.bellman_mono
#print axioms SargentStachurski.ADPTransformations.ADP.VU
#print axioms SargentStachurski.ADPTransformations.ADP.VSig
#print axioms SargentStachurski.ADPTransformations.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.ADPTransformations.ADP.vσ
#print axioms SargentStachurski.ADPTransformations.ADP.T_vσ
#print axioms SargentStachurski.ADPTransformations.ADP.eq_vσ
#print axioms SargentStachurski.ADPTransformations.ADP.VSig_eq_range
#print axioms SargentStachurski.ADPTransformations.ADP.IsOptimal
#print axioms SargentStachurski.ADPTransformations.ADP.IsValueFunction
#print axioms SargentStachurski.ADPTransformations.ADP.BellmanPrinciple
#print axioms SargentStachurski.ADPTransformations.ADP.FundamentalOptimality
#print axioms SargentStachurski.ADPTransformations.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.ADPTransformations.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.ADPTransformations.ADP.isOptimal_iff
#print axioms SargentStachurski.ADPTransformations.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.ADPTransformations.ADP.exists_solves_iff
#print axioms SargentStachurski.ADPTransformations.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.ADPTransformations.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.ADPTransformations.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.ADPTransformations.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.ADPTransformations.ADP.IsSelector
#print axioms SargentStachurski.ADPTransformations.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.ADPTransformations.ADP.howard
#print axioms SargentStachurski.ADPTransformations.ADP.opt
#print axioms SargentStachurski.ADPTransformations.ADP.IsSelector.T_eq
#print axioms SargentStachurski.ADPTransformations.ADP.mem_VU_iff
#print axioms SargentStachurski.ADPTransformations.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.ADPTransformations.ADP.iterate_mono_of_le
#print axioms SargentStachurski.ADPTransformations.ADP.bellman_le_opt
#print axioms SargentStachurski.ADPTransformations.ADP.chain_2_9
#print axioms SargentStachurski.ADPTransformations.ADP.mapsTo_VU
#print axioms SargentStachurski.ADPTransformations.ADP.bellman_le_of_le
#print axioms SargentStachurski.ADPTransformations.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.ADPTransformations.ADP.VFIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.OPIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.HPIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.opt_one
#print axioms SargentStachurski.ADPTransformations.ADP.OPIConverges.vfi
#print axioms SargentStachurski.ADPTransformations.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.ADPTransformations.ADP.iterates_le_vstar
#print axioms SargentStachurski.ADPTransformations.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.ADPTransformations.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.ADPTransformations.ADP.VU_nonempty
#print axioms SargentStachurski.ADPTransformations.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.ADPTransformations.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.ADPTransformations.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.ADPTransformations.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.ADPTransformations.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.ADPTransformations.ADP.OrderBounded
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderContinuous
#print axioms SargentStachurski.ADPTransformations.ADP.le_of_orderBounded
#print axioms SargentStachurski.ADPTransformations.ADP.convergence_of_dedekind
#print axioms SargentStachurski.ADPTransformations.ADP.dual
#print axioms SargentStachurski.ADPTransformations.ADP.dual_dual
#print axioms SargentStachurski.ADPTransformations.ADP.IsMinGreedy
#print axioms SargentStachurski.ADPTransformations.ADP.VGmin
#print axioms SargentStachurski.ADPTransformations.ADP.MinRegular
#print axioms SargentStachurski.ADPTransformations.ADP.MinOrderBounded
#print axioms SargentStachurski.ADPTransformations.ADP.IsMinBellmanValue
#print axioms SargentStachurski.ADPTransformations.ADP.SolvesMinBellman
#print axioms SargentStachurski.ADPTransformations.ADP.IsMinValueFunction
#print axioms SargentStachurski.ADPTransformations.ADP.IsMinOptimal
#print axioms SargentStachurski.ADPTransformations.ADP.MinBellmanPrinciple
#print axioms SargentStachurski.ADPTransformations.ADP.MinFundamentalOptimality
#print axioms SargentStachurski.ADPTransformations.ADP.isMinGreedy_iff
#print axioms SargentStachurski.ADPTransformations.ADP.minRegular_iff
#print axioms SargentStachurski.ADPTransformations.ADP.minOrderBounded_iff
#print axioms SargentStachurski.ADPTransformations.ADP.isMinBellmanValue_iff
#print axioms SargentStachurski.ADPTransformations.ADP.VGmin_eq
#print axioms SargentStachurski.ADPTransformations.ADP.dual_VSig
#print axioms SargentStachurski.ADPTransformations.ADP.WellPosed.dual
#print axioms SargentStachurski.ADPTransformations.ADP.dual_vσ
#print axioms SargentStachurski.ADPTransformations.ADP.isMinValueFunction_iff
#print axioms SargentStachurski.ADPTransformations.ADP.isMinOptimal_iff
#print axioms SargentStachurski.ADPTransformations.ADP.dual_opt_howard
#print axioms SargentStachurski.ADPTransformations.ADP.minBellmanPrinciple_iff
#print axioms SargentStachurski.ADPTransformations.ADP.minFundamentalOptimality_iff
#print axioms SargentStachurski.ADPTransformations.ADP.VD
#print axioms SargentStachurski.ADPTransformations.ADP.MinVFIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.minVFIConverges_iff
#print axioms SargentStachurski.ADPTransformations.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ADPTransformations.ADP.IsOrderStable.minFundamentalOptimality
#print axioms SargentStachurski.ADPTransformations.isLUB_of_tendsto_subtype
#print axioms SargentStachurski.ADPTransformations.isGLB_of_tendsto_subtype
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.nonempty_policy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_wellPosed
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_isOrderStable
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_isOrderContinuous
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.rbar
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.abs_r_le_rbar
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_orderBounded
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_2_3_7
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_regular
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_bellman_apply
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.proposition_2_3_1
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Vhat
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.mem_Vhat_iff
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Tσ_mapsTo_Vhat
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adpHat
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.vσ_mem_Vhat
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adpHat_isStronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adpHat_regular
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_2_3_10
#print axioms SargentStachurski.ADPTransformations.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.ADPTransformations.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.ADPTransformations.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.ADPTransformations.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.ADPTransformations.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.ADPTransformations.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_2
#print axioms SargentStachurski.ADPTransformations.ADP.corollary_3_1_3
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_4
#print axioms SargentStachurski.ADPTransformations.IsSupNonexpansive
#print axioms SargentStachurski.ADPTransformations.IsInfNonexpansive
#print axioms SargentStachurski.ADPTransformations.isInfNonexpansive_iff
#print axioms SargentStachurski.ADPTransformations.isSupNonexpansive_real
#print axioms SargentStachurski.ADPTransformations.isSupNonexpansive_pi
#print axioms SargentStachurski.ADPTransformations.ADP.lemma_A_5_21
#print axioms SargentStachurski.ADPTransformations.ADP.IsSemiRegular
#print axioms SargentStachurski.ADPTransformations.ADP.VFIGeometric
#print axioms SargentStachurski.ADPTransformations.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_5
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.ADPTransformations.ADP.IsMinSelector
#print axioms SargentStachurski.ADPTransformations.ADP.MinOPIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.MinHPIConverges
#print axioms SargentStachurski.ADPTransformations.ADP.isMinSelector_iff
#print axioms SargentStachurski.ADPTransformations.ADP.dual_opt_iterate
#print axioms SargentStachurski.ADPTransformations.ADP.dual_howard_iterate
#print axioms SargentStachurski.ADPTransformations.ADP.minOPIConverges_iff
#print axioms SargentStachurski.ADPTransformations.ADP.minHPIConverges_iff
#print axioms SargentStachurski.ADPTransformations.ADP.min_of_dual
#print axioms SargentStachurski.ADPTransformations.ADP.IsGloballyStable.dual
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_6
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_8
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_3_1_7
#print axioms SargentStachurski.ADPTransformations.vShapeOrder
#print axioms SargentStachurski.ADPTransformations.vShapeDist
#print axioms SargentStachurski.ADPTransformations.vShapeDist_metric
#print axioms SargentStachurski.ADPTransformations.vShape_isLUB
#print axioms SargentStachurski.ADPTransformations.vShape_sup_not_inf
#print axioms SargentStachurski.ADPTransformations.BM
#print axioms SargentStachurski.ADPTransformations.BM.mk
#print axioms SargentStachurski.ADPTransformations.BM.toFun
#print axioms SargentStachurski.ADPTransformations.BM.measurable'
#print axioms SargentStachurski.ADPTransformations.BM.bdd'
#print axioms SargentStachurski.ADPTransformations.BM.ext
#print axioms SargentStachurski.ADPTransformations.BM.bddAbove
#print axioms SargentStachurski.ADPTransformations.BM.const
#print axioms SargentStachurski.ADPTransformations.BM.toFun_injective
#print axioms SargentStachurski.ADPTransformations.BM.zero
#print axioms SargentStachurski.ADPTransformations.BM.add
#print axioms SargentStachurski.ADPTransformations.BM.neg
#print axioms SargentStachurski.ADPTransformations.BM.sub
#print axioms SargentStachurski.ADPTransformations.BM.smulReal
#print axioms SargentStachurski.ADPTransformations.BM.nsmul
#print axioms SargentStachurski.ADPTransformations.BM.zsmul
#print axioms SargentStachurski.ADPTransformations.BM.addCommGroup
#print axioms SargentStachurski.ADPTransformations.BM.supNorm
#print axioms SargentStachurski.ADPTransformations.BM.abs_le_supNorm
#print axioms SargentStachurski.ADPTransformations.BM.supNorm_le
#print axioms SargentStachurski.ADPTransformations.BM.supNorm_nonneg
#print axioms SargentStachurski.ADPTransformations.BM.normedAddCommGroup
#print axioms SargentStachurski.ADPTransformations.BM.add_apply
#print axioms SargentStachurski.ADPTransformations.BM.sub_apply
#print axioms SargentStachurski.ADPTransformations.BM.neg_apply
#print axioms SargentStachurski.ADPTransformations.BM.zero_apply
#print axioms SargentStachurski.ADPTransformations.BM.const_apply
#print axioms SargentStachurski.ADPTransformations.BM.norm_def
#print axioms SargentStachurski.ADPTransformations.BM.abs_le_norm
#print axioms SargentStachurski.ADPTransformations.BM.norm_le
#print axioms SargentStachurski.ADPTransformations.BM.abs_sub_le_dist
#print axioms SargentStachurski.ADPTransformations.BM.dist_le
#print axioms SargentStachurski.ADPTransformations.BM.module
#print axioms SargentStachurski.ADPTransformations.BM.smul_apply
#print axioms SargentStachurski.ADPTransformations.BM.normedSpace
#print axioms SargentStachurski.ADPTransformations.BM.lattice
#print axioms SargentStachurski.ADPTransformations.BM.le_def
#print axioms SargentStachurski.ADPTransformations.BM.sup_apply
#print axioms SargentStachurski.ADPTransformations.BM.inf_apply
#print axioms SargentStachurski.ADPTransformations.BM.abs_apply
#print axioms SargentStachurski.ADPTransformations.BM.isOrderedAddMonoid
#print axioms SargentStachurski.ADPTransformations.BM.hasSolidNorm
#print axioms SargentStachurski.ADPTransformations.BM.completeSpace
#print axioms SargentStachurski.ADPTransformations.BM.countablyDedekindComplete
#print axioms SargentStachurski.ADPTransformations.BM.isSupNonexpansive
#print axioms SargentStachurski.ADPTransformations.BM.isInfNonexpansive
#print axioms SargentStachurski.ADPTransformations.BM.mem_bX
#print axioms SargentStachurski.ADPTransformations.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.ADPTransformations.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.ADPTransformations.BM.globallyStable_of_bX
#print axioms SargentStachurski.ADPTransformations.globallyStable_of_supContraction
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.adp_isGloballyStable
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.section_3_2_1_1
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.G
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.finite_G
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.pairOf
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Sσ
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Sσ_mono
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qadp
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_3_2_3
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_3_2_3_converse
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exists_qgreedy
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qadp_regular
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_3_2_4
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_3_2_5
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qadp_isGloballyStable
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.exercise_3_2_6
#print axioms SargentStachurski.ADPTransformations.exercise_3_2_3_converse_fails
#print axioms SargentStachurski.ADPTransformations.pow_div_le_geometric
#print axioms SargentStachurski.ADPTransformations.theorem_4_1_1
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsNormalizedOrderUnit
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsNormalizedOrderUnit.smul_mono
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsNormalizedOrderUnit.le_add
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsNormalizedOrderUnit.norm_sub_le
#print axioms SargentStachurski.ADPTransformations.BanachLattice.isSupNonexpansive
#print axioms SargentStachurski.ADPTransformations.BanachLattice.isInfNonexpansive
#print axioms SargentStachurski.ADPTransformations.BanachLattice.isSupNonexpansive_subtype
#print axioms SargentStachurski.ADPTransformations.BanachLattice.lemma_4_1_2
#print axioms SargentStachurski.ADPTransformations.BanachLattice.lemma_4_1_2_subtype
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_3
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_3_univ
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsCertaintyEquivalent
#print axioms SargentStachurski.ADPTransformations.BanachLattice.exercise_4_1_2
#print axioms SargentStachurski.ADPTransformations.BanachLattice.exercise_4_1_2_subtype
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsDiscountOperator
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsDiscountOperator.exercise_4_1_3
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsDiscountOperator.iterate_nonneg
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsDiscountOperator.iterate_mono
#print axioms SargentStachurski.ADPTransformations.BanachLattice.specRad
#print axioms SargentStachurski.ADPTransformations.BanachLattice.exercise_A_4_2
#print axioms SargentStachurski.ADPTransformations.BanachLattice.specRad_le_norm
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsPositiveOp
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsPositiveOp.mono
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsPositiveOp.abs_le
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsPositiveOp.iterate
#print axioms SargentStachurski.ADPTransformations.BanachLattice.example_4_1_1
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsIsoOrderEmbedding
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsOrderContraction
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsOrderContraction.iterate
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_4
#print axioms SargentStachurski.ADPTransformations.BanachLattice.example_4_1_2
#print axioms SargentStachurski.ADPTransformations.BanachLattice.exercise_4_1_4
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_5
#print axioms SargentStachurski.ADPTransformations.BanachLattice.bellman_orderContraction
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_6
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsAdditive
#print axioms SargentStachurski.ADPTransformations.BanachLattice.IsAdditive.abs_sub
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_7
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_8
#print axioms SargentStachurski.ADPTransformations.BanachLattice.GloballyStableOn
#print axioms SargentStachurski.ADPTransformations.BanachLattice.DuConditions
#print axioms SargentStachurski.ADPTransformations.BanachLattice.abs_sub_le_of_mem_Icc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.norm_sub_le_of_mem_Icc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.iterate_mem_Icc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.du_concave
#print axioms SargentStachurski.ADPTransformations.BanachLattice.neg_mem_Icc_iff'
#print axioms SargentStachurski.ADPTransformations.BanachLattice.iterate_reflect
#print axioms SargentStachurski.ADPTransformations.BanachLattice.globallyStableOn_of_reflect
#print axioms SargentStachurski.ADPTransformations.BanachLattice.du_convex
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_10
#print axioms SargentStachurski.ADPTransformations.BanachLattice.lemma_4_1_9_concave
#print axioms SargentStachurski.ADPTransformations.BanachLattice.lemma_4_1_9_convex
#print axioms SargentStachurski.ADPTransformations.BanachLattice.lemma_4_1_9
#print axioms SargentStachurski.ADPTransformations.BanachLattice.extendIcc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.extendIcc_apply
#print axioms SargentStachurski.ADPTransformations.BanachLattice.extendIcc_iterate
#print axioms SargentStachurski.ADPTransformations.BanachLattice.globallyStable_of_extendIcc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_10_subtype
#print axioms SargentStachurski.ADPTransformations.BanachLattice.countablyDedekindComplete_Icc
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_11
#print axioms SargentStachurski.ADPTransformations.BM.posSMulMono
#print axioms SargentStachurski.ADPTransformations.BM.one_apply
#print axioms SargentStachurski.ADPTransformations.BM.isNormalizedOrderUnit_one
#print axioms SargentStachurski.ADPTransformations.BM.markovLin
#print axioms SargentStachurski.ADPTransformations.BM.markovCLM
#print axioms SargentStachurski.ADPTransformations.BM.markovCLM_apply
#print axioms SargentStachurski.ADPTransformations.BM.markovCLM_isPositive
#print axioms SargentStachurski.ADPTransformations.BM.markovCLM_const
#print axioms SargentStachurski.ADPTransformations.BM.mulLin
#print axioms SargentStachurski.ADPTransformations.BM.mulCLM
#print axioms SargentStachurski.ADPTransformations.BM.mulCLM_apply
#print axioms SargentStachurski.ADPTransformations.BM.mulCLM_isPositive
#print axioms SargentStachurski.ADPTransformations.sup'_add_const
#print axioms SargentStachurski.ADPTransformations.harrisonKreps
#print axioms SargentStachurski.ADPTransformations.exercise_4_1_1
#print axioms SargentStachurski.ADPTransformations.argmaxSet
#print axioms SargentStachurski.ADPTransformations.argmaxSet_nonempty
#print axioms SargentStachurski.ADPTransformations.argmaxSel
#print axioms SargentStachurski.ADPTransformations.argmaxSel_max
#print axioms SargentStachurski.ADPTransformations.measurable_argmaxSel
#print axioms SargentStachurski.ADPTransformations.SEPolicy
#print axioms SargentStachurski.ADPTransformations.IsCEOperator
#print axioms SargentStachurski.ADPTransformations.PostAction
#print axioms SargentStachurski.ADPTransformations.PostAction.mk
#print axioms SargentStachurski.ADPTransformations.PostAction.r
#print axioms SargentStachurski.ADPTransformations.PostAction.β
#print axioms SargentStachurski.ADPTransformations.PostAction.β_nonneg
#print axioms SargentStachurski.ADPTransformations.PostAction.β_lt_one
#print axioms SargentStachurski.ADPTransformations.PostAction.M
#print axioms SargentStachurski.ADPTransformations.PostAction.H
#print axioms SargentStachurski.ADPTransformations.PostAction.H_mono
#print axioms SargentStachurski.ADPTransformations.PostAction.H_shift
#print axioms SargentStachurski.ADPTransformations.PostAction.adp
#print axioms SargentStachurski.ADPTransformations.PostAction.blackwell
#print axioms SargentStachurski.ADPTransformations.PostAction.greedySE
#print axioms SargentStachurski.ADPTransformations.PostAction.H_le_greedy
#print axioms SargentStachurski.ADPTransformations.PostAction.greedySE_isGreedy
#print axioms SargentStachurski.ADPTransformations.PostAction.adp_regular
#print axioms SargentStachurski.ADPTransformations.PostAction.adp_bellman
#print axioms SargentStachurski.ADPTransformations.PostAction.proposition_4_2_6
#print axioms SargentStachurski.ADPTransformations.expectOp
#print axioms SargentStachurski.ADPTransformations.integrable_BM
#print axioms SargentStachurski.ADPTransformations.isCEOperator_expectOp
#print axioms SargentStachurski.ADPTransformations.postActionEU
#print axioms SargentStachurski.ADPTransformations.exercise_4_2_5
#print axioms SargentStachurski.ADPTransformations.bellman_EU
#print axioms SargentStachurski.ADPTransformations.proposition_4_2_4
#print axioms SargentStachurski.ADPTransformations.riskSensitive
#print axioms SargentStachurski.ADPTransformations.isCEOperator_riskSensitive
#print axioms SargentStachurski.ADPTransformations.riskSensitive_optimality
#print axioms SargentStachurski.ADPTransformations.IsUniqueFixed
#print axioms SargentStachurski.ADPTransformations.IsConjugate
#print axioms SargentStachurski.ADPTransformations.IsConjugate.symm
#print axioms SargentStachurski.ADPTransformations.IsConjugate.iterate
#print axioms SargentStachurski.ADPTransformations.IsConjugate.fixed_iff
#print axioms SargentStachurski.ADPTransformations.IsConjugate.fixed_iff_symm
#print axioms SargentStachurski.ADPTransformations.IsConjugate.isUniqueFixed_iff
#print axioms SargentStachurski.ADPTransformations.example_5_1_1
#print axioms SargentStachurski.ADPTransformations.coordChange
#print axioms SargentStachurski.ADPTransformations.example_5_1_2
#print axioms SargentStachurski.ADPTransformations.IsTopConjugate
#print axioms SargentStachurski.ADPTransformations.IsTopConjugate.symm
#print axioms SargentStachurski.ADPTransformations.IsTopConjugate.globallyStable
#print axioms SargentStachurski.ADPTransformations.proposition_5_1_2
#print axioms SargentStachurski.ADPTransformations.coordHomeo
#print axioms SargentStachurski.ADPTransformations.iterate_diagonal_mulVec
#print axioms SargentStachurski.ADPTransformations.globallyStable_diagonal_iff
#print axioms SargentStachurski.ADPTransformations.example_5_1_3
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate
#print axioms SargentStachurski.ADPTransformations.orderIso_increasesTo
#print axioms SargentStachurski.ADPTransformations.orderIso_decreasesTo
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.refl
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.symm
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.trans
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.orderStable
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.stronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.IsOrderConjugate.lemma_5_1_3
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.refl
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.symm
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.trans
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.T_apply
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.range_T
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.isBellmanValue_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.solvesBellman_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.isGreedy_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.mem_VG_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.regular_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.wellPosed_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.vσ_eq
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.VSig_eq
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.isValueFunction_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.isOptimal_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.orderStable_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.stronglyOrderStable_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.bellman_eq
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.bellmanPrinciple
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.fundamentalOptimality
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.fundamentalOptimality_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.mem_VU_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.isSelector_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.opt_eq
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.howard_eq
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.bellman_semiconj
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.vfiConverges
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.opiConverges
#print axioms SargentStachurski.ADPTransformations.ADP.IsIsomorphic.hpiConverges
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_5
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_6
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_7
#print axioms SargentStachurski.ADPTransformations.ADP.savingsAdd
#print axioms SargentStachurski.ADPTransformations.ADP.savingsMul
#print axioms SargentStachurski.ADPTransformations.ADP.expPi
#print axioms SargentStachurski.ADPTransformations.ADP.example_5_1_4
#print axioms SargentStachurski.ADPTransformations.ADP.IsAntiIsomorphic
#print axioms SargentStachurski.ADPTransformations.ADP.exercise_5_1_6
#print axioms SargentStachurski.ADPTransformations.ADP.IsAntiIsomorphic.iso
#print axioms SargentStachurski.ADPTransformations.ADP.IsAntiIsomorphic.orderStable_iff
#print axioms SargentStachurski.ADPTransformations.ADP.IsAntiIsomorphic.minSelector_iff
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_8
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_9
#print axioms SargentStachurski.ADPTransformations.ADP.theorem_5_1_10
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj
#print axioms SargentStachurski.ADPTransformations.OrderContinuousDown
#print axioms SargentStachurski.ADPTransformations.AntiContinuousUp
#print axioms SargentStachurski.ADPTransformations.AntiContinuousDown
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.swap
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.exercise_5_2_1
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.iterate_succ
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.fixed_F
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.fixed_G
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.isUniqueFixed
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.existsUnique_iff
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.orderStable_mono
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.orderStable_anti
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.lemma_5_2_2_i
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.increasesTo_of_succ
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.decreasesTo_of_succ
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.stronglyOrderStable_mono
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.stronglyOrderStable_anti
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.lemma_5_2_2_ii
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.theorem_5_2_3
#print axioms SargentStachurski.ADPTransformations.IsStronglySemiconj.theorem_5_2_4
#print axioms SargentStachurski.ADPTransformations.FDP
#print axioms SargentStachurski.ADPTransformations.FDP.mk
#print axioms SargentStachurski.ADPTransformations.FDP.F
#print axioms SargentStachurski.ADPTransformations.FDP.G
#print axioms SargentStachurski.ADPTransformations.FDP.greatest
#print axioms SargentStachurski.ADPTransformations.FDP.nonempty
#print axioms SargentStachurski.ADPTransformations.FDP.IsOrderPreserving
#print axioms SargentStachurski.ADPTransformations.FDP.IsOrderReversing
#print axioms SargentStachurski.ADPTransformations.FDP.Monotonic
#print axioms SargentStachurski.ADPTransformations.FDP.gsel
#print axioms SargentStachurski.ADPTransformations.FDP.Gsup
#print axioms SargentStachurski.ADPTransformations.FDP.G_le_Gsup
#print axioms SargentStachurski.ADPTransformations.FDP.isGreatest_Gsup
#print axioms SargentStachurski.ADPTransformations.FDP.primary
#print axioms SargentStachurski.ADPTransformations.FDP.sub
#print axioms SargentStachurski.ADPTransformations.FDP.primary_regular
#print axioms SargentStachurski.ADPTransformations.FDP.primary_bellman
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_9
#print axioms SargentStachurski.ADPTransformations.FDP.sub_isGreedy_of_eq
#print axioms SargentStachurski.ADPTransformations.FDP.sub_regular
#print axioms SargentStachurski.ADPTransformations.FDP.sub_bellman
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_10
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_11
#print axioms SargentStachurski.ADPTransformations.FDP.policy_semiconj
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_12
#print axioms SargentStachurski.ADPTransformations.FDP.sub_isValueFunction
#print axioms SargentStachurski.ADPTransformations.FDP.primary_isValueFunction
#print axioms SargentStachurski.ADPTransformations.FDP.fo_sub_of_primary
#print axioms SargentStachurski.ADPTransformations.FDP.fo_primary_of_sub
#print axioms SargentStachurski.ADPTransformations.FDP.theorem_5_2_13
#print axioms SargentStachurski.ADPTransformations.FDP.proposition_5_2_14
#print axioms SargentStachurski.ADPTransformations.FDP.dualize
#print axioms SargentStachurski.ADPTransformations.FDP.dualize_isOrderPreserving
#print axioms SargentStachurski.ADPTransformations.FDP.dualize_monotonic
#print axioms SargentStachurski.ADPTransformations.FDP.dualize_primary
#print axioms SargentStachurski.ADPTransformations.FDP.dualize_sub
#print axioms SargentStachurski.ADPTransformations.FDP.dualize_Gsup
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_16
#print axioms SargentStachurski.ADPTransformations.FDP.lemma_5_2_17
#print axioms SargentStachurski.ADPTransformations.FDP.theorem_5_2_18
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp_isOrderPreserving
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp_monotonic
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp_primary
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp_sub
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.le_Gsup
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.Gsup_eq_sup
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.proposition_5_3_1
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.qfdp_F_strictMono
#print axioms SargentStachurski.ADPTransformations.FiniteMDP.proposition_5_3_2
#print axioms SargentStachurski.ADPTransformations.zeroDiscountMDP
#print axioms SargentStachurski.ADPTransformations.proposition_5_3_2_needs_beta_pos
#print axioms SargentStachurski.ADPTransformations.seFDP
#print axioms SargentStachurski.ADPTransformations.seFDP_isOrderPreserving
#print axioms SargentStachurski.ADPTransformations.seFDP_monotonic
#print axioms SargentStachurski.ADPTransformations.seFDP_sub
#print axioms SargentStachurski.ADPTransformations.seFDP_primary_T
#print axioms SargentStachurski.ADPTransformations.seFDP_primary_bellman
#print axioms SargentStachurski.ADPTransformations.section_5_3_2
#print axioms SargentStachurski.ADPTransformations.EZ.f
#print axioms SargentStachurski.ADPTransformations.EZ.g
#print axioms SargentStachurski.ADPTransformations.EZ.f'
#print axioms SargentStachurski.ADPTransformations.EZ.g_pos
#print axioms SargentStachurski.ADPTransformations.EZ.f_monotoneOn
#print axioms SargentStachurski.ADPTransformations.EZ.f_rpow
#print axioms SargentStachurski.ADPTransformations.EZ.hasDerivAt_f
#print axioms SargentStachurski.ADPTransformations.EZ.deriv_f
#print axioms SargentStachurski.ADPTransformations.EZ.f'_inner_pos
#print axioms SargentStachurski.ADPTransformations.EZ.continuousOn_f
#print axioms SargentStachurski.ADPTransformations.EZ.differentiableOn_f
#print axioms SargentStachurski.ADPTransformations.EZ.convexOn_f
#print axioms SargentStachurski.ADPTransformations.EZ.concaveOn_f
#print axioms SargentStachurski.ADPTransformations.BanachLattice.neg_mem_Icc_neg
#print axioms SargentStachurski.ADPTransformations.BanachLattice.neg_mem_Icc_of_neg
#print axioms SargentStachurski.ADPTransformations.BanachLattice.negIcc
#print axioms SargentStachurski.ADPTransformations.ADP.reflect
#print axioms SargentStachurski.ADPTransformations.BanachLattice.reflect_isAntiIsomorphic
#print axioms SargentStachurski.ADPTransformations.BanachLattice.reflect_isFinite
#print axioms SargentStachurski.ADPTransformations.BanachLattice.extendIcc_reflect
#print axioms SargentStachurski.ADPTransformations.BanachLattice.duConditions_reflect
#print axioms SargentStachurski.ADPTransformations.BanachLattice.theorem_4_1_11_min
#print axioms SargentStachurski.ADPTransformations.hasSolidNorm_pi
#print axioms SargentStachurski.ADPTransformations.exists_eps_mul_le
#print axioms SargentStachurski.ADPTransformations.EZModel
#print axioms SargentStachurski.ADPTransformations.EZModel.mk
#print axioms SargentStachurski.ADPTransformations.EZModel.Γ
#print axioms SargentStachurski.ADPTransformations.EZModel.Γ_nonempty
#print axioms SargentStachurski.ADPTransformations.EZModel.r
#print axioms SargentStachurski.ADPTransformations.EZModel.r_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.β
#print axioms SargentStachurski.ADPTransformations.EZModel.β_nonneg
#print axioms SargentStachurski.ADPTransformations.EZModel.β_lt_one
#print axioms SargentStachurski.ADPTransformations.EZModel.P
#print axioms SargentStachurski.ADPTransformations.EZModel.P_nonneg
#print axioms SargentStachurski.ADPTransformations.EZModel.P_sum
#print axioms SargentStachurski.ADPTransformations.EZModel.α
#print axioms SargentStachurski.ADPTransformations.EZModel.ν
#print axioms SargentStachurski.ADPTransformations.EZModel.α_ne
#print axioms SargentStachurski.ADPTransformations.EZModel.ν_ne
#print axioms SargentStachurski.ADPTransformations.EZModel.c₁
#print axioms SargentStachurski.ADPTransformations.EZModel.c₂
#print axioms SargentStachurski.ADPTransformations.EZModel.c₁_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.c₁_lt_c₂
#print axioms SargentStachurski.ADPTransformations.EZModel.c₁_lt
#print axioms SargentStachurski.ADPTransformations.EZModel.lt_c₂
#print axioms SargentStachurski.ADPTransformations.EZModel.θ
#print axioms SargentStachurski.ADPTransformations.EZModel.θ_ne
#print axioms SargentStachurski.ADPTransformations.EZModel.Policy
#print axioms SargentStachurski.ADPTransformations.EZModel.nonempty_policy
#print axioms SargentStachurski.ADPTransformations.EZModel.finite_policy
#print axioms SargentStachurski.ADPTransformations.EZModel.c₂_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.lo
#print axioms SargentStachurski.ADPTransformations.EZModel.hi
#print axioms SargentStachurski.ADPTransformations.EZModel.lo_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.hi_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.lo_lt_hi
#print axioms SargentStachurski.ADPTransformations.EZModel.a
#print axioms SargentStachurski.ADPTransformations.EZModel.b
#print axioms SargentStachurski.ADPTransformations.EZModel.a_le_b
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ_const
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ_mono
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ_combo
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ_mem
#print axioms SargentStachurski.ADPTransformations.EZModel.Pσ_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.That
#print axioms SargentStachurski.ADPTransformations.EZModel.rα_pos
#print axioms SargentStachurski.ADPTransformations.EZModel.That_le
#print axioms SargentStachurski.ADPTransformations.EZModel.lo_lt_f_hi
#print axioms SargentStachurski.ADPTransformations.EZModel.exercise_5_1_9
#print axioms SargentStachurski.ADPTransformations.EZModel.That_mem
#print axioms SargentStachurski.ADPTransformations.EZModel.adpHat
#print axioms SargentStachurski.ADPTransformations.EZModel.exercise_5_1_10
#print axioms SargentStachurski.ADPTransformations.EZModel.adpHat_isFinite
#print axioms SargentStachurski.ADPTransformations.EZModel.exists_extremal
#print axioms SargentStachurski.ADPTransformations.EZModel.adpHat_regular
#print axioms SargentStachurski.ADPTransformations.EZModel.adpHat_minRegular
#print axioms SargentStachurski.ADPTransformations.EZModel.duConditions
#print axioms SargentStachurski.ADPTransformations.EZModel.adpHat_isOrderStable
#print axioms SargentStachurski.ADPTransformations.EZModel.lemma_5_1_11
#print axioms SargentStachurski.ADPTransformations.EZModel.V
#print axioms SargentStachurski.ADPTransformations.EZModel.Lσ
#print axioms SargentStachurski.ADPTransformations.EZModel.Tσ
#print axioms SargentStachurski.ADPTransformations.EZModel.exercise_5_1_11
#print axioms SargentStachurski.ADPTransformations.EZModel.Tσ_mem
#print axioms SargentStachurski.ADPTransformations.EZModel.Φ
#print axioms SargentStachurski.ADPTransformations.EZModel.Ψ
#print axioms SargentStachurski.ADPTransformations.EZModel.Φ_Ψ
#print axioms SargentStachurski.ADPTransformations.EZModel.Ψ_Φ
#print axioms SargentStachurski.ADPTransformations.EZModel.isoPos
#print axioms SargentStachurski.ADPTransformations.EZModel.isoNeg
#print axioms SargentStachurski.ADPTransformations.EZModel.Φ_T
#print axioms SargentStachurski.ADPTransformations.EZModel.adp
#print axioms SargentStachurski.ADPTransformations.EZModel.lemma_5_1_12_i
#print axioms SargentStachurski.ADPTransformations.EZModel.lemma_5_1_12_ii
#print axioms SargentStachurski.ADPTransformations.EZModel.adp_isOrderStable
#print axioms SargentStachurski.ADPTransformations.EZModel.proposition_5_1_13
#print axioms SargentStachurski.ADPTransformations.powerSum_pos
#print axioms SargentStachurski.ADPTransformations.powerMean_mono
#print axioms SargentStachurski.ADPTransformations.aggr_mono
#print axioms SargentStachurski.ADPTransformations.EZSavings
#print axioms SargentStachurski.ADPTransformations.EZSavings.mk
#print axioms SargentStachurski.ADPTransformations.EZSavings.Γ
#print axioms SargentStachurski.ADPTransformations.EZSavings.Γ_nonempty
#print axioms SargentStachurski.ADPTransformations.EZSavings.r
#print axioms SargentStachurski.ADPTransformations.EZSavings.r_pos
#print axioms SargentStachurski.ADPTransformations.EZSavings.β
#print axioms SargentStachurski.ADPTransformations.EZSavings.β_nonneg
#print axioms SargentStachurski.ADPTransformations.EZSavings.β_lt_one
#print axioms SargentStachurski.ADPTransformations.EZSavings.φ
#print axioms SargentStachurski.ADPTransformations.EZSavings.φ_nonneg
#print axioms SargentStachurski.ADPTransformations.EZSavings.φ_sum
#print axioms SargentStachurski.ADPTransformations.EZSavings.α
#print axioms SargentStachurski.ADPTransformations.EZSavings.ν
#print axioms SargentStachurski.ADPTransformations.EZSavings.α_ne
#print axioms SargentStachurski.ADPTransformations.EZSavings.ν_ne
#print axioms SargentStachurski.ADPTransformations.EZSavings.c₁
#print axioms SargentStachurski.ADPTransformations.EZSavings.c₂
#print axioms SargentStachurski.ADPTransformations.EZSavings.c₁_pos
#print axioms SargentStachurski.ADPTransformations.EZSavings.c₁_lt_c₂
#print axioms SargentStachurski.ADPTransformations.EZSavings.c₁_lt
#print axioms SargentStachurski.ADPTransformations.EZSavings.lt_c₂
#print axioms SargentStachurski.ADPTransformations.EZSavings.toEZ
#print axioms SargentStachurski.ADPTransformations.EZSavings.Fraw
#print axioms SargentStachurski.ADPTransformations.EZSavings.Graw
#print axioms SargentStachurski.ADPTransformations.EZSavings.Pσ_eq
#print axioms SargentStachurski.ADPTransformations.EZSavings.exercise_5_3_1
#print axioms SargentStachurski.ADPTransformations.EZSavings.Vhat
#print axioms SargentStachurski.ADPTransformations.EZSavings.Fraw_pos
#print axioms SargentStachurski.ADPTransformations.EZSavings.Graw_mem
#print axioms SargentStachurski.ADPTransformations.EZSavings.fdp
#print axioms SargentStachurski.ADPTransformations.EZSavings.Vhat_pos
#print axioms SargentStachurski.ADPTransformations.EZSavings.fdp_isOrderPreserving
#print axioms SargentStachurski.ADPTransformations.EZSavings.fdp_monotonic
#print axioms SargentStachurski.ADPTransformations.EZSavings.primary_isIsomorphic
#print axioms SargentStachurski.ADPTransformations.EZSavings.exercise_5_3_2
#print axioms SargentStachurski.ADPTransformations.EZSavings.section_5_3_3
#print axioms SargentStachurski.ADPTransformations.BM.tendsto_of_isLUB
#print axioms SargentStachurski.ADPTransformations.BM.tendsto_of_isGLB
#print axioms SargentStachurski.ADPTransformations.BM.isLUB_of_tendsto
#print axioms SargentStachurski.ADPTransformations.BM.isGLB_of_tendsto
#print axioms SargentStachurski.ADPTransformations.BM.tendsto_markov
#print axioms SargentStachurski.ADPTransformations.FirmEntry
#print axioms SargentStachurski.ADPTransformations.FirmEntry.mk
#print axioms SargentStachurski.ADPTransformations.FirmEntry.Q
#print axioms SargentStachurski.ADPTransformations.FirmEntry.φ
#print axioms SargentStachurski.ADPTransformations.FirmEntry.c
#print axioms SargentStachurski.ADPTransformations.FirmEntry.c_meas
#print axioms SargentStachurski.ADPTransformations.FirmEntry.c_nonneg
#print axioms SargentStachurski.ADPTransformations.FirmEntry.s
#print axioms SargentStachurski.ADPTransformations.FirmEntry.β
#print axioms SargentStachurski.ADPTransformations.FirmEntry.β_nonneg
#print axioms SargentStachurski.ADPTransformations.FirmEntry.integrable_section
#print axioms SargentStachurski.ADPTransformations.FirmEntry.F
#print axioms SargentStachurski.ADPTransformations.FirmEntry.G
#print axioms SargentStachurski.ADPTransformations.FirmEntry.S
#print axioms SargentStachurski.ADPTransformations.FirmEntry.T
#print axioms SargentStachurski.ADPTransformations.FirmEntry.S_apply
#print axioms SargentStachurski.ADPTransformations.FirmEntry.T_apply
#print axioms SargentStachurski.ADPTransformations.FirmEntry.F_mono
#print axioms SargentStachurski.ADPTransformations.FirmEntry.G_mono
#print axioms SargentStachurski.ADPTransformations.FirmEntry.lemma_5_2_6
#print axioms SargentStachurski.ADPTransformations.FirmEntry.K
#print axioms SargentStachurski.ADPTransformations.FirmEntry.K_isPositive
#print axioms SargentStachurski.ADPTransformations.FirmEntry.abs_T_sub_le
#print axioms SargentStachurski.ADPTransformations.FirmEntry.DiscountCondition
#print axioms SargentStachurski.ADPTransformations.FirmEntry.K_isDiscountOperator
#print axioms SargentStachurski.ADPTransformations.FirmEntry.lemma_5_2_5
#print axioms SargentStachurski.ADPTransformations.FirmEntry.tendsto_G
#print axioms SargentStachurski.ADPTransformations.FirmEntry.lemma_5_2_8
#print axioms SargentStachurski.ADPTransformations.FirmEntry.proposition_5_2_7
#print axioms SargentStachurski.ADPTransformations.orderContinuous_of_stabilizes
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.a
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.bot₁
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.bot₂
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.le
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.le_refl'
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.le_trans'
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fork.le_antisymm'
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.forkOrder
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Chain
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.shift
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fmap
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Gmap
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Smap
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.le_a_iff
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.isStronglySemiconj
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Fmap_mono
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Gmap_mono
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.chain_stabilizes
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.rank
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.rank_strictMono
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.fork_stabilizes
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.iterate_shift
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.shift_stronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.iterate_Smap
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.Smap_not_stronglyOrderStable
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.theorem_5_2_3_fails
#print axioms SargentStachurski.ADPTransformations.SemiconjCounterexample.theorem_5_2_4_fails
