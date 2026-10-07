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
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

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

namespace SargentStachurski.ApproximationAndLearning

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

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fitted value iteration and error bounds

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.2 (pp. 299–303).

`(V, 𝕋)` is an ADP on a partially ordered metric space. Under Assumption 9.1.1 (regular, each
`T_σ` a contraction of modulus `β`, the metric complete and sup-nonexpansive), the Bellman
operator is a contraction of modulus `β` (Lemma A.5.21) and Theorem 3.1.5 applies with
`V₀ = V`. An approximation operator `L : V → V` gives the approximate Bellman operator
`T̂ = L ∘ T`, and fitted value iteration (Algorithm 9.1) iterates `T̂`.

* `assumption_9_1_1`: the consequences of Assumption 9.1.1 listed on p. 299.
* **Lemma 9.1.2**: `T̂` is a contraction of modulus `β` when `L` is nonexpansive; FVI then
  converges to the fixed point of `T̂` and its stopping rule is eventually met.
* **Theorem 9.1.3** (9.5) and **Theorem 9.1.4** (9.10): bounds on `d(v*, v_σ)` for a policy
  `σ` greedy at the last iterate.
* **Proposition 9.1.5**: with `L` order preserving, `(L(V), 𝕋̂)` is an ADP.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace ADP

variable {V P : Type*} [PartialOrder V] [MetricSpace V]

/-- **Assumption 9.1.1** (p. 299): `(V, 𝕋)` is regular, each `T_σ` is a contraction of modulus
`β < 1`, and the metric is sup-nonexpansive (completeness is the instance `CompleteSpace V`). -/
structure Assumption911 (A : ADP V P) (β : ℝ) : Prop where
  regular : A.Regular
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  contraction : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w
  supNonexpansive : IsSupNonexpansive (dist : V → V → ℝ)

/-- A map is nonexpansive (9.4). -/
def Nonexpansive (L : V → V) : Prop := ∀ v w, dist (L v) (L w) ≤ dist v w

variable {A : ADP V P} {β : ℝ}

namespace Assumption911

variable (h : A.Assumption911 β)
include h

/-- Under Assumption 9.1.1 the Bellman operator is a contraction of modulus `β`. -/
theorem bellman_contraction (v w : V) : dist (A.bellman v) (A.bellman w) ≤ β * dist v w :=
  lemma_A_5_21 h.supNonexpansive h.β_nonneg h.contraction (h.regular v) (h.regular w)

/-- A `v`-greedy policy attains the Bellman operator: `T_σ v = Tv`. -/
theorem T_eq_bellman {v : V} {σ : P} (hσ : A.IsGreedy v σ) : A.T σ v = A.bellman v :=
  (A.isGreedy_iff (h.regular v) σ).1 hσ

/-- `d(v*, v) ≤ d(Tv, v)/(1 − β)` for the fixed point `v*` of `T`, (9.7). -/
theorem one_sub_mul_dist_fixed_le {vstar : V} (hvs : A.bellman vstar = vstar) (v : V) :
    (1 - β) * dist vstar v ≤ dist (A.bellman v) v := by
  have h1 := dist_triangle vstar (A.bellman v) v
  have h2 := h.bellman_contraction vstar v
  rw [hvs] at h2
  linarith

/-- `d(v, v_σ) ≤ d(v, Tv)/(1 − β)` for `σ` greedy at `v` and `v_σ = T_σ v_σ`. -/
theorem one_sub_mul_dist_vσ_le {v vσ : V} {σ : P} (hσ : A.IsGreedy v σ)
    (hvσ : A.T σ vσ = vσ) : (1 - β) * dist v vσ ≤ dist v (A.bellman v) := by
  have h1 := dist_triangle v (A.bellman v) vσ
  have h2 := h.contraction σ v vσ
  rw [h.T_eq_bellman hσ, hvσ] at h2
  linarith

end Assumption911

/-- Consequences of **Assumption 9.1.1** (p. 299), by Theorem 3.1.5 with `V₀ = V`: the
fundamental optimality properties hold, `T` is a contraction of modulus `β`, the value function
`v*` is the unique fixed point of `T`, and VFI, OPI and HPI converge. -/
theorem assumption_9_1_1 [CompleteSpace V] [OrderClosedTopology V] [Nonempty V]
    (h : A.Assumption911 β) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      (∀ v w, dist (A.bellman v) (A.bellman w) ≤ β * dist v w) ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.bellman vstar = vstar ∧
        (∀ w, A.bellman w = w → w = vstar) ∧ A.VFIGeometric univ vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := theorem_3_1_5 h.supNonexpansive h.β_nonneg h.β_lt_one
    h.contraction (V₀ := univ) ⟨isClosed_univ, fun v _ => h.regular v, mapsTo_univ _ _⟩
    univ_nonempty
  obtain ⟨w, hw, -, hws, huniq⟩ := hFO.2.1
  have hfix : A.bellman vstar = vstar := by
    rw [hgeo.1.unique hw]
    exact (A.solvesBellman_iff (h.regular w)).1 hws
  refine ⟨_, hFO, h.bellman_contraction, vstar, hgeo.1, hfix, fun u hu => ?_, hgeo,
    hconv h.regular⟩
  rw [hgeo.1.unique hw]
  exact huniq u (h.regular u) ((A.solvesBellman_iff (h.regular u)).2 hu)

/-- The approximate Bellman operator `T̂ = L ∘ T`. -/
noncomputable def approxBellman (A : ADP V P) (L : V → V) (v : V) : V := L (A.bellman v)

/-- **Lemma 9.1.2** (p. 300): if `L` is nonexpansive, `T̂ = L ∘ T` is a contraction of
modulus `β`. -/
theorem lemma_9_1_2 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L) (v w : V) :
    dist (A.approxBellman L v) (A.approxBellman L w) ≤ β * dist v w :=
  (hL _ _).trans (h.bellman_contraction v w)

/-- By Lemma 9.1.2 and Banach's theorem, `T̂` has a unique fixed point `v̂` and the FVI iterates
`T̂ⁿv₀` converge to it from every `v₀` (p. 300). -/
theorem approxBellman_globallyStable [CompleteSpace V] [Nonempty V] (h : A.Assumption911 β)
    {L : V → V} (hL : Nonexpansive L) :
    ∃ vhat, A.approxBellman L vhat = vhat ∧ (∀ w, A.approxBellman L w = w → w = vhat) ∧
      ∀ v₀, Tendsto (fun n => (A.approxBellman L)^[n] v₀) atTop (𝓝 vhat) := by
  have hc : ContractingWith ⟨β, h.β_nonneg⟩ (A.approxBellman L) :=
    ⟨h.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => lemma_9_1_2 h hL v w⟩
  exact ⟨hc.fixedPoint _, hc.fixedPoint_isFixedPt, fun w hw => hc.fixedPoint_unique hw,
    hc.tendsto_iterate_fixedPoint⟩

/-- The FVI step size `e_n = d(v_n, v_{n−1})` shrinks geometrically, so the stopping rule
`e_N ≤ τ` of Algorithm 9.1 is met for every tolerance `τ > 0`. -/
theorem fvi_terminates (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L) (v₀ : V)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ N, dist ((A.approxBellman L)^[N + 1] v₀) ((A.approxBellman L)^[N] v₀) ≤ τ := by
  set f := A.approxBellman L
  have hstep : ∀ n, dist (f^[n + 1] v₀) (f^[n] v₀) ≤ β ^ n * dist (f v₀) v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : f^[n + 1 + 1] v₀ = f (f^[n + 1] v₀) := iterate_succ_apply' f (n + 1) v₀
      have e2 : f^[n + 1] v₀ = f (f^[n] v₀) := iterate_succ_apply' f n v₀
      calc dist (f^[n + 1 + 1] v₀) (f^[n + 1] v₀) = dist (f (f^[n + 1] v₀)) (f (f^[n] v₀)) := by
            rw [← e1, ← e2]
        _ ≤ β * dist (f^[n + 1] v₀) (f^[n] v₀) := lemma_9_1_2 h hL _ _
        _ ≤ β * (β ^ n * dist (f v₀) v₀) := mul_le_mul_of_nonneg_left ih h.β_nonneg
        _ = β ^ (n + 1) * dist (f v₀) v₀ := by ring
  have hlim : Tendsto (fun n => β ^ n * dist (f v₀) v₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_nonneg h.β_lt_one).mul_const
      (dist (f v₀) v₀)
  obtain ⟨N, hN⟩ := (hlim.eventually (ge_mem_nhds hτ)).exists
  exact ⟨N, (hstep N).trans hN⟩

/-- **Theorem 9.1.3** (p. 301), (9.5): let `v = L(Tu)` be an FVI iterate following `u`, with step
size `e = d(v, u)`, and let `σ` be `v`-greedy. If `L` is nonexpansive, then
`d(v*, v_σ) ≤ 2/(1 − β) · (βe + d(LTv, Tv))`. -/
theorem theorem_9_1_3 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) {u v : V} (huv : v = A.approxBellman L u)
    {σ : P} (hσ : A.IsGreedy v σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) * (β * dist v u + dist (L (A.bellman v)) (A.bellman v)) := by
  have hb := sub_pos.2 h.β_lt_one
  -- `d(Tv, v) ≤ d(Tv, LTv) + βe`
  have hTv : dist (A.bellman v) v ≤ dist (L (A.bellman v)) (A.bellman v) + β * dist v u := by
    have h1 := dist_triangle (A.bellman v) (L (A.bellman v)) v
    have h2 : dist (L (A.bellman v)) v ≤ β * dist v u := by
      have := lemma_9_1_2 h hL v u
      rw [← huv] at this
      exact this
    linarith [dist_comm (A.bellman v) (L (A.bellman v))]
  have h98 := h.one_sub_mul_dist_fixed_le hvs v
  have h99 := h.one_sub_mul_dist_vσ_le hσ hvσ
  rw [dist_comm v (A.bellman v)] at h99
  have htri := mul_le_mul_of_nonneg_left (dist_triangle vstar v vσ) hb.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hb]
  linarith

/-- **Theorem 9.1.4** (p. 301), (9.10): with `v = L(Tu)`, `e = d(v, u)` and `σ` `v`-greedy, if `L`
is nonexpansive then `d(v*, v_σ) ≤ 2/(1 − β)² · (βe + d(Lv*, v*))`. -/
theorem theorem_9_1_4 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) {u v : V} (huv : v = A.approxBellman L u)
    {σ : P} (hσ : A.IsGreedy v σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) ^ 2 * (β * dist v u + dist (L vstar) vstar) := by
  have hb := sub_pos.2 h.β_lt_one
  -- (9.11): `(1 − β) d(v*, v_σ) ≤ 2 d(v, v*)`
  have hTv : dist v (A.bellman v) ≤ (1 + β) * dist v vstar := by
    have h1 := dist_triangle v vstar (A.bellman v)
    have h2 := h.bellman_contraction vstar v
    rw [hvs, dist_comm vstar v] at h2
    linarith
  have h99 := h.one_sub_mul_dist_vσ_le hσ hvσ
  have h911 : (1 - β) * dist vstar vσ ≤ 2 * dist v vstar := by
    have htri := dist_triangle vstar v vσ
    rw [dist_comm vstar v] at htri
    nlinarith
  -- `(1 − β) d(v*, v) ≤ d(v*, Lv*) + βe`
  have hvsv : (1 - β) * dist vstar v ≤ dist (L vstar) vstar + β * dist v u := by
    have h1 := dist_triangle vstar (L vstar) v
    have h2 : dist (L vstar) v ≤ β * dist vstar u := by
      have := lemma_9_1_2 h hL vstar u
      rw [← huv, show A.approxBellman L vstar = L vstar by rw [approxBellman, hvs]] at this
      exact this
    have h3 := dist_triangle vstar v u
    rw [dist_comm vstar (L vstar)] at h1
    nlinarith [mul_le_mul_of_nonneg_left h3 h.β_nonneg]
  rw [dist_comm v vstar] at h911
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb 2)]
  nlinarith [mul_le_mul_of_nonneg_left hvsv (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Theorem 9.1.3** for the FVI iterates `v_n = T̂ⁿv₀`: if the algorithm stops at `v_{N+1}` with
step size `e = d(v_{N+1}, v_N)` and `σ` is `v_{N+1}`-greedy, (9.5) holds. -/
theorem theorem_9_1_3_fvi (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) (v₀ : V) (N : ℕ) {σ : P}
    (hσ : A.IsGreedy ((A.approxBellman L)^[N + 1] v₀) σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) * (β * dist ((A.approxBellman L)^[N + 1] v₀)
      ((A.approxBellman L)^[N] v₀) + dist (L (A.bellman ((A.approxBellman L)^[N + 1] v₀)))
        (A.bellman ((A.approxBellman L)^[N + 1] v₀))) :=
  theorem_9_1_3 h hL hvs (iterate_succ_apply' _ N v₀) hσ hvσ

/-- **Theorem 9.1.4** for the FVI iterates: (9.10) at the stopping iterate `v_{N+1}`. -/
theorem theorem_9_1_4_fvi (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) (v₀ : V) (N : ℕ) {σ : P}
    (hσ : A.IsGreedy ((A.approxBellman L)^[N + 1] v₀) σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) ^ 2 * (β * dist ((A.approxBellman L)^[N + 1] v₀)
      ((A.approxBellman L)^[N] v₀) + dist (L vstar) vstar) :=
  theorem_9_1_4 h hL hvs (iterate_succ_apply' _ N v₀) hσ hvσ

/-- **Proposition 9.1.5** (p. 303): if `L` is order preserving, `(L(V), 𝕋̂)` with
`T̂_σ = L ∘ T_σ` is an ADP. (Nonexpansiveness, assumed in the book, is not needed.) -/
def approxADP (A : ADP V P) {L : V → V} (hL : Monotone L) : ADP (range L) P where
  T σ v := ⟨L (A.T σ v), mem_range_self _⟩
  mono σ _ _ hvw := hL (A.mono σ hvw)
  nonempty := A.nonempty

omit [MetricSpace V] in
theorem proposition_9_1_5 (A : ADP V P) {L : V → V} (hL : Monotone L) (σ : P) (v : range L) :
    ((A.approxADP hL).T σ v : V) = L (A.T σ v) := rfl

end ADP

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Approximation methods

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.1 (pp. 296–299), with
Lemma 9.1.6 and Remark 9.1.2 (p. 303).

* Kernel averagers (9.2)–(9.3): `(Lf)(x) = ∑ᵢ f(xᵢ)κᵢ(x)` with nonnegative weights summing to
  one. **Lemma 9.1.1**: `L` maps `bX` into itself and is nonexpansive in the supremum norm.
  **Lemma 9.1.6**: `L` is order preserving. **Remark 9.1.2**: so fitted value iteration with a
  kernel averager satisfies the hypotheses of §9.1.2.
* **Example 9.1.1**: Gaussian kernel averagers satisfy (9.2).
* **Example 9.1.2**: the hat functions of a grid `x₀ < ⋯ < xₙ` satisfy (9.2); the kernel
  averager interpolates `f` at the grid points, is affine between them, and is the unique such
  function.
* Global approximation (p. 299): with `Z` of full column rank, `θ̂ = (ZᵀZ)⁻¹Zᵀy` is the unique
  minimizer of the sum of squared residuals.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- A kernel averager (9.2)–(9.3): grid points `xᵢ` and measurable weights `κᵢ ≥ 0` with
`∑ᵢ κᵢ = 1`. -/
structure KernelAverager (X : Type*) [MeasurableSpace X] (n : ℕ) where
  /-- the grid points -/
  grid : Fin n → X
  /-- the weighting functions -/
  κ : Fin n → X → ℝ
  measurable_κ : ∀ i, Measurable (κ i)
  κ_nonneg : ∀ i x, 0 ≤ κ i x
  sum_κ : ∀ x, ∑ i, κ i x = 1

namespace KernelAverager

variable {X : Type*} [MeasurableSpace X] {n : ℕ} (K : KernelAverager X n)

/-- (9.3): `(Lf)(x) = ∑ᵢ f(xᵢ)κᵢ(x)`. -/
noncomputable def Lfun (f : X → ℝ) (x : X) : ℝ := ∑ i, f (K.grid i) * K.κ i x

theorem κ_le_one (i : Fin n) (x : X) : K.κ i x ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => K.κ_nonneg j x) (Finset.mem_univ i)
  rwa [K.sum_κ] at h

/-- `|Lf| ≤ C` when `|f| ≤ C`: `Lf(x)` is an average. -/
theorem abs_Lfun_le {f : X → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) (x : X) : |K.Lfun f x| ≤ C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f (K.grid i) * K.κ i x| ≤ ∑ i, C * K.κ i x := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (K.κ_nonneg i x)]
        exact mul_le_mul_of_nonneg_right (hf _) (K.κ_nonneg i x)
    _ = C := by rw [← Finset.mul_sum, K.sum_κ, mul_one]

theorem Lfun_sub (f g : X → ℝ) (x : X) : K.Lfun f x - K.Lfun g x = K.Lfun (f - g) x := by
  unfold Lfun
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_mul]

theorem Lfun_const (c : ℝ) (x : X) : K.Lfun (fun _ => c) x = c := by
  rw [Lfun, ← Finset.mul_sum, K.sum_κ, mul_one]

theorem measurable_Lfun (f : X → ℝ) : Measurable (K.Lfun f) :=
  Finset.measurable_sum _ fun i _ => measurable_const.mul (K.measurable_κ i)

/-- **Lemma 9.1.1** (p. 298), first part: `L` maps `bX` into itself. -/
noncomputable def L (f : BM X) : BM X :=
  ⟨K.Lfun f.toFun, K.measurable_Lfun _, ⟨‖f‖, fun x => K.abs_Lfun_le (BM.abs_le_norm f) x⟩⟩

theorem L_apply (f : BM X) (x : X) : (K.L f).toFun x = K.Lfun f.toFun x := rfl

/-- **Lemma 9.1.1** (p. 298), second part: `L` is nonexpansive under the supremum norm. -/
theorem lemma_9_1_1 (f g : BM X) : dist (K.L f) (K.L g) ≤ dist f g :=
  BM.dist_le dist_nonneg fun x => by
    rw [L_apply, L_apply, Lfun_sub]
    exact K.abs_Lfun_le (fun y => BM.abs_sub_le_dist f g y) x

/-- **Lemma 9.1.6** (p. 303): `L` is order preserving on `(bX, ≤)`. -/
theorem lemma_9_1_6 : Monotone K.L := fun f g hfg => BM.le_def.2 fun x => by
  change ∑ i, f.toFun (K.grid i) * K.κ i x ≤ ∑ i, g.toFun (K.grid i) * K.κ i x
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (BM.le_def.1 hfg _) (K.κ_nonneg i x)

/-- **Remark 9.1.2** (p. 303): a kernel averager is nonexpansive and order preserving on `bX`, so
Lemma 9.1.2, Theorems 9.1.3–9.1.4 and Proposition 9.1.5 apply to it. -/
theorem remark_9_1_2 : ADP.Nonexpansive K.L ∧ Monotone K.L := ⟨K.lemma_9_1_1, K.lemma_9_1_6⟩

end KernelAverager

/-! ### Example 9.1.1: Gaussian kernels -/

/-- The Gaussian kernel `K_h(x, xᵢ) = exp(−‖x − xᵢ‖²/(2h²))`. -/
noncomputable def gaussKernel {E : Type*} [NormedAddCommGroup E] (h : ℝ) (x y : E) : ℝ :=
  Real.exp (-(‖x - y‖ ^ 2) / (2 * h ^ 2))

/-- **Example 9.1.1** (p. 297): `κᵢ(x) = K_h(x, xᵢ)/∑ⱼ K_h(x, xⱼ)` satisfies (9.2), so it defines a
kernel averager. -/
noncomputable def gaussianAverager {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {n : ℕ} [NeZero n] (grid : Fin n → E) (h : ℝ) :
    KernelAverager E n where
  grid := grid
  κ i x := gaussKernel h x (grid i) / ∑ j, gaussKernel h x (grid j)
  measurable_κ i := by
    have hc : ∀ j, Continuous fun x : E => gaussKernel h x (grid j) := fun j =>
      Real.continuous_exp.comp (((continuous_id.sub continuous_const).norm.pow 2).neg.div_const _)
    exact ((hc i).div (continuous_finsetSum _ fun j _ => hc j) fun x =>
      (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty).ne').measurable
  κ_nonneg i x := div_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
  sum_κ x := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-! ### Example 9.1.2: piecewise linear interpolation -/

/-- The hat function `κᵢ` of the grid `x₀ < x₁ < ⋯ < xₙ`, extended by `1` beyond the end points
(the "obvious modifications"). -/
noncomputable def hat (x : ℕ → ℝ) (n i : ℕ) (t : ℝ) : ℝ :=
  if t ≤ x i then (if i = 0 then 1 else max 0 ((t - x (i - 1)) / (x i - x (i - 1))))
  else (if i = n then 1 else max 0 ((x (i + 1) - t) / (x (i + 1) - x i)))

namespace Hat

variable {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ}

theorem hat_nonneg (i : ℕ) (t : ℝ) : 0 ≤ hat x n i t := by
  unfold hat
  split_ifs <;> first | exact zero_le_one | exact le_max_left _ _

include hx in
/-- On `[xⱼ, xⱼ₊₁]` only `κⱼ` and `κⱼ₊₁` are nonzero, and they are the linear weights. -/
theorem hat_on {j : ℕ} (hj : j < n) {t : ℝ} (ht : t ∈ Set.Icc (x j) (x (j + 1))) (i : ℕ) :
    hat x n i t = if i = j then (x (j + 1) - t) / (x (j + 1) - x j)
      else if i = j + 1 then (t - x j) / (x (j + 1) - x j) else 0 := by
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  unfold hat
  rcases lt_trichotomy i j with hij | rfl | hij
  · -- `i < j`
    have hti : ¬ t ≤ x i := not_le.2 ((hx hij).trans_le ht.1)
    have hin : i ≠ n := by omega
    have h1 : x (i + 1) ≤ t := (hx.monotone (by omega : i + 1 ≤ j)).trans ht.1
    have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
    have h2 : i ≠ j := by omega
    have h3 : i ≠ j + 1 := by omega
    simp only [hti, hin, h2, h3, ↓reduceIte]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  · -- `i = j`
    simp only [↓reduceIte]
    by_cases htj : t ≤ x i
    · have hteq : t = x i := le_antisymm htj ht.1
      subst hteq
      simp only [htj, ↓reduceIte, div_self hΔ.ne']
      split_ifs with h0
      · rfl
      · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
        rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hin : i ≠ n := by omega
      simp only [htj, hin, ↓reduceIte]
      exact max_eq_right (div_nonneg (by linarith [ht.2]) hΔ.le)
  · rcases (Nat.succ_le_of_lt hij).eq_or_lt with hij' | hij'
    · -- `i = j + 1`
      subst hij'
      have h0 : j + 1 ≠ j := by omega
      have h1 : j + 1 ≠ 0 := by omega
      simp only [ht.2, ↓reduceIte, h0, h1, Nat.succ_sub_one]
      exact max_eq_right (div_nonneg (by linarith [ht.1]) hΔ.le)
    · -- `i > j + 1`
      have hti : t ≤ x i := ht.2.trans (hx hij').le
      have h1 : t ≤ x (i - 1) := ht.2.trans (hx.monotone (by omega))
      have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      have h2 : i ≠ 0 := by omega
      have h3 : i ≠ j := by omega
      have h4 : i ≠ j + 1 := by omega
      simp only [hti, ↓reduceIte, h2, h3, h4]
      exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

include hx in
theorem hat_left {t : ℝ} (ht : t ≤ x 0) (i : ℕ) : hat x n i t = if i = 0 then 1 else 0 := by
  unfold hat
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [ht]
  · have hti : t ≤ x i := ht.trans (hx.monotone (Nat.zero_le i))
    have h1 : t ≤ x (i - 1) := ht.trans (hx.monotone (Nat.zero_le _))
    have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
    have h2 : i ≠ 0 := by omega
    simp only [hti, ↓reduceIte, h2]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

include hx in
theorem hat_right (hn : 1 ≤ n) {t : ℝ} (ht : x n ≤ t) {i : ℕ} (hi : i ≤ n) :
    hat x n i t = if i = n then 1 else 0 := by
  unfold hat
  rcases hi.lt_or_eq with hi | rfl
  · have hti : ¬ t ≤ x i := not_le.2 ((hx hi).trans_le ht)
    have h1 : x (i + 1) ≤ t := (hx.monotone (by omega)).trans ht
    have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
    have hin : i ≠ n := by omega
    simp only [hti, hin, ↓reduceIte]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  · simp only [↓reduceIte]
    split_ifs with h1 h2
    · omega
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      rw [le_antisymm h1 ht, div_self hd.ne', max_eq_right zero_le_one]
    · rfl

/-- Every `t ∈ [x₀, xₙ]` lies in some `[xⱼ, xⱼ₊₁]`, `j < n`. -/
theorem exists_interval (hn : 1 ≤ n) {t : ℝ} (h0 : x 0 ≤ t) (hn' : t ≤ x n) :
    ∃ j < n, t ∈ Set.Icc (x j) (x (j + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, one_pos, h0, hn'⟩
  | succ m hm ih =>
    by_cases htm : t ≤ x m
    · obtain ⟨j, hj, hjt⟩ := ih htm
      exact ⟨j, by omega, hjt⟩
    · exact ⟨m, by omega, (not_le.1 htm).le, hn'⟩

/-- The sum of `f(i)` over `Fin (n + 1)` for a function vanishing off `{j, j + 1}`. -/
theorem sum_two {n j : ℕ} (hj : j < n) (a b : ℝ) :
    ∑ i : Fin (n + 1), (if (i : ℕ) = j then a else if (i : ℕ) = j + 1 then b else 0) = a + b := by
  have e : ∀ i : ℕ, (if i = j then a else if i = j + 1 then b else 0) =
      (if i = j then a else 0) + (if i = j + 1 then b else 0) := fun i => by
    split_ifs <;> first | omega | ring
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then a else if i = j + 1 then b else 0)]
  have h1 : j < n + 1 := by omega
  have h2 : j + 1 < n + 1 := by omega
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, h1, h2,
    ↓reduceIte]

include hx in
/-- (9.2) for the hat functions: they sum to one everywhere. -/
theorem sum_hat (hn : 1 ≤ n) (t : ℝ) : ∑ i : Fin (n + 1), hat x n i t = 1 := by
  by_cases h0 : t ≤ x 0
  · simp only [hat_left hx h0]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i = 0 then (1 : ℝ) else 0),
      Finset.sum_ite_eq' (Finset.range (n + 1)) 0 fun _ => (1 : ℝ)]
    simp
  by_cases hn' : x n ≤ t
  · rw [Finset.sum_congr rfl fun i _ => hat_right hx hn hn' (Nat.lt_succ_iff.1 i.2),
      Fin.sum_univ_eq_sum_range (fun i => if i = n then (1 : ℝ) else 0),
      Finset.sum_ite_eq' (Finset.range (n + 1)) n fun _ => (1 : ℝ)]
    simp
  obtain ⟨j, hj, hjt⟩ := exists_interval hn (not_le.1 h0).le (not_le.1 hn').le
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  rw [Finset.sum_congr rfl fun (i : Fin (n + 1)) _ => hat_on hx hj hjt (i : ℕ), sum_two hj]
  field_simp
  ring

include hx in
/-- The hat functions interpolate: `κᵢ(xⱼ) = 𝟙{i = j}`. -/
theorem hat_grid (hn : 1 ≤ n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    hat x n i (x j) = if i = j then 1 else 0 := by
  rcases hj.lt_or_eq with hj | rfl
  · have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
    rw [hat_on hx hj ⟨le_rfl, (hx (Nat.lt_succ_self j)).le⟩ i]
    split_ifs <;> first | omega | rfl | (rw [div_self hΔ.ne']) | (rw [sub_self, zero_div])
  · exact hat_right hx hn le_rfl hi

include hx in
theorem continuous_hat (i : ℕ) : Continuous (hat x n i) := by
  unfold hat
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const fun t ht => ?_
  · split_ifs
    · exact continuous_const
    · exact continuous_const.max ((continuous_id.sub continuous_const).div_const _)
  · split_ifs
    · exact continuous_const
    · exact continuous_const.max ((continuous_const.sub continuous_id).div_const _)
  · subst ht
    split_ifs with h1 h2
    · rfl
    · have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
      rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      have hd' : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
      rw [div_self hd.ne', div_self hd'.ne']

end Hat

open Hat

/-- **Example 9.1.2** (p. 297): the hat functions of a strictly increasing grid
`x₀ < x₁ < ⋯ < xₙ` define a kernel averager on `ℝ`. -/
noncomputable def hatAverager {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ} (hn : 1 ≤ n) :
    KernelAverager ℝ (n + 1) where
  grid i := x i
  κ i := hat x n i
  measurable_κ i := (continuous_hat hx i).measurable
  κ_nonneg i t := hat_nonneg i t
  sum_κ t := sum_hat hx hn t


variable {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ} (hn : 1 ≤ n)

include hx hn in
/-- **Example 9.1.2**: the kernel averager agrees with `f` at the grid points. -/
theorem example_9_1_2_interpolates (f : ℝ → ℝ) {j : ℕ} (hj : j ≤ n) :
    (hatAverager hx hn).Lfun f (x j) = f (x j) := by
  change ∑ i : Fin (n + 1), f (x i) * hat x n i (x j) = f (x j)
  simp only [hat_grid hx hn (Nat.lt_succ_iff.1 (Fin.is_lt _)) hj, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x i) else 0),
    Finset.sum_ite_eq' (Finset.range (n + 1)) j fun i => f (x i)]
  simp [Nat.lt_succ_iff.2 hj]

include hx hn in
/-- **Example 9.1.2**: between grid points the kernel averager is the linear interpolant. -/
theorem example_9_1_2_linear (f : ℝ → ℝ) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Icc (x j) (x (j + 1))) :
    (hatAverager hx hn).Lfun f t =
      f (x j) * ((x (j + 1) - t) / (x (j + 1) - x j)) +
        f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j)) := by
  change ∑ i : Fin (n + 1), f (x i) * hat x n i t = _
  simp only [hat_on hx hj ht, mul_ite, mul_zero]
  have e : ∀ i : ℕ, (if i = j then f (x i) * ((x (j + 1) - t) / (x (j + 1) - x j)) else
      if i = j + 1 then f (x i) * ((t - x j) / (x (j + 1) - x j)) else 0) =
      (if i = j then f (x j) * ((x (j + 1) - t) / (x (j + 1) - x j)) else
      if i = j + 1 then f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j)) else 0) := fun i => by
    split_ifs with h1 h2 <;> first | rfl | (subst h1; rfl) | (subst h2; rfl)
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x i) * ((x (j + 1) - t) /
    (x (j + 1) - x j)) else if i = j + 1 then f (x i) * ((t - x j) / (x (j + 1) - x j)) else 0)]
  simp only [e]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x j) * ((x (j + 1) - t) /
    (x (j + 1) - x j)) else if i = j + 1 then f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j))
    else 0), sum_two hj]

include hx hn in
/-- **Example 9.1.2**: `Lf` is continuous, and it is the unique function that agrees with `f` at
the grid points and is affine on each `[xⱼ, xⱼ₊₁]`. -/
theorem example_9_1_2_unique (f : ℝ → ℝ) :
    Continuous ((hatAverager hx hn).Lfun f) ∧
      ∀ g : ℝ → ℝ, (∀ j ≤ n, g (x j) = f (x j)) →
        (∀ j < n, ∃ c d : ℝ, ∀ t ∈ Set.Icc (x j) (x (j + 1)), g t = c + d * t) →
        ∀ t ∈ Set.Icc (x 0) (x n), g t = (hatAverager hx hn).Lfun f t := by
  refine ⟨continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hat hx i),
    fun g hg haff t ht => ?_⟩
  obtain ⟨j, hj, hjt⟩ := exists_interval hn ht.1 ht.2
  obtain ⟨c, d, hcd⟩ := haff j hj
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  have h1 := hcd (x j) ⟨le_rfl, (hx (Nat.lt_succ_self j)).le⟩
  have h2 := hcd (x (j + 1)) ⟨(hx (Nat.lt_succ_self j)).le, le_rfl⟩
  rw [hg j hj.le] at h1
  rw [hg (j + 1) hj] at h2
  rw [example_9_1_2_linear hx hn f hj hjt, hcd t hjt, h1, h2]
  field_simp
  ring

/-! ### Global approximation by least squares -/

/-- The least squares coefficients `θ̂ = (ZᵀZ)⁻¹Zᵀy`. -/
noncomputable def lsq {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) : Fin k → ℝ :=
  (Z.transpose * Z)⁻¹.mulVec (Z.transpose.mulVec y)

/-- The sum of squared residuals `∑ᵢ [(G_θ f)(xᵢ) − f(xᵢ)]²` with `Zᵢⱼ = bⱼ(xᵢ)`. -/
def ssr {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) (θ : Fin k → ℝ) : ℝ :=
  ∑ i, (Z.mulVec θ i - y i) ^ 2

/-- Global approximation (p. 299): if `Z` has full column rank (`θ ↦ Zθ` is injective), then
`θ̂ = (ZᵀZ)⁻¹Zᵀy` minimizes the sum of squared residuals, uniquely. -/
theorem least_squares {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ)
    (hZ : Injective Z.mulVec) (θ : Fin k → ℝ) :
    ssr Z y (lsq Z y) ≤ ssr Z y θ ∧ (ssr Z y θ = ssr Z y (lsq Z y) → θ = lsq Z y) := by
  have hdot : ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = v ⬝ᵥ v := fun v => by
    simp only [dotProduct, sq]
  -- `ZᵀZ` is invertible
  have hinj : Injective (Z.transpose * Z).mulVec := by
    intro a b hab
    have h0 : (Z.transpose * Z).mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 : Z.mulVec (a - b) ⬝ᵥ Z.mulVec (a - b) = 0 := by
      have := congrArg (dotProduct (a - b)) h0
      rwa [dotProduct_zero, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose] at this
    have h2 : Z.mulVec (a - b) = Z.mulVec 0 := by
      rw [dotProduct_self_eq_zero.1 h1, Matrix.mulVec_zero]
    exact sub_eq_zero.1 (hZ h2)
  have hunit : IsUnit (Z.transpose * Z) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (Z.transpose * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  -- the normal equations `Zᵀ(Zθ̂ − y) = 0`
  have hnormal : Z.transpose.mulVec (Z.mulVec (lsq Z y) - y) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, lsq, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
  set r := Z.mulVec (lsq Z y) - y
  have hsplit : Z.mulVec θ - y = Z.mulVec (θ - lsq Z y) + r := by
    simp only [r, Matrix.mulVec_sub]
    abel
  have hcross : Z.mulVec (θ - lsq Z y) ⬝ᵥ r = 0 := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, hnormal, dotProduct_zero]
  have hpy : ssr Z y θ = Z.mulVec (θ - lsq Z y) ⬝ᵥ Z.mulVec (θ - lsq Z y) + ssr Z y (lsq Z y) := by
    have e1 : ssr Z y θ = (Z.mulVec θ - y) ⬝ᵥ (Z.mulVec θ - y) := hdot (Z.mulVec θ - y)
    have e2 : ssr Z y (lsq Z y) = r ⬝ᵥ r := hdot r
    rw [e1, e2, hsplit, add_dotProduct, dotProduct_add, dotProduct_add, hcross,
      dotProduct_comm r, hcross]
    ring
  refine ⟨?_, fun h => ?_⟩
  · rw [hpy]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · rw [hpy] at h
    have h0 : Z.mulVec (θ - lsq Z y) ⬝ᵥ Z.mulVec (θ - lsq Z y) = 0 := by linarith
    have h2 : Z.mulVec (θ - lsq Z y) = Z.mulVec 0 := by
      rw [dotProduct_self_eq_zero.1 h0, Matrix.mulVec_zero]
    exact sub_eq_zero.1 (hZ h2)

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Damped iteration and the asset pricing example

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.3.1 and §9.1.3.4
(pp. 304–308).

* (9.13) and **Lemma 9.1.7**: if `T` is a contraction of modulus `β` on a convex set `Θ`, the
  damped map `Fθ = θ + α(Tθ − θ)` is a self-map of `Θ` and a contraction of modulus
  `1 − α + αβ < 1` with the same fixed points; damped iteration converges geometrically.
  Convexity is needed for `F` to map `Θ` into itself (`lemma_9_1_7_needs_convex`).
* §9.1.3.4: the asset pricing operator `(Tv)(x) = β ∑_{x'} [v(x') + d(x')]P(x, x')`.
  **Exercise 9.1.1**: `T` is a contraction of modulus `β` on `(ℝ^X, ‖·‖∞)`; it is order
  preserving; its fixed point is `v* = (I − K)⁻¹Kd`, `K = βP`. The sampled operator `T̂`
  is unbiased, `𝔼[(T̂v)(x)] = (Tv)(x)`, the update (9.15) is the Robbins–Monro rule (9.14) with
  `W = T̂v − Tv`, and the noise obeys the bounds of footnote 1 (condition (ii) of
  Theorem 9.1.8).
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The damped map `Fθ = θ + α(Tθ − θ)` (9.13). -/
def damped (T : E → E) (α : ℝ) (θ : E) : E := θ + α • (T θ - θ)

theorem damped_eq (T : E → E) (α : ℝ) (θ : E) :
    damped T α θ = (1 - α) • θ + α • T θ := by
  unfold damped
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- **Lemma 9.1.7** (p. 304): if `T` maps the convex set `Θ` into itself and is a contraction of
modulus `β` there, then for `α ∈ (0, 1]` the damped map `F` maps `Θ` into itself, is a
contraction of modulus `1 − α + αβ < 1`, and has the same fixed points as `T`. -/
theorem lemma_9_1_7 {T : E → E} {Θ : Set E} (hΘ : Convex ℝ Θ) (hT : MapsTo T Θ Θ) {β : ℝ}
    (hβ1 : β < 1) (hc : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖T θ - T θ'‖ ≤ β * ‖θ - θ'‖) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MapsTo (damped T α) Θ Θ ∧
      (∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖damped T α θ - damped T α θ'‖ ≤ (1 - α + α * β) * ‖θ - θ'‖) ∧
      1 - α + α * β < 1 ∧ ∀ θ, damped T α θ = θ ↔ T θ = θ := by
  refine ⟨fun θ hθ => ?_, fun θ hθ θ' hθ' => ?_, by nlinarith, fun θ => ?_⟩
  · rw [damped_eq]
    exact hΘ hθ (hT hθ) (by linarith) hα0.le (by ring)
  · rw [damped_eq, damped_eq]
    have e : (1 - α) • θ + α • T θ - ((1 - α) • θ' + α • T θ') =
        (1 - α) • (θ - θ') + α • (T θ - T θ') := by
      simp only [smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hα0.le]
    nlinarith [hc θ hθ θ' hθ', norm_nonneg (θ - θ')]
  · unfold damped
    constructor
    · intro h
      have h1 : α • (T θ - θ) = 0 := by
        have := congrArg (· - θ) h
        simpa using this
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hα0.ne'
      · exact sub_eq_zero.1 h2
    · intro h
      rw [h, sub_self, smul_zero, add_zero]

/-- Damped iteration converges geometrically to the fixed point `θ̄ ∈ Θ` of `T`:
`‖Fᵏθ − θ̄‖ ≤ (1 − α + αβ)ᵏ ‖θ − θ̄‖`. -/
theorem damped_iterate_le {T : E → E} {Θ : Set E} (hΘ : Convex ℝ Θ) (hT : MapsTo T Θ Θ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖T θ - T θ'‖ ≤ β * ‖θ - θ'‖) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {θbar : E} (hbar : θbar ∈ Θ) (hfix : T θbar = θbar)
    {θ : E} (hθ : θ ∈ Θ) (k : ℕ) :
    ‖(damped T α)^[k] θ - θbar‖ ≤ (1 - α + α * β) ^ k * ‖θ - θbar‖ := by
  obtain ⟨hmaps, hcon, -, hfixd⟩ := lemma_9_1_7 hΘ hT hβ1 hc hα0 hα1
  have hq : 0 ≤ 1 - α + α * β := by nlinarith [mul_nonneg hα0.le hβ0]
  have hF : damped T α θbar = θbar := (hfixd θbar).2 hfix
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', pow_succ]
    have hk := hmaps.iterate k hθ
    calc ‖damped T α ((damped T α)^[k] θ) - θbar‖
        = ‖damped T α ((damped T α)^[k] θ) - damped T α θbar‖ := by rw [hF]
      _ ≤ (1 - α + α * β) * ‖(damped T α)^[k] θ - θbar‖ := hcon _ hk _ hbar
      _ ≤ (1 - α + α * β) * ((1 - α + α * β) ^ k * ‖θ - θbar‖) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

/-- Convexity is needed in Lemma 9.1.7: on `Θ = {0, 1} ⊂ ℝ` the constant map `T ≡ 1` is a
contraction of modulus `0` mapping `Θ` into itself, yet the damped map sends `0` to `α ∉ Θ`
for `α ∈ (0, 1)`. -/
theorem lemma_9_1_7_needs_convex {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    MapsTo (fun _ : ℝ => (1 : ℝ)) ({0, 1} : Set ℝ) {0, 1} ∧
      ¬ MapsTo (damped (fun _ : ℝ => (1 : ℝ)) α) ({0, 1} : Set ℝ) {0, 1} := by
  refine ⟨fun _ _ => Or.inr rfl, fun h => ?_⟩
  have h0 := h (Or.inl rfl : (0 : ℝ) ∈ ({0, 1} : Set ℝ))
  simp only [damped, sub_zero, smul_eq_mul, mul_one, zero_add, Set.mem_insert_iff,
    Set.mem_singleton_iff] at h0
  rcases h0 with h0 | h0 <;> linarith

/-! ### The asset pricing example (§9.1.3.4) -/

/-- The asset pricing model: a `P`-Markov state on a finite set, dividends `d(X_{t+1})`, discount
factor `β ∈ [0, 1)`. -/
structure AssetPricing (X : Type*) [Fintype X] where
  /-- the transition matrix -/
  P : X → X → ℝ
  P_nonneg : ∀ x x', 0 ≤ P x x'
  P_sum : ∀ x, ∑ x', P x x' = 1
  /-- the dividend function -/
  d : X → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace AssetPricing

variable {X : Type*} [Fintype X] (M : AssetPricing X)

/-- `(Tv)(x) = β ∑_{x'} [v(x') + d(x')]P(x, x')`. -/
def T (v : X → ℝ) (x : X) : ℝ := M.β * ∑ x', (v x' + M.d x') * M.P x x'

/-- `T` is order preserving (p. 308). -/
theorem T_mono : Monotone M.T := fun _ _ h x =>
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (add_le_add (h x') le_rfl) (M.P_nonneg x x')) M.β_nonneg

theorem abs_sum_le {u : X → ℝ} {c : ℝ} (hu : ∀ y, |u y| ≤ c) (x : X) :
    |∑ x', u x' * M.P x x'| ≤ c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x', |u x' * M.P x x'| ≤ ∑ x', c * M.P x x' := Finset.sum_le_sum fun x' _ => by
        rw [abs_mul, abs_of_nonneg (M.P_nonneg x x')]
        exact mul_le_mul_of_nonneg_right (hu x') (M.P_nonneg x x')
    _ = c := by rw [← Finset.mul_sum, M.P_sum, mul_one]

/-- **Exercise 9.1.1** (p. 307): `T` is a contraction of modulus `β` on `(ℝ^X, ‖·‖∞)`. -/
theorem exercise_9_1_1 (v w : X → ℝ) : dist (M.T v) (M.T w) ≤ M.β * dist v w := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq]
  have e : M.T v x - M.T w x = M.β * ∑ x', (v x' - w x') * M.P x x' := by
    unfold T
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x' _ => by ring
  rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left (M.abs_sum_le (fun y => ?_) x) M.β_nonneg
  rw [← Real.dist_eq]
  exact dist_le_pi_dist v w y

/-- `K = βP` as a matrix. -/
def K : Matrix X X ℝ := Matrix.of fun x x' => M.β * M.P x x'

theorem T_eq_mulVec (v : X → ℝ) : M.T v = M.K.mulVec (v + M.d) := by
  funext x
  simp only [T, K, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- `I − K` is invertible, and `v* = (I − K)⁻¹Kd` is the unique fixed point of `T` (p. 307). -/
theorem fixedPoint [DecidableEq X] :
    IsUnit (1 - M.K) ∧ M.T ((1 - M.K)⁻¹.mulVec (M.K.mulVec M.d)) =
      (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d) ∧
      ∀ v, M.T v = v → v = (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d) := by
  -- `v = Kv` forces `v = 0`
  have hker : ∀ u : X → ℝ, M.K.mulVec u = u → u = 0 := fun u hu => by
    have h1 : dist u 0 ≤ M.β * dist u 0 := by
      have := M.exercise_9_1_1 u 0
      have e1 : M.T u = M.K.mulVec u + M.K.mulVec M.d := by
        rw [T_eq_mulVec, Matrix.mulVec_add]
      have e2 : M.T 0 = M.K.mulVec M.d := by rw [T_eq_mulVec, zero_add]
      have e3 : dist (M.K.mulVec u + M.K.mulVec M.d) (M.K.mulVec M.d) = dist u 0 := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_right, sub_zero, hu]
      rwa [e1, e2, e3] at this
    have h2 : dist u 0 = 0 := by
      nlinarith [dist_nonneg (x := u) (y := 0), M.β_lt_one]
    exact dist_eq_zero.1 h2
  have hinj : Injective (1 - M.K).mulVec := fun a b hab => by
    have h0 : (1 - M.K).mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact sub_eq_zero.1 (hker _ h0.symm)
  have hunit : IsUnit (1 - M.K) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (1 - M.K).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  set vs := (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d)
  have hvs : (1 - M.K).mulVec vs = M.K.mulVec M.d := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hfix : M.T vs = vs := by
    rw [T_eq_mulVec, Matrix.mulVec_add]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvs
    linear_combination -hvs
  refine ⟨hunit, hfix, fun v hv => ?_⟩
  have h1 : (1 - M.K).mulVec v = M.K.mulVec M.d := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [T_eq_mulVec, Matrix.mulVec_add] at hv
    linear_combination -hv
  exact hinj (h1.trans hvs.symm)

/-- The sampled operator: with draws `x'(x) ∼ P(x, ·)`, `(T̂v)(x) = β[v(x'(x)) + d(x'(x))]`. -/
def That (v : X → ℝ) (draw : X → X) (x : X) : ℝ := M.β * (v (draw x) + M.d (draw x))

/-- `T̂` is unbiased: `𝔼[(T̂v)(x)] = ∑_{x'} β[v(x') + d(x')]P(x, x') = (Tv)(x)` (p. 307). -/
theorem That_unbiased (v : X → ℝ) (x : X) :
    ∑ x', M.β * (v x' + M.d x') * M.P x x' = M.T v x := by
  unfold T
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- (9.15) is the Robbins–Monro rule (9.14) with `W = T̂v − Tv`. -/
theorem update_eq (v w : X → ℝ) (α : ℝ) :
    v + α • (w - v) = v + α • (M.T v + (w - M.T v) - v) := by
  congr 2
  abel

/-- Footnote 1 (p. 308): `|W(x)| ≤ 2β(‖v‖∞ + ‖d‖∞)`, whatever the draws. -/
theorem abs_noise_le (v : X → ℝ) (draw : X → X) (x : X) :
    |M.That v draw x - M.T v x| ≤ 2 * M.β * (‖v‖ + ‖M.d‖) := by
  have hb : ∀ y, |v y + M.d y| ≤ ‖v‖ + ‖M.d‖ := fun y =>
    (abs_add_le _ _).trans (add_le_add (by simpa using norm_le_pi_norm v y)
      (by simpa using norm_le_pi_norm M.d y))
  have h1 : |M.That v draw x| ≤ M.β * (‖v‖ + ‖M.d‖) := by
    rw [That, abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (hb _) M.β_nonneg
  have h2 : |M.T v x| ≤ M.β * (‖v‖ + ‖M.d‖) := by
    rw [T, abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (M.abs_sum_le hb x) M.β_nonneg
  calc |M.That v draw x - M.T v x| ≤ |M.That v draw x| + |M.T v x| := abs_sub _ _
    _ ≤ 2 * M.β * (‖v‖ + ‖M.d‖) := by linarith

/-- Footnote 1 (p. 308), condition (ii) of Theorem 9.1.8: whatever the draws,
`∑ₓ W(x)² ≤ C(1 + ‖v‖∞²)` with `C = 8|X|β²(1 + ‖d‖∞²)`, a constant depending only on `β`, `|X|`
and `‖d‖∞`. -/
theorem sum_sq_noise_le (v : X → ℝ) (draw : X → X) :
    ∑ x, (M.That v draw x - M.T v x) ^ 2 ≤
      8 * Fintype.card X * M.β ^ 2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
  have hpt : ∀ x, (M.That v draw x - M.T v x) ^ 2 ≤ 4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2 := fun x => by
    have h := M.abs_noise_le v draw x
    have h0 : 0 ≤ 2 * M.β * (‖v‖ + ‖M.d‖) :=
      mul_nonneg (mul_nonneg zero_le_two M.β_nonneg) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    calc (M.That v draw x - M.T v x) ^ 2 = |M.That v draw x - M.T v x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M.β * (‖v‖ + ‖M.d‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := by ring
  have hsq : (‖v‖ + ‖M.d‖) ^ 2 ≤ 2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖v‖ - ‖M.d‖), sq_nonneg ‖v‖, sq_nonneg ‖M.d‖,
      mul_nonneg (sq_nonneg ‖v‖) (sq_nonneg ‖M.d‖)]
  calc ∑ x, (M.That v draw x - M.T v x) ^ 2 ≤ ∑ _x : X, 4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2 :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = Fintype.card X * (4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card X * (4 * M.β ^ 2 * (2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2))) := by
        gcongr
    _ = _ := by ring

end AssetPricing

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Q-learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.1 (pp. 310–313).

For a finite MDP, the Q-factor Bellman operator is
`(Sq)(x, a) = r(x, a) + β ∑_{x'} max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')` (9.17), (3.7).

* §9.2.1.1: `S` has a unique fixed point `q*`, the Q-factor value function; with
  Proposition 5.3.1, `v*(x) = max_a q*(x, a)` and any `σ(x) ∈ argmax_a q*(x, a)` is optimal.
* §9.2.1.3: `S` is a contraction of modulus `β` for the supremum norm.
* The Q-learning update (9.18) moves only the visited entry, and there it is the Robbins–Monro
  step `q + α(Ŝq − q)` with the single-sample estimate `(Ŝq)(x, a) = r(x, a) + β max_{a'}
  q(X', a')`, whose mean under `X' ∼ P(x, a, ·)` is `(Sq)(x, a)`: the noise has mean zero.

Theorem 9.2.1 (almost sure convergence of Q-learning, Watkins–Dayan and Tsitsiklis) is cited in
the book and not formalised.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- `max_{a ∈ Γ(x)} q(x, a)`. -/
noncomputable def qmax (q : M.G → ℝ) (x : X) : ℝ :=
  (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach) fun a => q ⟨(x, a.1), a.2⟩

theorem le_qmax (q : M.G → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : q ⟨(x, a), ha⟩ ≤ M.qmax q x :=
  Finset.le_sup' (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩) (Finset.mem_attach _ ⟨a, ha⟩)

theorem abs_qmax_sub_le {q q' : M.G → ℝ} {c : ℝ} (h : ∀ p, |q p - q' p| ≤ c) (x : X) :
    |M.qmax q x - M.qmax q' x| ≤ c := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a _ => ?_)
    have := (abs_sub_le_iff.1 (h ⟨(x, a.1), a.2⟩)).1
    linarith [M.le_qmax q' a.2]
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a _ => ?_)
    have := (abs_sub_le_iff.1 (h ⟨(x, a.1), a.2⟩)).2
    linarith [M.le_qmax q a.2]

/-- The Q-factor Bellman operator `S` of (9.17). -/
noncomputable def S (q : M.G → ℝ) (p : M.G) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * ∑ x', M.qmax q x' * M.P p.1.1 p.1.2 x'

/-- `S` is the Bellman operator of the Q-factor ADP (Exercise 3.2.4). -/
theorem bellman_qadp (q : M.G → ℝ) : M.qadp.bellman q = M.S q :=
  funext fun p => M.exercise_3_2_4 q p

/-- §9.2.1.3 (p. 311): `S` is a contraction of modulus `β` for the supremum norm. -/
theorem S_contraction {q q' : M.G → ℝ} {c : ℝ} (h : ∀ p, |q p - q' p| ≤ c) (p : M.G) :
    |M.S q p - M.S q' p| ≤ M.β * c := by
  simp only [S, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le p.2 fun y => M.abs_qmax_sub_le h y)
    M.β_nonneg

/-- §9.2.1.1 (p. 310) with Proposition 5.3.1: `S` has a unique fixed point `q*`, the Q-factor
value function; `v*(x) = max_a q*(x, a)`; and a policy maximizing `q*(x, ·)` at every state is
optimal for the MDP. -/
theorem section_9_2_1 :
    ∃ qstar, M.qadp.IsValueFunction qstar ∧ M.S qstar = qstar ∧
      (∀ q, M.S q = q → q = qstar) ∧
      (∀ v, M.adp.IsValueFunction v → ∀ x, v x = M.qmax qstar x) ∧
      ∀ σ : M.Policy, (∀ x a (ha : a ∈ M.Γ x), qstar ⟨(x, a), ha⟩ ≤ qstar (M.pairOf σ x)) →
        M.adp.IsOptimal M.adp_wellPosed σ := by
  obtain ⟨⟨-, ⟨q, hq, -, hqs, huniq⟩, -⟩, -, -⟩ := M.exercise_3_2_6
  obtain ⟨h1, -, h3⟩ := M.proposition_5_3_1
  refine ⟨q, hq, ?_, fun w hw => ?_, fun v hv x => ((h1 v q hv hq).1 x), fun σ hσ =>
    h3 q σ hq hσ⟩
  · rw [← M.bellman_qadp]
    exact (M.qadp.solvesBellman_iff (M.qadp_regular q)).1 hqs
  · refine huniq w (M.qadp_regular w) ((M.qadp.solvesBellman_iff (M.qadp_regular w)).2 ?_)
    rw [M.bellman_qadp]
    exact hw

/-- The single-sample estimate `(Ŝq)(x, a) = r(x, a) + β max_{a'} q(x', a')` after observing
the next state `x'`. -/
noncomputable def Shat (q : M.G → ℝ) (p : M.G) (x' : X) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * M.qmax q x'

/-- The sample is unbiased: `∑_{x'} (Ŝq)(x, a; x') P(x, a, x') = (Sq)(x, a)`. -/
theorem Shat_unbiased (q : M.G → ℝ) (p : M.G) :
    ∑ x', M.Shat q p x' * M.P p.1.1 p.1.2 x' = M.S q p := by
  simp only [Shat, S, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, M.P_sum _ _ p.2, mul_one, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun x' _ => by ring)

/-- The noise `W = Ŝq − Sq` has mean zero under `P(x, a, ·)`. -/
theorem noise_mean_zero (q : M.G → ℝ) (p : M.G) :
    ∑ x', (M.Shat q p x' - M.S q p) * M.P p.1.1 p.1.2 x' = 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib, M.Shat_unbiased, ← Finset.mul_sum,
    M.P_sum _ _ p.2, mul_one, sub_self]

/-- The Q-learning update (9.18) at the visited pair `p = (X_t, A_t)` with next state `x'`. -/
noncomputable def qUpdate [DecidableEq M.G] (q : M.G → ℝ) (p : M.G) (x' : X) (α : ℝ) :
    M.G → ℝ :=
  update q p ((1 - α) * q p + α * M.Shat q p x')

/-- (9.18) is the Robbins–Monro step `q + α(Ŝq − q)` at the visited pair (as (9.16)), and it
leaves every other entry unchanged. -/
theorem qUpdate_apply [DecidableEq M.G] (q : M.G → ℝ) (p : M.G) (x' : X) (α : ℝ) (p' : M.G) :
    M.qUpdate q p x' α p' = if p' = p then q p + α * (M.Shat q p x' - q p) else q p' := by
  unfold qUpdate
  by_cases h : p' = p
  · subst h
    simp only [update_self, ↓reduceIte]
    ring
  · simp only [update_of_ne h, h, ↓reduceIte]

end FiniteMDP

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# From local to global optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.3.3 (pp. 320–321).

Policy gradient methods maximize `M(θ) = v_{σ(·, θ)}(x₀)` at a single initial state.

* **Theorem 9.2.2**: for a finite MDP with `β ∈ (0, 1)` and a policy `σ` whose transition matrix
  `P_σ` is irreducible, `v_σ(x) = v*(x)` at some state iff `σ` is optimal. The proof iterates
  `h ≥ βP_σh` for `h = v* − v_σ ≥ 0`, (9.27).
* Irreducibility is needed: in a two-state MDP with absorbing states, a policy can be optimal at
  one state and not at the other (`theorem_9_2_2_needs_irreducible`).
-/

open Set Function Filter Topology Matrix

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] [DecidableEq X] (M : FiniteMDP X A)

theorem Pσ_pow_nonneg (σ : M.Policy) (m : ℕ) (x y : X) : 0 ≤ (M.Pσ σ.1 ^ m) x y := by
  induction m generalizing x y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (M.P_nonneg _ _ (σ.2 z) y)

theorem Pσ_pow_mulVec_mono (σ : M.Policy) (m : ℕ) {u w : X → ℝ} (h : u ≤ w) :
    (M.Pσ σ.1 ^ m) *ᵥ u ≤ (M.Pσ σ.1 ^ m) *ᵥ w := fun x =>
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (M.Pσ_pow_nonneg σ m x y)

/-- **Theorem 9.2.2** (p. 320): for a finite MDP with `β > 0` and a policy `σ` such that `P_σ` is
irreducible, (i) `v_σ(x) = v*(x)` for some `x` iff (ii) `σ` is optimal. -/
theorem theorem_9_2_2 [Nonempty X] (hβ : 0 < M.β) (σ : M.Policy)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (M.Pσ σ.1 ^ m) x y) :
    (∃ x, M.toDP.vσ σ x = M.toDP.vstar x) ↔ M.toDP.IsOptimal σ := by
  constructor
  · rintro ⟨x₀, hx₀⟩
    rw [M.toDP.isOptimal_iff]
    set h := M.toDP.vstar - M.toDP.vσ σ
    have hnn : ∀ y, 0 ≤ h y := fun y => sub_nonneg.2 (M.toDP.vσ_le_vstar σ y)
    -- `h ≥ βP_σh`
    have hstep : (M.β • M.Pσ σ.1) *ᵥ h ≤ h := by
      have h1 : M.Tσ σ.1 M.toDP.vstar ≤ M.toDP.vstar := by
        have := M.toDP.T_le_bellman σ (mem_univ M.toDP.vstar)
        rwa [M.toDP.bellman_vstar] at this
      have h2 : M.Tσ σ.1 (M.toDP.vσ σ) = M.toDP.vσ σ := M.toDP.T_vσ σ
      intro y
      have e : ((M.β • M.Pσ σ.1) *ᵥ h) y =
          M.Tσ σ.1 M.toDP.vstar y - M.Tσ σ.1 (M.toDP.vσ σ) y := by
        rw [M.Tσ_eq_mulVec, M.Tσ_eq_mulVec]
        simp only [h, Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
        ring
      rw [e, h2]
      simp only [h, Pi.sub_apply]
      linarith [h1 y]
    -- iterating, `h ≥ βᵐP_σᵐh` (9.27)
    have hiter : ∀ m : ℕ, M.β ^ m • ((M.Pσ σ.1 ^ m) *ᵥ h) ≤ h := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have e : M.β ^ (m + 1) • ((M.Pσ σ.1 ^ (m + 1)) *ᵥ h) =
            M.β ^ m • ((M.Pσ σ.1 ^ m) *ᵥ ((M.β • M.Pσ σ.1) *ᵥ h)) := by
          rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ,
            smul_smul, ← pow_succ]
        rw [e]
        intro y
        have hm := M.Pσ_pow_mulVec_mono σ m hstep y
        have hb : 0 ≤ M.β ^ m := pow_nonneg hβ.le m
        simp only [Pi.smul_apply, smul_eq_mul] at hm ih ⊢
        exact (mul_le_mul_of_nonneg_left hm hb).trans (ih y)
    have hh0 : h x₀ = 0 := by simp only [h, Pi.sub_apply, hx₀, sub_self]
    refine (sub_eq_zero.1 (funext fun y => ?_)).symm
    change h y = 0
    refine le_antisymm ?_ (hnn y)
    by_contra hpos
    obtain ⟨m, hm⟩ := hirr x₀ y
    have h1 := hiter m x₀
    simp only [Pi.smul_apply, smul_eq_mul, hh0] at h1
    have h2 : (M.Pσ σ.1 ^ m) x₀ y * h y ≤ ((M.Pσ σ.1 ^ m) *ᵥ h) x₀ :=
      Finset.single_le_sum (f := fun z => (M.Pσ σ.1 ^ m) x₀ z * h z)
        (fun z _ => mul_nonneg (M.Pσ_pow_nonneg σ m x₀ z) (hnn z)) (Finset.mem_univ y)
    have h3 : 0 < (M.Pσ σ.1 ^ m) x₀ y * h y := mul_pos hm (lt_of_not_ge hpos)
    have h4 : 0 < M.β ^ m := pow_pos hβ m
    nlinarith
  · intro hopt
    rw [M.toDP.isOptimal_iff] at hopt
    exact ⟨Classical.arbitrary X, by rw [hopt]⟩

end FiniteMDP

/-- Two absorbing states `false, true`, two actions, reward `1` for action `true` at state `true`,
`β = 1/2`. -/
noncomputable def absorbingMDP : FiniteMDP Bool Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  r x a := if x && a then 1 else 0
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  P x _ x' := if x' = x then 1 else 0
  P_nonneg _ _ _ _ := by split_ifs <;> norm_num
  P_sum x _ _ := by simp

/-- Theorem 9.2.2 needs irreducibility: in `absorbingMDP` the policy `σ ≡ false` attains
`v*(false) = 0` at the state `false` but is not optimal (`v_σ(true) = 0 < 2 = v*(true)`). -/
theorem theorem_9_2_2_needs_irreducible :
    ∃ σ : absorbingMDP.Policy, absorbingMDP.toDP.vσ σ false = absorbingMDP.toDP.vstar false ∧
      ¬ absorbingMDP.toDP.IsOptimal σ := by
  let σ : absorbingMDP.Policy := ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
  -- `v_σ = 0`
  have hvσ : absorbingMDP.toDP.vσ σ = 0 := by
    refine (absorbingMDP.toDP.eq_vσ (mem_univ _) ?_).symm
    funext x
    simp [FiniteMDP.toDP, FiniteMDP.Tσ, FiniteMDP.Q, absorbingMDP, σ]
  -- `v* = 2·𝟙{true}`
  have hvs : absorbingMDP.toDP.vstar = fun x => if x then 2 else 0 := by
    refine (absorbingMDP.toDP.eq_vstar (mem_univ _) ?_).symm
    funext x
    rw [absorbingMDP.bellman_eq]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      cases x <;> cases a <;> norm_num [FiniteMDP.Q, absorbingMDP]
    · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ true))
      cases x <;> norm_num [FiniteMDP.Q, absorbingMDP]
  refine ⟨σ, by rw [hvσ, hvs]; rfl, fun hopt => ?_⟩
  rw [absorbingMDP.toDP.isOptimal_iff, hvσ, hvs] at hopt
  have := congrFun hopt true
  norm_num at this

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Risk-sensitive Q-learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.2 (pp. 313–317).

For a finite MDP and `γ > 0`, the risk-sensitive Bellman equation is (9.19),
`v(x) = max_a −γ⁻¹ ln ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. It is factored with
`V = ℝ^X`, `V̂ = ℝ^G_{++}`, `(Fv)(x, a) = ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')` (9.20)
and `(G_σq)(x) = −γ⁻¹ ln q(x, σ(x))` (9.21).

* **Exercise 9.2.1**: `F` and each `G_σ` are order reversing, and `{G_σq}_σ` has a greatest
  element, so `(V, F, V̂, 𝔾)` is an order-reversing FDP.
* §9.2.2.3: the primary policy operators and Bellman operator (9.19) (Lemma 5.2.15); the
  subordinate Bellman min-operator is (9.22),
  `q(x, a) = ∑_{x'} P(x, a, x') exp(−γr(x, a)) (min_{a'} q(x', a'))^β` (Lemma 5.2.16).
* By Theorem 5.2.18, the fundamental optimality properties hold for both ADPs, and a policy with
  `σ(x) ∈ argmin_a q▿*(x, a)` is optimal for (9.19). Each `T_σ` is a contraction of modulus `β`
  for the supremum norm, so Theorem 3.1.5 applies to the primary ADP.
* **Exercise 9.2.2**: `T̂_σ = F ∘ G_σ` is a contraction of modulus `β` for
  `d(q, q') = ‖ln q − ln q'‖∞`; it is order preserving (Remark 9.2.1).
* The update (9.23) is a single-sample version of (9.22) and keeps `q` positive.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- `ℝ^G_{++}`, the strictly positive functions on `G`. -/
abbrev QPos := {q : M.G → ℝ // ∀ p, 0 < q p}

theorem exists_P_pos (p : M.G) : ∃ x', 0 < M.P p.1.1 p.1.2 x' := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have h0 : ∑ x', M.P p.1.1 p.1.2 x' = 0 :=
    Finset.sum_eq_zero fun x' _ => le_antisymm (h x') (M.P_nonneg _ _ p.2 x')
  rw [M.P_sum _ _ p.2] at h0
  exact one_ne_zero h0

/-- `∑_{x'} exp(a(x'))P(x, a, x')`. -/
noncomputable def expSum (p : M.G) (e : X → ℝ) : ℝ := ∑ x', Real.exp (e x') * M.P p.1.1 p.1.2 x'

theorem expSum_pos (p : M.G) (e : X → ℝ) : 0 < M.expSum p e := by
  obtain ⟨x₀, hx₀⟩ := M.exists_P_pos p
  exact Finset.sum_pos' (fun x' _ => mul_nonneg (Real.exp_pos _).le (M.P_nonneg _ _ p.2 x'))
    ⟨x₀, Finset.mem_univ _, mul_pos (Real.exp_pos _) hx₀⟩

theorem expSum_mono (p : M.G) {e e' : X → ℝ} (h : e ≤ e') : M.expSum p e ≤ M.expSum p e' :=
  Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (h x'))
    (M.P_nonneg _ _ p.2 x')

/-- `ln ∑ e^{a}P ≤ d + ln ∑ e^{b}P` when `a ≤ b + d`. -/
theorem log_expSum_le (p : M.G) {e e' : X → ℝ} {d : ℝ} (h : ∀ x', e x' ≤ e' x' + d) :
    Real.log (M.expSum p e) ≤ d + Real.log (M.expSum p e') := by
  have h1 : M.expSum p e ≤ Real.exp d * M.expSum p e' := by
    calc M.expSum p e ≤ M.expSum p (fun x' => e' x' + d) := M.expSum_mono p h
      _ = Real.exp d * M.expSum p e' := by
          simp only [expSum, Real.exp_add, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x' _ => by ring
  calc Real.log (M.expSum p e) ≤ Real.log (Real.exp d * M.expSum p e') :=
        Real.log_le_log (M.expSum_pos p e) h1
    _ = d + Real.log (M.expSum p e') := by
        rw [Real.log_mul (Real.exp_pos d).ne' (M.expSum_pos p e').ne', Real.log_exp]

/-- `min_{a ∈ Γ(x)} q(x, a)`. -/
noncomputable def qmin (q : M.G → ℝ) (x : X) : ℝ :=
  (M.Γ x).attach.inf' ((M.Γ_nonempty x).attach) fun a => q ⟨(x, a.1), a.2⟩

theorem qmin_le (q : M.G → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.qmin q x ≤ q ⟨(x, a), ha⟩ :=
  Finset.inf'_le (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩) (Finset.mem_attach _ ⟨a, ha⟩)

theorem exists_qmin (q : M.G → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a (ha : a ∈ M.Γ x), q (M.pairOf σ x) ≤ q ⟨(x, a), ha⟩ := by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy fun p => -q p
  exact ⟨σ, fun x a ha => neg_le_neg_iff.1 (hσ x a ha)⟩

theorem qmin_eq {q : M.G → ℝ} {σ : M.Policy}
    (hσ : ∀ x, ∀ a (ha : a ∈ M.Γ x), q (M.pairOf σ x) ≤ q ⟨(x, a), ha⟩) (x : X) :
    q (M.pairOf σ x) = M.qmin q x :=
  le_antisymm (Finset.le_inf' _ _ fun a _ => hσ x a.1 a.2) (M.qmin_le q (σ.2 x))

theorem qmin_pos (q : M.QPos) (x : X) : 0 < M.qmin q.1 x := by
  obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
  rw [← M.qmin_eq hσ x]
  exact q.2 _

variable (γ : ℝ)

/-- (9.20): `(Fv)(x, a) = ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. -/
noncomputable def Fexp (v : X → ℝ) (p : M.G) : ℝ :=
  M.expSum p fun x' => -γ * (M.r p.1.1 p.1.2 + M.β * v x')

/-- (9.21): `(G_σq)(x) = −γ⁻¹ ln q(x, σ(x))`. -/
noncomputable def Glog (σ : M.Policy) (q : M.QPos) (x : X) : ℝ :=
  -(1 / γ) * Real.log (q.1 (M.pairOf σ x))

variable {γ} (hγ : 0 < γ)
include hγ

theorem Glog_le_Glog {σ τ : M.Policy} {q : M.QPos} {x : X}
    (h : q.1 (M.pairOf σ x) ≤ q.1 (M.pairOf τ x)) : M.Glog γ τ q x ≤ M.Glog γ σ q x := by
  unfold Glog
  exact mul_le_mul_of_nonpos_left (Real.log_le_log (q.2 _) h)
    (neg_nonpos.2 (one_div_pos.2 hγ).le)

theorem Glog_anti {σ : M.Policy} {q q' : M.QPos} {x : X}
    (h : q.1 (M.pairOf σ x) ≤ q'.1 (M.pairOf σ x)) : M.Glog γ σ q' x ≤ M.Glog γ σ q x := by
  unfold Glog
  exact mul_le_mul_of_nonpos_left (Real.log_le_log (q.2 _) h)
    (neg_nonpos.2 (one_div_pos.2 hγ).le)

/-- The risk-sensitive FDP `(ℝ^X, F, ℝ^G_{++}, 𝔾)` of §9.2.2.2. -/
noncomputable def rsfdp : FDP (X → ℝ) M.QPos M.Policy where
  F v := ⟨M.Fexp γ v, fun p => M.expSum_pos p _⟩
  G := M.Glog γ
  greatest q := by
    obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
    exact ⟨σ, fun τ x => M.Glog_le_Glog hγ (hσ x (τ.1 x) (τ.2 x))⟩
  nonempty := M.nonempty_policy

/-- **Exercise 9.2.1** (p. 314): `F` and every `G_σ` are order reversing, so
`(V, F, V̂, 𝔾)` is an order-reversing FDP. -/
theorem exercise_9_2_1 : (M.rsfdp hγ).IsOrderReversing := by
  refine ⟨fun v w hvw p => ?_, fun σ q q' hqq x => M.Glog_anti hγ (hqq _)⟩
  refine M.expSum_mono p fun x' => ?_
  have h1 := mul_le_mul_of_nonneg_left (hvw x') M.β_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h1 hγ.le]

theorem monotonic : (M.rsfdp hγ).Monotonic := Or.inr (M.exercise_9_2_1 hγ)

theorem Gsup_eq (q : M.QPos) (x : X) :
    (M.rsfdp hγ).Gsup q x = -(1 / γ) * Real.log (M.qmin q.1 x) := by
  obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
  have hσg : ∀ τ, (M.rsfdp hγ).G τ q ≤ (M.rsfdp hγ).G σ q := fun τ x =>
    M.Glog_le_Glog hγ (hσ x (τ.1 x) (τ.2 x))
  have heq : (M.rsfdp hγ).Gsup q = (M.rsfdp hγ).G σ q := by
    obtain ⟨⟨τ, hτ⟩, -⟩ := (M.rsfdp hγ).isGreatest_Gsup q
    refine le_antisymm ?_ ((M.rsfdp hγ).G_le_Gsup σ q)
    rw [← hτ]
    exact hσg τ
  rw [heq]
  change -(1 / γ) * Real.log (q.1 (M.pairOf σ x)) = _
  rw [M.qmin_eq hσ x]

/-- §9.2.2.3 (p. 314): the primary policy operators are the risk-sensitive operators
`(T_σv)(x) = −γ⁻¹ ln ∑_{x'} P(x, σ(x), x') exp[−γ(r(x, σ(x)) + βv(x'))]`. -/
theorem primary_T (σ : M.Policy) (v : X → ℝ) (x : X) :
    ((M.rsfdp hγ).primary (M.monotonic hγ)).T σ v x =
      -(1 / γ) * Real.log (∑ x', Real.exp (-γ * (M.r x (σ.1 x) + M.β * v x')) *
        M.P x (σ.1 x) x') := rfl

/-- §9.2.2.3 (p. 314), with Lemma 5.2.15: the primary Bellman operator is (9.19),
`(Tv)(x) = max_{a ∈ Γ(x)} −γ⁻¹ ln ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. -/
theorem primary_bellman_eq (v : X → ℝ) (x : X) :
    ((M.rsfdp hγ).primary (M.monotonic hγ)).bellman v x =
      (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach)
        fun a => -(1 / γ) * Real.log (M.Fexp γ v ⟨(x, a.1), a.2⟩) := by
  rw [FDP.primary_bellman, M.Gsup_eq hγ]
  set q : M.QPos := (M.rsfdp hγ).F v
  have hneg : -(1 / γ) ≤ 0 := neg_nonpos.2 (one_div_pos.2 hγ).le
  apply le_antisymm
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' ((M.Γ_nonempty x).attach)
      (fun a : M.Γ x => q.1 ⟨(x, a.1), a.2⟩)
    have : M.qmin q.1 x = q.1 ⟨(x, a.1), a.2⟩ := hmin
    rw [this]
    exact Finset.le_sup' (fun a : M.Γ x => -(1 / γ) * Real.log (M.Fexp γ v ⟨(x, a.1), a.2⟩)) ha
  · refine Finset.sup'_le _ _ fun a _ => mul_le_mul_of_nonpos_left
      (Real.log_le_log (M.qmin_pos q x) (M.qmin_le q.1 a.2)) hneg

/-- (9.22) (p. 314), with Lemma 5.2.16: the subordinate Bellman min-operator is
`(T̂▿q)(x, a) = ∑_{x'} P(x, a, x') exp(−γr(x, a)) (min_{a'} q(x', a'))^β`. -/
theorem sub_bellman_eq (q : M.QPos) :
    ((M.rsfdp hγ).sub (M.monotonic hγ)).IsMinBellmanValue q ((M.rsfdp hγ).F ((M.rsfdp hγ).Gsup q))
      ∧ ∀ p : M.G, ((M.rsfdp hγ).F ((M.rsfdp hγ).Gsup q)).1 p =
        ∑ x', M.P p.1.1 p.1.2 x' *
          (Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β) := by
  refine ⟨(FDP.lemma_5_2_16 (M.monotonic hγ) (M.exercise_9_2_1 hγ)).2.1 q, fun p => ?_⟩
  change M.expSum p (fun x' => -γ * (M.r p.1.1 p.1.2 + M.β * (M.rsfdp hγ).Gsup q x')) = _
  unfold expSum
  refine Finset.sum_congr rfl fun x' _ => ?_
  beta_reduce
  rw [M.Gsup_eq hγ, Real.rpow_def_of_pos (M.qmin_pos q x'), ← Real.exp_add]
  have e : -γ * (M.r p.1.1 p.1.2 + M.β * (-(1 / γ) * Real.log (M.qmin q.1 x'))) =
      -γ * M.r p.1.1 p.1.2 + Real.log (M.qmin q.1 x') * M.β := by
    field_simp
    ring
  rw [e, mul_comm]

/-- Each primary policy operator is a contraction of modulus `β` for the supremum norm (the
entropic certainty equivalent is nonexpansive). -/
theorem primary_contraction (σ : M.Policy) (v w : X → ℝ) :
    dist (((M.rsfdp hγ).primary (M.monotonic hγ)).T σ v)
      (((M.rsfdp hγ).primary (M.monotonic hγ)).T σ w) ≤ M.β * dist v w := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, M.primary_T hγ, M.primary_T hγ]
  set c := dist v w
  have hc : ∀ y, |v y - w y| ≤ c := fun y => by
    rw [← Real.dist_eq]
    exact dist_le_pi_dist v w y
  have key : ∀ u u' : X → ℝ, (∀ y, |u y - u' y| ≤ c) →
      Real.log (M.expSum (M.pairOf σ x) fun x' => -γ * (M.r x (σ.1 x) + M.β * u x')) ≤
        γ * (M.β * c) + Real.log (M.expSum (M.pairOf σ x)
          fun x' => -γ * (M.r x (σ.1 x) + M.β * u' x')) := fun u u' huu =>
    M.log_expSum_le _ fun x' => by
      have h1 := (abs_sub_le_iff.1 (huu x')).2
      have h2 := mul_le_mul_of_nonneg_left h1 M.β_nonneg
      nlinarith [mul_le_mul_of_nonneg_left h2 hγ.le]
  have h1 := key v w hc
  have h2 := key w v fun y => by rw [abs_sub_comm]; exact hc y
  change |-(1 / γ) * Real.log (M.expSum (M.pairOf σ x) _) -
    -(1 / γ) * Real.log (M.expSum (M.pairOf σ x) _)| ≤ _
  rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hγ), one_div,
    inv_mul_le_iff₀ hγ, abs_le]
  constructor <;> linarith

/-- §9.2.2.3 (p. 315), by Theorems 3.1.5 and 5.2.18: the fundamental optimality properties hold
for the risk-sensitive problem and the fundamental min-optimality properties for its Q-factor
problem; the min-value function `q▿*` solves (9.22); and any `σ` with
`σ(x) ∈ argmin_{a ∈ Γ(x)} q▿*(x, a)` is optimal for (9.19). -/
theorem section_9_2_2_3 :
    ∃ hw : ((M.rsfdp hγ).primary (M.monotonic hγ)).WellPosed,
    ∃ hw' : ((M.rsfdp hγ).sub (M.monotonic hγ)).WellPosed,
      ((M.rsfdp hγ).primary (M.monotonic hγ)).FundamentalOptimality hw ∧
      ((M.rsfdp hγ).sub (M.monotonic hγ)).MinFundamentalOptimality hw' ∧
      ∃ qstar, ((M.rsfdp hγ).sub (M.monotonic hγ)).IsMinValueFunction qstar ∧
        ((M.rsfdp hγ).sub (M.monotonic hγ)).SolvesMinBellman qstar ∧
        ∀ σ : M.Policy, (∀ x, ∀ a (ha : a ∈ M.Γ x), qstar.1 (M.pairOf σ x) ≤ qstar.1 ⟨(x, a), ha⟩) →
          ((M.rsfdp hγ).primary (M.monotonic hγ)).IsOptimal hw σ := by
  have hR := M.exercise_9_2_1 hγ
  have hm := M.monotonic hγ
  obtain ⟨hFO, -, -, -⟩ := ADP.theorem_3_1_5 isSupNonexpansive_pi M.β_nonneg M.β_lt_one
    (M.primary_contraction hγ) (V₀ := univ)
    ⟨isClosed_univ, fun v _ => FDP.primary_regular hm v, mapsTo_univ _ _⟩ univ_nonempty
  set hw := (ADP.isGloballyStable_of_contraction ⟨(univ_nonempty (α := X → ℝ)).some⟩
    M.β_nonneg M.β_lt_one (M.primary_contraction hγ)).wellPosed
  have hw' : ((M.rsfdp hγ).sub hm).WellPosed := ((FDP.lemma_5_2_12 hm).1).2 hw
  have h518 := FDP.theorem_5_2_18 hm hR hw hw'
  have hMFO := h518.1.1 hFO
  obtain ⟨q, hq, -, hqs, -⟩ := hMFO.2.1
  refine ⟨hw, hw', hFO, hMFO, q, hq, hqs, fun σ hσ => (h518.2 hFO).2.1 q σ hq ?_⟩
  funext x
  rw [M.Gsup_eq hγ, ← M.qmin_eq hσ x]
  rfl

/-- **Exercise 9.2.2** (p. 315): `T̂_σ = F ∘ G_σ` is a contraction of modulus `β` for
`d(q, q') = ‖ln q − ln q'‖∞`: if `|ln q − ln q'| ≤ c` then `|ln T̂_σq − ln T̂_σq'| ≤ βc`. -/
theorem exercise_9_2_2 (σ : M.Policy) (q q' : M.QPos) {c : ℝ}
    (h : ∀ p, |Real.log (q.1 p) - Real.log (q'.1 p)| ≤ c) (p : M.G) :
    |Real.log ((((M.rsfdp hγ).sub (M.monotonic hγ)).T σ q).1 p) -
      Real.log ((((M.rsfdp hγ).sub (M.monotonic hγ)).T σ q').1 p)| ≤ M.β * c := by
  have e : ∀ u : M.QPos, (((M.rsfdp hγ).sub (M.monotonic hγ)).T σ u).1 p =
      M.expSum p fun x' => -γ * M.r p.1.1 p.1.2 + M.β * Real.log (u.1 (M.pairOf σ x')) :=
    fun u => by
      change M.expSum p (fun x' => -γ * (M.r p.1.1 p.1.2 +
        M.β * (-(1 / γ) * Real.log (u.1 (M.pairOf σ x'))))) = _
      unfold expSum
      refine Finset.sum_congr rfl fun x' _ => ?_
      congr 2
      field_simp
      ring
  rw [e, e, abs_le]
  constructor
  · have := M.log_expSum_le p (e := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q'.1 (M.pairOf σ x'))) (e' := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q.1 (M.pairOf σ x'))) (d := M.β * c) fun x' => by
        have h1 := (abs_sub_le_iff.1 (h (M.pairOf σ x'))).2
        nlinarith [mul_le_mul_of_nonneg_left h1 M.β_nonneg]
    linarith
  · have := M.log_expSum_le p (e := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q.1 (M.pairOf σ x'))) (e' := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q'.1 (M.pairOf σ x'))) (d := M.β * c) fun x' => by
        have h1 := (abs_sub_le_iff.1 (h (M.pairOf σ x'))).1
        nlinarith [mul_le_mul_of_nonneg_left h1 M.β_nonneg]
    linarith

/-- Remark 9.2.1 (p. 317): each subordinate policy operator `T̂_σ` is order preserving. -/
theorem remark_9_2_1 (σ : M.Policy) :
    Monotone (((M.rsfdp hγ).sub (M.monotonic hγ)).T σ) :=
  ((M.rsfdp hγ).sub (M.monotonic hγ)).mono σ

omit hγ in
/-- The update (9.23) after observing `(x, a, R, X') = (x, a, r(x, a), x')`. -/
theorem update_9_23_pos (q : M.QPos) (p : M.G) (x' : X) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 < (1 - α) * q.1 p + α * (Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β) := by
  have h1 : 0 < Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (M.qmin_pos q x') _)
  rcases hα0.eq_or_lt with rfl | hα
  · simpa using q.2 p
  · nlinarith [q.2 p]

end FiniteMDP

end SargentStachurski.ApproximationAndLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Robbins–Monro algorithm

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.3.2–9.1.3.3 (pp. 305–306).

The Robbins–Monro iteration (9.14) is `θ_{k+1} = θ_k + α_k(Tθ_k + W_{k+1} − θ_k)`.
Theorem 9.1.8 (from Tsitsiklis, 1994) asserts almost sure convergence to the fixed point of an
order-preserving contraction `T` on `Θ ⊆ ℝⁿ` under (i) `𝔼[W_{k+1} | ℱ_k] = 0`,
(ii) `𝔼[‖W_{k+1}‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` and (iii) the Robbins–Monro conditions
`∑ α_k = ∞`, `∑ α_k² < ∞`.

We prove the theorem when `T` is a contraction of a real Hilbert space for its own norm (for
`ℝⁿ`, the Euclidean norm), with `Θ` the whole space; order preservation is then not needed.
The proof is the classical one:

* `robbins_siegmund`: a nonnegative adapted process with
  `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, `∑ a_k, ∑ b_k < ∞`, converges almost surely and
  `∑ c_k < ∞` almost surely (Robbins and Siegmund, 1971), by the martingale convergence theorem
  applied to a rescaled supermartingale;
* `robbins_monro`: `Y_k = ‖θ_k − θ̄‖²` satisfies this with `a_k = 2Cα_k²`, `b_k ∝ α_k²` and
  `c_k = (1 − β)α_kY_k`, so `Y_k → Y_∞` and `∑ α_kY_k < ∞`, which forces `Y_∞ = 0`.

The asynchronous version (Remark 9.1.3) and contractions for the supremum norm (as in the
asset pricing and Q-learning applications) are not covered.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ApproximationAndLearning

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- **Robbins–Siegmund lemma**: if `Y, c ≥ 0` are adapted and integrable, `a, b ≥ 0` are summable
and `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, then almost surely `Y_k` converges and
`∑ c_k < ∞`. -/
theorem robbins_siegmund {Y c : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hY : StronglyAdapted ℱ Y) (hc : StronglyAdapted ℱ c)
    (hYi : ∀ k, Integrable (Y k) P) (hci : ∀ k, Integrable (c k) P)
    (hY0 : ∀ k ω, 0 ≤ Y k ω) (hc0 : ∀ k ω, 0 ≤ c k ω) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hsa : Summable a) (hsb : Summable b)
    (hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω) :
    ∀ᵐ ω ∂P, (∃ L, Tendsto (fun k => Y k ω) atTop (𝓝 L)) ∧ Summable fun k => c k ω := by
  -- the products `π_k = ∏_{j<k} (1 + a_j)`
  set π : ℕ → ℝ := fun k => ∏ j ∈ Finset.range k, (1 + a j) with hπdef
  have hπsucc : ∀ k, π (k + 1) = π k * (1 + a k) := fun k => Finset.prod_range_succ _ _
  have hπ1 : ∀ k, 1 ≤ π k := by
    intro k
    induction k with
    | zero => simp [hπdef]
    | succ k ih =>
      rw [hπsucc]
      nlinarith [ha k]
  have hπpos : ∀ k, 0 < π k := fun k => one_pos.trans_le (hπ1 k)
  have hπmono : Monotone π := monotone_nat_of_le_succ fun k => by
    rw [hπsucc]
    nlinarith [ha k, hπ1 k]
  have hπbdd : ∀ k, π k ≤ Real.exp (∑' j, a j) := by
    have h : ∀ k, π k ≤ Real.exp (∑ j ∈ Finset.range k, a j) := by
      intro k
      induction k with
      | zero => simp [hπdef]
      | succ k ih =>
        rw [hπsucc, Finset.sum_range_succ, Real.exp_add]
        have h1 : 1 + a k ≤ Real.exp (a k) := by linarith [Real.add_one_le_exp (a k)]
        exact mul_le_mul ih h1 (by linarith [ha k]) (Real.exp_pos _).le
    exact fun k => (h k).trans (Real.exp_le_exp.2 (hsa.sum_le_tsum _ fun j _ => ha j))
  -- partial sums
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, c j ω with hSdef
  set Bs : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, b j / π (j + 1) with hBsdef
  have hSm : ∀ k i, k ≤ i → StronglyMeasurable[ℱ i] (S k) := fun k i hki => by
    have h := Finset.stronglyMeasurable_sum (f := c) (Finset.range k) fun j hj =>
      (hc j).mono (ℱ.mono (show j ≤ i by have := Finset.mem_range.1 hj; omega))
    convert h using 1
    funext ω
    simp [hSdef, Finset.sum_apply]
  have hSm' : ∀ k, StronglyMeasurable[ℱ k] (S (k + 1)) := fun k => by
    have h := Finset.stronglyMeasurable_sum (f := c) (Finset.range (k + 1)) fun j hj =>
      (hc j).mono (ℱ.mono (show j ≤ k by have := Finset.mem_range.1 hj; omega))
    convert h using 1
    funext ω
    simp [hSdef, Finset.sum_apply]
  have hSi : ∀ k, Integrable (S k) P := fun k => integrable_finsetSum _ fun j _ => hci j
  have hS0 : ∀ k ω, 0 ≤ S k ω := fun k ω => Finset.sum_nonneg fun j _ => hc0 j ω
  set Btot := ∑' j, b j
  have hB0 : 0 ≤ Btot := tsum_nonneg hb
  have hBs : ∀ k, Bs k ≤ Btot := fun k =>
    (Finset.sum_le_sum fun j _ => div_le_self (hb j) (hπ1 (j + 1))).trans
      (hsb.sum_le_tsum _ fun j _ => hb j)
  -- the supermartingale `Z_k = π_k⁻¹(Y_k + S_k) − B_k`
  set Z : ℕ → Ω → ℝ := fun k ω => (π k)⁻¹ * (Y k ω + S k ω) - Bs k with hZdef
  have hZad : StronglyAdapted ℱ Z := fun k =>
    (stronglyMeasurable_const.mul ((hY k).add (hSm k k le_rfl))).sub stronglyMeasurable_const
  have hZi : ∀ k, Integrable (Z k) P := fun k =>
    (((hYi k).add (hSi k)).const_mul _).sub (integrable_const _)
  have hsup : Supermartingale Z ℱ P := supermartingale_nat hZad hZi fun k => by
    set R : Ω → ℝ := fun ω => (π (k + 1))⁻¹ * S (k + 1) ω - Bs (k + 1)
    have hRm : StronglyMeasurable[ℱ k] R :=
      (stronglyMeasurable_const.mul (hSm' k)).sub stronglyMeasurable_const
    have hRi : Integrable R P := ((hSi (k + 1)).const_mul _).sub (integrable_const _)
    have hsplit : Z (k + 1) = (π (k + 1))⁻¹ • Y (k + 1) + R := by
      funext ω
      simp only [hZdef, R, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit]
    filter_upwards [condExp_add ((hYi (k + 1)).smul ((π (k + 1))⁻¹)) hRi (ℱ k),
      condExp_smul ((π (k + 1))⁻¹) (Y (k + 1)) (ℱ k), hstep k] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable (ℱ.le k) hRm hRi, Pi.smul_apply,
      smul_eq_mul]
    have hpk := hπpos k
    have ha1 : 0 < 1 + a k := by linarith [ha k]
    have hS1 : S (k + 1) ω = S k ω + c k ω := Finset.sum_range_succ _ _
    have hB1 : Bs (k + 1) = Bs k + b k / π (k + 1) := Finset.sum_range_succ _ _
    have hinv : (π (k + 1))⁻¹ * (1 + a k) = (π k)⁻¹ := by
      rw [hπsucc]
      field_simp
    have hinvle : (π (k + 1))⁻¹ ≤ (π k)⁻¹ := inv_anti₀ hpk (hπmono (Nat.le_succ k))
    simp only [R, hS1, hB1, hZdef]
    calc (π (k + 1))⁻¹ * P[Y (k + 1)|ℱ k] ω +
          ((π (k + 1))⁻¹ * (S k ω + c k ω) - (Bs k + b k / π (k + 1)))
        ≤ (π (k + 1))⁻¹ * ((1 + a k) * Y k ω + b k - c k ω) +
          ((π (k + 1))⁻¹ * (S k ω + c k ω) - (Bs k + b k / π (k + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (hπpos _).le)) le_rfl
      _ = (π (k + 1))⁻¹ * (1 + a k) * Y k ω + (π (k + 1))⁻¹ * S k ω - Bs k := by ring
      _ ≤ (π k)⁻¹ * (Y k ω + S k ω) - Bs k := by
          rw [hinv]
          nlinarith [mul_le_mul_of_nonneg_right hinvle (hS0 k ω)]
  -- `L¹` bound
  have hZlow : ∀ k ω, -Btot ≤ Z k ω := fun k ω => by
    have := mul_nonneg (inv_nonneg.2 (hπpos k).le) (add_nonneg (hY0 k ω) (hS0 k ω))
    simp only [hZdef]
    linarith [hBs k]
  have hint : ∀ k, ∫ ω, Z k ω ∂P ≤ ∫ ω, Z 0 ω ∂P := fun k => by
    have := hsup.setIntegral_le (Nat.zero_le k) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this
  have hbdd : ∀ k, eLpNorm ((-Z) k) 1 P ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂P + 2 * Btot) := by
    intro k
    rw [Pi.neg_apply, eLpNorm_neg, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hZi k)]
    · refine ENNReal.ofReal_le_ofReal ?_
      calc ∫ ω, ‖Z k ω‖ ∂P ≤ ∫ ω, (Z k ω + 2 * Btot) ∂P := integral_mono (hZi k).norm
            ((hZi k).add (integrable_const _)) fun ω => by
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hZlow k ω]
        _ = ∫ ω, Z k ω ∂P + 2 * Btot := by
            rw [integral_add (hZi k) (integrable_const _)]
            simp
        _ ≤ _ := by linarith [hint k]
    · exact (hZi k).aestronglyMeasurable
  have hconv := hsup.neg.ae_tendsto_limitProcess hbdd
  -- the deterministic limits
  have hπlim : ∃ l, Tendsto π atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciSup hπmono ⟨_, by rintro _ ⟨k, rfl⟩; exact hπbdd k⟩⟩
  obtain ⟨πl, hπl⟩ := hπlim
  have hsB : Summable fun j => b j / π (j + 1) :=
    Summable.of_nonneg_of_le (fun j => div_nonneg (hb j) (hπpos _).le)
      (fun j => div_le_self (hb j) (hπ1 (j + 1))) hsb
  have hBlim : Tendsto Bs atTop (𝓝 (∑' j, b j / π (j + 1))) := hsB.hasSum.tendsto_sum_nat
  filter_upwards [hconv] with ω hω
  have hZω : Tendsto (fun k => Z k ω) atTop (𝓝 (-ℱ.limitProcess (-Z) P ω)) := by
    have := hω.neg
    simpa using this
  -- `W_k = Y_k + S_k = π_k(Z_k + B_k)` converges
  have hW : Tendsto (fun k => Y k ω + S k ω) atTop
      (𝓝 (πl * (-ℱ.limitProcess (-Z) P ω + ∑' j, b j / π (j + 1)))) := by
    have e : (fun k => Y k ω + S k ω) = fun k => π k * (Z k ω + Bs k) := funext fun k => by
      simp only [hZdef]
      field_simp [(hπpos k).ne']
      ring
    rw [e]
    exact hπl.mul (hZω.add hBlim)
  obtain ⟨M, hM⟩ := hW.bddAbove_range
  have hcs : Summable fun k => c k ω :=
    summable_of_sum_range_le (fun k => hc0 k ω) fun n =>
      le_trans (le_add_of_nonneg_left (hY0 n ω)) (hM ⟨n, rfl⟩)
  have hSlim : Tendsto (fun k => S k ω) atTop (𝓝 (∑' j, c j ω)) := hcs.hasSum.tendsto_sum_nat
  have hYlim : Tendsto (fun k => Y k ω) atTop
      (𝓝 (πl * (-ℱ.limitProcess (-Z) P ω + ∑' j, b j / π (j + 1)) - ∑' j, c j ω)) := by
    have := hW.sub hSlim
    simpa using this
  exact ⟨⟨_, hYlim⟩, hcs⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Theorem 9.1.8** (p. 306) for contractions of a real Hilbert space: let `T` be a contraction
of modulus `β < 1` with fixed point `θ̄`, and let `θ_{k+1} = θ_k + α_k(Tθ_k + W_{k+1} − θ_k)`
(9.14) with `θ₀` and the `W_k` square integrable and adapted. If (i) `𝔼[W_{k+1} | ℱ_k] = 0`,
(ii) `𝔼[‖W_{k+1}‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` and (iii) `α_k ∈ [0, 1]`, `∑ α_k = ∞`,
`∑ α_k² < ∞`, then `θ_k → θ̄` almost surely. -/
theorem robbins_monro {T : E → E} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ β * ‖x - y‖) {θbar : E} (hfix : T θbar = θbar)
    {α : ℕ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∀ k, α k ≤ 1) (hdiv : ¬ Summable α)
    (hsq : Summable fun k => α k ^ 2) {θ W : ℕ → Ω → E}
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (T (θ k ω) + W (k + 1) ω - θ k ω))
    (hθ0m : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0 : MemLp (θ 0) 2 P)
    (hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W (k + 1))) (hW2 : ∀ k, MemLp (W (k + 1)) 2 P)
    (hW0 : ∀ k, P[W (k + 1) | ℱ k] =ᵐ[P] 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, P[fun ω => ‖W (k + 1) ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  have hTc : Continuous T := (LipschitzWith.of_dist_le_mul (K := ⟨β, hβ0⟩) fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hT x y).continuous
  have hTb : ∀ x, ‖T x‖ ≤ ‖T 0‖ + β * ‖x‖ := fun x => by
    have := hT x 0
    rw [sub_zero] at this
    linarith [norm_le_norm_add_norm_sub' (T x) (T 0), norm_sub_rev (T x) (T 0)]
  -- adaptedness and square integrability of the iterates
  have hθ : ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 P := by
    intro k
    induction k with
    | zero => exact ⟨hθ0m, hθ0⟩
    | succ k ih =>
      obtain ⟨hm, hL⟩ := ih
      have he : θ (k + 1) = fun ω => θ k ω + α k • (T (θ k ω) + W (k + 1) ω - θ k ω) :=
        funext (hrec k)
      have hm' : StronglyMeasurable[ℱ (k + 1)] (θ k) := hm.mono (ℱ.mono k.le_succ)
      have hTm : StronglyMeasurable[ℱ (k + 1)] fun ω => T (θ k ω) :=
        hTc.comp_stronglyMeasurable hm'
      have hTL : MemLp (fun ω => T (θ k ω)) 2 P :=
        ((memLp_const ‖T 0‖).add (hL.norm.const_mul β)).mono'
          (hTc.comp_aestronglyMeasurable hL.aestronglyMeasurable) (Eventually.of_forall fun ω => by
            simp only [Pi.add_apply]
            exact hTb _)
      rw [he]
      exact ⟨hm'.add (((hTm.add (hWm k)).sub hm').const_smul (α k)),
        hL.add (((hTL.add (hW2 k)).sub hL).const_smul (α k))⟩
  -- `Y_k = ‖θ_k − θ̄‖²`
  set Y : ℕ → Ω → ℝ := fun k ω => ‖θ k ω - θbar‖ ^ 2 with hYdef
  have hYm : StronglyAdapted ℱ Y := fun k =>
    ((hθ k).1.sub stronglyMeasurable_const).norm.pow 2
  have hYi : ∀ k, Integrable (Y k) P := fun k =>
    (memLp_two_iff_integrable_sq_norm
      ((hθ k).2.sub (memLp_const θbar)).aestronglyMeasurable).1
      ((hθ k).2.sub (memLp_const θbar))
  have hY0 : ∀ k ω, 0 ≤ Y k ω := fun k ω => sq_nonneg _
  set c : ℕ → Ω → ℝ := fun k ω => (1 - β) * α k * Y k ω with hcdef
  set a : ℕ → ℝ := fun k => 2 * C * α k ^ 2
  set b : ℕ → ℝ := fun k => C * (1 + 2 * ‖θbar‖ ^ 2) * α k ^ 2
  have hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω := by
    intro k
    set u : Ω → E := fun ω => θ k ω - θbar + α k • (T (θ k ω) - θ k ω)
    have hum : StronglyMeasurable[ℱ k] u :=
      ((hθ k).1.sub stronglyMeasurable_const).add
        (((hTc.comp_stronglyMeasurable (hθ k).1).sub (hθ k).1).const_smul (α k))
    have huL : MemLp u 2 P := by
      have hTL : MemLp (fun ω => T (θ k ω)) 2 P :=
        ((memLp_const ‖T 0‖).add ((hθ k).2.norm.const_mul β)).mono'
          (hTc.comp_aestronglyMeasurable (hθ k).2.aestronglyMeasurable)
          (Eventually.of_forall fun ω => by
            simp only [Pi.add_apply]
            exact hTb _)
      exact ((hθ k).2.sub (memLp_const θbar)).add ((hTL.sub (hθ k).2).const_smul (α k))
    have hsplit : ∀ ω, θ (k + 1) ω - θbar = u ω + α k • W (k + 1) ω := fun ω => by
      rw [hrec]
      simp only [u, smul_sub, smul_add]
      abel
    -- the three pieces of `Y_{k+1}`
    set U : Ω → ℝ := fun ω => ‖u ω‖ ^ 2
    set I : Ω → ℝ := fun ω => innerSL ℝ (u ω) (W (k + 1) ω)
    set N : Ω → ℝ := fun ω => ‖W (k + 1) ω‖ ^ 2
    have hYsplit : Y (k + 1) = U + (2 * α k) • I + (α k ^ 2) • N := by
      funext ω
      simp only [hYdef, U, I, N, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsplit,
        innerSL_apply_apply]
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hUi : Integrable U P := (memLp_two_iff_integrable_sq_norm huL.aestronglyMeasurable).1 huL
    have hNi : Integrable N P := (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1
      (hW2 k)
    have hIi : Integrable I P := by
      refine (hUi.add hNi).mono' ?_ (Eventually.of_forall fun ω => ?_)
      · exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂.comp_aestronglyMeasurable₂
          huL.aestronglyMeasurable (hW2 k).aestronglyMeasurable)
      · simp only [I, Pi.add_apply, U, N, innerSL_apply_apply, Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        nlinarith [sq_nonneg (‖u ω‖ - ‖W (k + 1) ω‖), norm_nonneg (u ω),
          norm_nonneg (W (k + 1) ω)]
    have hUm : StronglyMeasurable[ℱ k] U := hum.norm.pow 2
    have hcI : P[I | ℱ k] =ᵐ[P] 0 := by
      have h1 := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
        hum.aestronglyMeasurable hIi ((hW2 k).integrable one_le_two)
      filter_upwards [h1, hW0 k] with ω h1 h2
      rw [h1, h2]
      simp
    rw [hYsplit]
    have hsum := condExp_add (hUi.add (hIi.smul (2 * α k))) (hNi.smul (α k ^ 2)) (ℱ k)
    have hsum2 := condExp_add hUi (hIi.smul (2 * α k)) (ℱ k)
    have hs1 := condExp_smul (μ := P) (2 * α k) I (ℱ k)
    have hs2 := condExp_smul (μ := P) (α k ^ 2) N (ℱ k)
    have hU := condExp_of_stronglyMeasurable (ℱ.le k) hUm hUi
    filter_upwards [hsum, hsum2, hs1, hs2, hcI, hC k] with ω e1 e2 e3 e4 e5 e6
    have e6' : P[N | ℱ k] ω ≤ C * (1 + ‖θ k ω‖ ^ 2) := e6
    rw [e1, Pi.add_apply, e2, Pi.add_apply, hU, e3, e4, Pi.smul_apply, Pi.smul_apply, e5,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    -- `‖u‖ ≤ (1 − α(1 − β))‖θ_k − θ̄‖`
    have hq0 : 0 ≤ 1 - α k * (1 - β) := by nlinarith [hα1 k, hα0 k]
    have hq1 : 1 - α k * (1 - β) ≤ 1 := by nlinarith [hα0 k]
    have hu : ‖u ω‖ ≤ (1 - α k * (1 - β)) * ‖θ k ω - θbar‖ := by
      have e : u ω = (1 - α k) • (θ k ω - θbar) + α k • (T (θ k ω) - T θbar) := by
        rw [hfix]
        simp only [u, smul_sub, sub_smul, one_smul]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hα1 k]),
        Real.norm_of_nonneg (hα0 k)]
      nlinarith [mul_le_mul_of_nonneg_left (hT (θ k ω) θbar) (hα0 k),
        norm_nonneg (θ k ω - θbar)]
    have hU' : U ω ≤ (1 - α k * (1 - β)) * Y k ω := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      simp only [U, hYdef]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hq0 hq1)
        (sq_nonneg ‖θ k ω - θbar‖), sq_nonneg (1 - α k * (1 - β))]
    have hθsq : ‖θ k ω‖ ^ 2 ≤ 2 * Y k ω + 2 * ‖θbar‖ ^ 2 := by
      have h1 : ‖θ k ω‖ ≤ ‖θ k ω - θbar‖ + ‖θbar‖ := by
        have := norm_add_le (θ k ω - θbar) θbar
        rwa [sub_add_cancel] at this
      simp only [hYdef]
      nlinarith [sq_nonneg (‖θ k ω - θbar‖ - ‖θbar‖), norm_nonneg (θ k ω),
        norm_nonneg (θ k ω - θbar), norm_nonneg θbar]
    simp only [a, b, hcdef]
    nlinarith [mul_le_mul_of_nonneg_left e6' (sq_nonneg (α k)),
      mul_le_mul_of_nonneg_left hθsq (mul_nonneg (sq_nonneg (α k)) hC0)]
  -- Robbins–Siegmund
  have hcad : StronglyAdapted ℱ c := fun k => stronglyMeasurable_const.mul (hYm k)
  have hci : ∀ k, Integrable (c k) P := fun k => (hYi k).const_mul _
  have hc0 : ∀ k ω, 0 ≤ c k ω := fun k ω =>
    mul_nonneg (mul_nonneg (sub_nonneg.2 hβ1.le) (hα0 k)) (hY0 k ω)
  have ha : ∀ k, 0 ≤ a k := fun k => mul_nonneg (mul_nonneg zero_le_two hC0) (sq_nonneg _)
  have hb : ∀ k, 0 ≤ b k := fun k =>
    mul_nonneg (mul_nonneg hC0 (by positivity)) (sq_nonneg _)
  have hRS := robbins_siegmund hYm hcad hYi hci hY0 hc0 ha hb (hsq.mul_left (2 * C))
    (hsq.mul_left _) hstep
  filter_upwards [hRS] with ω hω
  obtain ⟨⟨L, hL⟩, hcs⟩ := hω
  have hL0 : L = 0 := by
    have hLnn : 0 ≤ L := ge_of_tendsto' hL fun k => hY0 k ω
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
    have hev : ∀ᶠ k in atTop, L / 2 < Y k ω := hL.eventually (lt_mem_nhds (half_lt_self hLpos))
    have h1b : 0 < 1 - β := sub_pos.2 hβ1
    apply hdiv
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (2 / ((1 - β) * L))) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hα0 k), div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos h1b hLpos)]
    simp only [hcdef]
    nlinarith [mul_le_mul_of_nonneg_left hk.le (mul_nonneg h1b.le (hα0 k))]
  rw [hL0] at hL
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun k => ‖θ k ω - θbar‖) = fun k => Real.sqrt (Y k ω) :=
    funext fun k => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [e]
  have h := (Real.continuous_sqrt.tendsto 0).comp hL
  rw [Real.sqrt_zero] at h
  exact h

end SargentStachurski.ApproximationAndLearning

set_option linter.style.longLine false
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.mk
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.nonneg
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.rowsum
#print axioms SargentStachurski.ApproximationAndLearning.IsDistribution
#print axioms SargentStachurski.ApproximationAndLearning.IsDistribution.mk
#print axioms SargentStachurski.ApproximationAndLearning.IsDistribution.nonneg
#print axioms SargentStachurski.ApproximationAndLearning.IsDistribution.sum_eq_one
#print axioms SargentStachurski.ApproximationAndLearning.mulVec_apply_eq
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.mul
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.pow
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.mulVec_const
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.ApproximationAndLearning.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.ApproximationAndLearning.GloballyStable
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.mk
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.mapsTo
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.nonneg
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.lt_one
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.iterate_mem
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.ApproximationAndLearning.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.ApproximationAndLearning.fixedPt_le_of_le
#print axioms SargentStachurski.ApproximationAndLearning.le_fixedPt_of_le_apply
#print axioms SargentStachurski.ApproximationAndLearning.isContractionOn_of_blackwell
#print axioms SargentStachurski.ApproximationAndLearning.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.ApproximationAndLearning.IsBdd
#print axioms SargentStachurski.ApproximationAndLearning.IsSupContraction
#print axioms SargentStachurski.ApproximationAndLearning.IsUniformlyClosed
#print axioms SargentStachurski.ApproximationAndLearning.isBdd_const
#print axioms SargentStachurski.ApproximationAndLearning.IsBdd.sub
#print axioms SargentStachurski.ApproximationAndLearning.IsBdd.add
#print axioms SargentStachurski.ApproximationAndLearning.IsBdd.nonneg_bound
#print axioms SargentStachurski.ApproximationAndLearning.IsBdd.exists_dist
#print axioms SargentStachurski.ApproximationAndLearning.IsSupContraction.iterate
#print axioms SargentStachurski.ApproximationAndLearning.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.ApproximationAndLearning.IsSupContraction.exists_limit
#print axioms SargentStachurski.ApproximationAndLearning.IsSupContraction.globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.le_of_le_map_of_tendsto
#print axioms SargentStachurski.ApproximationAndLearning.le_of_map_le_of_tendsto
#print axioms SargentStachurski.ApproximationAndLearning.bX
#print axioms SargentStachurski.ApproximationAndLearning.isUniformlyClosed_bX
#print axioms SargentStachurski.ApproximationAndLearning.const_mem_bX
#print axioms SargentStachurski.ApproximationAndLearning.abs_max_sub_max_le
#print axioms SargentStachurski.ApproximationAndLearning.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.mk
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.V
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.T
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.β
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.β_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.β_lt_one
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.nonempty
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bdd
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.closed
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.mapsTo
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.mono
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.contraction
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.exists_greedy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_mem
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.T_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.eq_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.le_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_le
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.IsGreedy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.nonempty_policy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.greedy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.T_le_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_mono
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_contraction
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vstar
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vstar_mem
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.bellman_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.eq_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.IsOptimal
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.optimality
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.hpiPolicy
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.hpi_terminates
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.opi
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.opi_step
#print axioms SargentStachurski.ApproximationAndLearning.ContractingDP.tendsto_opi
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.mk
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Γ
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Γ_nonempty
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.r
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.β
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.β_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.β_lt_one
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.P
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.P_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.P_sum
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Policy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Q
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Tσ
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.isBdd_of_finite
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_sum_sub_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Q_mono
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_Q_sub_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Q_sub_const
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exists_greedy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.toDP
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.IsGreedy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.isGreedy_iff
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.bellman_eq
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.bellman_contraction
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Pσ
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.rσ
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Tσ_eq_mulVec
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_Pσ_mulVec_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.vσ_eq_inv
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.vσ_hasSum
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_vσ_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.finite_policy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.theorem_1_2_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.theorem_1_2_2
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.vstar_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.IsLPFeasible
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.lp_solution
#print axioms SargentStachurski.ApproximationAndLearning.OrderStable
#print axioms SargentStachurski.ApproximationAndLearning.IncreasesTo
#print axioms SargentStachurski.ApproximationAndLearning.DecreasesTo
#print axioms SargentStachurski.ApproximationAndLearning.StronglyOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.orderStable_of_up_down
#print axioms SargentStachurski.ApproximationAndLearning.StronglyOrderStable.orderStable
#print axioms SargentStachurski.ApproximationAndLearning.dualMap
#print axioms SargentStachurski.ApproximationAndLearning.orderStable_dual_iff
#print axioms SargentStachurski.ApproximationAndLearning.dualMap_iterate
#print axioms SargentStachurski.ApproximationAndLearning.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete.exists_least
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.ApproximationAndLearning.ChainComplete.orderStable
#print axioms SargentStachurski.ApproximationAndLearning.chainComplete_Icc
#print axioms SargentStachurski.ApproximationAndLearning.CountablyDedekindComplete
#print axioms SargentStachurski.ApproximationAndLearning.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.ApproximationAndLearning.CountablyDedekindComplete.dual
#print axioms SargentStachurski.ApproximationAndLearning.OrderContinuous
#print axioms SargentStachurski.ApproximationAndLearning.OrderContinuous.monotone
#print axioms SargentStachurski.ApproximationAndLearning.isLUB_range_succ_iff
#print axioms SargentStachurski.ApproximationAndLearning.tarski_kantorovich
#print axioms SargentStachurski.ApproximationAndLearning.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP
#print axioms SargentStachurski.ApproximationAndLearning.ADP.mk
#print axioms SargentStachurski.ApproximationAndLearning.ADP.T
#print axioms SargentStachurski.ApproximationAndLearning.ADP.mono
#print axioms SargentStachurski.ApproximationAndLearning.ADP.nonempty
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGreedy
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VG
#print axioms SargentStachurski.ApproximationAndLearning.ADP.WellPosed
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsFinite
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Regular
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsBellmanValue
#print axioms SargentStachurski.ApproximationAndLearning.ADP.SolvesBellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.ApproximationAndLearning.ADP.regular_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.greedy
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isGreedy_greedy
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.T_le_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isGreedy_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.ApproximationAndLearning.ADP.solvesBellman_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman_mono
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VU
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VSig
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.ApproximationAndLearning.ADP.vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.T_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.eq_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VSig_eq_range
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOptimal
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.BellmanPrinciple
#print axioms SargentStachurski.ApproximationAndLearning.ADP.FundamentalOptimality
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isOptimal_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.ApproximationAndLearning.ADP.exists_solves_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.ApproximationAndLearning.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsSelector
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.ApproximationAndLearning.ADP.howard
#print axioms SargentStachurski.ApproximationAndLearning.ADP.opt
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsSelector.T_eq
#print axioms SargentStachurski.ApproximationAndLearning.ADP.mem_VU_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.ApproximationAndLearning.ADP.iterate_mono_of_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman_le_opt
#print axioms SargentStachurski.ApproximationAndLearning.ADP.chain_2_9
#print axioms SargentStachurski.ApproximationAndLearning.ADP.mapsTo_VU
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman_le_of_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VFIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.OPIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.HPIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.opt_one
#print axioms SargentStachurski.ApproximationAndLearning.ADP.OPIConverges.vfi
#print axioms SargentStachurski.ApproximationAndLearning.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.iterates_le_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VU_nonempty
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.ApproximationAndLearning.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.ApproximationAndLearning.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.ApproximationAndLearning.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.ApproximationAndLearning.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.ApproximationAndLearning.ADP.OrderBounded
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderContinuous
#print axioms SargentStachurski.ApproximationAndLearning.ADP.le_of_orderBounded
#print axioms SargentStachurski.ApproximationAndLearning.ADP.convergence_of_dedekind
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_dual
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsMinGreedy
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VGmin
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinRegular
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinOrderBounded
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsMinBellmanValue
#print axioms SargentStachurski.ApproximationAndLearning.ADP.SolvesMinBellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsMinValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsMinOptimal
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinBellmanPrinciple
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinFundamentalOptimality
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isMinGreedy_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minRegular_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minOrderBounded_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isMinBellmanValue_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VGmin_eq
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_VSig
#print axioms SargentStachurski.ApproximationAndLearning.ADP.WellPosed.dual
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isMinValueFunction_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isMinOptimal_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_opt_howard
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minBellmanPrinciple_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minFundamentalOptimality_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VD
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinVFIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minVFIConverges_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsOrderStable.minFundamentalOptimality
#print axioms SargentStachurski.ApproximationAndLearning.isLUB_of_tendsto_subtype
#print axioms SargentStachurski.ApproximationAndLearning.isGLB_of_tendsto_subtype
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.nonempty_policy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_wellPosed
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_isOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_isOrderContinuous
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.rbar
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_r_le_rbar
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_orderBounded
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_2_3_7
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_regular
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_bellman_apply
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.proposition_2_3_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Vhat
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.mem_Vhat_iff
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Tσ_mapsTo_Vhat
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adpHat
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.vσ_mem_Vhat
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adpHat_isStronglyOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adpHat_regular
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_2_3_10
#print axioms SargentStachurski.ApproximationAndLearning.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.ApproximationAndLearning.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_2
#print axioms SargentStachurski.ApproximationAndLearning.ADP.corollary_3_1_3
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_4
#print axioms SargentStachurski.ApproximationAndLearning.IsSupNonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.IsInfNonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.isInfNonexpansive_iff
#print axioms SargentStachurski.ApproximationAndLearning.isSupNonexpansive_real
#print axioms SargentStachurski.ApproximationAndLearning.isSupNonexpansive_pi
#print axioms SargentStachurski.ApproximationAndLearning.ADP.lemma_A_5_21
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsSemiRegular
#print axioms SargentStachurski.ApproximationAndLearning.ADP.VFIGeometric
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_5
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsMinSelector
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinOPIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.MinHPIConverges
#print axioms SargentStachurski.ApproximationAndLearning.ADP.isMinSelector_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_opt_iterate
#print axioms SargentStachurski.ApproximationAndLearning.ADP.dual_howard_iterate
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minOPIConverges_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.minHPIConverges_iff
#print axioms SargentStachurski.ApproximationAndLearning.ADP.min_of_dual
#print axioms SargentStachurski.ApproximationAndLearning.ADP.IsGloballyStable.dual
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_6
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_8
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_3_1_7
#print axioms SargentStachurski.ApproximationAndLearning.vShapeOrder
#print axioms SargentStachurski.ApproximationAndLearning.vShapeDist
#print axioms SargentStachurski.ApproximationAndLearning.vShapeDist_metric
#print axioms SargentStachurski.ApproximationAndLearning.vShape_isLUB
#print axioms SargentStachurski.ApproximationAndLearning.vShape_sup_not_inf
#print axioms SargentStachurski.ApproximationAndLearning.BM
#print axioms SargentStachurski.ApproximationAndLearning.BM.mk
#print axioms SargentStachurski.ApproximationAndLearning.BM.toFun
#print axioms SargentStachurski.ApproximationAndLearning.BM.measurable'
#print axioms SargentStachurski.ApproximationAndLearning.BM.bdd'
#print axioms SargentStachurski.ApproximationAndLearning.BM.ext
#print axioms SargentStachurski.ApproximationAndLearning.BM.bddAbove
#print axioms SargentStachurski.ApproximationAndLearning.BM.const
#print axioms SargentStachurski.ApproximationAndLearning.BM.toFun_injective
#print axioms SargentStachurski.ApproximationAndLearning.BM.zero
#print axioms SargentStachurski.ApproximationAndLearning.BM.add
#print axioms SargentStachurski.ApproximationAndLearning.BM.neg
#print axioms SargentStachurski.ApproximationAndLearning.BM.sub
#print axioms SargentStachurski.ApproximationAndLearning.BM.smulReal
#print axioms SargentStachurski.ApproximationAndLearning.BM.nsmul
#print axioms SargentStachurski.ApproximationAndLearning.BM.zsmul
#print axioms SargentStachurski.ApproximationAndLearning.BM.addCommGroup
#print axioms SargentStachurski.ApproximationAndLearning.BM.supNorm
#print axioms SargentStachurski.ApproximationAndLearning.BM.abs_le_supNorm
#print axioms SargentStachurski.ApproximationAndLearning.BM.supNorm_le
#print axioms SargentStachurski.ApproximationAndLearning.BM.supNorm_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.BM.normedAddCommGroup
#print axioms SargentStachurski.ApproximationAndLearning.BM.add_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.sub_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.neg_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.zero_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.const_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.norm_def
#print axioms SargentStachurski.ApproximationAndLearning.BM.abs_le_norm
#print axioms SargentStachurski.ApproximationAndLearning.BM.norm_le
#print axioms SargentStachurski.ApproximationAndLearning.BM.abs_sub_le_dist
#print axioms SargentStachurski.ApproximationAndLearning.BM.dist_le
#print axioms SargentStachurski.ApproximationAndLearning.BM.module
#print axioms SargentStachurski.ApproximationAndLearning.BM.smul_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.normedSpace
#print axioms SargentStachurski.ApproximationAndLearning.BM.lattice
#print axioms SargentStachurski.ApproximationAndLearning.BM.le_def
#print axioms SargentStachurski.ApproximationAndLearning.BM.sup_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.inf_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.abs_apply
#print axioms SargentStachurski.ApproximationAndLearning.BM.isOrderedAddMonoid
#print axioms SargentStachurski.ApproximationAndLearning.BM.hasSolidNorm
#print axioms SargentStachurski.ApproximationAndLearning.BM.completeSpace
#print axioms SargentStachurski.ApproximationAndLearning.BM.countablyDedekindComplete
#print axioms SargentStachurski.ApproximationAndLearning.BM.isSupNonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.BM.isInfNonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.BM.mem_bX
#print axioms SargentStachurski.ApproximationAndLearning.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.ApproximationAndLearning.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.ApproximationAndLearning.BM.globallyStable_of_bX
#print axioms SargentStachurski.ApproximationAndLearning.globallyStable_of_supContraction
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.adp_isGloballyStable
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.section_3_2_1_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.G
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.finite_G
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.pairOf
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Sσ
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Sσ_mono
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qadp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_3_2_3
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_3_2_3_converse
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exists_qgreedy
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qadp_regular
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_3_2_4
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_3_2_5
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qadp_isGloballyStable
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_3_2_6
#print axioms SargentStachurski.ApproximationAndLearning.exercise_3_2_3_converse_fails
#print axioms SargentStachurski.ApproximationAndLearning.IsUniqueFixed
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate.symm
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate.iterate
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate.fixed_iff
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate.fixed_iff_symm
#print axioms SargentStachurski.ApproximationAndLearning.IsConjugate.isUniqueFixed_iff
#print axioms SargentStachurski.ApproximationAndLearning.example_5_1_1
#print axioms SargentStachurski.ApproximationAndLearning.coordChange
#print axioms SargentStachurski.ApproximationAndLearning.example_5_1_2
#print axioms SargentStachurski.ApproximationAndLearning.IsTopConjugate
#print axioms SargentStachurski.ApproximationAndLearning.IsTopConjugate.symm
#print axioms SargentStachurski.ApproximationAndLearning.IsTopConjugate.globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.proposition_5_1_2
#print axioms SargentStachurski.ApproximationAndLearning.coordHomeo
#print axioms SargentStachurski.ApproximationAndLearning.iterate_diagonal_mulVec
#print axioms SargentStachurski.ApproximationAndLearning.globallyStable_diagonal_iff
#print axioms SargentStachurski.ApproximationAndLearning.example_5_1_3
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate
#print axioms SargentStachurski.ApproximationAndLearning.orderIso_increasesTo
#print axioms SargentStachurski.ApproximationAndLearning.orderIso_decreasesTo
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.refl
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.symm
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.trans
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.orderStable
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.stronglyOrderStable
#print axioms SargentStachurski.ApproximationAndLearning.IsOrderConjugate.lemma_5_1_3
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj
#print axioms SargentStachurski.ApproximationAndLearning.OrderContinuousDown
#print axioms SargentStachurski.ApproximationAndLearning.AntiContinuousUp
#print axioms SargentStachurski.ApproximationAndLearning.AntiContinuousDown
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.swap
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.exercise_5_2_1
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.iterate_succ
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.fixed_F
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.fixed_G
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.isUniqueFixed
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.existsUnique_iff
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.orderStable_mono
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.orderStable_anti
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.lemma_5_2_2_i
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.increasesTo_of_succ
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.decreasesTo_of_succ
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.stronglyOrderStable_mono
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.stronglyOrderStable_anti
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.lemma_5_2_2_ii
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.theorem_5_2_3
#print axioms SargentStachurski.ApproximationAndLearning.IsStronglySemiconj.theorem_5_2_4
#print axioms SargentStachurski.ApproximationAndLearning.FDP
#print axioms SargentStachurski.ApproximationAndLearning.FDP.mk
#print axioms SargentStachurski.ApproximationAndLearning.FDP.F
#print axioms SargentStachurski.ApproximationAndLearning.FDP.G
#print axioms SargentStachurski.ApproximationAndLearning.FDP.greatest
#print axioms SargentStachurski.ApproximationAndLearning.FDP.nonempty
#print axioms SargentStachurski.ApproximationAndLearning.FDP.IsOrderPreserving
#print axioms SargentStachurski.ApproximationAndLearning.FDP.IsOrderReversing
#print axioms SargentStachurski.ApproximationAndLearning.FDP.Monotonic
#print axioms SargentStachurski.ApproximationAndLearning.FDP.gsel
#print axioms SargentStachurski.ApproximationAndLearning.FDP.Gsup
#print axioms SargentStachurski.ApproximationAndLearning.FDP.G_le_Gsup
#print axioms SargentStachurski.ApproximationAndLearning.FDP.isGreatest_Gsup
#print axioms SargentStachurski.ApproximationAndLearning.FDP.primary
#print axioms SargentStachurski.ApproximationAndLearning.FDP.sub
#print axioms SargentStachurski.ApproximationAndLearning.FDP.primary_regular
#print axioms SargentStachurski.ApproximationAndLearning.FDP.primary_bellman
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_9
#print axioms SargentStachurski.ApproximationAndLearning.FDP.sub_isGreedy_of_eq
#print axioms SargentStachurski.ApproximationAndLearning.FDP.sub_regular
#print axioms SargentStachurski.ApproximationAndLearning.FDP.sub_bellman
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_10
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_11
#print axioms SargentStachurski.ApproximationAndLearning.FDP.policy_semiconj
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_12
#print axioms SargentStachurski.ApproximationAndLearning.FDP.sub_isValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.FDP.primary_isValueFunction
#print axioms SargentStachurski.ApproximationAndLearning.FDP.fo_sub_of_primary
#print axioms SargentStachurski.ApproximationAndLearning.FDP.fo_primary_of_sub
#print axioms SargentStachurski.ApproximationAndLearning.FDP.theorem_5_2_13
#print axioms SargentStachurski.ApproximationAndLearning.FDP.proposition_5_2_14
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize_isOrderPreserving
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize_monotonic
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize_primary
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize_sub
#print axioms SargentStachurski.ApproximationAndLearning.FDP.dualize_Gsup
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_16
#print axioms SargentStachurski.ApproximationAndLearning.FDP.lemma_5_2_17
#print axioms SargentStachurski.ApproximationAndLearning.FDP.theorem_5_2_18
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp_isOrderPreserving
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp_monotonic
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp_primary
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp_sub
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.le_Gsup
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Gsup_eq_sup
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.proposition_5_3_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qfdp_F_strictMono
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.proposition_5_3_2
#print axioms SargentStachurski.ApproximationAndLearning.zeroDiscountMDP
#print axioms SargentStachurski.ApproximationAndLearning.proposition_5_3_2_needs_beta_pos
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.mk
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.regular
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.β_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.β_lt_one
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.contraction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.supNonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Nonexpansive
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.bellman_contraction
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.T_eq_bellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.one_sub_mul_dist_fixed_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.Assumption911.one_sub_mul_dist_vσ_le
#print axioms SargentStachurski.ApproximationAndLearning.ADP.assumption_9_1_1
#print axioms SargentStachurski.ApproximationAndLearning.ADP.approxBellman
#print axioms SargentStachurski.ApproximationAndLearning.ADP.lemma_9_1_2
#print axioms SargentStachurski.ApproximationAndLearning.ADP.approxBellman_globallyStable
#print axioms SargentStachurski.ApproximationAndLearning.ADP.fvi_terminates
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_9_1_3
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_9_1_4
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_9_1_3_fvi
#print axioms SargentStachurski.ApproximationAndLearning.ADP.theorem_9_1_4_fvi
#print axioms SargentStachurski.ApproximationAndLearning.ADP.approxADP
#print axioms SargentStachurski.ApproximationAndLearning.ADP.proposition_9_1_5
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.mk
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.grid
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.κ
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.measurable_κ
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.κ_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.sum_κ
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.Lfun
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.κ_le_one
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.abs_Lfun_le
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.Lfun_sub
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.Lfun_const
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.measurable_Lfun
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.L
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.L_apply
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.lemma_9_1_1
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.lemma_9_1_6
#print axioms SargentStachurski.ApproximationAndLearning.KernelAverager.remark_9_1_2
#print axioms SargentStachurski.ApproximationAndLearning.gaussKernel
#print axioms SargentStachurski.ApproximationAndLearning.gaussianAverager
#print axioms SargentStachurski.ApproximationAndLearning.hat
#print axioms SargentStachurski.ApproximationAndLearning.Hat.hat_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.Hat.hat_on
#print axioms SargentStachurski.ApproximationAndLearning.Hat.hat_left
#print axioms SargentStachurski.ApproximationAndLearning.Hat.hat_right
#print axioms SargentStachurski.ApproximationAndLearning.Hat.exists_interval
#print axioms SargentStachurski.ApproximationAndLearning.Hat.sum_two
#print axioms SargentStachurski.ApproximationAndLearning.Hat.sum_hat
#print axioms SargentStachurski.ApproximationAndLearning.Hat.hat_grid
#print axioms SargentStachurski.ApproximationAndLearning.Hat.continuous_hat
#print axioms SargentStachurski.ApproximationAndLearning.hatAverager
#print axioms SargentStachurski.ApproximationAndLearning.example_9_1_2_interpolates
#print axioms SargentStachurski.ApproximationAndLearning.example_9_1_2_linear
#print axioms SargentStachurski.ApproximationAndLearning.example_9_1_2_unique
#print axioms SargentStachurski.ApproximationAndLearning.lsq
#print axioms SargentStachurski.ApproximationAndLearning.ssr
#print axioms SargentStachurski.ApproximationAndLearning.least_squares
#print axioms SargentStachurski.ApproximationAndLearning.damped
#print axioms SargentStachurski.ApproximationAndLearning.damped_eq
#print axioms SargentStachurski.ApproximationAndLearning.lemma_9_1_7
#print axioms SargentStachurski.ApproximationAndLearning.damped_iterate_le
#print axioms SargentStachurski.ApproximationAndLearning.lemma_9_1_7_needs_convex
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.mk
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.P
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.P_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.P_sum
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.d
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.β
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.β_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.β_lt_one
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.T
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.T_mono
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.abs_sum_le
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.exercise_9_1_1
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.K
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.T_eq_mulVec
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.fixedPoint
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.That
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.That_unbiased
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.update_eq
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.abs_noise_le
#print axioms SargentStachurski.ApproximationAndLearning.AssetPricing.sum_sq_noise_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qmax
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.le_qmax
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.abs_qmax_sub_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.S
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.bellman_qadp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.S_contraction
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.section_9_2_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Shat
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Shat_unbiased
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.noise_mean_zero
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qUpdate
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qUpdate_apply
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Pσ_pow_nonneg
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Pσ_pow_mulVec_mono
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.theorem_9_2_2
#print axioms SargentStachurski.ApproximationAndLearning.absorbingMDP
#print axioms SargentStachurski.ApproximationAndLearning.theorem_9_2_2_needs_irreducible
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.QPos
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exists_P_pos
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.expSum
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.expSum_pos
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.expSum_mono
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.log_expSum_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qmin
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qmin_le
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exists_qmin
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qmin_eq
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.qmin_pos
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Fexp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Glog
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Glog_le_Glog
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Glog_anti
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.rsfdp
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_9_2_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.monotonic
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.Gsup_eq
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.primary_T
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.primary_bellman_eq
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.sub_bellman_eq
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.primary_contraction
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.section_9_2_2_3
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.exercise_9_2_2
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.remark_9_2_1
#print axioms SargentStachurski.ApproximationAndLearning.FiniteMDP.update_9_23_pos
#print axioms SargentStachurski.ApproximationAndLearning.robbins_siegmund
#print axioms SargentStachurski.ApproximationAndLearning.robbins_monro
