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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

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

namespace SargentStachurski.LinearDecisionProcesses

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

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exogenous discount processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.4.1 (pp. 194–195).

`Z` is finite (as in §6.1.4.2), `Q` a stochastic matrix and `β ≥ 0` the discount function, and
`(K_Q h)(z) = β(z) ∑_{z'} h(z')Q(z, z')` (6.10) acts on `ℝ^Z` with the supremum norm.

* **Lemma 6.1.4**: `(K_Q^n h)(z) = 𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`, the expectation being the sum over
  the paths `z = z₀, z₁, …, z_n` weighted by `∏ Q(z_t, z_{t+1})`.
* **Lemma 6.1.5**: `ρ(K) < 1` iff `‖Kⁿh‖ ≤ λ‖h‖` for some `n ≥ 1` and `λ ∈ [0, 1)`; this holds for
  every bounded linear operator on a Banach lattice.
* **Exercise 6.1.1**: if `ρ(K_Q) < 1`, the price `q = ∑_{t ≥ 0} K_Q^t h` of the cash flow
  `(h(Z_t))` exists and is the unique solution of `q = h + K_Q q`, i.e. `q = (I − K_Q)⁻¹h`.
-/

open Set Function Filter Topology

namespace SargentStachurski.LinearDecisionProcesses

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E]

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- **Lemma 6.1.5** (p. 195): `ρ(K) < 1` iff `‖Kⁿh‖ ≤ λ‖h‖` for all `h`, for some `n ≥ 1` and
`λ ∈ [0, 1)` (Gelfand's formula, as in Example 4.1.1). -/
theorem lemma_6_1_5 (K : E →L[ℝ] E) :
    specRad K < 1 ↔ ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ h, ‖(K ^ n) h‖ ≤ lam * ‖h‖ := by
  constructor
  · intro hρ
    obtain ⟨k, hk, hlt⟩ := exercise_A_4_2 hρ
    exact ⟨k, hk, ‖K ^ k‖, norm_nonneg _, hlt, fun h => (K ^ k).le_opNorm h⟩
  · rintro ⟨n, hn, lam, hlam0, hlam1, hK⟩
    have hnorm : ‖K ^ n‖ ≤ lam := ContinuousLinearMap.opNorm_le_bound _ hlam0 hK
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : specRad K ≤ ‖K ^ (m + 1)‖ ^ (1 / ((m : ℝ) + 1)) :=
      ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ m
    refine hle.trans_lt ((Real.rpow_le_rpow (norm_nonneg _) hnorm (by positivity)).trans_lt ?_)
    exact Real.rpow_lt_one hlam0 hlam1 (by positivity)

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- Iterating `v ↦ h + Kv` from `0` gives the partial sums `∑_{t < n} Kᵗh`. -/
theorem iterate_affine_zero (K : E →L[ℝ] E) (h : E) (n : ℕ) :
    (fun v => h + K v)^[n] 0 = ∑ t ∈ Finset.range n, (K ^ t) h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ', map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ']
    rfl

variable [CompleteSpace E]

/-- **Exercise 6.1.1** (p. 195), operator form: if `K` is positive and `ρ(K) < 1`, then the
partial sums `∑_{t < n} Kᵗh` converge to the unique `q` with `q = h + Kq`, i.e. `q = (I − K)⁻¹h`. -/
theorem exercise_6_1_1 {K : E →L[ℝ] E} (hK : IsPositiveOp K) (hρ : specRad K < 1) (h : E) :
    ∃ q, q = h + K q ∧ (∀ w, w = h + K w → w = q) ∧
      Tendsto (fun n => ∑ t ∈ Finset.range n, (K ^ t) h) atTop (𝓝 q) := by
  have : Nonempty E := ⟨0⟩
  have hι : IsIsoOrderEmbedding (id : E → E) :=
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩
  have hcon : IsOrderContraction id (fun v => h + K v) K := ⟨example_4_1_1 hK hρ, fun v w => by
    change |h + K v - (h + K w)| ≤ K |v - w|
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact hK.abs_le _⟩
  obtain ⟨q, hq, huniq, hlim⟩ := (theorem_4_1_4 hι hcon).1
  refine ⟨q, hq.symm, fun w hw => huniq w hw.symm, (hlim 0).congr fun n => ?_⟩
  exact iterate_affine_zero K h n

end BanachLattice

/-! ### The finite exogenous discount operator -/

namespace Exo

variable {Z : Type*} [Fintype Z]

/-- `(K_Q h)(z) = β(z) ∑_{z'} h(z')Q(z, z')` (6.10), linear. -/
def KLin (β : Z → ℝ) (Q : Z → Z → ℝ) : (Z → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun h z := β z * ∑ z', h z' * Q z z'
  map_add' h g := funext fun z => by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c h := funext fun z => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z' _ => by ring

/-- `K_Q` as a bounded linear operator on `ℝ^Z`. -/
noncomputable def K (β : Z → ℝ) (Q : Z → Z → ℝ) : (Z → ℝ) →L[ℝ] (Z → ℝ) :=
  LinearMap.toContinuousLinearMap (KLin β Q)

theorem K_apply (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (z : Z) :
    K β Q h z = β z * ∑ z', h z' * Q z z' := rfl

theorem K_isPositive {β : Z → ℝ} {Q : Z → Z → ℝ} (hβ : ∀ z, 0 ≤ β z)
    (hQ : ∀ z z', 0 ≤ Q z z') : BanachLattice.IsPositiveOp (K β Q) := fun h hh z => by
  rw [K_apply]
  exact mul_nonneg (hβ z) (Finset.sum_nonneg fun z' _ => mul_nonneg (hh z') (hQ z z'))

/-- `𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`: the sum over paths `z₀ = z, z₁, …, z_n` of
`∏_{t < n} β(z_t)Q(z_t, z_{t+1}) · h(z_n)`. -/
noncomputable def pathExp (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) :
    (n : ℕ) → Z → ℝ
  | 0, z => h z
  | n + 1, z => ∑ p : Fin (n + 1) → Z,
      (∏ t : Fin (n + 1), β ((Fin.cons z p : Fin (n + 2) → Z) t.castSucc) *
        Q ((Fin.cons z p : Fin (n + 2) → Z) t.castSucc) (p t)) * h (p (Fin.last n))

/-- The path sum unfolds one step: `𝔼_z[β₀ ⋯ β_n h(Z_{n+1})] = β(z) ∑_{z₁} Q(z, z₁)
𝔼_{z₁}[β₀ ⋯ β_{n−1} h(Z_n)]` (Markov property and iterated expectations). -/
theorem pathExp_succ (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (n : ℕ) (z : Z) :
    pathExp β Q h (n + 1) z = β z * ∑ z₁, pathExp β Q h n z₁ * Q z z₁ := by
  cases n with
  | zero =>
    rw [pathExp, Finset.mul_sum, ← (Equiv.funUnique (Fin 1) Z).symm.sum_comp]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    simp only [pathExp, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.castSucc_zero,
      Fin.cons_zero, Equiv.funUnique_symm_apply, Fin.last_zero]
    simp
    ring
  | succ n =>
    rw [pathExp, Finset.mul_sum, ← (Fin.consEquiv fun _ : Fin (n + 2) => Z).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [pathExp, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ (n := n + 1), Fin.castSucc_zero,
      Fin.cons_zero, Fin.cons_succ]
    have hcast : ∀ t : Fin (n + 1), (Fin.cons z (Fin.cons z₁ p : Fin (n + 2) → Z) :
        Fin (n + 3) → Z) t.succ.castSucc = (Fin.cons z₁ p : Fin (n + 2) → Z) t.castSucc :=
      fun t => by rw [← Fin.succ_castSucc, Fin.cons_succ]
    have hce : (Fin.consEquiv fun _ : Fin (n + 2) => Z) (z₁, p) = Fin.cons z₁ p := rfl
    have hlast : (Fin.cons z₁ p : Fin (n + 2) → Z) (Fin.last (n + 1)) = p (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    simp only [hce, hcast, hlast]
    ring

/-- **Lemma 6.1.4** (p. 194): `(K_Qⁿ h)(z) = 𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`. -/
theorem lemma_6_1_4 (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (n : ℕ) (z : Z) :
    (K β Q ^ n) h z = pathExp β Q h n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pathExp_succ, pow_succ']
    change K β Q ((K β Q ^ n) h) z = _
    rw [K_apply]
    congr 1
    exact Finset.sum_congr rfl fun z₁ _ => by rw [ih]

/-- **Exercise 6.1.1** (p. 195): if `ρ(K_Q) < 1`, the price of the cash flow `(h(Z_t))_{t ≥ 0}`,
`q(z) = 𝔼_z ∑_{t ≥ 0} ∏_{i < t} β(Z_i) h(Z_t) = lim_n ∑_{t < n} 𝔼_z β₀ ⋯ β_{t−1} h(Z_t)`, exists and
is the unique solution of `q = h + K_Q q`, i.e. `q = (I − K_Q)⁻¹h`. -/
theorem exercise_6_1_1 {β : Z → ℝ} {Q : Z → Z → ℝ} (hβ : ∀ z, 0 ≤ β z) (hQ : ∀ z z', 0 ≤ Q z z')
    (hρ : BanachLattice.specRad (K β Q) < 1) (h : Z → ℝ) :
    ∃ q, q = h + K β Q q ∧ (∀ w, w = h + K β Q w → w = q) ∧
      ∀ z, Tendsto (fun n => ∑ t ∈ Finset.range n, pathExp β Q h t z) atTop (𝓝 (q z)) := by
  obtain ⟨q, hq, huniq, hlim⟩ := BanachLattice.exercise_6_1_1 (K_isPositive hβ hQ) hρ h
  refine ⟨q, hq, huniq, fun z => ?_⟩
  have := (continuous_apply z).continuousAt.tendsto.comp hlim
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, Finset.sum_apply, lemma_6_1_4]

end Exo

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An LDP with exogenous discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.4.2 (pp. 195–197).

The state is `x = (y, z) ∈ Y × Z` with `Z` finite and discrete, and the kernel has the form
`(Kh)(y, z, a) = β(z) ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')`: the endogenous state moves by
`R`, the exogenous state by `Q`, and only `z` drives discounting.

* `continuousOn_of_slices`: with `Z` discrete, continuity on `G` reduces to continuity on each
  slice `G_z`, which is the form of Assumption 6.1.2.
* **Proposition 6.1.6**: under Assumptions 6.1.1–6.1.2 and `ρ(K_Q) < 1`, the fundamental optimality
  properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`.

The book's discount operator
`(Dh)(y, z) = β(z) sup_{a ∈ Γ(y, z)} ∫ ∑_{z'} h(y', z')Q R(y, z, a, dy')` need not be Borel
measurable in `y` for measurable `h` (a supremum over an uncountable family), so it
need not map `bX` into itself. The proof uses instead
`(Dh)(y, z) = β(z) ∑_{z'} sup_{y'} h(y', z') Q(z, z')`, which also dominates every `K_σ`, depends on
`z` only, and satisfies `Dⁿh = K_Qⁿ m_h` with `m_h(z') = sup_{y'} h(y', z')`, so the book's
eventual contraction argument goes through.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono hasSolidNorm_pi

/-- With `Z` discrete, a function continuous on every slice `G_z` is continuous on `G`. -/
theorem continuousOn_of_slices {Y Z A : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [DiscreteTopology Z] [TopologicalSpace A] {G : Set ((Y × Z) × A)} {f : (Y × Z) × A → ℝ}
    (h : ∀ z, ContinuousOn (fun q : Y × A => f ((q.1, z), q.2)) {q | ((q.1, z), q.2) ∈ G}) :
    ContinuousOn f G := by
  intro p hp
  let z₀ := p.1.2
  let U : Set ((Y × Z) × A) := {p' | p'.1.2 = z₀}
  have hU : U ∈ 𝓝 p :=
    ((isOpen_discrete {z₀}).preimage (continuous_snd.comp continuous_fst)).mem_nhds rfl
  let π : (Y × Z) × A → Y × A := fun p' => (p'.1.1, p'.2)
  have hπ : Continuous π := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo π (G ∩ U) {q | ((q.1, z₀), q.2) ∈ G} := fun p' ⟨hp', hz⟩ => by
    change ((p'.1.1, z₀), p'.2) ∈ G
    rw [← show p'.1.2 = z₀ from hz]
    exact hp'
  have hc := (h z₀ (π p) (by change ((p.1.1, p.1.2), p.2) ∈ G; exact hp)).comp
    hπ.continuousWithinAt hmaps
  have heq : EqOn f ((fun q : Y × A => f ((q.1, z₀), q.2)) ∘ π) (G ∩ U) := fun p' ⟨_, hz⟩ => by
    change f p' = f ((p'.1.1, z₀), p'.2)
    rw [← show p'.1.2 = z₀ from hz]
  exact (continuousWithinAt_inter hU).1 (hc.congr heq (heq ⟨hp, rfl⟩))

namespace LDP

attribute [local instance] LDP.P_markov

variable {Y Z A : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace A]

/-- `m_h(z') = sup_{y'} h(y', z')`. -/
noncomputable def supY (h : BM (Y × Z)) (z : Z) : ℝ := ⨆ y, h.toFun (y, z)

theorem bddAbove_slice (h : BM (Y × Z)) (z : Z) : BddAbove (range fun y => h.toFun (y, z)) :=
  ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h _)⟩

theorem le_supY (h : BM (Y × Z)) (y : Y) (z : Z) : h.toFun (y, z) ≤ supY h z :=
  le_ciSup (bddAbove_slice h z) y

theorem abs_supY_le (h : BM (Y × Z)) (z : Z) : |supY h z| ≤ ‖h‖ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · rw [supY, Real.iSup_of_isEmpty, abs_zero]
    exact norm_nonneg _
  · refine abs_le.2 ⟨?_, ciSup_le fun y => (le_abs_self _).trans (BM.abs_le_norm h _)⟩
    obtain ⟨y⟩ := hY
    exact (neg_le.2 ((neg_le_abs _).trans (BM.abs_le_norm h (y, z)))).trans (le_supY h y z)

theorem abs_supY_sub_le (u v : BM (Y × Z)) (z : Z) : |supY u z - supY v z| ≤ ‖u - v‖ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · simp [supY]
  · exact abs_ciSup_sub_ciSup_le (bddAbove_slice u z) (bddAbove_slice v z) fun y =>
      (BM.abs_sub_le_dist u v (y, z)).trans (dist_eq_norm u v).le

/-- The measurable discount operator `(Dh)(y, z) = β(z) ∑_{z'} sup_{y'} h(y', z') Q(z, z')`. -/
noncomputable def Dexo [Fintype Z] [MeasurableSingletonClass Z] (βz : Z → ℝ) (Q : Z → Z → ℝ)
    (h : BM (Y × Z)) : BM (Y × Z) :=
  ⟨fun x => Exo.K βz Q (supY h) x.2, (measurable_of_countable _).comp measurable_snd,
    ⟨‖Exo.K βz Q (supY h)‖, fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (Exo.K βz Q (supY h)) x.2⟩⟩

theorem supY_lift [Nonempty Y] (g : Z → ℝ) (hm : Measurable fun x : Y × Z => g x.2)
    (hb : ∃ C, ∀ x : Y × Z, |g x.2| ≤ C) :
    supY (⟨fun x => g x.2, hm, hb⟩ : BM (Y × Z)) = g := funext fun z => by
  change (⨆ _ : Y, g z) = g z
  exact ciSup_const

theorem Dexo_iterate [Fintype Z] [MeasurableSingletonClass Z] [Nonempty Y] (βz : Z → ℝ)
    (Q : Z → Z → ℝ) (h : BM (Y × Z)) (n : ℕ)
    (x : Y × Z) : ((Dexo βz Q)^[n + 1] h).toFun x = (Exo.K βz Q ^ (n + 1)) (supY h) x.2 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    change Exo.K βz Q (supY ((Dexo βz Q)^[n + 1] h)) x.2 = _
    have : supY ((Dexo βz Q)^[n + 1] h) = (Exo.K βz Q ^ (n + 1)) (supY h) :=
      funext fun z => by
        rw [supY]
        simp_rw [ih]
        exact ciSup_const
    rw [this, pow_succ' (Exo.K βz Q) (n + 1)]
    rfl

/-- `D` is a discount operator when `ρ(K_Q) < 1` (proof of Proposition 6.1.6). -/
theorem Dexo_isDiscountOperator [Fintype Z] [MeasurableSingletonClass Z] {βz : Z → ℝ}
    (hβ : ∀ z, 0 ≤ βz z) {Q : Z → Z → ℝ}
    (hQ : ∀ z z', 0 ≤ Q z z') (hρ : BanachLattice.specRad (Exo.K βz Q) < 1) :
    BanachLattice.IsDiscountOperator (Dexo (Y := Y) βz Q) := by
  have hpos := Exo.K_isPositive hβ hQ
  have hsupmono : ∀ u v : BM (Y × Z), u ≤ v → supY u ≤ supY v := fun u v huv z => by
    rcases isEmpty_or_nonempty Y with hY | hY
    · simp [supY]
    · exact ciSup_le fun y => (huv (y, z)).trans (le_supY v y z)
  obtain ⟨n, hn, lam, hlam0, hlam1, hK⟩ := (BanachLattice.lemma_6_1_5 (Exo.K βz Q)).1 hρ
  refine ⟨BM.ext fun x => ?_, fun h hh x => ?_, fun u _ v _ huv x => ?_, n, hn, lam, hlam0,
    hlam1, fun u _ v _ => ?_⟩
  · change Exo.K βz Q (supY 0) x.2 = 0
    have : supY (0 : BM (Y × Z)) = 0 := funext fun z => by
      rcases isEmpty_or_nonempty Y with hY | hY
      · exact Real.iSup_of_isEmpty _
      · exact ciSup_const
    rw [this, map_zero]
    rfl
  · exact hpos _ (fun z => Real.iSup_nonneg fun y => hh (y, z)) x.2
  · exact hpos.mono (hsupmono u v huv) x.2
  · rcases isEmpty_or_nonempty Y with hY | hY
    · have : IsEmpty (Y × Z) := inferInstance
      rw [show (Dexo βz Q)^[n] u - (Dexo βz Q)^[n] v = 0 from BM.ext fun x => isEmptyElim x,
        norm_zero]
      exact mul_nonneg hlam0 (norm_nonneg _)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine BM.norm_le (mul_nonneg hlam0 (norm_nonneg _)) fun x => ?_
      rw [BM.sub_apply, Dexo_iterate, Dexo_iterate, ← Pi.sub_apply, ← map_sub]
      have h1 : ‖supY u - supY v‖ ≤ ‖u - v‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => by
          rw [Real.norm_eq_abs]; exact abs_supY_sub_le u v z
      calc |(Exo.K βz Q ^ (m + 1)) (supY u - supY v) x.2|
          ≤ ‖(Exo.K βz Q ^ (m + 1)) (supY u - supY v)‖ := by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ x.2
        _ ≤ lam * ‖supY u - supY v‖ := hK _
        _ ≤ lam * ‖u - v‖ := mul_le_mul_of_nonneg_left h1 hlam0

variable (M : LDP (Y × Z) A)

/-- `K_σ ≤ D` (proof of Proposition 6.1.6). -/
theorem K_le_Dexo [Fintype Z] [MeasurableSingletonClass Z] {βz : Z → ℝ} (hβ : ∀ z, 0 ≤ βz z)
    {Q : Z → Z → ℝ} (hQ : ∀ z z', 0 ≤ Q z z')
    (hβM : ∀ p : (Y × Z) × A, M.β.toFun p = βz p.1.2) (R : Kernel ((Y × Z) × A) Y)
    [IsMarkovKernel R]
    (hP : ∀ (h : BM (Y × Z)) (p : (Y × Z) × A),
      ∫ x', h.toFun x' ∂(M.P p) = ∫ y', ∑ z', h.toFun (y', z') * Q p.1.2 z' ∂(R p))
    (σ : M.Policy) (h : BM (Y × Z)) : M.K σ h ≤ Dexo βz Q h := fun x => by
  rw [K_apply, hβM, hP]
  change βz x.2 * _ ≤ βz x.2 * ∑ z', supY h z' * Q x.2 z'
  refine mul_le_mul_of_nonneg_left ?_ (hβ _)
  have hint : Integrable (fun y' => ∑ z', h.toFun (y', z') * Q x.2 z') (R (x, σ.1 x)) :=
    integrable_finsetSum _ fun z' _ => (Integrable.of_bound
      (h.measurable'.comp measurable_prodMk_right).aestronglyMeasurable ‖h‖
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)).mul_const _
  calc ∫ y', ∑ z', h.toFun (y', z') * Q x.2 z' ∂(R (x, σ.1 x))
      ≤ ∫ _, ∑ z', supY h z' * Q x.2 z' ∂(R (x, σ.1 x)) :=
        integral_mono hint (integrable_const _) fun y' => Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_right (le_supY h y' z') (hQ _ _)
    _ = ∑ z', supY h z' * Q x.2 z' := by simp

/-- **Proposition 6.1.6** (p. 196): for an LDP on `X = Y × Z` with `Z` finite and
`(Kh)(y, z, a) = β(z) ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')`, under Assumption 6.1.1 (`Γ` with
the maximum theorem, `r` continuous on `G`), Assumption 6.1.2 (`(y, a) ↦ ∫ g(y')R(y, z, a, dy')`
continuous on `G_z` for `g ∈ bcY`) and `ρ(K_Q) < 1`, (i) the fundamental optimality properties
hold, (ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. -/
theorem proposition_6_1_6 [TopologicalSpace Y] [TopologicalSpace Z] [DiscreteTopology Z]
    [TopologicalSpace A] [Fintype Z] [MeasurableSingletonClass Z] (hB : HasMaxSelections M.Γ)
    (hr : ContinuousOn M.r.toFun M.G) {βz : Z → ℝ} (hβ : ∀ z, 0 ≤ βz z) {Q : Z → Z → ℝ}
    (hQ : ∀ z z', 0 ≤ Q z z') (hβM : ∀ p : (Y × Z) × A, M.β.toFun p = βz p.1.2)
    (R : Kernel ((Y × Z) × A) Y) [IsMarkovKernel R]
    (hP : ∀ (h : BM (Y × Z)) (p : (Y × Z) × A),
      ∫ x', h.toFun x' ∂(M.P p) = ∫ y', ∑ z', h.toFun (y', z') * Q p.1.2 z' ∂(R p))
    (hR : ∀ z, ∀ g : BM Y, Continuous g.toFun →
      ContinuousOn (fun q : Y × A => ∫ y', g.toFun y' ∂(R ((q.1, z), q.2)))
        {q | q.2 ∈ M.Γ (q.1, z)})
    (hρ : BanachLattice.specRad (Exo.K βz Q) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ bc (Y × Z),
      M.adp.VFIGeometric (bc (Y × Z)) vstar := by
  -- `K` is weak Feller
  have hK : M.IsWeakFeller := by
    intro h hc
    refine continuousOn_of_slices fun z => ?_
    have hslice : ∀ z' : Z, ∃ g : BM Y, Continuous g.toFun ∧ ∀ y, g.toFun y = h.toFun (y, z') :=
      fun z' => ⟨⟨fun y => h.toFun (y, z'), h.measurable'.comp measurable_prodMk_right,
        ⟨‖h‖, fun _ => BM.abs_le_norm h _⟩⟩, hc.comp (continuous_id.prodMk continuous_const),
        fun _ => rfl⟩
    choose g hgc hg using hslice
    have hform : ∀ q : Y × A, M.β.toFun ((q.1, z), q.2) * ∫ x', h.toFun x' ∂(M.P ((q.1, z), q.2))
        = βz z * ∑ z', Q z z' * ∫ y', (g z').toFun y' ∂(R ((q.1, z), q.2)) := fun q => by
      have hint : ∀ z' ∈ Finset.univ, Integrable (fun y' => h.toFun (y', z') * Q z z')
          (R ((q.1, z), q.2)) := fun z' _ => (Integrable.of_bound
        (h.measurable'.comp measurable_prodMk_right).aestronglyMeasurable ‖h‖
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)).mul_const _
      have e1 : ∫ y', ∑ z', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) =
          ∑ z', ∫ y', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) :=
        integral_finsetSum Finset.univ hint
      rw [hβM, hP]
      change βz z * ∫ y', ∑ z', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) = _
      rw [e1]
      congr 1
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [integral_mul_const, mul_comm]
      simp_rw [hg]
    simp_rw [hform]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun z' _ =>
      continuousOn_const.mul (hR z (g z') (hgc z')))
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := M.proposition_6_1_3 hB hr hK
    (Dexo_isDiscountOperator hβ hQ hρ) fun σ h _ => M.K_le_Dexo hβ hQ hβM R hP σ h
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

end LDP

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov decision processes on general state spaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.5 (pp. 197–199).

An MDP `(Γ, r, β, P)` is an LDP whose kernel is `K = βP` (6.12) with `β ∈ [0, 1)` and `P`
stochastic (`ofMDP`); `T_σ = r_σ + βP_σ` (6.13). This also covers **Example 6.1.3** (a finite
MDP is the LDP with `K = βP`, and `‖K_σ‖ ≤ β`).

* **Proposition 6.1.7** (Feller MDPs): under Assumption 6.1.1 with `P` weak Feller, the fundamental
  optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`; if `P` is strong
  Feller, OPI and HPI converge. The discount operator is `Dh = β (sup h) 𝟙` in place of the book's
  `(Dh)(x) = β max_{a ∈ Γ(x)} ∫ h dP(x, a)`, which need not be measurable for merely measurable `h`;
  both dominate `K_σ` on `bX₊` and contract with modulus `β`.
* §6.1.5.2: under strong Feller, greedy policies are the pointwise maximizers (6.14) and the
  Bellman operator is (6.15) (from §6.1.3.2).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The MDP `(Γ, r, β, P)` (§6.1.5.1) as an LDP with `K = βP` (6.12). -/
noncomputable def ofMDP (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    LDP X A where
  Γ := Γ
  r := r
  β := BM.const β
  β_nonneg _ := hβ0
  P := P
  exists_policy := hσ

/-- (6.13): `(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`. -/
theorem ofMDP_T_apply (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) (v : BM X) (x : X) :
    ((ofMDP Γ r hβ0 P hσ).adp.T σ v).toFun x =
      r.toFun (x, σ.1 x) + β * ∫ x', v.toFun x' ∂(P (x, σ.1 x)) := rfl

/-- **Example 6.1.3** (p. 190): for an MDP, `|∫ v dK(x, a)| ≤ β‖v‖`, so `Kv ∈ bG` and
`‖K_σ‖ ≤ β`. -/
theorem example_6_1_3 (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) : ‖(ofMDP Γ r hβ0 P hσ).K σ‖ ≤ β := by
  refine ((ofMDP Γ r hβ0 P hσ).norm_K_le σ).trans ?_
  exact BM.norm_le hβ0 fun _ => by simp [ofMDP, abs_of_nonneg hβ0]

/-- `Dh = β (sup h) 𝟙`. -/
noncomputable def Dsup (β : ℝ) (h : BM X) : BM X := BM.const (β * ⨆ x, h.toFun x)

theorem abs_iSup_sub_le (u v : BM X) : |(⨆ x, u.toFun x) - ⨆ x, v.toFun x| ≤ ‖u - v‖ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  · have hbu : BddAbove (range u.toFun) :=
      ⟨‖u‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm u x)⟩
    have hbv : BddAbove (range v.toFun) :=
      ⟨‖v‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm v x)⟩
    exact abs_ciSup_sub_ciSup_le hbu hbv fun x =>
      (BM.abs_sub_le_dist u v x).trans (dist_eq_norm u v).le

/-- `Dh = β (sup h) 𝟙` is a discount operator for `0 ≤ β < 1`. -/
theorem Dsup_isDiscountOperator {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    BanachLattice.IsDiscountOperator (Dsup (X := X) β) := by
  refine ⟨BM.ext fun x => ?_, fun h hh x => ?_, fun u _ v _ huv x => ?_, 1, one_pos, β, hβ0, hβ1,
    fun u _ v _ => ?_⟩
  · change β * (⨆ x, (0 : ℝ)) = 0
    rcases isEmpty_or_nonempty X with hX | hX
    · simp
    · simp
  · exact mul_nonneg hβ0 (Real.iSup_nonneg fun x => hh x)
  · change β * (⨆ x, u.toFun x) ≤ β * ⨆ x, v.toFun x
    refine mul_le_mul_of_nonneg_left ?_ hβ0
    rcases isEmpty_or_nonempty X with hX | hX
    · simp
    · exact ciSup_le fun x => (huv x).trans (le_ciSup ⟨‖v‖, by
        rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm v y)⟩ x)
  · refine BM.norm_le (mul_nonneg hβ0 (norm_nonneg _)) fun x => ?_
    change |β * (⨆ x, u.toFun x) - β * ⨆ x, v.toFun x| ≤ β * ‖u - v‖
    rw [← mul_sub, abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (abs_iSup_sub_le u v) hβ0

theorem K_le_Dsup (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) (h : BM X) : (ofMDP Γ r hβ0 P hσ).K σ h ≤ Dsup β h :=
  fun x => by
    rw [LDP.K_apply]
    change β * _ ≤ β * ⨆ x, h.toFun x
    refine mul_le_mul_of_nonneg_left ?_ hβ0
    have hb : BddAbove (range h.toFun) :=
      ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h y)⟩
    calc ∫ x', h.toFun x' ∂(P (x, σ.1 x)) ≤ ∫ _, (⨆ y, h.toFun y) ∂(P (x, σ.1 x)) :=
          integral_mono (Integrable.of_bound h.measurable'.aestronglyMeasurable ‖h‖
            (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h y))
            (integrable_const _)
            fun y => le_ciSup hb y
      _ = ⨆ y, h.toFun y := by simp

variable [TopologicalSpace X] [TopologicalSpace A]

/-- **Proposition 6.1.7** (p. 198): under Assumption 6.1.1 (`Γ` with the maximum theorem, `r`
continuous on `G`), if `P` is weak Feller then (i) the fundamental optimality properties hold, (ii)
`v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`; if `P` is strong Feller, OPI and HPI
converge. -/
theorem proposition_6_1_7 (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (hB : HasMaxSelections Γ) (hr : ContinuousOn r.toFun {p | p.2 ∈ Γ p.1})
    (hP : ∀ h : BM X, Continuous h.toFun →
      ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P p)) {p | p.2 ∈ Γ p.1}) :
    ∃ hw : (ofMDP Γ r hβ0 P hσ).adp.WellPosed, (ofMDP Γ r hβ0 P hσ).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X, (ofMDP Γ r hβ0 P hσ).adp.VFIGeometric (LDP.bc X) vstar ∧
        ((∀ h : BM X, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P p)) {p | p.2 ∈ Γ p.1}) →
          ∀ g, (ofMDP Γ r hβ0 P hσ).adp.IsSelector g →
            (ofMDP Γ r hβ0 P hσ).adp.OPIConverges g vstar ∧
              (ofMDP Γ r hβ0 P hσ).adp.HPIConverges hw g vstar) := by
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := (ofMDP Γ r hβ0 P hσ).proposition_6_1_3 hB hr
    (fun h hc => continuousOn_const.mul (hP h hc)) (Dsup_isDiscountOperator hβ0 hβ1)
    fun σ h _ => K_le_Dsup Γ r hβ0 P hσ σ h
  exact ⟨hw, hFO, vstar, hv, hgeo, fun hS => hconv fun h => continuousOn_const.mul (hS h)⟩

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Natural resource management

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.2.1 (pp. 199–203).

The Bellman equation is
`v(y, z) = max_{0 ≤ e ≤ y} {π(e) + β(z) ∫ ∑_{z'} v(f(y − e)ξ, z')Q(z, z')φ(dξ)}`: stock `y`, usage
`e`, profit `π` (bounded, continuous), growth `f` (continuous), multiplicative shock `ξ ∼ φ`, and a
finite exogenous state `z` (stochastic matrix `Q`) driving the discount factor `β(z) ≥ 0`.

* `finiteKernel Q`: the stochastic kernel of a stochastic matrix,
  `∫ g dQ(z) = ∑_{z'} g(z')Q(z, z')`.
* `ResourceModel.ldp`: the model as an LDP on `X = ℝ × Z` with `Γ(y, z) = [0, max(y, 0)]` (the
  stock is nonnegative on every path), `r = π(e)`, endogenous kernel
  `R(y, z, e) = law of f(y − e)ξ`,
  and `P = R ⊗ Q(z, ·)`.
* **Proposition 6.2.1**: if `ρ(K_Q) < 1`, the fundamental optimality properties hold, `v* ∈ bcX`,
  and
  VFI converges geometrically on `bcX` (Proposition 6.1.6; Exercise A.3.1 for `Γ`, dominated
  convergence for Assumption 6.1.2).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### The kernel of a stochastic matrix -/

/-- The distribution `Q(z, ·)` as a probability mass function. -/
noncomputable def rowPMF {Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (z : Z) : PMF Z :=
  PMF.ofFintype (fun z' => ENNReal.ofReal (Q z z')) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => hQ0 z z', hQ1 z, ENNReal.ofReal_one])

/-- The stochastic kernel of the stochastic matrix `Q`. -/
noncomputable def finiteKernel {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) : Kernel Z Z :=
  Kernel.ofFunOfCountable fun z => (rowPMF Q hQ0 hQ1 z).toMeasure

theorem finiteKernel_isMarkov {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) : IsMarkovKernel (finiteKernel Q hQ0 hQ1) :=
  ⟨fun z => by
    change IsProbabilityMeasure (rowPMF Q hQ0 hQ1 z).toMeasure
    infer_instance⟩

/-- `∫ g dQ(z) = ∑_{z'} g(z')Q(z, z')`. -/
theorem integral_finiteKernel {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (g : Z → ℝ) (z : Z) :
    ∫ z', g z' ∂(finiteKernel Q hQ0 hQ1 z) = ∑ z', g z' * Q z z' := by
  change ∫ z', g z' ∂(rowPMF Q hQ0 hQ1 z).toMeasure = _
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun z' _ => ?_
  simp only [rowPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hQ0 z z'), smul_eq_mul]
  ring

/-! ### The model -/

/-- The natural resource management model of §6.2.1. -/
structure ResourceModel (Z : Type*) [Fintype Z] where
  /-- the profit function -/
  π : ℝ → ℝ
  π_cont : Continuous π
  π_bdd : ∃ C, ∀ e, |π e| ≤ C
  /-- the growth function -/
  f : ℝ → ℝ
  f_cont : Continuous f
  /-- the distribution of the multiplicative shock -/
  φ : Measure ℝ
  [φ_prob : IsProbabilityMeasure φ]
  /-- the discount factor function -/
  βz : Z → ℝ
  βz_nonneg : ∀ z, 0 ≤ βz z
  /-- the exogenous stochastic matrix -/
  Q : Z → Z → ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1

namespace ResourceModel

attribute [local instance] ResourceModel.φ_prob

variable {Z : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  (M : ResourceModel Z)

omit [MeasurableSingletonClass Z] in
theorem measurable_next :
    Measurable (uncurry fun (p : (ℝ × Z) × ℝ) (ξ : ℝ) => M.f (p.1.1 - p.2) * ξ) :=
  ((M.f_cont.measurable.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
    (measurable_snd.comp measurable_fst))).mul measurable_snd)

/-- The endogenous kernel `R(y, z, e) = law of f(y − e)ξ`. -/
noncomputable def R : Kernel ((ℝ × Z) × ℝ) ℝ :=
  shockKernel (fun (p : (ℝ × Z) × ℝ) (ξ : ℝ) => M.f (p.1.1 - p.2) * ξ) M.measurable_next M.φ

/-- The exogenous kernel `Q(z, ·)`, read on state-action pairs. -/
noncomputable def Qk : Kernel ((ℝ × Z) × ℝ) Z :=
  (finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p => p.1.2)
    (measurable_snd.comp measurable_fst)

omit [MeasurableSingletonClass Z] in
theorem R_isMarkov : IsMarkovKernel M.R := shockKernel_isMarkov _ _ _

theorem Qk_isMarkov : IsMarkovKernel M.Qk := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  unfold Qk
  infer_instance

/-- The model as an LDP on `X = ℝ × Z`, `A = ℝ`. -/
noncomputable def ldp : LDP (ℝ × Z) ℝ :=
  have := M.R_isMarkov
  have := M.Qk_isMarkov
  { Γ := fun x => Icc 0 (max x.1 0)
    r := ⟨fun p => M.π p.2, M.π_cont.measurable.comp measurable_snd,
      ⟨M.π_bdd.choose, fun _ => M.π_bdd.choose_spec _⟩⟩
    β := ⟨fun p => M.βz p.1.2, (measurable_of_countable M.βz).comp
      (measurable_snd.comp measurable_fst),
      ⟨∑ z, |M.βz z|, fun p => Finset.single_le_sum (f := fun z => |M.βz z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1.2)⟩⟩
    β_nonneg := fun p => M.βz_nonneg p.1.2
    P := M.R ×ₖ M.Qk
    exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ }

/-- The integral identity for the kernel:
`∫ h dP(y, z, e) = ∫ ∑_{z'} h(y', z')Q(z, z') R(y, z, e, dy')`. -/
theorem integral_P (h : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    ∫ x', h.toFun x' ∂(M.ldp.P p) = ∫ y', ∑ z', h.toFun (y', z') * M.Q p.1.2 z' ∂(M.R p) := by
  have := M.R_isMarkov
  have := M.Qk_isMarkov
  change ∫ x', h.toFun x' ∂((M.R ×ₖ M.Qk) p) = _
  rw [Kernel.prod_apply, integral_prod _ (Integrable.of_bound h.measurable'.aestronglyMeasurable
    ‖h‖ (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h x))]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  change ∫ z', h.toFun (y', z') ∂(finiteKernel M.Q M.Q_nonneg M.Q_sum p.1.2) = _
  exact integral_finiteKernel _ _ _ _ _

/-- **Proposition 6.2.1** (p. 200): for the natural resource model, if `ρ(K_Q) < 1`, then the
fundamental optimality properties hold, the value function `v*` lies in `bcX`, and VFI converges
geometrically on `bcX`. -/
theorem proposition_6_2_1 [TopologicalSpace Z] [DiscreteTopology Z]
    (hρ : BanachLattice.specRad (Exo.K M.βz M.Q) < 1) :
    ∃ hw : M.ldp.adp.WellPosed, M.ldp.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ LDP.bc (ℝ × Z),
      M.ldp.adp.VFIGeometric (LDP.bc (ℝ × Z)) vstar := by
  have := M.R_isMarkov
  have hB : HasMaxSelections M.ldp.Γ := hasMaxSelections_Icc (X := ℝ × Z) (g := fun _ => 0)
    (h := fun x => max x.1 0) continuous_const (continuous_fst.max continuous_const)
    fun x => le_max_right _ _
  refine M.ldp.proposition_6_1_6 hB (M.π_cont.comp continuous_snd).continuousOn M.βz_nonneg
    M.Q_nonneg (fun _ => rfl) M.R M.integral_P (fun z g hg => ?_) hρ
  -- Assumption 6.1.2: dominated convergence
  have heq : ∀ q : ℝ × ℝ, ∫ y', g.toFun y' ∂(M.R ((q.1, z), q.2)) =
      ∫ ξ, g.toFun (M.f (q.1 - q.2) * ξ) ∂M.φ := fun q =>
    integral_shockKernel _ _ _ g.measurable' _
  simp_rw [heq]
  refine (continuous_of_dominated (bound := fun _ => ‖g‖)
    (fun _ => (g.measurable'.comp ((measurable_const.mul measurable_id))).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm g _)
    (integrable_const _) (Eventually.of_forall fun ξ => ?_)).continuousOn
  exact hg.comp ((M.f_cont.comp (continuous_fst.sub continuous_snd)).mul continuous_const)

end ResourceModel

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic rates of return

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.2.2 (pp. 203–206).

Wealth `w ≥ 0`, a finite exogenous state `z` (stochastic matrix `Q`), consumption `c ∈ [0, w]`,
bounded continuous utility `u`, a constant `β ∈ [0, 1)`, and
`∫ v(x')P(x, c, dx') = ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z'] φ(ds') Q(z, z')`: the return
`R(z')` and labour income `y(z', s')` depend on the next exogenous state and an iid shock `s' ∼ φ`.

* `mixKernel κ F φ`: draw `z' ∼ κ(d)`, then `s' ∼ φ`, and move to `F(d, z', s')`, with
  `∫ g dP(d) = ∫ ∫ g(F(d, z', s'))φ(ds')κ(d, dz')`.
* `section_6_2_2`: Proposition 6.1.7 applies (Exercise A.3.1 for `Γ`, dominated convergence for the
  weak Feller property), so the fundamental optimality properties hold, `v* ∈ bcX`, VFI converges
  geometrically on `bcX`, and the Bellman operator is
  `(Tv)(w, z) = max_{0 ≤ c ≤ w} {u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')}`
  for
  `v ∈ bcX`.
* **Exercise 6.2.1**: with survival probabilities `q(t) ∈ [0, 1]` and age `t` in the state,
  `K = βq(t)P` and Proposition 6.1.3 applies with the discount operator `Dh = β (sup h) 𝟙`.

Wealth is a real state with `Γ(w, z) = [0, max(w, 0)]`; it stays nonnegative when `R, y ≥ 0`, but
nothing in the optimality results needs that.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Mixtures of shock kernels -/

/-- Draw `z' ∼ κ(d)`, then `s' ∼ φ`, and move to `F(d, z', s')`. -/
noncomputable def mixKernel {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ] :
    Kernel D E :=
  have := shockKernel_isMarkov F hF φ
  Kernel.snd (κ ⊗ₖ shockKernel F hF φ)

theorem mixKernel_isMarkov {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ] :
    IsMarkovKernel (mixKernel κ F hF φ) := by
  have := shockKernel_isMarkov F hF φ
  unfold mixKernel
  infer_instance

/-- `∫ g dP(d) = ∫ ∫ g(F(d, z', s'))φ(ds')κ(d, dz')` for bounded measurable `g`. -/
theorem integral_mixKernel {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ]
    (g : BM E) (d : D) :
    ∫ x, g.toFun x ∂(mixKernel κ F hF φ d) = ∫ z', ∫ s, g.toFun (F (d, z') s) ∂φ ∂(κ d) := by
  have := shockKernel_isMarkov F hF φ
  change ∫ x, g.toFun x ∂(Kernel.snd (κ ⊗ₖ shockKernel F hF φ) d) = _
  have hcp := ProbabilityTheory.integral_compProd (κ := κ) (η := shockKernel F hF φ) (a := d)
    (f := fun x : Z × E => g.toFun x.2)
    (Integrable.of_bound (g.measurable'.comp measurable_snd).aestronglyMeasurable ‖g‖
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm g _))
  rw [Kernel.snd_apply, integral_map measurable_snd.aemeasurable
    g.measurable'.aestronglyMeasurable, hcp]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  exact integral_shockKernel F hF φ g.measurable' (d, z')

/-! ### The model -/

/-- The optimal savings model with stochastic returns of §6.2.2. -/
structure ReturnsModel (Z S : Type*) [Fintype Z] [MeasurableSpace S] where
  /-- the utility function -/
  u : ℝ → ℝ
  u_cont : Continuous u
  u_bdd : ∃ C, ∀ c, |u c| ≤ C
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the exogenous stochastic matrix -/
  Q : Z → Z → ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1
  /-- the gross return `R(z')` -/
  Rz : Z → ℝ
  /-- labour income `y(z', s')` -/
  yf : Z → S → ℝ
  yf_meas : ∀ z, Measurable (yf z)
  /-- the distribution of the iid income shock -/
  φ : Measure S
  [φ_prob : IsProbabilityMeasure φ]

namespace ReturnsModel

attribute [local instance] ReturnsModel.φ_prob

variable {Z S : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [MeasurableSpace S] (M : ReturnsModel Z S)

omit [Fintype Z] [MeasurableSingletonClass Z] in
theorem measurable_zproj : Measurable fun p : (ℝ × Z) × ℝ => p.1.2 :=
  measurable_snd.comp measurable_fst

omit [Fintype Z] [MeasurableSingletonClass Z] in
theorem measurable_zprojT : Measurable fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1 :=
  (measurable_fst.comp measurable_snd).comp measurable_fst

/-- The reward `u(c)` as an element of `bG`. -/
noncomputable def reward {X : Type*} [MeasurableSpace X] : BM (X × ℝ) :=
  ⟨fun p => M.u p.2, M.u_cont.measurable.comp measurable_snd,
    ⟨M.u_bdd.choose, fun _ => M.u_bdd.choose_spec _⟩⟩

omit [MeasurableSingletonClass Z] in
theorem measurable_income {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass Z] :
    Measurable fun p : (T × Z) × S => M.Rz p.1.2 * 0 + M.yf p.1.2 p.2 := by
  simp only [mul_zero, zero_add]
  exact (measurable_from_prod_countable_right (f := fun zs : Z × S => M.yf zs.1 zs.2)
    fun z => M.yf_meas z).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Next period's state `(R(z')(w − c) + y(z', s'), z')`. -/
def next (q : ((ℝ × Z) × ℝ) × Z) (s : S) : ℝ × Z :=
  (M.Rz q.2 * (q.1.1.1 - q.1.2) + M.yf q.2 s, q.2)

theorem measurable_next : Measurable (uncurry M.next) := by
  have hy : Measurable fun p : (((ℝ × Z) × ℝ) × Z) × S => M.yf p.1.2 p.2 := by
    have := M.measurable_income (T := (ℝ × Z) × ℝ)
    simpa using this
  refine Measurable.prodMk (Measurable.add (Measurable.mul
    ((measurable_of_countable M.Rz).comp (measurable_snd.comp measurable_fst))
    (((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
      (measurable_snd.comp (measurable_fst.comp measurable_fst))))) hy)
    (measurable_snd.comp measurable_fst)

theorem finiteKernel_comap_isMarkov :
    IsMarkovKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × Z) × ℝ => p.1.2)
      measurable_zproj) := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  infer_instance

/-- The transition kernel `P` of §6.2.2. -/
noncomputable def P : Kernel ((ℝ × Z) × ℝ) (ℝ × Z) :=
  have := M.finiteKernel_comap_isMarkov
  mixKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × Z) × ℝ => p.1.2)
    measurable_zproj) M.next M.measurable_next M.φ

theorem P_isMarkov : IsMarkovKernel M.P := by
  have := M.finiteKernel_comap_isMarkov
  exact mixKernel_isMarkov _ _ _ _

/-- `∫ v dP(w, z, c) = ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds') Q(z, z')`. -/
theorem integral_P (v : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    ∫ x, v.toFun x ∂(M.P p) = ∑ z', (∫ s, v.toFun (M.next (p, z') s) ∂M.φ) * M.Q p.1.2 z' := by
  have := M.finiteKernel_comap_isMarkov
  change ∫ x, v.toFun x ∂(mixKernel _ M.next M.measurable_next M.φ p) = _
  rw [integral_mixKernel]
  exact integral_finiteKernel M.Q M.Q_nonneg M.Q_sum _ p.1.2

/-- The model as an MDP on `X = ℝ × Z`, `A = ℝ`, `Γ(w, z) = [0, max(w, 0)]`. -/
noncomputable def ldp : LDP (ℝ × Z) ℝ :=
  have := M.P_isMarkov
  ofMDP (fun x => Icc 0 (max x.1 0)) M.reward M.β_nonneg M.P
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- The objective `u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')`. -/
theorem obj_apply (v : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    M.ldp.obj v p =
      M.u p.2 + M.β * ∑ z', (∫ s, v.toFun (M.next (p, z') s) ∂M.φ) * M.Q p.1.2 z' := by
  rw [show M.ldp.obj v p = M.u p.2 + M.β * ∫ x, v.toFun x ∂(M.P p) from rfl, M.integral_P]

/-- For continuous `v`, the expected continuation `(w, c) ↦ ∫ v dP(w, z, c)` is continuous on `G`
(dominated convergence, slice by slice). -/
theorem weakFeller [TopologicalSpace Z] [DiscreteTopology Z] (v : BM (ℝ × Z))
    (hv : Continuous v.toFun) :
    ContinuousOn (fun p => ∫ x, v.toFun x ∂(M.P p)) {p | p.2 ∈ Icc 0 (max p.1.1 0)} := by
  simp_rw [M.integral_P]
  refine continuousOn_of_slices fun z => ?_
  have hcont : ∀ z' : Z, Continuous fun q : ℝ × ℝ =>
      ∫ s, v.toFun (M.Rz z' * (q.1 - q.2) + M.yf z' s, z') ∂M.φ := fun z' =>
    continuous_of_dominated (bound := fun _ => ‖v‖)
      (fun _ => (v.measurable'.comp ((measurable_const.add (M.yf_meas z')).prodMk
        measurable_const)).aestronglyMeasurable)
      (fun _ => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
      (integrable_const _) (Eventually.of_forall fun s => hv.comp
        (((continuous_const.mul (continuous_fst.sub continuous_snd)).add
          continuous_const).prodMk continuous_const))
  change ContinuousOn (fun q : ℝ × ℝ =>
    ∑ z', (∫ s, v.toFun (M.Rz z' * (q.1 - q.2) + M.yf z' s, z') ∂M.φ) * M.Q z z') _
  exact (continuous_finsetSum _ fun z' _ => (hcont z').mul continuous_const).continuousOn

/-- §6.2.2 (p. 205): Proposition 6.1.7 applies to the savings model with stochastic returns: the
fundamental optimality properties hold, `v* ∈ bcX`, VFI converges geometrically on `bcX`, and for
`v ∈ bcX` the Bellman operator is
`(Tv)(w, z) = max_{0 ≤ c ≤ w} {u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')}`. -/
theorem section_6_2_2 [TopologicalSpace Z] [DiscreteTopology Z] :
    ∃ hw : M.ldp.adp.WellPosed, M.ldp.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × Z), M.ldp.adp.VFIGeometric (LDP.bc (ℝ × Z)) vstar ∧
        ∀ v ∈ LDP.bc (ℝ × Z), ∀ x, IsGreatest ((fun c => M.ldp.obj v (x, c)) '' Icc 0 (max x.1 0))
          ((M.ldp.adp.bellman v).toFun x) := by
  have := M.P_isMarkov
  have hB : HasMaxSelections fun x : ℝ × Z => Icc (0 : ℝ) (max x.1 0) :=
    hasMaxSelections_Icc (X := ℝ × Z) (g := fun _ => 0) (h := fun x => max x.1 0)
      continuous_const (continuous_fst.max continuous_const) fun x => le_max_right _ _
  have hr : ContinuousOn M.ldp.r.toFun M.ldp.G := (M.u_cont.comp continuous_snd).continuousOn
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := proposition_6_1_7 (fun x : ℝ × Z => Icc 0 (max x.1 0))
    M.reward M.β_nonneg M.β_lt_one M.P
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ hB hr M.weakFeller
  refine ⟨hw, hFO, vstar, hv, hgeo, fun v hv' x => ?_⟩
  exact (M.ldp.implications_bc hB hr (fun h hc => continuousOn_const.mul (M.weakFeller h hc))
    hv').2 x

/-! ### Exercise 6.2.1: mortality -/

/-- Next period's state with age: `(R(z')(w − c) + y(z', s'), z', t + 1)`. -/
def nextT (q : ((ℝ × (Z × ℕ)) × ℝ) × Z) (s : S) : ℝ × (Z × ℕ) :=
  (M.Rz q.2 * (q.1.1.1 - q.1.2) + M.yf q.2 s, (q.2, q.1.1.2.2 + 1))

theorem measurable_nextT : Measurable (uncurry M.nextT) := by
  have hy : Measurable fun p : (((ℝ × (Z × ℕ)) × ℝ) × Z) × S => M.yf p.1.2 p.2 := by
    have := M.measurable_income (T := (ℝ × (Z × ℕ)) × ℝ)
    simpa using this
  refine Measurable.prodMk (Measurable.add (Measurable.mul
    ((measurable_of_countable M.Rz).comp (measurable_snd.comp measurable_fst))
    (((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
      (measurable_snd.comp (measurable_fst.comp measurable_fst))))) hy)
    ((measurable_snd.comp measurable_fst).prodMk ((measurable_of_countable (· + 1)).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst))))))

theorem finiteKernel_comapT_isMarkov :
    IsMarkovKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap
      (fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1) measurable_zprojT) := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  infer_instance

/-- The transition kernel with age. -/
noncomputable def PT : Kernel ((ℝ × (Z × ℕ)) × ℝ) (ℝ × (Z × ℕ)) :=
  have := M.finiteKernel_comapT_isMarkov
  mixKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1)
    measurable_zprojT) M.nextT M.measurable_nextT M.φ

theorem PT_isMarkov : IsMarkovKernel M.PT := by
  have := M.finiteKernel_comapT_isMarkov
  exact mixKernel_isMarkov _ _ _ _

theorem integral_PT (v : BM (ℝ × (Z × ℕ))) (p : (ℝ × (Z × ℕ)) × ℝ) :
    ∫ x, v.toFun x ∂(M.PT p) = ∑ z', (∫ s, v.toFun (M.nextT (p, z') s) ∂M.φ) * M.Q p.1.2.1 z' := by
  have := M.finiteKernel_comapT_isMarkov
  change ∫ x, v.toFun x ∂(mixKernel _ M.nextT M.measurable_nextT M.φ p) = _
  rw [integral_mixKernel]
  exact integral_finiteKernel M.Q M.Q_nonneg M.Q_sum _ p.1.2.1

/-- The model with survival probabilities `q(t) ∈ [0, 1]` (Exercise 6.2.1): an LDP on
`X = ℝ × Z × ℤ₊` with `K(x, c, dx') = βq(t)P(x, c, dx')`. -/
noncomputable def ldpT (q : ℕ → ℝ) (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1) :
    LDP (ℝ × (Z × ℕ)) ℝ :=
  have := M.PT_isMarkov
  { Γ := fun x => Icc 0 (max x.1 0)
    r := M.reward
    β := ⟨fun p => M.β * q p.1.2.2, measurable_const.mul ((measurable_of_countable q).comp
        (measurable_snd.comp (measurable_snd.comp measurable_fst))),
      ⟨M.β, fun p => by
        rw [abs_of_nonneg (mul_nonneg M.β_nonneg (hq0 _))]
        exact mul_le_of_le_one_right M.β_nonneg (hq1 _)⟩⟩
    β_nonneg := fun p => mul_nonneg M.β_nonneg (hq0 _)
    P := M.PT
    exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ }

/-- **Exercise 6.2.1** (p. 205): with survival probabilities `q(t) ∈ [0, 1]`, Proposition 6.1.3
applies (with `Dh = β (sup h) 𝟙`, since `q ≤ 1`): the fundamental optimality properties hold,
`v* ∈ bcX` and VFI converges geometrically on `bcX`. -/
theorem exercise_6_2_1 [TopologicalSpace Z] [DiscreteTopology Z] (q : ℕ → ℝ)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1) :
    ∃ hw : (M.ldpT q hq0 hq1).adp.WellPosed, (M.ldpT q hq0 hq1).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × (Z × ℕ)),
        (M.ldpT q hq0 hq1).adp.VFIGeometric (LDP.bc (ℝ × (Z × ℕ))) vstar := by
  have := M.PT_isMarkov
  have hB : HasMaxSelections fun x : ℝ × (Z × ℕ) => Icc (0 : ℝ) (max x.1 0) :=
    hasMaxSelections_Icc (X := ℝ × (Z × ℕ)) (g := fun _ => 0) (h := fun x => max x.1 0)
      continuous_const (continuous_fst.max continuous_const) fun x => le_max_right _ _
  have hr : ContinuousOn (M.ldpT q hq0 hq1).r.toFun (M.ldpT q hq0 hq1).G :=
    (M.u_cont.comp continuous_snd).continuousOn
  have hK : (M.ldpT q hq0 hq1).IsWeakFeller := by
    intro h hc
    change ContinuousOn (fun p => M.β * q p.1.2.2 * ∫ x, h.toFun x ∂(M.PT p)) _
    simp_rw [M.integral_PT]
    refine continuousOn_of_slices fun zt => ?_
    have hcont : ∀ z' : Z, Continuous fun c : ℝ × ℝ =>
        ∫ s, h.toFun (M.Rz z' * (c.1 - c.2) + M.yf z' s, (z', zt.2 + 1)) ∂M.φ := fun z' =>
      continuous_of_dominated (bound := fun _ => ‖h‖)
        (fun _ => (h.measurable'.comp ((measurable_const.add (M.yf_meas z')).prodMk
          measurable_const)).aestronglyMeasurable)
        (fun _ => Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)
        (integrable_const _) (Eventually.of_forall fun s => hc.comp
          (((continuous_const.mul (continuous_fst.sub continuous_snd)).add
            continuous_const).prodMk continuous_const))
    change ContinuousOn (fun c : ℝ × ℝ => M.β * q zt.2 * ∑ z',
      (∫ s, h.toFun (M.Rz z' * (c.1 - c.2) + M.yf z' s, (z', zt.2 + 1)) ∂M.φ) * M.Q zt.1 z') _
    exact (continuous_const.mul (continuous_finsetSum _ fun z' _ =>
      (hcont z').mul continuous_const)).continuousOn
  have hKD : ∀ σ h, 0 ≤ h → (M.ldpT q hq0 hq1).K σ h ≤ Dsup M.β h := fun σ h hh x => by
    rw [LDP.K_apply]
    change M.β * q (x, σ.1 x).1.2.2 * _ ≤ M.β * ⨆ y, h.toFun y
    have hb : BddAbove (range h.toFun) :=
      ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h y)⟩
    have h1 : 0 ≤ ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) := integral_nonneg hh
    have h2 : ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) ≤ ⨆ y, h.toFun y :=
      (integral_mono (Integrable.of_bound h.measurable'.aestronglyMeasurable ‖h‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h y))
        (integrable_const _) fun y => le_ciSup hb y).trans_eq (by simp)
    calc M.β * q (x, σ.1 x).1.2.2 * ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x))
        ≤ M.β * ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right M.β_nonneg (hq1 _)) h1
      _ ≤ M.β * ⨆ y, h.toFun y := mul_le_mul_of_nonneg_left h2 M.β_nonneg
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := (M.ldpT q hq0 hq1).proposition_6_1_3 hB hr hK
    (Dsup_isDiscountOperator M.β_nonneg M.β_lt_one) hKD
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

end ReturnsModel

end SargentStachurski.LinearDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings as a linear decision process

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Example 6.1.5 (p. 191) and Example 6.1.8
(p. 198).

Wealth `x`, consumption `a ∈ Γ(x) = [0, x]`, utility `u` bounded and continuous, gross return `R`,
and iid income `y ∼ φ`:
`∫ v(x')K(x, a, dx') = β ∫ v(R(x − a) + y)φ(dy)`. Wealth is a real state with
`Γ(x) = [0, max(x, 0)]`.

* **Example 6.1.5**: the savings model is an LDP (an MDP with `P(x, a) = law of R(x − a) + y`).
* **Example 6.1.8**: if `φ` has a continuous density, `P` is strong Feller (Example 6.1.2), so by
  Proposition 6.1.7 the fundamental optimality properties hold, `v* ∈ bcX`, VFI converges
  geometrically on `bcX`, and OPI and HPI converge.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace Savings

theorem measurable_next (R : ℝ) :
    Measurable (uncurry fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y) :=
  (measurable_const.mul ((measurable_fst.comp measurable_fst).sub
    (measurable_snd.comp measurable_fst))).add measurable_snd

/-- The kernel `P(x, a) = law of R(x − a) + y`, `y ∼ φ`. -/
noncomputable abbrev P (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] : Kernel (ℝ × ℝ) ℝ :=
  shockKernel (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y) (measurable_next R) φ

/-- The reward `u(a)`. -/
noncomputable def reward (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) :
    BM (ℝ × ℝ) :=
  ⟨fun p => u p.2, hu.measurable.comp measurable_snd, ⟨hub.choose, fun _ => hub.choose_spec _⟩⟩

/-- The savings model as an LDP (an MDP with `K = βP`). -/
noncomputable def ldp (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] : LDP ℝ ℝ :=
  have := shockKernel_isMarkov (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y)
    (measurable_next R) φ
  ofMDP (fun x => Icc 0 (max x 0)) (reward u hu hub) hβ0 (P R φ)
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- **Example 6.1.5** (p. 191): the savings model is an LDP with
`(T_σ v)(x) = u(σ(x)) + β ∫ v(R(x − σ(x)) + y)φ(dy)`. -/
theorem example_6_1_5 (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ]
    (σ : (ldp u hu hub hβ0 R φ).Policy) (v : BM ℝ) (x : ℝ) :
    ((ldp u hu hub hβ0 R φ).adp.T σ v).toFun x =
      u (σ.1 x) + β * ∫ y, v.toFun (R * (x - σ.1 x) + y) ∂φ := by
  rw [show ((ldp u hu hub hβ0 R φ).adp.T σ v).toFun x =
      u (σ.1 x) + β * ∫ x', v.toFun x' ∂(P R φ (x, σ.1 x)) from rfl, P,
    integral_shockKernel _ _ _ v.measurable']

/-- The income distribution with continuous density `φ`. -/
noncomputable def densityMeasure (φ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun y => ((φ y).toNNReal : ENNReal)

theorem densityMeasure_isProbability {φ : ℝ → ℝ} (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) : IsProbabilityMeasure (densityMeasure φ) := by
  have hint : Integrable φ := Integrable.of_integral_ne_zero (by rw [hφ1]; exact one_ne_zero)
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ0)
  rw [hφ1, ENNReal.ofReal_one] at this
  rw [this]
  rfl

/-- **Example 6.1.8** (p. 198): if income has a continuous density `φ`, the savings model is a
strong Feller MDP, so by Proposition 6.1.7 the fundamental optimality properties hold, `v* ∈ bcX`,
VFI converges geometrically on `bcX`, and OPI and HPI converge. -/
theorem example_6_1_8 (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R : ℝ) {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) :
    have := densityMeasure_isProbability hφ0 hφ1
    (∀ h : BM ℝ, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p))
      {p | p.2 ∈ Icc 0 (max p.1 0)}) ∧
    ∃ hw : (ldp u hu hub hβ0 R (densityMeasure φ)).adp.WellPosed,
      (ldp u hu hub hβ0 R (densityMeasure φ)).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc ℝ,
        (ldp u hu hub hβ0 R (densityMeasure φ)).adp.VFIGeometric (LDP.bc ℝ) vstar ∧
        ∀ g, (ldp u hu hub hβ0 R (densityMeasure φ)).adp.IsSelector g →
          (ldp u hu hub hβ0 R (densityMeasure φ)).adp.OPIConverges g vstar ∧
            (ldp u hu hub hβ0 R (densityMeasure φ)).adp.HPIConverges hw g vstar := by
  intro hprob
  have hmark := shockKernel_isMarkov (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y)
    (measurable_next R) (densityMeasure φ)
  -- strong Feller, by a change of variable (Example 6.1.2)
  have hS : ∀ h : BM ℝ, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p))
      {p | p.2 ∈ Icc 0 (max p.1 0)} := fun h => by
    have heq : ∀ p : ℝ × ℝ, ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p) =
        1 * ∫ y, h.toFun (R * (p.1 - p.2) + y) * φ y := fun p => by
      rw [P, integral_shockKernel _ _ _ h.measurable', densityMeasure,
        integral_withDensity_eq_integral_smul (f := fun y => (φ y).toNNReal)
          hφc.measurable.real_toNNReal, one_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 y), smul_eq_mul]
      ring
    simp_rw [heq]
    exact example_6_1_2 (β := fun _ => 1) continuousOn_const
      (g := fun p : ℝ × ℝ => R * (p.1 - p.2))
      (continuous_const.mul (continuous_fst.sub continuous_snd)).continuousOn hφc hφ0 hφ1
      h.measurable' (fun x => BM.abs_le_norm h x)
  have hB : HasMaxSelections fun x : ℝ => Icc (0 : ℝ) (max x 0) :=
    hasMaxSelections_Icc (g := fun _ => 0) (h := fun x => max x 0) continuous_const
      (continuous_id.max continuous_const) fun x => le_max_right _ _
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := proposition_6_1_7 (fun x : ℝ => Icc 0 (max x 0))
    (reward u hu hub) hβ0 hβ1 (P R (densityMeasure φ))
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ hB
    (hu.comp continuous_snd).continuousOn fun h _ => hS h
  exact ⟨hS, hw, hFO, vstar, hv, hgeo, hconv hS⟩

end Savings

end SargentStachurski.LinearDecisionProcesses

set_option linter.style.longLine false
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.mk
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.rowsum
#print axioms SargentStachurski.LinearDecisionProcesses.IsDistribution
#print axioms SargentStachurski.LinearDecisionProcesses.IsDistribution.mk
#print axioms SargentStachurski.LinearDecisionProcesses.IsDistribution.nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.IsDistribution.sum_eq_one
#print axioms SargentStachurski.LinearDecisionProcesses.mulVec_apply_eq
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.mul
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.pow
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.mulVec_const
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.LinearDecisionProcesses.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.GloballyStable
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.mk
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.mapsTo
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.lt_one
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.iterate_mem
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.LinearDecisionProcesses.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.LinearDecisionProcesses.fixedPt_le_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.le_fixedPt_of_le_apply
#print axioms SargentStachurski.LinearDecisionProcesses.isContractionOn_of_blackwell
#print axioms SargentStachurski.LinearDecisionProcesses.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.LinearDecisionProcesses.IsBdd
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupContraction
#print axioms SargentStachurski.LinearDecisionProcesses.IsUniformlyClosed
#print axioms SargentStachurski.LinearDecisionProcesses.isBdd_const
#print axioms SargentStachurski.LinearDecisionProcesses.IsBdd.sub
#print axioms SargentStachurski.LinearDecisionProcesses.IsBdd.add
#print axioms SargentStachurski.LinearDecisionProcesses.IsBdd.nonneg_bound
#print axioms SargentStachurski.LinearDecisionProcesses.IsBdd.exists_dist
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupContraction.iterate
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupContraction.exists_limit
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupContraction.globallyStable
#print axioms SargentStachurski.LinearDecisionProcesses.le_of_le_map_of_tendsto
#print axioms SargentStachurski.LinearDecisionProcesses.le_of_map_le_of_tendsto
#print axioms SargentStachurski.LinearDecisionProcesses.bX
#print axioms SargentStachurski.LinearDecisionProcesses.isUniformlyClosed_bX
#print axioms SargentStachurski.LinearDecisionProcesses.const_mem_bX
#print axioms SargentStachurski.LinearDecisionProcesses.abs_max_sub_max_le
#print axioms SargentStachurski.LinearDecisionProcesses.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp
#print axioms SargentStachurski.LinearDecisionProcesses.integrable_of_mem_bX
#print axioms SargentStachurski.LinearDecisionProcesses.measurable_markovOp
#print axioms SargentStachurski.LinearDecisionProcesses.abs_markovOp_le
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_mem_bX
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_mono
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_const
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_add
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_sub
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_smul
#print axioms SargentStachurski.LinearDecisionProcesses.markovOp_sub_const
#print axioms SargentStachurski.LinearDecisionProcesses.abs_markovOp_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.OrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.IncreasesTo
#print axioms SargentStachurski.LinearDecisionProcesses.DecreasesTo
#print axioms SargentStachurski.LinearDecisionProcesses.StronglyOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.orderStable_of_up_down
#print axioms SargentStachurski.LinearDecisionProcesses.StronglyOrderStable.orderStable
#print axioms SargentStachurski.LinearDecisionProcesses.dualMap
#print axioms SargentStachurski.LinearDecisionProcesses.orderStable_dual_iff
#print axioms SargentStachurski.LinearDecisionProcesses.dualMap_iterate
#print axioms SargentStachurski.LinearDecisionProcesses.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete.exists_least
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.LinearDecisionProcesses.ChainComplete.orderStable
#print axioms SargentStachurski.LinearDecisionProcesses.chainComplete_Icc
#print axioms SargentStachurski.LinearDecisionProcesses.CountablyDedekindComplete
#print axioms SargentStachurski.LinearDecisionProcesses.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.LinearDecisionProcesses.CountablyDedekindComplete.dual
#print axioms SargentStachurski.LinearDecisionProcesses.OrderContinuous
#print axioms SargentStachurski.LinearDecisionProcesses.OrderContinuous.monotone
#print axioms SargentStachurski.LinearDecisionProcesses.isLUB_range_succ_iff
#print axioms SargentStachurski.LinearDecisionProcesses.tarski_kantorovich
#print axioms SargentStachurski.LinearDecisionProcesses.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.mk
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.T
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.mono
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.nonempty
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGreedy
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VG
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.WellPosed
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsFinite
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.Regular
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsBellmanValue
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.SolvesBellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.regular_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.greedy
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isGreedy_greedy
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.T_le_bellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isGreedy_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.solvesBellman_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman_mono
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VU
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VSig
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.vσ
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.T_vσ
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.eq_vσ
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VSig_eq_range
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOptimal
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsValueFunction
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.BellmanPrinciple
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.FundamentalOptimality
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isOptimal_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.exists_solves_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsSelector
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.howard
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.opt
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsSelector.T_eq
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.mem_VU_iff
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.iterate_mono_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman_le_opt
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.chain_2_9
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.mapsTo_VU
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman_le_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VFIConverges
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.OPIConverges
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.HPIConverges
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.opt_one
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.OPIConverges.vfi
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.iterates_le_vstar
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VU_nonempty
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.OrderBounded
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsOrderContinuous
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.le_of_orderBounded
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.convergence_of_dedekind
#print axioms SargentStachurski.LinearDecisionProcesses.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGloballyStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.theorem_3_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.corollary_3_1_3
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.theorem_3_1_4
#print axioms SargentStachurski.LinearDecisionProcesses.IsSupNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.IsInfNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.isInfNonexpansive_iff
#print axioms SargentStachurski.LinearDecisionProcesses.isSupNonexpansive_real
#print axioms SargentStachurski.LinearDecisionProcesses.isSupNonexpansive_pi
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.lemma_A_5_21
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.IsSemiRegular
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.VFIGeometric
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.theorem_3_1_5
#print axioms SargentStachurski.LinearDecisionProcesses.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.LinearDecisionProcesses.BM
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mk
#print axioms SargentStachurski.LinearDecisionProcesses.BM.toFun
#print axioms SargentStachurski.LinearDecisionProcesses.BM.measurable'
#print axioms SargentStachurski.LinearDecisionProcesses.BM.bdd'
#print axioms SargentStachurski.LinearDecisionProcesses.BM.ext
#print axioms SargentStachurski.LinearDecisionProcesses.BM.bddAbove
#print axioms SargentStachurski.LinearDecisionProcesses.BM.const
#print axioms SargentStachurski.LinearDecisionProcesses.BM.toFun_injective
#print axioms SargentStachurski.LinearDecisionProcesses.BM.zero
#print axioms SargentStachurski.LinearDecisionProcesses.BM.add
#print axioms SargentStachurski.LinearDecisionProcesses.BM.neg
#print axioms SargentStachurski.LinearDecisionProcesses.BM.sub
#print axioms SargentStachurski.LinearDecisionProcesses.BM.smulReal
#print axioms SargentStachurski.LinearDecisionProcesses.BM.nsmul
#print axioms SargentStachurski.LinearDecisionProcesses.BM.zsmul
#print axioms SargentStachurski.LinearDecisionProcesses.BM.addCommGroup
#print axioms SargentStachurski.LinearDecisionProcesses.BM.supNorm
#print axioms SargentStachurski.LinearDecisionProcesses.BM.abs_le_supNorm
#print axioms SargentStachurski.LinearDecisionProcesses.BM.supNorm_le
#print axioms SargentStachurski.LinearDecisionProcesses.BM.supNorm_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.BM.normedAddCommGroup
#print axioms SargentStachurski.LinearDecisionProcesses.BM.add_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.sub_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.neg_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.zero_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.const_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.norm_def
#print axioms SargentStachurski.LinearDecisionProcesses.BM.abs_le_norm
#print axioms SargentStachurski.LinearDecisionProcesses.BM.norm_le
#print axioms SargentStachurski.LinearDecisionProcesses.BM.abs_sub_le_dist
#print axioms SargentStachurski.LinearDecisionProcesses.BM.dist_le
#print axioms SargentStachurski.LinearDecisionProcesses.BM.module
#print axioms SargentStachurski.LinearDecisionProcesses.BM.smul_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.normedSpace
#print axioms SargentStachurski.LinearDecisionProcesses.BM.lattice
#print axioms SargentStachurski.LinearDecisionProcesses.BM.le_def
#print axioms SargentStachurski.LinearDecisionProcesses.BM.sup_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.inf_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.abs_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.isOrderedAddMonoid
#print axioms SargentStachurski.LinearDecisionProcesses.BM.hasSolidNorm
#print axioms SargentStachurski.LinearDecisionProcesses.BM.completeSpace
#print axioms SargentStachurski.LinearDecisionProcesses.BM.countablyDedekindComplete
#print axioms SargentStachurski.LinearDecisionProcesses.BM.isSupNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.BM.isInfNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mem_bX
#print axioms SargentStachurski.LinearDecisionProcesses.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.LinearDecisionProcesses.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.LinearDecisionProcesses.BM.globallyStable_of_bX
#print axioms SargentStachurski.LinearDecisionProcesses.pow_div_le_geometric
#print axioms SargentStachurski.LinearDecisionProcesses.theorem_4_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsNormalizedOrderUnit
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.smul_mono
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.le_add
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.norm_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.isSupNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.isInfNonexpansive
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.isSupNonexpansive_subtype
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.lemma_4_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.lemma_4_1_2_subtype
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_3
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_3_univ
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsCertaintyEquivalent
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.exercise_4_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.exercise_4_1_2_subtype
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsDiscountOperator
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsDiscountOperator.exercise_4_1_3
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsDiscountOperator.iterate_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsDiscountOperator.iterate_mono
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.specRad
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.exercise_A_4_2
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.specRad_le_norm
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsPositiveOp
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsPositiveOp.mono
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsPositiveOp.abs_le
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsPositiveOp.iterate
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.example_4_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsIsoOrderEmbedding
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsOrderContraction
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsOrderContraction.iterate
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_4
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.example_4_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.exercise_4_1_4
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_5
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.bellman_orderContraction
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_6
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsAdditive
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.IsAdditive.abs_sub
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_7
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.theorem_4_1_8
#print axioms SargentStachurski.LinearDecisionProcesses.BM.posSMulMono
#print axioms SargentStachurski.LinearDecisionProcesses.BM.one_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.isNormalizedOrderUnit_one
#print axioms SargentStachurski.LinearDecisionProcesses.BM.markovLin
#print axioms SargentStachurski.LinearDecisionProcesses.BM.markovCLM
#print axioms SargentStachurski.LinearDecisionProcesses.BM.markovCLM_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.markovCLM_isPositive
#print axioms SargentStachurski.LinearDecisionProcesses.BM.markovCLM_const
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mulLin
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mulCLM
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mulCLM_apply
#print axioms SargentStachurski.LinearDecisionProcesses.BM.mulCLM_isPositive
#print axioms SargentStachurski.LinearDecisionProcesses.sup'_add_const
#print axioms SargentStachurski.LinearDecisionProcesses.harrisonKreps
#print axioms SargentStachurski.LinearDecisionProcesses.exercise_4_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.IsLHC
#print axioms SargentStachurski.LinearDecisionProcesses.IsUHC
#print axioms SargentStachurski.LinearDecisionProcesses.IsContinuousCorr
#print axioms SargentStachurski.LinearDecisionProcesses.clamp_mem
#print axioms SargentStachurski.LinearDecisionProcesses.clamp_eq
#print axioms SargentStachurski.LinearDecisionProcesses.exists_subseq_Icc
#print axioms SargentStachurski.LinearDecisionProcesses.exercise_A_3_1
#print axioms SargentStachurski.LinearDecisionProcesses.HasMaxSelections
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.argmax
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.sel
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.continuousOn_section
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.argmax_nonempty
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.isClosed_argmax
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.sel_mem
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.isClosed_le_sel
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.exists_param
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.continuous_max
#print axioms SargentStachurski.LinearDecisionProcesses.IccMax.measurable_sel
#print axioms SargentStachurski.LinearDecisionProcesses.hasMaxSelections_Icc
#print axioms SargentStachurski.LinearDecisionProcesses.LDP
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.mk
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Γ
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.r
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.β
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.β_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.P
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.exists_policy
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Policy
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.nonempty_policy
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.measurable_graph
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.along
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.rσ
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.βσ
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Pσ
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.K
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.K_apply
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.K_isPositive
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.norm_K_le
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.adp
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.T_apply
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.isAdditive
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.obj
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.T_apply_obj
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.isGreedy_iff
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.isGreedy_of_argmax
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.argmax_of_isGreedy
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.iterate_T_zero
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.globallyStable_T
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.lifetime_value
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.firm
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.firm_T_apply
#print axioms SargentStachurski.LinearDecisionProcesses.example_6_1_6
#print axioms SargentStachurski.LinearDecisionProcesses.argmaxSet
#print axioms SargentStachurski.LinearDecisionProcesses.argmaxSet_nonempty
#print axioms SargentStachurski.LinearDecisionProcesses.argmaxSel
#print axioms SargentStachurski.LinearDecisionProcesses.argmaxSel_max
#print axioms SargentStachurski.LinearDecisionProcesses.measurable_argmaxSel
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.regular_of_isFinite
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.proposition_6_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.G
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.IsWeakFeller
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.IsStrongFeller
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.IsStrongFeller.isWeakFeller
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.bc
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.isClosed_bc
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.zero_mem_bc
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.continuousOn_obj
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.greedy_of_continuousOn
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.proposition_6_1_3
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.implications
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.implications_bc
#print axioms SargentStachurski.LinearDecisionProcesses.measurable_section
#print axioms SargentStachurski.LinearDecisionProcesses.shockKernel
#print axioms SargentStachurski.LinearDecisionProcesses.shockKernel_apply
#print axioms SargentStachurski.LinearDecisionProcesses.shockKernel_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.integral_shockKernel
#print axioms SargentStachurski.LinearDecisionProcesses.example_6_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.scheffe
#print axioms SargentStachurski.LinearDecisionProcesses.lemma_6_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.example_6_1_2
#print axioms SargentStachurski.LinearDecisionProcesses.hasSolidNorm_pi
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.lemma_6_1_5
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.iterate_affine_zero
#print axioms SargentStachurski.LinearDecisionProcesses.BanachLattice.exercise_6_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.KLin
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.K
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.K_apply
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.K_isPositive
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.pathExp
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.pathExp_succ
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.lemma_6_1_4
#print axioms SargentStachurski.LinearDecisionProcesses.Exo.exercise_6_1_1
#print axioms SargentStachurski.LinearDecisionProcesses.continuousOn_of_slices
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.supY
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.bddAbove_slice
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.le_supY
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.abs_supY_le
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.abs_supY_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Dexo
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.supY_lift
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Dexo_iterate
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.Dexo_isDiscountOperator
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.K_le_Dexo
#print axioms SargentStachurski.LinearDecisionProcesses.LDP.proposition_6_1_6
#print axioms SargentStachurski.LinearDecisionProcesses.ofMDP
#print axioms SargentStachurski.LinearDecisionProcesses.ofMDP_T_apply
#print axioms SargentStachurski.LinearDecisionProcesses.example_6_1_3
#print axioms SargentStachurski.LinearDecisionProcesses.Dsup
#print axioms SargentStachurski.LinearDecisionProcesses.abs_iSup_sub_le
#print axioms SargentStachurski.LinearDecisionProcesses.Dsup_isDiscountOperator
#print axioms SargentStachurski.LinearDecisionProcesses.K_le_Dsup
#print axioms SargentStachurski.LinearDecisionProcesses.proposition_6_1_7
#print axioms SargentStachurski.LinearDecisionProcesses.rowPMF
#print axioms SargentStachurski.LinearDecisionProcesses.finiteKernel
#print axioms SargentStachurski.LinearDecisionProcesses.finiteKernel_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.integral_finiteKernel
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.mk
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.π
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.π_cont
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.π_bdd
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.f
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.f_cont
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.φ
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.βz
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.βz_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.Q
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.Q_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.Q_sum
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.measurable_next
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.R
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.Qk
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.R_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.Qk_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.ldp
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.integral_P
#print axioms SargentStachurski.LinearDecisionProcesses.ResourceModel.proposition_6_2_1
#print axioms SargentStachurski.LinearDecisionProcesses.mixKernel
#print axioms SargentStachurski.LinearDecisionProcesses.mixKernel_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.integral_mixKernel
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.mk
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.u
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.u_cont
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.u_bdd
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.β
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.β_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.β_lt_one
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.Q
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.Q_nonneg
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.Q_sum
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.Rz
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.yf
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.yf_meas
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.φ
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.measurable_zproj
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.measurable_zprojT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.reward
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.measurable_income
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.next
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.measurable_next
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.finiteKernel_comap_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.P
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.P_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.integral_P
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.ldp
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.obj_apply
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.weakFeller
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.section_6_2_2
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.nextT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.measurable_nextT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.finiteKernel_comapT_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.PT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.PT_isMarkov
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.integral_PT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.ldpT
#print axioms SargentStachurski.LinearDecisionProcesses.ReturnsModel.exercise_6_2_1
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.measurable_next
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.P
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.reward
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.ldp
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.example_6_1_5
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.densityMeasure
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.densityMeasure_isProbability
#print axioms SargentStachurski.LinearDecisionProcesses.Savings.example_6_1_8
