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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.MeasureTheory.Integral.Prod
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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Certainty equivalents

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.4 (pp. 225–230).

`L∞` is represented by functions `Z : Ω → ℝ` that are a.e. strongly measurable and essentially
bounded (`IsLInf`); a functional on `L∞` is a map on functions whose axioms are imposed on `L∞`.
Monotonicity in the a.e. order makes it constant on a.e. classes.

* Risk measures (R1)–(R2) and certainty equivalents (C1)–(C2); **Exercise 7.2.5**: `ℰ` is a
  certainty equivalent iff `−ℰ` is a risk measure, and convex combinations of certainty
  equivalents are certainty equivalents.
* Convex and coherent risk measures; concave and coherent certainty equivalents; a coherent
  certainty equivalent is superadditive.
* Examples: the mean `𝔼` (coherent); the pessimistic certainty equivalent
  `ℰ_p(Z) = sup{a : ℙ{Z < a} = 0} = ess inf Z` (coherent); the entropic certainty equivalent
  `ℰ^θ(Z) = θ⁻¹ ln 𝔼 exp(θZ)`, `θ ≠ 0` ((7.21) is `θ = −γ`); the Kreps–Porteus expectation
  `𝒦(Z) = (𝔼 Z^{1−γ})^{1/(1−γ)}` fails cash invariance (a two-point example with `γ = 2`).
* Continuity (§7.2.4.3): **Example 7.2.1** (`𝔼`) and **Exercise 7.2.6** (`ℰ^θ`).

The dual representation (Theorem 7.2.9, Föllmer–Schied) and its instances (7.22), and the quantile
and CVaR certainty equivalents with Example 7.2.2, are not formalised; see the corrections file.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- `Z ∈ L∞(Ω, ℱ, ℙ)`: `Z` is a.e. strongly measurable and `|Z| ≤ N` almost surely. -/
def IsLInf (Z : Ω → ℝ) : Prop := AEStronglyMeasurable Z P ∧ ∃ N, ∀ᵐ ω ∂P, |Z ω| ≤ N

/-- A **risk measure** (§7.2.4): (R1) monotonicity, `Z ≤ Z'` a.s. implies `ℛ(Z') ≤ ℛ(Z)`, and (R2)
cash invariance, `ℛ(Z + a) = ℛ(Z) − a`. -/
structure IsRiskMeasure (R : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ Z Z', IsLInf P Z → IsLInf P Z' → Z ≤ᵐ[P] Z' → R Z' ≤ R Z
  cash : ∀ Z, IsLInf P Z → ∀ a : ℝ, R (fun ω => Z ω + a) = R Z - a

/-- A **certainty equivalent** (§7.2.4): (C1) monotonicity, `Z ≤ Z'` a.s. implies
`ℰ(Z) ≤ ℰ(Z')`, and (C2) cash invariance, `ℰ(Z + a) = ℰ(Z) + a`. -/
structure IsCertEquiv (E : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ Z Z', IsLInf P Z → IsLInf P Z' → Z ≤ᵐ[P] Z' → E Z ≤ E Z'
  cash : ∀ Z, IsLInf P Z → ∀ a : ℝ, E (fun ω => Z ω + a) = E Z + a

variable {P}

theorem IsLInf.add_const {Z : Ω → ℝ} (hZ : IsLInf P Z) (a : ℝ) : IsLInf P fun ω => Z ω + a := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine ⟨hm.add aestronglyMeasurable_const, N + |a|, ?_⟩
  filter_upwards [hN] with ω hω
  exact (abs_add_le _ _).trans (add_le_add hω le_rfl)

theorem IsLInf.const_mul {Z : Ω → ℝ} (hZ : IsLInf P Z) (c : ℝ) : IsLInf P fun ω => c * Z ω := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine ⟨hm.const_mul c, |c| * N, ?_⟩
  filter_upwards [hN] with ω hω
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg c)

theorem IsLInf.add {Z Z' : Ω → ℝ} (hZ : IsLInf P Z) (hZ' : IsLInf P Z') :
    IsLInf P fun ω => Z ω + Z' ω := by
  obtain ⟨hm, N, hN⟩ := hZ
  obtain ⟨hm', N', hN'⟩ := hZ'
  refine ⟨hm.add hm', N + N', ?_⟩
  filter_upwards [hN, hN'] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem isLInf_const (a : ℝ) : IsLInf P fun _ => a :=
  ⟨aestronglyMeasurable_const, |a|, Eventually.of_forall fun _ => le_rfl⟩

theorem IsLInf.integrable [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : IsLInf P Z) : Integrable Z P :=
  Integrable.of_bound hZ.1 hZ.2.choose (by simpa [Real.norm_eq_abs] using hZ.2.choose_spec)

/-- **Exercise 7.2.5 (i)** (p. 226): `ℰ` is a certainty equivalent iff `ℛ = −ℰ` is a risk
measure. -/
theorem exercise_7_2_5_i (E : (Ω → ℝ) → ℝ) :
    IsCertEquiv P E ↔ IsRiskMeasure P fun Z => -E Z := by
  constructor
  · rintro ⟨hm, hc⟩
    exact ⟨fun Z Z' hZ hZ' h => neg_le_neg (hm Z Z' hZ hZ' h), fun Z hZ a => by
      rw [hc Z hZ a]
      ring⟩
  · rintro ⟨hm, hc⟩
    exact ⟨fun Z Z' hZ hZ' h => neg_le_neg_iff.1 (hm Z Z' hZ hZ' h), fun Z hZ a => by
      have := hc Z hZ a
      linarith⟩

/-- **Exercise 7.2.5 (ii)** (p. 226): a convex combination of certainty equivalents is a certainty
equivalent. -/
theorem exercise_7_2_5_ii {E₀ E₁ : (Ω → ℝ) → ℝ} (h₀ : IsCertEquiv P E₀) (h₁ : IsCertEquiv P E₁)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    IsCertEquiv P fun Z => lam * E₀ Z + (1 - lam) * E₁ Z := by
  refine ⟨fun Z Z' hZ hZ' h => ?_, fun Z hZ a => ?_⟩
  · exact add_le_add (mul_le_mul_of_nonneg_left (h₀.mono Z Z' hZ hZ' h) hl0)
      (mul_le_mul_of_nonneg_left (h₁.mono Z Z' hZ hZ' h) (sub_nonneg.2 hl1))
  · rw [h₀.cash Z hZ a, h₁.cash Z hZ a]
    ring

variable (P)

/-- A convex risk measure (p. 226). -/
def IsConvexRisk (R : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z Z', IsLInf P Z → IsLInf P Z' → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    R (fun ω => lam * Z ω + (1 - lam) * Z' ω) ≤ lam * R Z + (1 - lam) * R Z'

/-- A concave certainty equivalent (p. 226). -/
def IsConcaveCE (E : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z Z', IsLInf P Z → IsLInf P Z' → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    lam * E Z + (1 - lam) * E Z' ≤ E (fun ω => lam * Z ω + (1 - lam) * Z' ω)

/-- Positive homogeneity: `F(λZ) = λF(Z)` for `λ > 0` (p. 227). -/
def IsPosHomogeneous (F : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z, IsLInf P Z → ∀ lam : ℝ, 0 < lam → F (fun ω => lam * Z ω) = lam * F Z

/-- A coherent risk measure: convex and positively homogeneous (p. 227). -/
def IsCoherentRisk (R : (Ω → ℝ) → ℝ) : Prop :=
  IsRiskMeasure P R ∧ IsConvexRisk P R ∧ IsPosHomogeneous P R

/-- A coherent certainty equivalent: concave and positively homogeneous (p. 227). -/
def IsCoherentCE (E : (Ω → ℝ) → ℝ) : Prop :=
  IsCertEquiv P E ∧ IsConcaveCE P E ∧ IsPosHomogeneous P E

variable {P}

/-- `ℛ` is a convex (coherent) risk measure iff `ℰ = −ℛ` is a concave (coherent) certainty
equivalent (p. 226). -/
theorem isCoherentRisk_neg_iff (E : (Ω → ℝ) → ℝ) :
    IsCoherentRisk P (fun Z => -E Z) ↔ IsCoherentCE P E := by
  refine and_congr (exercise_7_2_5_i E).symm (and_congr ?_ ?_)
  · refine forall_congr' fun Z => forall_congr' fun Z' => forall_congr' fun hZ =>
      forall_congr' fun hZ' => forall_congr' fun lam => forall_congr' fun _ =>
        forall_congr' fun _ => ?_
    constructor <;> intro h <;> linarith
  · refine forall_congr' fun Z => forall_congr' fun hZ => forall_congr' fun lam =>
      forall_congr' fun _ => ?_
    constructor <;> intro h <;> linarith

/-- A coherent certainty equivalent is superadditive: `ℰ(Z) + ℰ(Z') ≤ ℰ(Z + Z')` (p. 227). -/
theorem IsCoherentCE.superadditive {E : (Ω → ℝ) → ℝ} (h : IsCoherentCE P E) {Z Z' : Ω → ℝ}
    (hZ : IsLInf P Z) (hZ' : IsLInf P Z') : E Z + E Z' ≤ E fun ω => Z ω + Z' ω := by
  have hc := h.2.1 Z Z' hZ hZ' (1 / 2) (by norm_num) (by norm_num)
  have hh := h.2.2 _ ((hZ.const_mul (1 / 2)).add (hZ'.const_mul (1 - 1 / 2))) 2 two_pos
  have heq : (fun ω => 2 * ((1 / 2) * Z ω + (1 - 1 / 2) * Z' ω)) = fun ω => Z ω + Z' ω :=
    funext fun ω => by ring
  rw [heq] at hh
  rw [hh]
  linarith

/-! ### The mean -/

variable (P) in
/-- The risk-neutral certainty equivalent `ℰ(Z) = 𝔼 Z` (p. 228). -/
noncomputable def meanCE (Z : Ω → ℝ) : ℝ := ∫ ω, Z ω ∂P

variable [IsProbabilityMeasure P]

/-- `𝔼` is a coherent certainty equivalent (p. 228). -/
theorem meanCE_isCoherent : IsCoherentCE P (meanCE P) := by
  refine ⟨⟨fun Z Z' hZ hZ' h => integral_mono_ae hZ.integrable hZ'.integrable h,
    fun Z hZ a => ?_⟩, fun Z Z' hZ hZ' lam _ _ => le_of_eq ?_, fun Z hZ lam _ => ?_⟩
  · rw [meanCE, meanCE, integral_add hZ.integrable (integrable_const a), integral_const,
      probReal_univ, one_smul]
  · rw [meanCE, meanCE, meanCE, integral_add ((hZ.const_mul lam).integrable)
      ((hZ'.const_mul (1 - lam)).integrable), integral_const_mul, integral_const_mul]
  · rw [meanCE, meanCE, integral_const_mul]

variable (P) in
/-- `IsContinuousCE`: `ℰ(Zₙ) → ℰ(Z)` whenever `Zₙ → Z` almost surely with `|Zₙ| ≤ M`
(§7.2.4.3). -/
def IsContinuousCE (E : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (Zs : ℕ → Ω → ℝ) (Z : Ω → ℝ) (M : ℝ), (∀ n, AEStronglyMeasurable (Zs n) P) →
    (∀ n, ∀ᵐ ω ∂P, |Zs n ω| ≤ M) → IsLInf P Z →
    (∀ᵐ ω ∂P, Tendsto (fun n => Zs n ω) atTop (𝓝 (Z ω))) →
    Tendsto (fun n => E (Zs n)) atTop (𝓝 (E Z))

/-- **Example 7.2.1** (p. 229): `𝔼` is continuous (dominated convergence). -/
theorem example_7_2_1 : IsContinuousCE P (meanCE P) := fun Zs Z M hm hb _ hlim =>
  tendsto_integral_of_dominated_convergence (fun _ => M) hm (integrable_const M)
    (fun n => by simpa [Real.norm_eq_abs] using hb n) hlim

/-! ### The pessimistic certainty equivalent -/

variable (P) in
/-- The pessimistic certainty equivalent `ℰ_p(Z) = sup{a : ℙ{Z < a} = 0}` (p. 228). -/
noncomputable def pessCE (Z : Ω → ℝ) : ℝ := sSup {a : ℝ | P {ω | Z ω < a} = 0}

omit [IsProbabilityMeasure P] in
theorem mem_pess_iff {Z : Ω → ℝ} {a : ℝ} : P {ω | Z ω < a} = 0 ↔ ∀ᵐ ω ∂P, a ≤ Z ω := by
  rw [ae_iff]
  simp only [not_le]

omit [IsProbabilityMeasure P] in
theorem pess_nonempty {Z : Ω → ℝ} (hZ : IsLInf P Z) : {a : ℝ | P {ω | Z ω < a} = 0}.Nonempty := by
  obtain ⟨-, N, hN⟩ := hZ
  exact ⟨-N, mem_pess_iff.2 (hN.mono fun ω hω => neg_le_of_abs_le hω)⟩

theorem pess_bddAbove {Z : Ω → ℝ} (hZ : IsLInf P Z) : BddAbove {a : ℝ | P {ω | Z ω < a} = 0} := by
  obtain ⟨-, N, hN⟩ := hZ
  refine ⟨N, fun a ha => ?_⟩
  obtain ⟨ω, h1, h2⟩ := ((mem_pess_iff.1 ha).and hN).exists
  exact h1.trans (le_of_abs_le h2)

omit [IsProbabilityMeasure P] in
/-- `Z ≥ ℰ_p(Z)` almost surely. -/
theorem ae_pess_le {Z : Ω → ℝ} (hZ : IsLInf P Z) : ∀ᵐ ω ∂P, pessCE P Z ≤ Z ω := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, pessCE P Z - 1 / (n + 1) ≤ Z ω := fun n => by
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup (pess_nonempty hZ)
      (sub_lt_self (pessCE P Z) (Nat.one_div_pos_of_nat (n := n)))
    exact (mem_pess_iff.1 ha).mono fun ω hω => hlt.le.trans hω
  filter_upwards [ae_all_iff.2 hn] with ω hω
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hω n]

theorem le_pess {Z : Ω → ℝ} (hZ : IsLInf P Z) {a : ℝ} (ha : ∀ᵐ ω ∂P, a ≤ Z ω) : a ≤ pessCE P Z :=
  le_csSup (pess_bddAbove hZ) (mem_pess_iff.2 ha)

/-- The pessimistic certainty equivalent is a coherent certainty equivalent (p. 228). -/
theorem pessCE_isCoherent : IsCoherentCE P (pessCE P) := by
  refine ⟨⟨fun Z Z' hZ hZ' h => le_pess hZ' ((ae_pess_le hZ).mp (h.mono fun ω h1 h2 =>
    h2.trans h1)), fun Z hZ a => le_antisymm ?_ ?_⟩, fun Z Z' hZ hZ' lam hl0 hl1 => ?_,
    fun Z hZ lam hl => le_antisymm ?_ ?_⟩
  · -- `ℰ_p(Z + a) ≤ ℰ_p(Z) + a`
    have h := ae_pess_le (hZ.add_const a)
    have : pessCE P (fun ω => Z ω + a) - a ≤ pessCE P Z :=
      le_pess hZ (h.mono fun ω hω => by linarith)
    linarith
  · exact le_pess (hZ.add_const a) ((ae_pess_le hZ).mono fun ω hω => by linarith)
  · refine le_pess ((hZ.const_mul lam).add (hZ'.const_mul (1 - lam))) ?_
    filter_upwards [ae_pess_le hZ, ae_pess_le hZ'] with ω h1 h2
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hl0)
      (mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hl1))
  · have h := ae_pess_le (hZ.const_mul lam)
    have : pessCE P (fun ω => lam * Z ω) / lam ≤ pessCE P Z :=
      le_pess hZ (h.mono fun ω hω => by rw [div_le_iff₀ hl]; linarith)
    rwa [div_le_iff₀ hl, mul_comm] at this
  · exact le_pess (hZ.const_mul lam) ((ae_pess_le hZ).mono fun ω hω =>
      mul_le_mul_of_nonneg_left hω hl.le)

/-! ### The entropic certainty equivalent -/

variable (P) in
/-- The entropic certainty equivalent `ℰ^θ(Z) = θ⁻¹ ln 𝔼 exp(θZ)`; (7.21) is `θ = −γ`. -/
noncomputable def entropicCE (θ : ℝ) (Z : Ω → ℝ) : ℝ := θ⁻¹ * Real.log (∫ ω, Real.exp (θ * Z ω) ∂P)

theorem integrable_exp {Z : Ω → ℝ} (hZ : IsLInf P Z) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * Z ω)) P := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (hm.const_mul θ))
    (Real.exp (|θ| * N)) ?_
  filter_upwards [hN] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg θ)

theorem integral_exp_pos' {Z : Ω → ℝ} (hZ : IsLInf P Z) (θ : ℝ) :
    0 < ∫ ω, Real.exp (θ * Z ω) ∂P :=
  integral_exp_pos (integrable_exp hZ θ)

/-- The entropic certainty equivalent is a certainty equivalent for every `θ ≠ 0`. -/
theorem entropicCE_isCertEquiv {θ : ℝ} (hθ : θ ≠ 0) : IsCertEquiv P (entropicCE P θ) := by
  refine ⟨fun Z Z' hZ hZ' h => ?_, fun Z hZ a => ?_⟩
  · rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have hle : ∫ ω, Real.exp (θ * Z' ω) ∂P ≤ ∫ ω, Real.exp (θ * Z ω) ∂P :=
        integral_mono_ae (integrable_exp hZ' θ) (integrable_exp hZ θ)
          (h.mono fun ω hω => Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hω hneg.le))
      exact mul_le_mul_of_nonpos_left (Real.log_le_log (integral_exp_pos' hZ' θ) hle)
        (inv_nonpos.2 hneg.le)
    · have hle : ∫ ω, Real.exp (θ * Z ω) ∂P ≤ ∫ ω, Real.exp (θ * Z' ω) ∂P :=
        integral_mono_ae (integrable_exp hZ θ) (integrable_exp hZ' θ)
          (h.mono fun ω hω => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hpos.le))
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (integral_exp_pos' hZ θ) hle)
        (inv_nonneg.2 hpos.le)
  · have heq : ∫ ω, Real.exp (θ * (Z ω + a)) ∂P =
        Real.exp (θ * a) * ∫ ω, Real.exp (θ * Z ω) ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      change Real.exp (θ * (Z ω + a)) = Real.exp (θ * a) * Real.exp (θ * Z ω)
      rw [← Real.exp_add]
      ring_nf
    rw [entropicCE, heq, Real.log_mul (Real.exp_pos _).ne' (integral_exp_pos' hZ θ).ne',
      Real.log_exp, entropicCE]
    field_simp
    ring

/-- **Exercise 7.2.6** (p. 230): the entropic certainty equivalent is continuous. -/
theorem exercise_7_2_6 (θ : ℝ) : IsContinuousCE P (entropicCE P θ) := by
  intro Zs Z M hm hb hZ hlim
  have hint : Tendsto (fun n => ∫ ω, Real.exp (θ * Zs n ω) ∂P) atTop
      (𝓝 (∫ ω, Real.exp (θ * Z ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (|θ| * M))
      (fun n => Real.continuous_exp.comp_aestronglyMeasurable ((hm n).const_mul θ))
      (integrable_const _) (fun n => ?_) ?_
    · filter_upwards [hb n] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg θ)
    · filter_upwards [hlim] with ω hω
      exact (Real.continuous_exp.tendsto _).comp (hω.const_mul θ)
  exact (hint.log (integral_exp_pos' hZ θ).ne').const_mul θ⁻¹

/-! ### Kreps–Porteus expectations -/

variable (P) in
/-- The Kreps–Porteus expectation `𝒦(Z) = (𝔼 Z^{1−γ})^{1/(1−γ)}` (p. 229). -/
noncomputable def kpExp (γ : ℝ) (Z : Ω → ℝ) : ℝ := (∫ ω, Z ω ^ (1 - γ) ∂P) ^ (1 - γ)⁻¹

/-- The Kreps–Porteus expectation fails cash invariance (p. 229): with `γ = 2`, `Ω = {0, 1}`
uniform and `Z = (1, 2)`, `𝒦(Z + 1) = 12/5 ≠ 7/3 = 𝒦(Z) + 1`. -/
theorem kpExp_not_cash_invariant :
    ∃ (Q : Measure Bool) (_ : IsProbabilityMeasure Q) (Z : Bool → ℝ) (a : ℝ),
      IsLInf Q Z ∧ kpExp Q 2 (fun ω => Z ω + a) ≠ kpExp Q 2 Z + a := by
  let Q : Measure Bool := (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) •
    Measure.dirac false
  have hQ : IsProbabilityMeasure Q := ⟨by
    simp only [Q, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.add_halves]⟩
  have hint : ∀ f : Bool → ℝ, ∫ ω, f ω ∂Q = f true / 2 + f false / 2 := fun f => by
    have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac true) :=
      (integrable_dirac (f := f) (by simp)).smul_measure (by simp)
    have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac false) :=
      (integrable_dirac (f := f) (by simp)).smul_measure (by simp)
    rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  refine ⟨Q, hQ, fun ω => if ω then 1 else 2, 1,
    ⟨(measurable_of_countable _).aestronglyMeasurable, 2, ?_⟩, ?_⟩
  · exact Eventually.of_forall fun ω => by cases ω <;> norm_num
  · simp only [kpExp, hint]
    norm_num [Real.rpow_neg_one]

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# MDPs with certainty equivalents

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.5 (pp. 230–231).

* The aggregator (7.24), `B_ℰ(x, a, v) = r(x, a) + β ℰ[v(f(x, a, ξ))]` with `ξ ∼ φ` on `Z`, as an
  RDP on `bX` (`ceBRDP`). With `ℰ = 𝔼` this is (7.23). `r` need only be bounded on `G`, and the
  measurability of `(x, a) ↦ ℰ[v(f(x, a, ξ))]` is the book's standing assumption.
* Cash invariance of `ℰ` gives Blackwell's condition with `λ = β`.
* **Proposition 7.2.10**: under Assumption 7.2.11, with `ℰ` continuous, the fundamental optimality
  properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX` (Proposition 7.2.2).
  Assumption 7.2.11 (i) is stated as the maximum theorem for `Γ` (`HasMaxSelections`); the state
  and action spaces are first countable, as the book's metric spaces are.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A Z : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Z]

/-- The aggregator (7.24): `B_ℰ(x, a, v) = r(x, a) + β ℰ[v(f(x, a, ξ))]`. -/
def ceAgg (r : X × A → ℝ) (β : ℝ) (f : X × A → Z → X) (E : (Z → ℝ) → ℝ) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => r (x, a) + β * E fun z => v (f (x, a) z)

theorem isLInf_comp (φ : Measure Z) {f : X × A → Z → X} (hf : Measurable (uncurry f))
    (v : BM X) (p : X × A) : IsLInf φ fun z => v.toFun (f p z) :=
  ⟨(v.measurable'.comp (measurable_section hf p)).aestronglyMeasurable, ‖v‖,
    Eventually.of_forall fun _ => BM.abs_le_norm v _⟩

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- A certainty equivalent maps `|W| ≤ N` into `[ℰ(0) − N, ℰ(0) + N]`. -/
theorem IsCertEquiv.abs_sub_le {φ : Measure Z} {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    {W : Z → ℝ} (hW : IsLInf φ W) {N : ℝ} (hN : ∀ᵐ z ∂φ, |W z| ≤ N) :
    |E W - E fun _ => 0| ≤ N := by
  have h1 := hE.cash (fun _ => 0) (isLInf_const 0) N
  have h2 := hE.cash (fun _ => 0) (isLInf_const 0) (-N)
  have hup := hE.mono W _ hW ((isLInf_const 0).add_const N)
    (hN.mono fun z hz => by simpa using le_of_abs_le hz)
  have hlo := hE.mono _ W ((isLInf_const 0).add_const (-N)) hW
    (hN.mono fun z hz => by simpa using neg_le_of_abs_le hz)
  rw [h1] at hup
  rw [h2] at hlo
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The RDP `(Γ, bX, B_ℰ)` of §7.2.5.2: `r` measurable and bounded on `G`, `0 ≤ β`, `ξ ∼ φ`,
`f` measurable, `ℰ` a certainty equivalent on `L∞(Z, φ)` with `(x, a) ↦ ℰ[v(f(x, a, ξ))]`
measurable. -/
noncomputable def ceBRDP (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Z)
    {f : X × A → Z → X} (hf : Measurable (uncurry f)) {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : BRDP X A where
  Γ := Γ
  B := ceAgg r β f E
  measurable v := hr.add ((hEm v).const_mul β)
  mono x a _ v w hvw := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hE.mono _ _
    (isLInf_comp φ hf v (x, a)) (isLInf_comp φ hf w (x, a))
    (Eventually.of_forall fun _ => BM.le_def.1 hvw _)) hβ)
  bdd v := by
    obtain ⟨C, hC⟩ := hrb
    refine ⟨C + β * (|E fun _ => 0| + ‖v‖), fun x a ha => ?_⟩
    have hW := hE.abs_sub_le (isLInf_comp φ hf v (x, a))
      (Eventually.of_forall fun z => BM.abs_le_norm v (f (x, a) z))
    have hEW : |E fun z => v.toFun (f (x, a) z)| ≤ |E fun _ => 0| + ‖v‖ := by
      have := abs_sub_abs_le_abs_sub (E fun z => v.toFun (f (x, a) z)) (E fun _ => 0)
      linarith
    change |r (x, a) + β * E (fun z => v.toFun (f (x, a) z))| ≤ _
    refine (abs_add_le _ _).trans (add_le_add (hC x a ha) ?_)
    rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hEW hβ
  exists_policy := hΓ

/-- Cash invariance gives Blackwell's condition with `λ = β`:
`B_ℰ(x, a, v + κ) = B_ℰ(x, a, v) + βκ` (proof of Proposition 7.2.10). -/
theorem ceBRDP_isBlackwell (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Z)
    {f : X × A → Z → X} (hf : Measurable (uncurry f)) {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).IsBlackwell β := by
  intro x a _ v κ _
  have h := hE.cash _ (isLInf_comp φ hf v (x, a)) κ
  change r (x, a) + β * (E fun z => v.toFun (f (x, a) z) + κ) ≤
    r (x, a) + β * (E fun z => v.toFun (f (x, a) z)) + β * κ
  rw [h]
  linarith

/-- If `ℰ` is continuous, `f(·, z)` is continuous on `G` and `v` is continuous, then
`(x, a) ↦ ℰ[v(f(x, a, ξ))]` is continuous on `G` (proof of Proposition 7.2.10). -/
theorem continuousOn_ce [TopologicalSpace X] [TopologicalSpace A] [FirstCountableTopology X]
    [FirstCountableTopology A] {φ : Measure Z} {f : X × A → Z → X} (hf : Measurable (uncurry f))
    {E : (Z → ℝ) → ℝ} (hEc : IsContinuousCE φ E) {G : Set (X × A)}
    (hfc : ∀ z, ContinuousOn (fun p => f p z) G) {v : BM X} (hv : Continuous v.toFun) :
    ContinuousOn (fun p => E fun z => v.toFun (f p z)) G := by
  intro p hp
  refine tendsto_iff_seq_tendsto.2 fun ps hps => ?_
  exact hEc (fun n z => v.toFun (f (ps n) z)) (fun z => v.toFun (f p z)) ‖v‖
    (fun n => (isLInf_comp φ hf v (ps n)).1)
    (fun _ => Eventually.of_forall fun _ => BM.abs_le_norm v _) (isLInf_comp φ hf v p)
    (Eventually.of_forall fun z => (hv.tendsto _).comp ((hfc z p hp).tendsto.comp hps))

/-- **Proposition 7.2.10** (p. 231): under Assumption 7.2.11 (the maximum theorem for `Γ`, `r`
bounded and continuous on `G`, `f(·, z)` continuous on `G`), if `ℰ` is a continuous certainty
equivalent and `0 ≤ β < 1`, then for `(Γ, bX, B_ℰ)` (i) the fundamental optimality properties hold,
(ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. -/
theorem proposition_7_2_10 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    [FirstCountableTopology X] [FirstCountableTopology A] (Γ : X → Set A) (r : X × A → ℝ)
    (hr : Measurable r) (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) (φ : Measure Z) {f : X × A → Z → X} (hf : Measurable (uncurry f))
    {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (hΓmax : HasMaxSelections Γ)
    (hrc : ContinuousOn r {p | p.2 ∈ Γ p.1})
    (hfc : ∀ z, ContinuousOn (fun p => f p z) {p | p.2 ∈ Γ p.1}) (hEc : IsContinuousCE φ E) :
    ∃ hw : (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.WellPosed,
      (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X,
        (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.VFIGeometric (LDP.bc X) vstar := by
  have hΓ' : HasMaxSelections (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).Γ := hΓmax
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).proposition_7_2_2
    hΓ' hβ hβ1 (ceBRDP_isBlackwell Γ r hr hrb hβ φ hf hE hEm hΓ) fun v hv =>
      hrc.add (continuousOn_const.mul (continuousOn_ce hf hEc hfc hv))
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-- `p ↦ ∫ h(f(p, ξ))φ(dξ)` is measurable. -/
theorem measurable_integral_comp {Y : Type*} [MeasurableSpace Y] {φ : Measure Z} [SFinite φ]
    {f : Y → Z → X} (hf : Measurable (uncurry f)) {h : X → ℝ} (hh : Measurable h) :
    Measurable fun p => ∫ z, h (f p z) ∂φ :=
  ((hh.comp hf).stronglyMeasurable.integral_prod_right' (ν := φ)).measurable

/-- The measurability assumption of §7.2.5.2 holds for `ℰ = 𝔼`. -/
theorem measurable_meanCE_comp {φ : Measure Z} [SFinite φ] {f : X × A → Z → X}
    (hf : Measurable (uncurry f)) (v : BM X) :
    Measurable fun p : X × A => meanCE φ fun z => v.toFun (f p z) :=
  measurable_integral_comp hf v.measurable'

/-- The measurability assumption of §7.2.5.2 holds for the entropic certainty equivalent. -/
theorem measurable_entropicCE_comp {φ : Measure Z} [SFinite φ] {f : X × A → Z → X}
    (hf : Measurable (uncurry f)) (θ : ℝ) (v : BM X) :
    Measurable fun p : X × A => entropicCE φ θ fun z => v.toFun (f p z) :=
  (Real.measurable_log.comp (measurable_integral_comp hf
    (Real.measurable_exp.comp (measurable_const.mul v.measurable')))).const_mul _

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.1.1.2–§7.1.1.8 (pp. 209–212) and
§7.1.2.1 (p. 213).

* **Exercise 7.1.1**: a finite MDP is an RDP with `V = ℝ^X`; its Bellman operator is (1.19).
* §7.1.1.3: the firm valuation problem (7.4) with `A = Γ(x) = {0, 1}` and `V = bX`; its Bellman
  operator is `max{s, π(x) + β ∫ v(x')P(x, dx')}` (Theorem 1.1.1).
* **Exercise 7.1.2**: with unbounded profits, `|π| ≤ ηℓ + δ` and `∫ ℓ dP(x) ≤ αℓ(x)`, (7.4) is an
  RDP on `bℓX`. The book's (7.5) bounds `π` above only; the solution uses `|π| ≤ ηℓ + δ`.
* §7.1.1.5: optimal savings, as the LDP of Example 6.1.5 (via (7.9)).
* **Exercise 7.1.3**: savings with Kreps–Porteus expectations (7.6) is an RDP on the measurable
  `v : X → [u̲, ū]`.
* §7.1.1.7: MDPs with rewards depending on the next state (7.7).
* **Exercise 7.1.4**: the risk-sensitive aggregator (7.8) gives an RDP for every `θ ≠ 0`.
* §7.1.2.1: every LDP is an RDP (7.9), with the same policy operators.

The state space of the savings problems is `ℝ` with `Γ(w) = [0, max(w, 0)]`, as in Chapter 6.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Finite MDPs -/

/-- The finite MDP aggregator `B(x, a, v) = r(x, a) + β ∑_{x'} v(x')P(x, a, x')` (§7.1.1.2). -/
def mdpAgg [Fintype X] (r : X → A → ℝ) (β : ℝ) (Pm : X → A → X → ℝ) : X → A → (X → ℝ) → ℝ :=
  fun x a v => r x a + β * ∑ y, v y * Pm x a y

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- **Exercise 7.1.1** (p. 209): the finite MDP aggregator satisfies the monotonicity condition
(7.2); consistency (7.3) is automatic with `V = ℝ^X`. -/
theorem exercise_7_1_1 [Fintype X] (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β) {Pm : X → A → X → ℝ}
    (hP : ∀ x a y, 0 ≤ Pm x a y) (x : X) (a : A) {v w : X → ℝ} (h : v ≤ w) :
    mdpAgg r β Pm x a v ≤ mdpAgg r β Pm x a w :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (h y) (hP x a y)) hβ)

/-- The finite MDP as an RDP with `V = ℝ^X` (§7.1.1.2). -/
def finiteMDP [Fintype X] (Γ : X → Set A) (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := mdpAgg r β Pm
  mono x a _ _ _ h := exercise_7_1_1 r hβ hP x a h
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-- For finite `X` and `A`, the Bellman operator of the finite MDP is (1.19),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑_{x'} v(x')P(x, a, x')}` (Lemma 7.1.1). -/
theorem finiteMDP_bellman [Fintype X] [MeasurableSingletonClass X] [Finite A]
    (Γ : X → Set A) (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β) {Pm : X → A → X → ℝ}
    (hP : ∀ x a y, 0 ≤ Pm x a y) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (v : X → ℝ) (x : X) :
    IsGreatest ((fun a => mdpAgg r β Pm x a v) '' Γ x)
      ((finiteMDP Γ r hβ hP hΓ).adp.bellman v x) :=
  ((finiteMDP Γ r hβ hP hΓ).lemma_7_1_1 (fun _ => (Set.toFinite _).measurableSet) v
    fun _ => measurable_of_finite _).2.2 x

/-- MDPs with modified rewards (7.7): `B(x, a, v) = ∑_{x'} {r(x, a, x') + βv(x')}P(x, a, x')`. -/
def modifiedMDP [Fintype X] (Γ : X → Set A) (r : X → A → X → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B x a v := ∑ y, (r x a y + β * v y) * Pm x a y
  mono x a _ _ _ h := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (h y) hβ)) (hP x a y)
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-- The risk-sensitive aggregator (7.8):
`B(x, a, v) = r(x, a) + (β/θ) ln ∑_{x'} exp(θv(x'))P(x, a, x')`. -/
noncomputable def rsAgg [Fintype X] (r : X → A → ℝ) (β θ : ℝ) (Pm : X → A → X → ℝ) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => r x a + β / θ * Real.log (∑ y, Real.exp (θ * v y) * Pm x a y)

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- **Exercise 7.1.4** (p. 212): for every `θ ≠ 0`, the risk-sensitive aggregator (7.8) satisfies
the monotonicity condition (7.2); consistency (7.3) is automatic with `V = ℝ^X`. -/
theorem exercise_7_1_4 [Fintype X] (r : X → A → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ≠ 0)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y) (hP1 : ∀ x a, ∑ y, Pm x a y = 1)
    (x : X) (a : A) {v w : X → ℝ} (h : v ≤ w) :
    rsAgg r β θ Pm x a v ≤ rsAgg r β θ Pm x a w := by
  have hpos : ∀ u : X → ℝ, 0 < ∑ y, Real.exp (θ * u y) * Pm x a y := fun u => by
    obtain ⟨y, hy⟩ : ∃ y, 0 < Pm x a y := by
      by_contra hcon
      have : ∑ y, Pm x a y = 0 := Finset.sum_eq_zero fun y _ =>
        le_antisymm (not_lt.1 fun hy => hcon ⟨y, hy⟩) (hP x a y)
      rw [hP1] at this
      exact one_ne_zero this
    exact Finset.sum_pos' (fun y _ => mul_nonneg (Real.exp_pos _).le (hP x a y))
      ⟨y, Finset.mem_univ _, mul_pos (Real.exp_pos _) hy⟩
  refine add_le_add le_rfl ?_
  rcases lt_or_gt_of_ne hθ with hneg | hθpos
  · have hle : ∑ y, Real.exp (θ * w y) * Pm x a y ≤ ∑ y, Real.exp (θ * v y) * Pm x a y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (h y) hneg.le)) (hP x a y)
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos w) hle)
      (div_nonpos_of_nonneg_of_nonpos hβ hneg.le)
  · have hle : ∑ y, Real.exp (θ * v y) * Pm x a y ≤ ∑ y, Real.exp (θ * w y) * Pm x a y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h y) hθpos.le)) (hP x a y)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos v) hle) (div_nonneg hβ hθpos.le)

/-- The risk-sensitive MDP of §7.1.1.8 as an RDP with `V = ℝ^X`. -/
noncomputable def riskSensitiveMDP [Fintype X] (Γ : X → Set A) (r : X → A → ℝ) {β θ : ℝ}
    (hβ : 0 ≤ β) (hθ : θ ≠ 0) {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hP1 : ∀ x a, ∑ y, Pm x a y = 1) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := rsAgg r β θ Pm
  mono x a _ _ _ h := exercise_7_1_4 r hβ hθ hP hP1 x a h
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-! ### LDPs are RDPs -/

/-- (7.9), §7.1.2.1 (p. 213): an LDP `(Γ, r, K)` is the RDP `(Γ, bX, B)` with
`B(x, a, v) = r(x, a) + ∫ v(x')K(x, a, dx')`. -/
noncomputable def LDP.toRDP (M : LDP X A) : RDP X A (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ := M.Γ
  B x a v := M.r.toFun (x, a) + M.β.toFun (x, a) * ∫ x', v x' ∂(M.P (x, a))
  mono x a _ v w h := by
    have := M.P_markov
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun y =>
      BM.le_def.1 h y) (M.β_nonneg (x, a)))
    · exact Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)
    · exact Integrable.of_bound w.measurable'.aestronglyMeasurable ‖w‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm w y)
  consistent σ hσ hσΓ v := ⟨M.adp.T ⟨σ, hσ, hσΓ⟩ v, rfl⟩
  exists_policy := M.exists_policy

/-- The RDP of an LDP has the LDP's policy operators (7.9). -/
theorem LDP.toRDP_T (M : LDP X A) (σ : M.Policy) (v : BM X) :
    M.toRDP.adp.T σ v = M.adp.T σ v :=
  BM.ext fun x => M.toRDP.ev_adp_T σ v x

/-- §7.1.1.5 (p. 210): the optimal savings problem is an RDP (through the LDP of Example 6.1.5)
with `B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)φ(dy)`. -/
theorem savings_B (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] (w c : ℝ) (v : BM ℝ) :
    (Savings.ldp u hu hub hβ0 R φ).toRDP.B w c v.toFun =
      u c + β * ∫ y, v.toFun (R * (w - c) + y) ∂φ := by
  change u c + β * ∫ x', v.toFun x' ∂(Savings.P R φ (w, c)) = _
  rw [Savings.P, integral_shockKernel _ _ _ v.measurable']

/-! ### The firm valuation problem -/

/-- The firm valuation aggregator (7.4): `B(x, a, v) = as + (1 − a)[π(x) + β ∫ v(x')P(x, dx')]`. -/
noncomputable def firmAgg (P : Kernel X X) (s : ℝ) (π : X → ℝ) (β : ℝ) :
    X → ℝ → (X → ℝ) → ℝ :=
  fun x a v => a * s + (1 - a) * (π x + β * ∫ x', v x' ∂(P x))

/-- §7.1.1.3 (p. 209): the firm valuation problem as an RDP with `A = ℝ`, `Γ(x) = {0, 1}` and
`V = bX`. -/
noncomputable def firmRDP (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π : BM X) {β : ℝ}
    (hβ : 0 ≤ β) : RDP X ℝ (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ _ := {0, 1}
  B := firmAgg P s π.toFun β
  mono x a ha v w h := by
    have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (markovOp_mono P (BM.mem_bX v) (BM.mem_bX w) h x) hβ)) h1)
  consistent σ hσ hσΓ v := by
    refine ⟨⟨fun x => firmAgg P s π.toFun β x (σ x) v.toFun, ?_, |s| + ‖π‖ + β * ‖v‖,
      fun x => ?_⟩, rfl⟩
    · exact (hσ.mul measurable_const).add ((measurable_const.sub hσ).mul
        (π.measurable'.add ((measurable_markovOp P v.measurable').const_mul β)))
    · have hint := abs_markovOp_le P (BM.abs_le_norm v) x
      have hπ := BM.abs_le_norm π x
      change |σ x * s + (1 - σ x) * (π.toFun x + β * markovOp P v.toFun x)| ≤ _
      rcases hσΓ x with h | h <;> rw [h]
      · simp only [zero_mul, sub_zero, one_mul, zero_add]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hβ]
        nlinarith [abs_nonneg s, mul_le_mul_of_nonneg_left hint hβ]
      · simp only [one_mul, sub_self, zero_mul, add_zero]
        nlinarith [norm_nonneg π, norm_nonneg v, mul_nonneg hβ (norm_nonneg v)]
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

/-- §7.1.1.3 (p. 210): the RDP Bellman operator of the firm valuation problem is
`(Tv)(x) = max{s, π(x) + β ∫ v(x')P(x, dx')}`, as in Theorem 1.1.1. -/
theorem firmRDP_bellman (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π : BM X) {β : ℝ}
    (hβ : 0 ≤ β) (v : BM X) (x : X) :
    ((firmRDP P s π hβ).adp.bellman v).toFun x =
      max s (π.toFun x + β * ∫ x', v.toFun x' ∂(P x)) := by
  let c : X → ℝ := fun x => π.toFun x + β * ∫ x', v.toFun x' ∂(P x)
  have hc : Measurable c := π.measurable'.add ((measurable_markovOp P v.measurable').const_mul β)
  let σ : X → ℝ := fun x => if c x ≤ s then 1 else 0
  have hσm : Measurable σ := Measurable.ite (measurableSet_le hc measurable_const)
    measurable_const measurable_const
  have hσΓ : ∀ x, σ x ∈ (firmRDP P s π hβ).Γ x := fun x => by
    change σ x ∈ ({0, 1} : Set ℝ)
    by_cases h : c x ≤ s
    · simp [σ, h]
    · simp [σ, h]
  have hval : ∀ x, firmAgg P s π.toFun β x (σ x) v.toFun = max s (c x) := fun x => by
    by_cases h : c x ≤ s
    · simp only [σ, firmAgg, h, ↓reduceIte]
      rw [max_eq_left h]
      ring
    · simp only [σ, firmAgg, h, ↓reduceIte]
      rw [max_eq_right (not_le.1 h).le]
      ring
  have hσ : (firmRDP P s π hβ).IsArgmax v ⟨σ, hσm, hσΓ⟩ := fun x a ha => by
    change firmAgg P s π.toFun β x a v.toFun ≤ firmAgg P s π.toFun β x (σ x) v.toFun
    rw [hval]
    rcases ha with rfl | rfl
    · simp only [firmAgg, zero_mul, sub_zero, one_mul, zero_add]
      exact le_max_right _ _
    · simp only [firmAgg, one_mul, sub_self, zero_mul, add_zero]
      exact le_max_left _ _
  rw [show ((firmRDP P s π hβ).adp.bellman v).toFun x =
    (firmRDP P s π hβ).ev ((firmRDP P s π hβ).adp.bellman v) x from rfl,
    ((firmRDP P s π hβ).bellman_of_isArgmax hσ).2.1 x]
  exact hval x

/-- `v ∈ bℓX` is `ℓh` for `h = v / ℓ ∈ bX`. -/
theorem exists_wevB_eq {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ bl ℓ) : ∃ h : BM X, wevB ℓ h = v := by
  obtain ⟨hm, C, hC⟩ := hv
  refine ⟨⟨fun x => v x / ℓ x, hm.div hℓm, C, fun x => ?_⟩, funext fun x => ?_⟩
  · have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hC x
  · exact mul_div_cancel₀ _ (zero_lt_one.trans_le (hℓ1 x)).ne'

/-- **Exercise 7.1.2** (p. 210): firm valuation with unbounded profits. If `ℓ ≥ 1` is a weight
function, `|π| ≤ ηℓ + δ` and `∫ ℓ dP(x) ≤ αℓ(x)` (with `ℓ` integrable under each `P(x)`), then the
aggregator (7.4) is monotone on `bℓX` (7.2) and maps `bℓX` into `bℓX` along every policy (7.3). -/
theorem exercise_7_1_2 (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) {π ℓ : X → ℝ}
    (hπm : Measurable π) (hℓ1 : ∀ x, 1 ≤ ℓ x)
    (hℓi : ∀ x, Integrable ℓ (P x)) {η δ α β : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hπ : ∀ x, |π x| ≤ η * ℓ x + δ) (hP : ∀ x, ∫ x', ℓ x' ∂(P x) ≤ α * ℓ x) :
    (∀ x, ∀ a ∈ ({0, 1} : Set ℝ), ∀ v ∈ bl ℓ, ∀ w ∈ bl ℓ, v ≤ w →
      firmAgg P s π β x a v ≤ firmAgg P s π β x a w) ∧
    ∀ σ : X → ℝ, Measurable σ → (∀ x, σ x ∈ ({0, 1} : Set ℝ)) → ∀ v ∈ bl ℓ,
      (fun x => firmAgg P s π β x (σ x) v) ∈ bl ℓ := by
  have hint : ∀ v ∈ bl ℓ, ∀ x, Integrable v (P x) := fun v hv x => by
    obtain ⟨hm, C, hC⟩ := hv
    refine ((hℓi x).const_mul |C|).mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (hC y).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (zero_le_one.trans (hℓ1 y)))
  refine ⟨fun x a ha v hv w hw h => ?_, fun σ hσ hσΓ v hv => ⟨?_, ?_⟩⟩
  · have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (integral_mono (hint v hv x) (hint w hw x) h) hβ)) h1)
  · exact (hσ.mul measurable_const).add ((measurable_const.sub hσ).mul (hπm.add
      ((hv.1.stronglyMeasurable.integral_kernel (κ := P)).measurable.const_mul β)))
  · obtain ⟨hvm, C, hC⟩ := hv
    refine ⟨|s| + δ + η + β * (|C| * α), fun x => ?_⟩
    have hl : 1 ≤ ℓ x := hℓ1 x
    have hI : |∫ x', v x' ∂(P x)| ≤ |C| * (α * ℓ x) := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ x', |v x'| ∂(P x) ≤ ∫ x', |C| * ℓ x' ∂(P x) :=
            integral_mono (hint v ⟨hvm, C, hC⟩ x).abs ((hℓi x).const_mul _) fun y =>
              (hC y).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
                (zero_le_one.trans (hℓ1 y)))
        _ = |C| * ∫ x', ℓ x' ∂(P x) := integral_const_mul _ _
        _ ≤ |C| * (α * ℓ x) := mul_le_mul_of_nonneg_left (hP x) (abs_nonneg C)
    have hπx := hπ x
    change |σ x * s + (1 - σ x) * (π x + β * ∫ x', v x' ∂(P x))| ≤ _
    rcases hσΓ x with h | h <;> rw [h]
    · simp only [zero_mul, sub_zero, one_mul, zero_add]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hβ]
      have := mul_le_mul_of_nonneg_left hI hβ
      nlinarith [abs_nonneg s, abs_nonneg C, mul_nonneg hβ (mul_nonneg (abs_nonneg C) hα)]
    · simp only [one_mul, sub_self, zero_mul, add_zero]
      nlinarith [abs_nonneg s, abs_nonneg C, mul_nonneg hβ (mul_nonneg (abs_nonneg C) hα)]

/-- The firm valuation problem with unbounded profits as an RDP on `bℓX` (Exercise 7.1.2), with
`bℓX` represented as `bX` through `v = ℓh`. -/
noncomputable def firmWeighted (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) {π ℓ : X → ℝ}
    (hπm : Measurable π) (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x)
    (hℓi : ∀ x, Integrable ℓ (P x)) {η δ α β : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hπ : ∀ x, |π x| ≤ η * ℓ x + δ) (hP : ∀ x, ∫ x', ℓ x' ∂(P x) ≤ α * ℓ x) :
    RDP X ℝ (BM X) where
  ev := wevB ℓ
  ev_le_iff h h' := by
    change (∀ x, h.toFun x ≤ h'.toFun x) ↔ ∀ x, ℓ x * h.toFun x ≤ ℓ x * h'.toFun x
    exact forall_congr' fun x =>
      (mul_le_mul_iff_of_pos_left (zero_lt_one.trans_le (hℓ1 x))).symm
  Γ _ := {0, 1}
  B := firmAgg P s π β
  mono x a ha v w h := (exercise_7_1_2 P s hπm hℓ1 hℓi hη hδ hα hβ hπ hP).1 x a ha _
    (wevB_mem hℓm hℓ1 v) _ (wevB_mem hℓm hℓ1 w) fun y =>
      mul_le_mul_of_nonneg_left (BM.le_def.1 h y) (zero_le_one.trans (hℓ1 y))
  consistent σ hσ hσΓ v := exists_wevB_eq hℓm hℓ1
    ((exercise_7_1_2 P s hπm hℓ1 hℓi hη hδ hα hβ hπ hP).2 σ hσ hσΓ _ (wevB_mem hℓm hℓ1 v))
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

/-! ### Savings with Kreps–Porteus expectations -/

/-- The value space of §7.1.1.6: measurable `v : ℝ → [u̲, ū]`. -/
abbrev KPValues (lo hi : ℝ) : Type := {v : ℝ → ℝ // Measurable v ∧ ∀ x, v x ∈ Icc lo hi}

/-- The Kreps–Porteus expectation `(∫ v(s + y)^{1−γ} φ(dy))^{1/(1−γ)}` of continuation values. -/
noncomputable def kpCont (γ : ℝ) (φ : Measure ℝ) (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ y, v (s + y) ^ (1 - γ) ∂φ) ^ (1 - γ)⁻¹

/-- The aggregator of (7.6):
`B(w, c, v) = (1 − β)u(c) + β (∫ v(R(w − c) + y)^{1−γ} φ(dy))^{1/(1−γ)}`. -/
noncomputable def kpAgg (u : ℝ → ℝ) (β R γ : ℝ) (φ : Measure ℝ) : ℝ → ℝ → (ℝ → ℝ) → ℝ :=
  fun w c v => (1 - β) * u c + β * kpCont γ φ v (R * (w - c))

/-- The Kreps–Porteus expectation is monotone on functions with values in `[u̲, ū] ⊆ (0, ∞)`. -/
theorem kpCont_mono {γ : ℝ} (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] {lo hi : ℝ}
    (hlo : 0 < lo) {v w : ℝ → ℝ} (hvm : Measurable v) (hwm : Measurable w)
    (hv : ∀ x, v x ∈ Icc lo hi) (hw : ∀ x, w x ∈ Icc lo hi) (h : v ≤ w) (s : ℝ) :
    kpCont γ φ v s ≤ kpCont γ φ w s := by
  have hpos : ∀ {g : ℝ → ℝ}, (∀ x, g x ∈ Icc lo hi) → ∀ x, 0 < g x := fun hg x =>
    hlo.trans_le (hg x).1
  -- `g^{1−γ}` is bounded and measurable, hence integrable
  have hint : ∀ {g : ℝ → ℝ}, Measurable g → (∀ x, g x ∈ Icc lo hi) →
      Integrable (fun y => g (s + y) ^ (1 - γ)) φ := fun hgm hg => by
    refine Integrable.of_bound
      ((hgm.comp (measurable_const_add s)).pow_const _).aestronglyMeasurable
      (lo ^ (1 - γ) + hi ^ (1 - γ)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hpos hg _) _)]
    rcases le_total 0 (1 - γ) with hp | hp
    · exact (Real.rpow_le_rpow (hpos hg _).le (hg _).2 hp).trans
        (le_add_of_nonneg_left (Real.rpow_pos_of_pos hlo _).le)
    · exact (Real.rpow_le_rpow_of_nonpos hlo (hg _).1 hp).trans
        (le_add_of_nonneg_right
          (Real.rpow_pos_of_pos (hlo.trans_le ((hg 0).1.trans (hg 0).2)) _).le)
  have hIpos : ∀ {g : ℝ → ℝ}, Measurable g → (∀ x, g x ∈ Icc lo hi) →
      0 < ∫ y, g (s + y) ^ (1 - γ) ∂φ := fun {g} hgm hg =>
    integral_pos_iff_support_of_nonneg (fun y => (Real.rpow_pos_of_pos (hpos hg _) _).le)
      (hint hgm hg) |>.2 (by
        have : Function.support (fun y => g (s + y) ^ (1 - γ)) = univ :=
          eq_univ_of_forall fun y => (Real.rpow_pos_of_pos (hpos hg _) _).ne'
        rw [this, measure_univ]
        exact one_pos)
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hγ.symm) with hp | hp
  · -- `1 − γ < 0`: both powers reverse the order
    have hle : ∫ y, w (s + y) ^ (1 - γ) ∂φ ≤ ∫ y, v (s + y) ^ (1 - γ) ∂φ :=
      integral_mono (hint hwm hw) (hint hvm hv) fun y =>
        Real.rpow_le_rpow_of_nonpos (hpos hv _) (h _) hp.le
    exact Real.rpow_le_rpow_of_nonpos (hIpos hwm hw) hle (inv_nonpos.2 hp.le)
  · have hle : ∫ y, v (s + y) ^ (1 - γ) ∂φ ≤ ∫ y, w (s + y) ^ (1 - γ) ∂φ :=
      integral_mono (hint hvm hv) (hint hwm hw) fun y =>
        Real.rpow_le_rpow (hpos hv _).le (h _) hp.le
    exact Real.rpow_le_rpow (hIpos hvm hv).le hle (inv_nonneg.2 hp.le)

theorem kpCont_const {γ : ℝ} (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] {c : ℝ}
    (hc : 0 < c) (s : ℝ) : kpCont γ φ (fun _ => c) s = c := by
  rw [kpCont, integral_const, probReal_univ, one_smul,
    Real.rpow_rpow_inv hc.le (sub_ne_zero.2 hγ.symm)]

/-- **Exercise 7.1.3** (p. 211): for `γ ≠ 1`, `0 ≤ β ≤ 1`, `u` measurable with values in
`[u̲, ū] ⊆ (0, ∞)`, the Kreps–Porteus savings aggregator is monotone (7.2) and maps the measurable
`v : ℝ → [u̲, ū]` into themselves along every policy (7.3). -/
theorem exercise_7_1_3 {u : ℝ → ℝ} (hum : Measurable u) {lo hi : ℝ} (hlo : 0 < lo)
    (hu : ∀ c, u c ∈ Icc lo hi) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℝ) {γ : ℝ}
    (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] :
    (∀ w c, ∀ v w' : ℝ → ℝ, Measurable v → Measurable w' → (∀ x, v x ∈ Icc lo hi) →
      (∀ x, w' x ∈ Icc lo hi) → v ≤ w' → kpAgg u β R γ φ w c v ≤ kpAgg u β R γ φ w c w') ∧
    ∀ σ : ℝ → ℝ, Measurable σ → ∀ v : ℝ → ℝ, Measurable v → (∀ x, v x ∈ Icc lo hi) →
      Measurable (fun w => kpAgg u β R γ φ w (σ w) v) ∧
        ∀ w, kpAgg u β R γ φ w (σ w) v ∈ Icc lo hi := by
  refine ⟨fun w c v w' hv hw' hvI hwI h => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (kpCont_mono hγ φ hlo hv hw' hvI hwI h _) hβ0), fun σ hσ v hvm hvI => ⟨?_, fun w => ?_⟩⟩
  · have hm : Measurable fun p : ℝ × ℝ => v (R * (p.1 - σ p.1) + p.2) ^ (1 - γ) :=
      (hvm.comp ((measurable_const.mul (measurable_fst.sub (hσ.comp measurable_fst))).add
        measurable_snd)).pow_const _
    exact ((measurable_const.mul (hum.comp hσ))).add (measurable_const.mul
      ((hm.stronglyMeasurable.integral_prod_right' (ν := φ)).measurable.pow_const _))
  · have hconst : ∀ c, 0 < c → c ∈ Icc lo hi → ∀ x, (fun _ : ℝ => c) x ∈ Icc lo hi :=
      fun c _ hc _ => hc
    have hlohi : lo ≤ hi := (hvI 0).1.trans (hvI 0).2
    have h1 := kpCont_mono hγ φ hlo measurable_const hvm (hconst lo hlo ⟨le_rfl, hlohi⟩) hvI
      (fun x => (hvI x).1) (R * (w - σ w))
    have h2 := kpCont_mono hγ φ hlo hvm measurable_const hvI
      (hconst hi (hlo.trans_le hlohi) ⟨hlohi, le_rfl⟩) (fun x => (hvI x).2) (R * (w - σ w))
    rw [kpCont_const hγ φ hlo] at h1
    rw [kpCont_const hγ φ (hlo.trans_le hlohi)] at h2
    have hu1 := hu (σ w)
    change (1 - β) * u (σ w) + β * kpCont γ φ v (R * (w - σ w)) ∈ Icc lo hi
    constructor <;> nlinarith [hu1.1, hu1.2]

/-- Savings with Kreps–Porteus expectations (7.6) as an RDP (Exercise 7.1.3), `Γ(w) = [0, w⁺]`. -/
noncomputable def kpSavings {u : ℝ → ℝ} (hum : Measurable u) {lo hi : ℝ} (hlo : 0 < lo)
    (hu : ∀ c, u c ∈ Icc lo hi) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℝ) {γ : ℝ}
    (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] : RDP ℝ ℝ (KPValues lo hi) where
  ev v := v.1
  ev_le_iff _ _ := Iff.rfl
  Γ w := Icc 0 (max w 0)
  B := kpAgg u β R γ φ
  mono w c _ v v' h := (exercise_7_1_3 hum hlo hu hβ0 hβ1 R hγ φ).1 w c v.1 v'.1 v.2.1 v'.2.1
    v.2.2 v'.2.2 h
  consistent σ hσ _ v := by
    obtain ⟨hm, hI⟩ := (exercise_7_1_3 hum hlo hu hβ0 hβ1 R hγ φ).2 σ hσ v.1 v.2.1 v.2.2
    exact ⟨⟨_, hm, hI⟩, rfl⟩
  exists_policy := ⟨fun _ => 0, measurable_const, fun w => ⟨le_rfl, le_max_right _ _⟩⟩

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings with utility unbounded above

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.1 (pp. 232–233), with
Exercises 7.2.2–7.2.4 (pp. 224–225).

Wealth `w`, consumption `c ∈ Γ(w) = [0, max(w, 0)]`, utility `u` continuous, nonnegative and
increasing, gross return `R ≥ 0`, income `y ∼ ψ`, and
`B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)ψ(dy)` on `V = bℓX₊`.

The weight function (7.25) is `ℓ(w) = 𝔼 ∑_t δᵗ u(Ŵ_t)` along the zero-consumption wealth path. The
proofs use only the properties that the solutions to Exercises 7.3.1–7.3.2 derive from it: `ℓ` is
measurable and increasing, `ℓ(s + ·)` is integrable for every shift, and the recursion
`u(w⁺) + δ ∫ ℓ(Rw + y)ψ(dy) ≤ ℓ(w)`. A weight function must be `≥ 1`; the expected discounted sum
with `u + 1` in place of `u` satisfies all of these, while (7.25) itself can be below `1`. The
path-space expectation is not constructed.

* **Exercise 7.3.1**: (U1) with `λ = β/δ < 1`, and (U2).
* **Exercise 7.3.2**: Assumption 7.2.7 when income has a continuous density `φ` and `ℓ` is
  continuous: `(w, c) ↦ B(w, c, v)` is continuous for every `v ∈ bℓX₊`. The proof writes
  `∫ v(s + y)φ(y) dy = ∫ v(x)φ(x − s) dx` and applies Scheffé's lemma to `ℓ(x)φ(x − s)`, whose
  integral `∫ ℓ(s + y)φ(y) dy` is continuous in `s` by dominated convergence (`ℓ` increasing).
* So Proposition 7.2.5 applies: `v* ∈ bℓcX₊` and VFI, OPI and HPI converge (`section_7_3_1`).
* **Exercise 7.2.2**: Assumption 7.2.8, so `v*` is increasing (Proposition 7.2.6).
* **Exercise 7.2.3**: with `u` concave on `ℝ₊` and income nonnegative, `v*` is increasing and
  concave on `ℝ₊`.
* **Exercise 7.2.4**: with `u` strictly concave, the optimal policy is unique and continuous.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- **Scheffé's lemma** (p. 365), general form: if nonnegative integrable `q_z → q₀` almost
everywhere and `∫ q_z → ∫ q₀`, then `∫ |q_z − q₀| → 0`. -/
theorem scheffe_general {Y X : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter Y}
    [l.IsCountablyGenerated] {q : Y → X → ℝ} {q₀ : X → ℝ} (hq0 : ∀ z x, 0 ≤ q z x)
    (hq₀0 : ∀ x, 0 ≤ q₀ x) (hint : ∀ z, Integrable (q z) μ) (hint₀ : Integrable q₀ μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun z => q z x) l (𝓝 (q₀ x)))
    (hI : Tendsto (fun z => ∫ x, q z x ∂μ) l (𝓝 (∫ x, q₀ x ∂μ))) :
    Tendsto (fun z => ∫ x, |q z x - q₀ x| ∂μ) l (𝓝 0) := by
  have hkey : ∀ z, ∫ x, |q z x - q₀ x| ∂μ =
      2 * ∫ x, max (q₀ x - q z x) 0 ∂μ + (∫ x, q z x ∂μ - ∫ x, q₀ x ∂μ) := by
    intro z
    have hi1 : Integrable (fun x => q₀ x - q z x) μ := hint₀.sub (hint z)
    have habs : ∀ x, |q z x - q₀ x| = 2 * max (q₀ x - q z x) 0 - (q₀ x - q z x) := by
      intro x
      rcases le_total (q₀ x) (q z x) with h | h
      · rw [max_eq_right (sub_nonpos.2 h), abs_of_nonneg (sub_nonneg.2 h)]
        ring
      · rw [max_eq_left (sub_nonneg.2 h), abs_of_nonpos (sub_nonpos.2 h)]
        ring
    simp_rw [habs]
    rw [integral_sub (hi1.pos_part.const_mul 2) hi1, integral_const_mul,
      integral_sub hint₀ (hint z)]
    ring
  have hpos : Tendsto (fun z => ∫ x, max (q₀ x - q z x) 0 ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (F := fun z x => max (q₀ x - q z x) 0) (f := fun _ => (0 : ℝ)) q₀
      (Eventually.of_forall fun z => (hint₀.sub (hint z)).pos_part.aestronglyMeasurable)
      (Eventually.of_forall fun z => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hq0 z x]) (hq₀0 x))
      hint₀ (by
        filter_upwards [hlim] with x hx
        have h2 := (tendsto_const_nhds (x := q₀ x)).sub hx
        rw [sub_self] at h2
        have h3 := h2.max (tendsto_const_nhds (x := (0 : ℝ)))
        rwa [max_self] at h3)
    simpa using this
  have hsub : Tendsto (fun z => ∫ x, q z x ∂μ - ∫ x, q₀ x ∂μ) l (𝓝 0) := by
    have := hI.sub (tendsto_const_nhds (x := ∫ x, q₀ x ∂μ))
    rwa [sub_self] at this
  have := (hpos.const_mul 2).add hsub
  rw [mul_zero, add_zero] at this
  exact this.congr fun z => (hkey z).symm

/-- The optimal savings model of §7.3.1, with the weight function `ℓ` and its properties. -/
structure SavingsU where
  /-- utility -/
  u : ℝ → ℝ
  continuous_u : Continuous u
  u_nonneg : ∀ c, 0 ≤ u c
  monotone_u : Monotone u
  /-- gross return -/
  R : ℝ
  R_nonneg : 0 ≤ R
  /-- discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  /-- the discount factor in (7.25), `δ ∈ (β, 1)` -/
  δ : ℝ
  β_lt_δ : β < δ
  δ_lt_one : δ < 1
  /-- the income distribution -/
  ψ : Measure ℝ
  [isProb : IsProbabilityMeasure ψ]
  /-- the weight function -/
  ℓ : ℝ → ℝ
  measurable_ℓ : Measurable ℓ
  one_le_ℓ : ∀ w, 1 ≤ ℓ w
  monotone_ℓ : Monotone ℓ
  integrable_ℓ : ∀ s, Integrable (fun y => ℓ (s + y)) ψ
  /-- the recursion satisfied by (7.25) -/
  ℓ_rec : ∀ w, u (max w 0) + δ * ∫ y, ℓ (R * w + y) ∂ψ ≤ ℓ w

namespace SavingsU

attribute [local instance] SavingsU.isProb

variable (M : SavingsU)

/-- `B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)ψ(dy)`. -/
noncomputable def B : ℝ → ℝ → (ℝ → ℝ) → ℝ :=
  fun w c v => M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ

theorem δ_pos : 0 < M.δ := M.β_nonneg.trans_lt M.β_lt_δ

theorem integrable_v {v : ℝ → ℝ} (hv : v ∈ blPlus M.ℓ) (s : ℝ) :
    Integrable (fun y => v (s + y)) M.ψ := by
  obtain ⟨hm, h0, C, hC⟩ := hv
  refine ((M.integrable_ℓ s).const_mul |C|).mono'
    (hm.comp (measurable_const_add s)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
  exact (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (zero_le_one.trans (M.one_le_ℓ _)))

theorem integral_ℓ_le (w : ℝ) : ∫ y, M.ℓ (M.R * w + y) ∂M.ψ ≤ M.ℓ w / M.δ := by
  rw [le_div_iff₀ M.δ_pos]
  have h1 := M.ℓ_rec w
  have h2 := M.u_nonneg (max w 0)
  linarith

/-- For feasible `c ≥ 0`, `∫ ℓ(R(w − c) + y) ≤ ∫ ℓ(Rw + y) ≤ ℓ(w)/δ` (`ℓ` increasing). -/
theorem integral_ℓ_feasible_le {w c : ℝ} (hc : 0 ≤ c) :
    ∫ y, M.ℓ (M.R * (w - c) + y) ∂M.ψ ≤ M.ℓ w / M.δ :=
  (integral_mono (M.integrable_ℓ _) (M.integrable_ℓ _) fun y => M.monotone_ℓ (by
    have := mul_le_mul_of_nonneg_left hc M.R_nonneg
    linarith)).trans (M.integral_ℓ_le w)

/-- The savings model as a weighted RDP (§7.3.1); (U2) is the second half of Exercise 7.3.1. -/
noncomputable def wrdp : WRDP ℝ ℝ where
  ℓ := M.ℓ
  measurable_ℓ := M.measurable_ℓ
  one_le_ℓ := M.one_le_ℓ
  Γ w := Icc 0 (max w 0)
  B := M.B
  measurable v hv := by
    have hf : Measurable fun q : (ℝ × ℝ) × ℝ => v (M.R * (q.1.1 - q.1.2) + q.2) :=
      hv.1.comp ((measurable_const.mul ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst))).add measurable_snd)
    exact (M.continuous_u.measurable.comp measurable_snd).add (measurable_const.mul
      (hf.stronglyMeasurable.integral_prod_right' (ν := M.ψ)).measurable)
  nonneg _ c _ v hv := add_nonneg (M.u_nonneg c)
    (mul_nonneg M.β_nonneg (integral_nonneg fun _ => hv.2.1 _))
  mono _ _ _ v hv v' hv' h := add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono (M.integrable_v hv _) (M.integrable_v hv' _) fun _ => h _) M.β_nonneg)
  U2 v hv := by
    obtain ⟨hm, h0, C, hC⟩ := hv
    refine ⟨0, 1 + M.β * |C| / M.δ, le_rfl, add_nonneg zero_le_one
      (div_nonneg (mul_nonneg M.β_nonneg (abs_nonneg C)) M.δ_pos.le), fun w c hc => ?_⟩
    have hI : ∫ y, v (M.R * (w - c) + y) ∂M.ψ ≤ |C| * (M.ℓ w / M.δ) :=
      (integral_mono (M.integrable_v ⟨hm, h0, C, hC⟩ _) ((M.integrable_ℓ _).const_mul |C|)
        fun y => (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
          (zero_le_one.trans (M.one_le_ℓ _)))).trans (by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (M.integral_ℓ_feasible_le hc.1) (abs_nonneg C))
    have hu : M.u c ≤ M.ℓ w := by
      have h1 := M.monotone_u hc.2
      have h2 := M.ℓ_rec w
      have h3 : 0 ≤ ∫ y, M.ℓ (M.R * w + y) ∂M.ψ :=
        integral_nonneg fun _ => zero_le_one.trans (M.one_le_ℓ _)
      nlinarith [M.δ_pos]
    change M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ ≤ 0 + (1 + M.β * |C| / M.δ) * M.ℓ w
    have := mul_le_mul_of_nonneg_left hI M.β_nonneg
    have heq : M.β * (|C| * (M.ℓ w / M.δ)) = M.β * |C| / M.δ * M.ℓ w := by ring
    linarith
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- **Exercise 7.3.1** (p. 232): (U1) holds with `λ = β/δ < 1`, and (U2) holds. -/
theorem exercise_7_3_1 :
    M.wrdp.IsBlackwell (M.β / M.δ) ∧ 0 ≤ M.β / M.δ ∧ M.β / M.δ < 1 ∧
      ∀ v ∈ blPlus M.ℓ, ∃ K N : ℝ, 0 ≤ K ∧ 0 ≤ N ∧
        ∀ w, ∀ c ∈ Set.Icc 0 (max w 0), M.B w c v ≤ K + N * M.ℓ w := by
  refine ⟨fun w c hc v hv κ hκ => ?_, div_nonneg M.β_nonneg M.δ_pos.le,
    (div_lt_one M.δ_pos).2 M.β_lt_δ, M.wrdp.U2⟩
  change M.u c + M.β * ∫ y, (v (M.R * (w - c) + y) + κ * M.ℓ (M.R * (w - c) + y)) ∂M.ψ ≤
    M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ + M.β / M.δ * κ * M.ℓ w
  rw [integral_add (M.integrable_v hv _) ((M.integrable_ℓ _).const_mul κ), integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (M.integral_ℓ_feasible_le (w := w) hc.1) hκ
  have h2 := mul_le_mul_of_nonneg_left h1 M.β_nonneg
  have heq : M.β * (κ * (M.ℓ w / M.δ)) = M.β / M.δ * κ * M.ℓ w := by ring
  nlinarith

/-! ### Continuity with a density -/

/-- Integrals against the density `φ`: `∫ g(s + y)ψ(dy) = ∫ g(x)φ(x − s) dx`. -/
theorem integral_shift_density {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hψ : M.ψ = Savings.densityMeasure φ) (g : ℝ → ℝ) (s : ℝ) :
    ∫ y, g (s + y) ∂M.ψ = ∫ x, g x * φ (x - s) := by
  rw [hψ, Savings.densityMeasure, integral_withDensity_eq_integral_smul
    (f := fun y => (φ y).toNNReal) hφc.measurable.real_toNNReal,
    ← integral_sub_right_eq_self (μ := volume) (fun y => (φ y).toNNReal • g (s + y)) s]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 _), smul_eq_mul, add_sub_cancel]
  ring

theorem integrable_shift_density {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hψ : M.ψ = Savings.densityMeasure φ) {g : ℝ → ℝ} {s : ℝ}
    (hg : Integrable (fun y => g (s + y)) M.ψ) : Integrable (fun x => g x * φ (x - s)) := by
  rw [hψ, Savings.densityMeasure, integrable_withDensity_iff_integrable_smul
    hφc.measurable.real_toNNReal] at hg
  refine (hg.comp_sub_right s).congr (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 _), smul_eq_mul, add_sub_cancel]
  ring

/-- `s ↦ ∫ ℓ(s + y)ψ(dy)` is continuous when `ℓ` is (dominated convergence, `ℓ` increasing). -/
theorem continuous_integral_ℓ (hℓc : Continuous M.ℓ) :
    Continuous fun s => ∫ y, M.ℓ (s + y) ∂M.ψ := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  refine continuousAt_of_dominated (bound := fun y => M.ℓ (s₀ + 1 + y))
    (Eventually.of_forall fun s =>
      (M.measurable_ℓ.comp (measurable_const_add s)).aestronglyMeasurable)
    ?_ (M.integrable_ℓ _) (Eventually.of_forall fun y =>
      (hℓc.comp (continuous_id.add continuous_const)).continuousAt)
  filter_upwards [Iio_mem_nhds (lt_add_one s₀)] with s hs
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (M.one_le_ℓ _))]
  exact M.monotone_ℓ (by linarith [mem_Iio.1 hs])

/-- **Exercise 7.3.2** (p. 232): if income has a continuous density `φ` and `ℓ` is continuous, then
`(w, c) ↦ B(w, c, v)` is continuous for every `v ∈ bℓX₊` (Assumption 7.2.7). -/
theorem exercise_7_3_2 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) {v : ℝ → ℝ}
    (hv : v ∈ blPlus M.ℓ) : Continuous fun p : ℝ × ℝ => M.B p.1 p.2 v := by
  obtain ⟨hm, h0, C, hC⟩ := hv
  have hvbl : v ∈ blPlus M.ℓ := ⟨hm, h0, C, hC⟩
  -- `q_s(x) = ℓ(x)φ(x − s)`
  let q : ℝ → ℝ → ℝ := fun s x => M.ℓ x * φ (x - s)
  have hqint : ∀ s, Integrable (q s) := fun s =>
    M.integrable_shift_density hφc hφ0 hψ (M.integrable_ℓ s)
  have hvint : ∀ s, Integrable fun x => v x * φ (x - s) := fun s =>
    M.integrable_shift_density hφc hφ0 hψ (M.integrable_v hvbl s)
  have hI : Continuous fun s => ∫ y, v (s + y) ∂M.ψ := by
    refine continuous_iff_continuousAt.2 fun s₀ => ?_
    have hS := scheffe_general (μ := volume) (l := 𝓝 s₀) (q := q) (q₀ := q s₀)
      (fun s x => mul_nonneg (zero_le_one.trans (M.one_le_ℓ x)) (hφ0 _))
      (fun x => mul_nonneg (zero_le_one.trans (M.one_le_ℓ x)) (hφ0 _)) hqint (hqint s₀)
      (Eventually.of_forall fun x =>
        ((hφc.comp (continuous_const.sub continuous_id)).tendsto s₀).const_mul (M.ℓ x))
      (by
        have h := (M.continuous_integral_ℓ hℓc).tendsto s₀
        simp only [M.integral_shift_density hφc hφ0 hψ M.ℓ] at h
        exact h)
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ (by simpa using hS.const_mul |C|))
    refine Eventually.of_forall fun s => ?_
    dsimp only
    rw [M.integral_shift_density hφc hφ0 hψ v s, M.integral_shift_density hφc hφ0 hψ v s₀,
      ← integral_sub (hvint s) (hvint s₀), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (((hqint s).sub (hqint s₀)).abs.const_mul _)
      (Eventually.of_forall fun x => ?_)
    have hl : 0 ≤ M.ℓ x := zero_le_one.trans (M.one_le_ℓ x)
    have hvx : |v x| ≤ |C| * M.ℓ x := by
      rw [abs_of_nonneg (h0 x)]
      exact (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hl)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, show q s x - q s₀ x = M.ℓ x * (φ (x - s) - φ (x - s₀))
      from by ring, abs_mul, abs_of_nonneg hl, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hvx (abs_nonneg _)
  exact (M.continuous_u.comp continuous_snd).add (continuous_const.mul
    (hI.comp ((continuous_const.mul (continuous_fst.sub continuous_snd)))))

theorem hasMaxSelections : HasMaxSelections M.wrdp.Γ :=
  hasMaxSelections_Icc (g := fun _ => 0) (h := fun w => max w 0) continuous_const
    (continuous_id.max continuous_const) fun _ => le_max_right _ _

/-- The savings model with a continuous income density satisfies the conditions of
Proposition 7.2.5, with Assumption 7.2.7 (Exercises 7.3.1 and 7.3.2). -/
theorem continuousCase (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) : M.wrdp.ContinuousCase :=
  ⟨hℓc, M.hasMaxSelections, ⟨_, M.exercise_7_3_1.2.1, M.exercise_7_3_1.2.2.1,
    M.exercise_7_3_1.1⟩, fun _ hv _ => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn⟩

/-- §7.3.1 (p. 232): the conclusions of Proposition 7.2.5 hold: the fundamental optimality
properties, `v* ∈ bℓcℝ₊` satisfies the Bellman equation, VFI converges geometrically on `bℓcℝ₊`,
and OPI and HPI converge. -/
theorem section_7_3_1 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) :
    ∃ hw : M.wrdp.toRDP.adp.WellPosed, M.wrdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus ℝ, Continuous (wev M.ℓ vstar) ∧
        M.wrdp.toRDP.adp.VFIGeometric (bcPlus ℝ) vstar ∧
        ∀ g, M.wrdp.toRDP.adp.IsSelector g →
          M.wrdp.toRDP.adp.OPIConverges g vstar ∧ M.wrdp.toRDP.adp.HPIConverges hw g vstar := by
  obtain ⟨hw, hFO, vstar, hv, hvc, hgeo, hconv⟩ := M.wrdp.proposition_7_2_5 hℓc
    M.hasMaxSelections M.exercise_7_3_1.2.1 M.exercise_7_3_1.2.2.1 M.exercise_7_3_1.1
    fun _ hv _ => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn
  exact ⟨hw, hFO, vstar, hv, hvc, hgeo,
    hconv fun _ hv => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn⟩

/-! ### Shape of the value function and the optimal policy -/

/-- **Exercise 7.2.2** (p. 224): Assumption 7.2.8 holds: `Γ` is increasing and
`B(w, c, v) ≤ B(w', c, v)` for `w ≤ w'`, `c ∈ Γ(w)` and increasing `v`. -/
theorem exercise_7_2_2 :
    (∀ w w', w ≤ w' → M.wrdp.Γ w ⊆ M.wrdp.Γ w') ∧
      ∀ w w', w ≤ w' → ∀ v ∈ blPlus M.ℓ, Continuous v → Monotone v →
        ∀ c ∈ M.wrdp.Γ w, M.wrdp.B w c v ≤ M.wrdp.B w' c v := by
  refine ⟨fun w w' h => Icc_subset_Icc le_rfl (max_le_max h le_rfl),
    fun w w' h v hv _ hmono c _ => ?_⟩
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono (M.integrable_v hv _)
    (M.integrable_v hv _) fun y => hmono ?_) M.β_nonneg)
  have := mul_le_mul_of_nonneg_left h M.R_nonneg
  linarith

/-- Under Exercise 7.2.2, `v*` is increasing (Proposition 7.2.6). -/
theorem vstar_monotone (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) :
    ∃ vstar, M.wrdp.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) := by
  obtain ⟨-, -, vstar, -, hv, hmono⟩ := WRDP.proposition_7_2_6 (M.continuousCase hℓc hφc hφ0 hψ)
    M.exercise_7_2_2.1 M.exercise_7_2_2.2
  exact ⟨vstar, hv, hmono⟩

/-- The feasible pairs with `w ≥ 0`, `{(w, c) : 0 ≤ c ≤ w}`, form a convex set. -/
theorem convex_feasibleOn : Convex ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) := by
  rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
  have h1 : (0 : ℝ) ≤ w₁ := hw₁
  have h2 : (0 : ℝ) ≤ w₂ := hw₂
  change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
  change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
  rw [max_eq_left h1] at hc₁
  rw [max_eq_left h2] at hc₂
  change (0 : ℝ) ≤ a * w₁ + b * w₂ ∧ a * c₁ + b * c₂ ∈ Icc 0 (max (a * w₁ + b * w₂) 0)
  refine ⟨by positivity, ⟨by nlinarith [hc₁.1, hc₂.1], le_max_of_le_left ?_⟩⟩
  nlinarith [hc₁.2, hc₂.2]

/-- The integral term is concave in `(w, c)` over feasible pairs, for `v` concave on `ℝ₊`, when
income is nonnegative. -/
theorem integral_concave (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y) {v : ℝ → ℝ} (hv : v ∈ blPlus M.ℓ)
    (hconc : ConcaveOn ℝ (Ici 0) v) {w₁ c₁ w₂ c₂ a b : ℝ} (hc₁ : c₁ ≤ w₁) (hc₂ : c₂ ≤ w₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ + b * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ ≤
      ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((M.integrable_v hv _).const_mul a) ((M.integrable_v hv _).const_mul b)]
  refine integral_mono_ae (((M.integrable_v hv _).const_mul a).add
    ((M.integrable_v hv _).const_mul b)) (M.integrable_v hv _) ?_
  filter_upwards [hψ0] with y hy
  have hx₁ : M.R * (w₁ - c₁) + y ∈ Ici (0 : ℝ) :=
    add_nonneg (mul_nonneg M.R_nonneg (sub_nonneg.2 hc₁)) hy
  have hx₂ : M.R * (w₂ - c₂) + y ∈ Ici (0 : ℝ) :=
    add_nonneg (mul_nonneg M.R_nonneg (sub_nonneg.2 hc₂)) hy
  have := hconc.2 hx₁ hx₂ ha hb hab
  simp only [smul_eq_mul] at this
  have heq : a * (M.R * (w₁ - c₁) + y) + b * (M.R * (w₂ - c₂) + y) =
      M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y := by
    linear_combination y * hab
  rw [heq] at this
  exact this

/-- **Exercise 7.2.3** (p. 224): if `u` is also concave on `ℝ₊` and income is nonnegative, then
`v*` is increasing and concave on `ℝ₊` (Propositions 7.2.6 and 7.2.7). -/
theorem exercise_7_2_3 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y)
    (hu : ConcaveOn ℝ (Ici 0) M.u) :
    ∃ vstar, M.wrdp.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) ∧
      ConcaveOn ℝ (Ici 0) (wev M.ℓ vstar) := by
  have hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      ConcaveOn ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) fun p => M.wrdp.B p.1 p.2 v := by
    intro v hv _ hconc
    refine ⟨M.convex_feasibleOn, ?_⟩
    rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
    have h1 : (0 : ℝ) ≤ w₁ := hw₁
    have h2 : (0 : ℝ) ≤ w₂ := hw₂
    change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
    change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
    rw [max_eq_left h1] at hc₁
    rw [max_eq_left h2] at hc₂
    have hU := hu.2 (mem_Ici.2 hc₁.1) (mem_Ici.2 hc₂.1) ha hb hab
    have hI := M.integral_concave hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
    simp only [smul_eq_mul] at hU
    change a * (M.u c₁ + M.β * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ) +
        b * (M.u c₂ + M.β * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ) ≤
      M.u (a * c₁ + b * c₂) +
        M.β * ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ
    nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
  obtain ⟨-, -, v₁, -, hv₁, hconc⟩ := WRDP.proposition_7_2_7 (M.continuousCase hℓc hφc hφ0 hψ)
    (convex_Ici 0) M.convex_feasibleOn hBc
  obtain ⟨v₂, hv₂, hmono⟩ := M.vstar_monotone hℓc hφc hφ0 hψ
  rw [hv₂.unique hv₁] at hmono
  exact ⟨v₁, hv₁, hmono, hconc⟩

/-- **Exercise 7.2.4** (p. 225): if `u` is strictly concave on `ℝ₊` and income is nonnegative,
the optimal policy is unique and continuous (Proposition 7.2.8). -/
theorem exercise_7_2_4 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y)
    (hu : StrictConcaveOn ℝ (Ici 0) M.u) :
    ∃ hw : M.wrdp.toRDP.adp.WellPosed, M.wrdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ σ, M.wrdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, M.wrdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        Continuous σ.1 := by
  have hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      ConcaveOn ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) fun p => M.wrdp.B p.1 p.2 v := by
    intro v hv _ hconc
    refine ⟨M.convex_feasibleOn, ?_⟩
    rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
    have h1 : (0 : ℝ) ≤ w₁ := hw₁
    have h2 : (0 : ℝ) ≤ w₂ := hw₂
    change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
    change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
    rw [max_eq_left h1] at hc₁
    rw [max_eq_left h2] at hc₂
    have hU := hu.concaveOn.2 (mem_Ici.2 hc₁.1) (mem_Ici.2 hc₂.1) ha hb hab
    have hI := M.integral_concave hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
    simp only [smul_eq_mul] at hU
    change a * (M.u c₁ + M.β * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ) +
        b * (M.u c₂ + M.β * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ) ≤
      M.u (a * c₁ + b * c₂) +
        M.β * ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ
    nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
  have hstrict : ∀ w, ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      StrictConcaveOn ℝ (M.wrdp.Γ w) fun c => M.wrdp.B w c v := by
    intro w v hv _ hconc
    change StrictConcaveOn ℝ (Icc 0 (max w 0)) fun c =>
      M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ
    rcases le_or_gt 0 w with hw | hw
    · rw [max_eq_left hw]
      have hconcI : ConcaveOn ℝ (Icc 0 w) fun c => M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ := by
        refine ⟨convex_Icc 0 w, fun c₁ hc₁ c₂ hc₂ a b ha hb hab => ?_⟩
        have hI := M.integral_concave (w₁ := w) (w₂ := w) hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
        have hw' : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
        rw [hw'] at hI
        simp only [smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
      exact (hu.subset Icc_subset_Ici_self (convex_Icc 0 w)).add_concaveOn hconcI
    · rw [max_eq_right hw.le]
      refine ⟨convex_Icc 0 0, fun x hx y hy hxy => absurd ?_ hxy⟩
      rw [le_antisymm hx.2 hx.1, le_antisymm hy.2 hy.1]
  obtain ⟨hw, hFO, σ, hσ, huniq, hcont⟩ := WRDP.proposition_7_2_8 (M.continuousCase hℓc hφc hφ0 hψ)
    (convex_Ici 0) M.convex_feasibleOn hBc hstrict
  exact ⟨hw, hFO, σ, hσ, huniq, hcont (hasContinuousUniqueMax_Icc continuous_const
    (continuous_id.max continuous_const) fun _ => le_max_right _ _)⟩

end SavingsU

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Irreversible investment

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.2–§7.3.3 (pp. 233–241).

Capital `k ∈ ℝ`, an exogenous state `z ∈ E` with `Z' = g(Z, ξ)`, `ξ ∼ φ`, investment
`i ∈ Γ(k, z) = [0, θf(k, z)]`, and the aggregator
`B(k, z, i, v) = f(k, z) − i + β ℰ[v(i + (1 − δ)k, g(z, ξ))]`.

* Assumption 7.3.1: `f` bounded and continuous; `g` measurable with `g(·, ξ)` continuous for each
  `ξ` (implied by joint continuity). Nonemptiness of `Γ` needs `θf ≥ 0`; `f ≥ 0` and `θ ≥ 0` are
  assumed. The exogenous state lies in any first countable Borel space (`ℝᵐ` in the book).
* **Proposition 7.3.1** and **Exercise 7.3.3**: with `ℰ = 𝔼`, the conclusions of
  Proposition 7.2.10.
* **Proposition 7.3.2**: the same for any continuous certainty equivalent `ℰ` (§7.3.2.2).
* **Example 7.3.1**: Proposition 7.3.2 applies to the entropic certainty equivalent (the CVaR case
  rests on Example 7.2.2, not formalised).
* §7.3.3.2: the risk-sensitive form of the robust firm problem,
  `B = f − i − (β/γ) ln ∫ exp[−γ v(k', g(z, ξ))]φ(dξ)`, `γ > 0`, satisfies the conclusions of
  Proposition 7.3.2. The passage from the robust (7.3.3.1) to the risk-sensitive form is the
  duality (7.22), which is not formalised.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable (E Ξ : Type*) [TopologicalSpace E] [MeasurableSpace E] [MeasurableSpace Ξ] in
/-- The irreversible investment model of §7.3.2.1 under Assumption 7.3.1. -/
structure Investment where
  /-- production (revenue) -/
  F : ℝ × E → ℝ
  continuous_F : Continuous F
  F_nonneg : ∀ x, 0 ≤ F x
  F_bdd : ∃ C, ∀ x, F x ≤ C
  /-- the exogenous law of motion -/
  g : E → Ξ → E
  measurable_g : Measurable (uncurry g)
  continuous_g : ∀ ξ, Continuous fun z => g z ξ
  /-- the borrowing constraint parameter -/
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  /-- the depreciation rate -/
  δ : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the shock distribution -/
  φ : Measure Ξ
  [isProb : IsProbabilityMeasure φ]

namespace Investment

attribute [local instance] Investment.isProb

variable {E Ξ : Type*} [TopologicalSpace E] [FirstCountableTopology E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace Ξ] (M : Investment E Ξ)

/-- `Γ(k, z) = [0, θf(k, z)]`. -/
def Γ (x : ℝ × E) : Set ℝ := Icc 0 (M.θ * M.F x)

/-- The reward `r(k, z, i) = f(k, z) − i`. -/
def r (p : (ℝ × E) × ℝ) : ℝ := M.F p.1 - p.2

/-- The transition `(k, z, i, ξ) ↦ (i + (1 − δ)k, g(z, ξ))`. -/
def next (p : (ℝ × E) × ℝ) (ξ : Ξ) : ℝ × E := (p.2 + (1 - M.δ) * p.1.1, M.g p.1.2 ξ)

omit [FirstCountableTopology E] in
theorem measurable_r : Measurable M.r :=
  (M.continuous_F.measurable.comp measurable_fst).sub measurable_snd

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem r_bdd : ∃ C, ∀ x, ∀ a ∈ M.Γ x, |M.r (x, a)| ≤ C := by
  obtain ⟨C, hC⟩ := M.F_bdd
  refine ⟨C + M.θ * C, fun x a ha => ?_⟩
  have h1 := hC x
  have h2 := M.F_nonneg x
  have h3 := mul_le_mul_of_nonneg_left h1 M.θ_nonneg
  change |M.F x - a| ≤ _
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2]

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem measurable_next : Measurable (uncurry M.next) :=
  ((measurable_snd.comp measurable_fst).add (measurable_const.mul
    (measurable_fst.comp (measurable_fst.comp measurable_fst)))).prodMk
    (M.measurable_g.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd))

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem exists_policy : ∃ σ : ℝ × E → ℝ, Measurable σ ∧ ∀ x, σ x ∈ M.Γ x :=
  ⟨fun _ => 0, measurable_const, fun x => ⟨le_rfl, mul_nonneg M.θ_nonneg (M.F_nonneg x)⟩⟩

theorem hasMaxSelections : HasMaxSelections M.Γ :=
  hasMaxSelections_Icc continuous_const (continuous_const.mul M.continuous_F)
    fun x => mul_nonneg M.θ_nonneg (M.F_nonneg x)

/-- The measurability assumption of §7.3.2.2: `(k, z, i) ↦ ℰ[v(i + (1 − δ)k, g(z, ξ))]` is
measurable for every `v ∈ bX`. -/
def IsMeasurableCE (E' : (Ξ → ℝ) → ℝ) : Prop :=
  ∀ v : BM (ℝ × E), Measurable fun p : (ℝ × E) × ℝ => E' fun ξ => v.toFun (M.next p ξ)

/-- The firm problem with certainty equivalent `ℰ` as an RDP on `bX` (§7.3.2.2). -/
noncomputable def rdp {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E') (hEm : M.IsMeasurableCE E') :
    BRDP (ℝ × E) ℝ :=
  ceBRDP M.Γ M.r M.measurable_r M.r_bdd M.β_nonneg M.φ M.measurable_next hE hEm M.exists_policy

omit [FirstCountableTopology E] in
/-- The aggregator (7.26): `B(k, z, i, v) = f(k, z) − i + β ℰ[v(i + (1 − δ)k, g(z, ξ))]`. -/
theorem rdp_B {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E') (hEm : M.IsMeasurableCE E')
    (k : ℝ) (z : E) (i : ℝ) (v : ℝ × E → ℝ) :
    (M.rdp hE hEm).B (k, z) i v =
      M.F (k, z) - i + M.β * E' fun ξ => v (i + (1 - M.δ) * k, M.g z ξ) :=
  rfl

/-- **Proposition 7.3.2** (p. 237): if Assumption 7.3.1 holds and `ℰ` is a continuous certainty
equivalent, then (i) the fundamental optimality properties hold, (ii) `v* ∈ bcX` and (iii) VFI
converges geometrically on `bcX`. -/
theorem proposition_7_3_2 [Nonempty E] {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E')
    (hEm : M.IsMeasurableCE E') (hEc : IsContinuousCE M.φ E') :
    ∃ hw : (M.rdp hE hEm).toRDP.adp.WellPosed, (M.rdp hE hEm).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), (M.rdp hE hEm).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  proposition_7_2_10 M.Γ M.r M.measurable_r M.r_bdd M.β_nonneg M.β_lt_one M.φ M.measurable_next
    hE hEm M.exists_policy M.hasMaxSelections
    ((M.continuous_F.comp continuous_fst).sub continuous_snd).continuousOn
    (fun ξ => ((continuous_snd.add (continuous_const.mul
      (continuous_fst.comp continuous_fst))).prodMk
      ((M.continuous_g ξ).comp (continuous_snd.comp continuous_fst))).continuousOn) hEc

/-- The risk-neutral firm problem (§7.3.2.1): `ℰ = 𝔼`. -/
noncomputable def meanRDP : BRDP (ℝ × E) ℝ :=
  M.rdp meanCE_isCoherent.1 (measurable_meanCE_comp M.measurable_next)

/-- The firm problem with the entropic certainty equivalent `ℰ^θ`. -/
noncomputable def entropicRDP {θ : ℝ} (hθ : θ ≠ 0) : BRDP (ℝ × E) ℝ :=
  M.rdp (entropicCE_isCertEquiv hθ) (measurable_entropicCE_comp M.measurable_next θ)

/-- **Proposition 7.3.1** (p. 234) and **Exercise 7.3.3** (p. 234): under Assumption 7.3.1, the
risk-neutral firm problem `B(k, z, i, v) = f(k, z) − i + β ∫ v(i + (1 − δ)k, g(z, ξ))φ(dξ)` is an
RDP, the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on
`bcX` (Proposition 7.2.10 with `ℰ = 𝔼`). -/
theorem proposition_7_3_1 [Nonempty E] :
    ∃ hw : M.meanRDP.toRDP.adp.WellPosed, M.meanRDP.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), M.meanRDP.toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  M.proposition_7_3_2 _ _ example_7_2_1

/-- **Example 7.3.1** (p. 237): Proposition 7.3.2 applies with the entropic certainty equivalent
(Exercise 7.2.6), for every `θ ≠ 0`. -/
theorem example_7_3_1 [Nonempty E] {θ : ℝ} (hθ : θ ≠ 0) :
    ∃ hw : (M.entropicRDP hθ).toRDP.adp.WellPosed,
      (M.entropicRDP hθ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), (M.entropicRDP hθ).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  M.proposition_7_3_2 _ _ (exercise_7_2_6 θ)

/-- §7.3.3.2 (p. 240): the risk-sensitive form of the robust firm problem has aggregator
`f(k, z) − i − (β/γ) ln ∫ exp[−γ v(k', g(z, ξ))]φ(dξ)`, the case `ℰ = ℰ_γ` (`θ = −γ`) of (7.26);
for `γ > 0` the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges
geometrically on `bcX`. -/
theorem section_7_3_3 [Nonempty E] {γ : ℝ} (hγ : 0 < γ) :
    (∀ k z i (v : ℝ × E → ℝ), (M.entropicRDP (neg_ne_zero.2 hγ.ne')).B (k, z) i v =
        M.F (k, z) - i - M.β / γ *
          Real.log (∫ ξ, Real.exp (-γ * v (i + (1 - M.δ) * k, M.g z ξ)) ∂M.φ)) ∧
    ∃ hw : (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.WellPosed,
      (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E),
        (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar := by
  refine ⟨fun k z i v => ?_, M.example_7_3_1 (neg_ne_zero.2 hγ.ne')⟩
  change M.F (k, z) - i + M.β * ((-γ)⁻¹ * Real.log
    (∫ ξ, Real.exp (-γ * v (i + (1 - M.δ) * k, M.g z ξ)) ∂M.φ)) = _
  field_simp
  ring

end Investment

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Kreps–Porteus versus risk sensitivity

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.4 (pp. 241–244).

In the setting of §7.2.5 (`ξ ∼ φ`, transition `f(x, a, ξ)`):

* the risk-sensitive MDP (7.28), `B_RS(x, a, v) = r(x, a) + (β/θ) ln 𝔼 exp(θ v(f(x, a, ξ)))`, is
  the case `ℰ = ℰ^θ` of (7.24); Proposition 7.2.10 applies (`section_7_3_4`);
* the multiplicative Kreps–Porteus aggregator
  `B_MKP(x, a, v) = r(x, a) {𝔼 v(f(x, a, ξ))^ν}^{β/ν}`, `ν ≠ 0`, with `r = exp r̂` positive, gives
  an RDP (`mkpRDP`) on the measurable `v` with `e^{−K} ≤ v ≤ e^K` for some `K`;
* **Exercise 7.3.4**: `v ↦ ln v` is an isomorphism of the generated ADPs, with
  `B_MKP(x, a, v) = exp[B_RS(x, a, ln v)]` (with `r̂ = ln r`, `θ = ν`; Exercise 7.1.5).

The book's solution takes the bounded measurable `v > 0`, whose logarithms need not be bounded
below; `ln v ∈ bX` exactly when `v` is bounded above and away from zero, which is the value space
used here. The reward `r̂ = ln r` is bounded on `G`, as `(Γ, bX, B_RS)` requires.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A Ξ : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Ξ]

/-- The risk-sensitive MDP (7.28): `B_RS(x, a, v) = r(x, a) + (β/θ) ln 𝔼 exp(θ v(f(x, a, ξ)))`. -/
noncomputable def rsRDP (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {θ : ℝ}
    (hθ : θ ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : BRDP X A :=
  ceBRDP Γ r hr hrb hβ φ hf (entropicCE_isCertEquiv hθ) (measurable_entropicCE_comp hf θ) hΓ

theorem rsRDP_B (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {θ : ℝ}
    (hθ : θ ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (x : X) (a : A)
    (v : X → ℝ) :
    (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).B x a v =
      r (x, a) + β / θ * Real.log (∫ ξ, Real.exp (θ * v (f (x, a) ξ)) ∂φ) := by
  change r (x, a) + β * (θ⁻¹ * Real.log (∫ ξ, Real.exp (θ * v (f (x, a) ξ)) ∂φ)) = _
  ring

/-- §7.3.4 (p. 243): the risk-sensitive MDP satisfies the conclusions of Proposition 7.2.10 under
Assumption 7.2.11: the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges
geometrically on `bcX`. -/
theorem section_7_3_4 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    [FirstCountableTopology X] [FirstCountableTopology A] (Γ : X → Set A) (r : X × A → ℝ)
    (hr : Measurable r) (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) (φ : Measure Ξ) [IsProbabilityMeasure φ] {f : X × A → Ξ → X}
    (hf : Measurable (uncurry f)) {θ : ℝ} (hθ : θ ≠ 0)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (hΓmax : HasMaxSelections Γ)
    (hrc : ContinuousOn r {p | p.2 ∈ Γ p.1})
    (hfc : ∀ z, ContinuousOn (fun p => f p z) {p | p.2 ∈ Γ p.1}) :
    ∃ hw : (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.WellPosed,
      (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X,
        (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.VFIGeometric (LDP.bc X) vstar :=
  proposition_7_2_10 Γ r hr hrb hβ hβ1 φ hf _ _ hΓ hΓmax hrc hfc (exercise_7_2_6 θ)

/-- Measurable `v : X → ℝ` with `e^{−K} ≤ v ≤ e^K` for some `K`: the positive functions with
`ln v ∈ bX`. -/
abbrev PosValues (X : Type*) [MeasurableSpace X] : Type _ :=
  {v : X → ℝ // Measurable v ∧ ∃ K, ∀ x, Real.exp (-K) ≤ v x ∧ v x ≤ Real.exp K}

theorem PosValues.pos (v : PosValues X) (x : X) : 0 < v.1 x := by
  obtain ⟨K, hK⟩ := v.2.2
  exact (Real.exp_pos _).trans_le (hK x).1

theorem PosValues.abs_log_le (v : PosValues X) : ∃ K, ∀ x, |Real.log (v.1 x)| ≤ K := by
  obtain ⟨K, hK⟩ := v.2.2
  refine ⟨K, fun x => abs_le.2 ⟨?_, ?_⟩⟩
  · have := Real.log_le_log (Real.exp_pos _) (hK x).1
    rwa [Real.log_exp] at this
  · have := Real.log_le_log (v.pos x) (hK x).2
    rwa [Real.log_exp] at this

/-- `ln v ∈ bX`. -/
noncomputable def PosValues.log (v : PosValues X) : BM X :=
  ⟨fun x => Real.log (v.1 x), Real.measurable_log.comp v.2.1, v.abs_log_le⟩

/-- `exp h` for `h ∈ bX`. -/
noncomputable def PosValues.exp (h : BM X) : PosValues X :=
  ⟨fun x => Real.exp (h.toFun x), Real.measurable_exp.comp h.measurable', ‖h‖, fun x =>
    ⟨Real.exp_le_exp.2 (neg_le_of_abs_le (BM.abs_le_norm h x)),
      Real.exp_le_exp.2 (le_of_abs_le (BM.abs_le_norm h x))⟩⟩

/-- The multiplicative Kreps–Porteus aggregator
`B_MKP(x, a, v) = r(x, a) {𝔼 v(f(x, a, ξ))^ν}^{β/ν}` with `r = exp r̂`. -/
noncomputable def mkpAgg (rhat : X × A → ℝ) (β ν : ℝ) (φ : Measure Ξ) (f : X × A → Ξ → X) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => Real.exp (rhat (x, a)) * (∫ ξ, v (f (x, a) ξ) ^ ν ∂φ) ^ (β / ν)

/-- Taking logs (p. 243): `B_MKP(x, a, v) = exp[B_RS(x, a, ln v)]` with `r̂ = ln r` and `θ = ν`. -/
theorem mkpAgg_eq_exp (rhat : X × A → ℝ) (β ν : ℝ) (φ : Measure Ξ) [IsProbabilityMeasure φ]
    {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) (v : PosValues X) (x : X) (a : A) :
    mkpAgg rhat β ν φ f x a v.1 =
      Real.exp (ceAgg rhat β f (entropicCE φ ν) x a (Real.log ∘ v.1)) := by
  have hL : IsLInf φ fun ξ => Real.log (v.1 (f (x, a) ξ)) := by
    obtain ⟨K, hK⟩ := v.abs_log_le
    exact ⟨(Real.measurable_log.comp
      (v.2.1.comp (measurable_section hf (x, a)))).aestronglyMeasurable,
      K, Eventually.of_forall fun ξ => hK _⟩
  have hI : ∫ ξ, v.1 (f (x, a) ξ) ^ ν ∂φ = ∫ ξ, Real.exp (ν * Real.log (v.1 (f (x, a) ξ))) ∂φ :=
    integral_congr_ae (Eventually.of_forall fun ξ => by
      change v.1 (f (x, a) ξ) ^ ν = Real.exp (ν * Real.log (v.1 (f (x, a) ξ)))
      rw [Real.rpow_def_of_pos (v.pos _), mul_comm])
  change Real.exp (rhat (x, a)) * (∫ ξ, v.1 (f (x, a) ξ) ^ ν ∂φ) ^ (β / ν) =
    Real.exp (rhat (x, a) +
      β * (ν⁻¹ * Real.log (∫ ξ, Real.exp (ν * Real.log (v.1 (f (x, a) ξ))) ∂φ)))
  rw [hI, Real.rpow_def_of_pos (integral_exp_pos' hL ν), ← Real.exp_add]
  congr 1
  ring

/-- The multiplicative Kreps–Porteus RDP `(Γ, V, B_MKP)` (§7.3.4), with `V` the measurable `v`
satisfying `e^{−K} ≤ v ≤ e^K` for some `K`. -/
noncomputable def mkpRDP (Γ : X → Set A) (rhat : X × A → ℝ) (hr : Measurable rhat)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |rhat (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {ν : ℝ}
    (hν : ν ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    RDP X A (PosValues X) where
  ev v := v.1
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := mkpAgg rhat β ν φ f
  mono x a ha v w h := by
    rw [mkpAgg_eq_exp rhat β ν φ hf v, mkpAgg_eq_exp rhat β ν φ hf w]
    exact Real.exp_le_exp.2 ((rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).mono x a ha v.log w.log
      (BM.le_def.2 fun y => Real.log_le_log (v.pos y) (h y)))
  consistent σ hσ hσΓ v := by
    let R := rsRDP Γ rhat hr hrb hβ φ hf hν hΓ
    refine ⟨PosValues.exp (R.toRDP.adp.T ⟨σ, hσ, hσΓ⟩ v.log), funext fun x => ?_⟩
    change Real.exp ((R.toRDP.adp.T ⟨σ, hσ, hσΓ⟩ v.log).toFun x) = _
    rw [R.toRDP_T_apply, mkpAgg_eq_exp rhat β ν φ hf v]
    rfl
  exists_policy := hΓ

/-- **Exercise 7.3.4** (p. 244): the multiplicative Kreps–Porteus RDP and the risk-sensitive RDP
(with `r̂ = ln r` and `θ = ν`) generate isomorphic ADPs: `v ↦ ln v` is an order isomorphism
conjugating their policy operators (Exercise 7.1.5 with `φ = ln`). -/
theorem exercise_7_3_4 (Γ : X → Set A) (rhat : X × A → ℝ) (hr : Measurable rhat)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |rhat (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {ν : ℝ}
    (hν : ν ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    ∃ F : PosValues X ≃o BM X, (∀ v, (F v).toFun = Real.log ∘ v.1) ∧
      ∀ (σ : (mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).Policy)
        (σ' : (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP.Policy), σ.1 = σ'.1 → ∀ v,
        F ((mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).adp.T σ v) =
          (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP.adp.T σ' (F v) :=
  (mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).exercise_7_1_5 (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP
    Real.log Real.exp Real.strictMonoOn_log (fun _ ht => Real.exp_log ht)
    (fun v x => v.pos x) (fun v => ⟨v.log, rfl⟩)
    (fun h => ⟨PosValues.exp h, funext fun _ => (Real.log_exp _).symm⟩)
    (fun x a _ v => mkpAgg_eq_exp rhat β ν φ hf v x a)

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
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBdd
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupContraction
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsUniformlyClosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.isBdd_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBdd.sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBdd.add
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBdd.nonneg_bound
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBdd.exists_dist
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupContraction.iterate
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupContraction.exists_limit
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupContraction.globallyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_of_le_map_of_tendsto
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_of_map_le_of_tendsto
#print axioms SargentStachurski.RecursiveDecisionProcesses.bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.isUniformlyClosed_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.const_mem_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_max_sub_max_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.integrable_of_mem_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_markovOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_markovOp_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_mem_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_add
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_smul
#print axioms SargentStachurski.RecursiveDecisionProcesses.markovOp_sub_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_markovOp_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.OrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.IncreasesTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.DecreasesTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.StronglyOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.orderStable_of_up_down
#print axioms SargentStachurski.RecursiveDecisionProcesses.StronglyOrderStable.orderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.dualMap
#print axioms SargentStachurski.RecursiveDecisionProcesses.orderStable_dual_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.dualMap_iterate
#print axioms SargentStachurski.RecursiveDecisionProcesses.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete.exists_least
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.ChainComplete.orderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.chainComplete_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.CountablyDedekindComplete
#print axioms SargentStachurski.RecursiveDecisionProcesses.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.RecursiveDecisionProcesses.CountablyDedekindComplete.dual
#print axioms SargentStachurski.RecursiveDecisionProcesses.OrderContinuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.OrderContinuous.monotone
#print axioms SargentStachurski.RecursiveDecisionProcesses.isLUB_range_succ_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.tarski_kantorovich
#print axioms SargentStachurski.RecursiveDecisionProcesses.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.T
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VG
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.WellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsFinite
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.Regular
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsBellmanValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.SolvesBellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.regular_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isGreedy_greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.T_le_bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isGreedy_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.solvesBellman_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VU
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VSig
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.T_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.eq_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VSig_eq_range
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOptimal
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsValueFunction
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.BellmanPrinciple
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.FundamentalOptimality
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isOptimal_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.exists_solves_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsSelector
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.howard
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.opt
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsSelector.T_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.mem_VU_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.iterate_mono_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman_le_opt
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.chain_2_9
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.mapsTo_VU
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman_le_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VFIConverges
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.OPIConverges
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.HPIConverges
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.opt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.OPIConverges.vfi
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.iterates_le_vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VU_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.OrderBounded
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsOrderContinuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.le_of_orderBounded
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.convergence_of_dedekind
#print axioms SargentStachurski.RecursiveDecisionProcesses.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.theorem_3_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.corollary_3_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.theorem_3_1_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsSupNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsInfNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.isInfNonexpansive_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.isSupNonexpansive_real
#print axioms SargentStachurski.RecursiveDecisionProcesses.isSupNonexpansive_pi
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.lemma_A_5_21
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.IsSemiRegular
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VFIGeometric
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.theorem_3_1_5
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.toFun
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.measurable'
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.bdd'
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.ext
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.bddAbove
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.const
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.toFun_injective
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.zero
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.add
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.smulReal
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.nsmul
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.zsmul
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.addCommGroup
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.supNorm
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.abs_le_supNorm
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.supNorm_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.supNorm_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.normedAddCommGroup
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.add_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.sub_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.neg_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.zero_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.const_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.norm_def
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.abs_le_norm
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.norm_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.abs_sub_le_dist
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.dist_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.module
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.smul_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.normedSpace
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.lattice
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.le_def
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.sup_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.inf_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.abs_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.isOrderedAddMonoid
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.hasSolidNorm
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.completeSpace
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.countablyDedekindComplete
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.isSupNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.isInfNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mem_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.globallyStable_of_bX
#print axioms SargentStachurski.RecursiveDecisionProcesses.pow_div_le_geometric
#print axioms SargentStachurski.RecursiveDecisionProcesses.theorem_4_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsNormalizedOrderUnit
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.smul_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.le_add
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsNormalizedOrderUnit.norm_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.isSupNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.isInfNonexpansive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.isSupNonexpansive_subtype
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.lemma_4_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.lemma_4_1_2_subtype
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_3_univ
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsCertaintyEquivalent
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.exercise_4_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.exercise_4_1_2_subtype
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsDiscountOperator
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsDiscountOperator.exercise_4_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsDiscountOperator.iterate_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsDiscountOperator.iterate_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.specRad
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.exercise_A_4_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.specRad_le_norm
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsPositiveOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsPositiveOp.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsPositiveOp.abs_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsPositiveOp.iterate
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.example_4_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsIsoOrderEmbedding
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsOrderContraction
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsOrderContraction.iterate
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.example_4_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.exercise_4_1_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_5
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.bellman_orderContraction
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_6
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsAdditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.IsAdditive.abs_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_7
#print axioms SargentStachurski.RecursiveDecisionProcesses.BanachLattice.theorem_4_1_8
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.posSMulMono
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.one_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.isNormalizedOrderUnit_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.markovLin
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.markovCLM
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.markovCLM_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.markovCLM_isPositive
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.markovCLM_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mulLin
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mulCLM
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mulCLM_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BM.mulCLM_isPositive
#print axioms SargentStachurski.RecursiveDecisionProcesses.sup'_add_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.harrisonKreps
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_4_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLHC
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsUHC
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContinuousCorr
#print axioms SargentStachurski.RecursiveDecisionProcesses.clamp_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.clamp_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_subseq_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_A_3_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.HasMaxSelections
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.argmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.sel
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.continuousOn_section
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.argmax_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.isClosed_argmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.sel_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.isClosed_le_sel
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.exists_param
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.continuous_max
#print axioms SargentStachurski.RecursiveDecisionProcesses.IccMax.measurable_sel
#print axioms SargentStachurski.RecursiveDecisionProcesses.hasMaxSelections_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.r
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.β_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.P
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.exists_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.Policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.nonempty_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.measurable_graph
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.along
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.rσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.βσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.Pσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.K
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.K_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.K_isPositive
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.norm_K_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.adp
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.T_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.isAdditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.obj
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.T_apply_obj
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.isGreedy_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.isGreedy_of_argmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.argmax_of_isGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.iterate_T_zero
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.globallyStable_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.lifetime_value
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.firm
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.firm_T_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.example_6_1_6
#print axioms SargentStachurski.RecursiveDecisionProcesses.argmaxSet
#print axioms SargentStachurski.RecursiveDecisionProcesses.argmaxSet_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.argmaxSel
#print axioms SargentStachurski.RecursiveDecisionProcesses.argmaxSel_max
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_argmaxSel
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.regular_of_isFinite
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.proposition_6_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.G
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.IsWeakFeller
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.IsStrongFeller
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.IsStrongFeller.isWeakFeller
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.bc
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.isClosed_bc
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.zero_mem_bc
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.continuousOn_obj
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.greedy_of_continuousOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.proposition_6_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.implications
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.implications_bc
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_section
#print axioms SargentStachurski.RecursiveDecisionProcesses.shockKernel
#print axioms SargentStachurski.RecursiveDecisionProcesses.shockKernel_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.shockKernel_isMarkov
#print axioms SargentStachurski.RecursiveDecisionProcesses.integral_shockKernel
#print axioms SargentStachurski.RecursiveDecisionProcesses.example_6_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.scheffe
#print axioms SargentStachurski.RecursiveDecisionProcesses.lemma_6_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.example_6_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.ofMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.ofMDP_T_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.example_6_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.Dsup
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_iSup_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.Dsup_isDiscountOperator
#print axioms SargentStachurski.RecursiveDecisionProcesses.K_le_Dsup
#print axioms SargentStachurski.RecursiveDecisionProcesses.proposition_6_1_7
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.measurable_next
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.P
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.reward
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.ldp
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.example_6_1_5
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.densityMeasure
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.densityMeasure_isProbability
#print axioms SargentStachurski.RecursiveDecisionProcesses.Savings.example_6_1_8
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_measurable_argmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.HasContinuousUniqueMax
#print axioms SargentStachurski.RecursiveDecisionProcesses.hasContinuousUniqueMax_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.FeasiblePolicy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.ev
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.ev_le_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.consistent
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.ev_injective
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.nonempty_Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.ev_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.adp
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.ev_adp_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreedy_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsArgmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreedy_of_isArgmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.bellman_of_isArgmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreedy_iff_isArgmax
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.lemma_7_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.lemma_7_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exercise_7_1_5
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.measurable
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.bdd
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.exists_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.toRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.toRDP_T_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.IsBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.T_blackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.regular_of_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.proposition_7_2_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.proposition_7_2_1_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.greedy_of_continuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.BRDP.proposition_7_2_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.wnorm
#print axioms SargentStachurski.RecursiveDecisionProcesses.bl
#print axioms SargentStachurski.RecursiveDecisionProcesses.blPlus
#print axioms SargentStachurski.RecursiveDecisionProcesses.wevB
#print axioms SargentStachurski.RecursiveDecisionProcesses.wevB_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_eq_wnorm
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_A_5_22
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_A_5_24
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_A_5_25
#print axioms SargentStachurski.RecursiveDecisionProcesses.posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.isClosed_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.add_mem_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.wev
#print axioms SargentStachurski.RecursiveDecisionProcesses.wev_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.ofBl
#print axioms SargentStachurski.RecursiveDecisionProcesses.wev_ofBl
#print axioms SargentStachurski.RecursiveDecisionProcesses.wev_le_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.bcPlus
#print axioms SargentStachurski.RecursiveDecisionProcesses.isClosed_bcPlus
#print axioms SargentStachurski.RecursiveDecisionProcesses.zero_mem_bcPlus
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.measurable_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.one_le_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.measurable
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.U2
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.exists_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.toRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.toRDP_T_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.IsBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.T_blackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.regular_of_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_4_finite
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.greedy_of_continuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_5
#print axioms SargentStachurski.RecursiveDecisionProcesses.lemma_A_2_6
#print axioms SargentStachurski.RecursiveDecisionProcesses.eq_of_isMax_of_strictConcaveOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.ADP.VFIGeometric.tendsto
#print axioms SargentStachurski.RecursiveDecisionProcesses.coneZero
#print axioms SargentStachurski.RecursiveDecisionProcesses.wev_coneZero
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_2_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.ℓ_continuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.maxSel
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.blackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.continuousOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.prop
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.ContinuousCase.vstar_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_6
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.isClosed_concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.feasibleOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_7
#print axioms SargentStachurski.RecursiveDecisionProcesses.WRDP.proposition_7_2_8
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLInf
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsRiskMeasure
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsRiskMeasure.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsRiskMeasure.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsRiskMeasure.cash
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.cash
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLInf.add_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLInf.const_mul
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLInf.add
#print axioms SargentStachurski.RecursiveDecisionProcesses.isLInf_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsLInf.integrable
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_2_5_i
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_2_5_ii
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsConvexRisk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsConcaveCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsPosHomogeneous
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCoherentRisk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCoherentCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCoherentRisk_neg_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCoherentCE.superadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.meanCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.meanCE_isCoherent
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContinuousCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.example_7_2_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.pessCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.mem_pess_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.pess_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.pess_bddAbove
#print axioms SargentStachurski.RecursiveDecisionProcesses.ae_pess_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_pess
#print axioms SargentStachurski.RecursiveDecisionProcesses.pessCE_isCoherent
#print axioms SargentStachurski.RecursiveDecisionProcesses.entropicCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.integrable_exp
#print axioms SargentStachurski.RecursiveDecisionProcesses.integral_exp_pos'
#print axioms SargentStachurski.RecursiveDecisionProcesses.entropicCE_isCertEquiv
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_2_6
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpExp
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpExp_not_cash_invariant
#print axioms SargentStachurski.RecursiveDecisionProcesses.ceAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.isLInf_comp
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.abs_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.ceBRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.ceBRDP_isBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.continuousOn_ce
#print axioms SargentStachurski.RecursiveDecisionProcesses.proposition_7_2_10
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_integral_comp
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_meanCE_comp
#print axioms SargentStachurski.RecursiveDecisionProcesses.measurable_entropicCE_comp
#print axioms SargentStachurski.RecursiveDecisionProcesses.mdpAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_1_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.finiteMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.finiteMDP_bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.modifiedMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.rsAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_1_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.riskSensitiveMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.toRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.LDP.toRDP_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.savings_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmRDP_bellman
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_wevB_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_1_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmWeighted
#print axioms SargentStachurski.RecursiveDecisionProcesses.KPValues
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpCont
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpCont_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpCont_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_1_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpSavings
#print axioms SargentStachurski.RecursiveDecisionProcesses.scheffe_general
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.u
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.continuous_u
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.u_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.monotone_u
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.R
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.R_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.β_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.δ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.β_lt_δ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.δ_lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.ψ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.measurable_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.one_le_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.monotone_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integrable_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.ℓ_rec
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.δ_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integrable_v
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integral_ℓ_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integral_ℓ_feasible_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.wrdp
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.exercise_7_3_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integral_shift_density
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integrable_shift_density
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.continuous_integral_ℓ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.exercise_7_3_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.hasMaxSelections
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.continuousCase
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.section_7_3_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.exercise_7_2_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.vstar_monotone
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.convex_feasibleOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.integral_concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.exercise_7_2_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.SavingsU.exercise_7_2_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.F
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.continuous_F
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.F_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.F_bdd
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.g
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.measurable_g
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.continuous_g
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.θ
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.θ_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.δ
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.β_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.β_lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.φ
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.r
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.next
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.measurable_r
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.r_bdd
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.measurable_next
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.exists_policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.hasMaxSelections
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.IsMeasurableCE
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.rdp
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.rdp_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.proposition_7_3_2
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.meanRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.entropicRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.proposition_7_3_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.example_7_3_1
#print axioms SargentStachurski.RecursiveDecisionProcesses.Investment.section_7_3_3
#print axioms SargentStachurski.RecursiveDecisionProcesses.rsRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.rsRDP_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.section_7_3_4
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosValues
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosValues.pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosValues.abs_log_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosValues.log
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosValues.exp
#print axioms SargentStachurski.RecursiveDecisionProcesses.mkpAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.mkpAgg_eq_exp
#print axioms SargentStachurski.RecursiveDecisionProcesses.mkpRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.exercise_7_3_4
