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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.Prod
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Volume 2, Chapter 3 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential analysis

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.4 (pp. 49–54).

Draws `Z₁, Z₂, …` are iid with density `f₀` or `f₁`; the state is the posterior probability
`π` that `f = f₁`.

* Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))` stays in `[0, 1]`, and the
  predictive density `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)` (1.57) integrates to one.
* Beliefs are a martingale: `∫ κ(π, z)ψ(π, z) dz = π`.
* The Bellman operator of (1.58), `(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`,
  is order preserving and maps nonnegative functions to functions between `0` and
  `min{πL₀, (1 − π)L₁}`.

Theorem 1.4.1 (the optimal loss function uniquely solves (1.58), with optimal policies the
minimizers of `Q(π, a)`) has no discounting; the book proves it as Theorem 3.2.9, in Chapter 3.
-/

open MeasureTheory

namespace SargentStachurski.ADPsOnPospaces

variable {f₀ f₁ : ℝ → ℝ}

/-- The predictive density (1.57): `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)`. -/
def predDensity (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := (1 - π) * f₀ z + π * f₁ z

/-- Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))`. -/
noncomputable def bayesUpdate (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := π * f₁ z / predDensity f₀ f₁ π z

/-- (1.56): the posterior is a probability. -/
theorem bayesUpdate_mem_Icc (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) : bayesUpdate f₀ f₁ π z ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  refine ⟨div_nonneg hb (add_nonneg ha hb), ?_⟩
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · simp [bayesUpdate, predDensity, ← h]
  · exact (div_le_one h).2 (by linarith)

/-- `κ(π, z)ψ(π, z) = πf₁(z)`, also where `ψ(π, z) = 0`. -/
theorem bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π * f₁ z := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  rcases eq_or_ne (predDensity f₀ f₁ π z) 0 with h | h
  · have : π * f₁ z = 0 := by simp only [predDensity] at h; linarith
    rw [h, this, mul_zero]
  · exact div_mul_cancel₀ _ h

/-- (1.57): the predictive density integrates to one. -/
theorem integral_predDensity (hi₀ : Integrable f₀) (hi₁ : Integrable f₁)
    (h₀ : ∫ z, f₀ z = 1) (h₁ : ∫ z, f₁ z = 1) (π : ℝ) : ∫ z, predDensity f₀ f₁ π z = 1 := by
  simp only [predDensity]
  rw [integral_add (hi₀.const_mul _) (hi₁.const_mul _), integral_const_mul, integral_const_mul,
    h₀, h₁]
  ring

/-- §1.4.1: beliefs are a martingale, `∫ κ(π, z)ψ(π, z) dz = π`. -/
theorem integral_bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z)
    (h₁ : ∫ z, f₁ z = 1) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    ∫ z, bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π := by
  simp only [bayesUpdate_mul_predDensity hf₀ hf₁ hπ, integral_const_mul, h₁, mul_one]

/-- The Bellman operator of (1.58):
`(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`. -/
noncomputable def seqBellman (f₀ f₁ : ℝ → ℝ) (L₀ L₁ c : ℝ) (g : ℝ → ℝ) (π : ℝ) : ℝ :=
  min (π * L₀) (min ((1 - π) * L₁)
    (c + ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z))

/-- The Bellman operator (1.58) is order preserving on bounded measurable functions. -/
theorem seqBellman_mono (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) (hm₀ : Measurable f₀)
    (hm₁ : Measurable f₁) (hi₀ : Integrable f₀) (hi₁ : Integrable f₁) {L₀ L₁ c : ℝ}
    {g g' : ℝ → ℝ} (hg : Measurable g) (hg' : Measurable g') {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    (hgM' : ∀ x, |g' x| ≤ M) (hle : g ≤ g') {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    seqBellman f₀ f₁ L₀ L₁ c g π ≤ seqBellman f₀ f₁ L₀ L₁ c g' π := by
  have hψ : Integrable (predDensity f₀ f₁ π) := (hi₀.const_mul _).add (hi₁.const_mul _)
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith [hπ.2]) (hf₀ z)) (mul_nonneg hπ.1 (hf₁ z))
  have hκm : Measurable (bayesUpdate f₀ f₁ π) :=
    (measurable_const.mul hm₁).div ((measurable_const.mul hm₀).add (measurable_const.mul hm₁))
  have hint : ∀ {h : ℝ → ℝ}, Measurable h → (∀ x, |h x| ≤ M) →
      Integrable fun z => h (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z := by
    intro h hh hhM
    refine hψ.bdd_mul (hh.comp hκm).aestronglyMeasurable (c := M) ?_
    exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hhM _
  refine min_le_min le_rfl (min_le_min le_rfl (add_le_add le_rfl ?_))
  exact integral_mono (hint hg hgM) (hint hg' hgM') fun z =>
    mul_le_mul_of_nonneg_right (hle _) (hψ0 z)

/-- The Bellman operator (1.58) maps nonnegative functions into `[0, min{πL₀, (1 − π)L₁}]`. -/
theorem seqBellman_mem (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {L₀ L₁ c : ℝ}
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hc : 0 ≤ c) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ seqBellman f₀ f₁ L₀ L₁ c g π ∧
      seqBellman f₀ f₁ L₀ L₁ c g π ≤ min (π * L₀) ((1 - π) * L₁) := by
  obtain ⟨h0, h1⟩ := hπ
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith) (hf₀ z)) (mul_nonneg h0 (hf₁ z))
  have hI : 0 ≤ ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z :=
    integral_nonneg fun z => mul_nonneg (hg _) (hψ0 z)
  refine ⟨le_min (mul_nonneg h0 hL₀) (le_min (mul_nonneg (by linarith) hL₁) (by linarith)),
    le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))⟩

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonstationary policies

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.4 (pp. 103–105).

A policy plan is a sequence `σ̄ = (σ_t)_{t ≥ 0}` of policies. Its lifetime value is (3.2),
`v_σ̄ = lim_n T_{σ₀} ⋯ T_{σₙ} v`, the policy operators being applied backwards from the terminal
condition `v`.

* **Assumption 3.1.1**: a complete sup-nonexpansive metric, a common contraction modulus
  `λ ∈ (0, 1)` and `sup_σ d(v, T_σ v) < ∞` for every `v`.
* **Lemma 3.1.9**: (i) the limit (3.2) exists and does not depend on `v`; (ii) each `T_σ` is
  continuous and globally stable; (iii) under semi-regularity on a nonempty `V₀`, some `v` solves
  `v = ⋁_σ T_σ v`.
* **Theorem 3.1.10**: for a regular ADP the fundamental optimality properties hold, and every
  policy plan is weakly dominated by a stationary policy.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnPospaces

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- `T_{σ₀} ∘ ⋯ ∘ T_{σ_{n-1}}` for a policy plan `σs` (the identity when `n = 0`). -/
def planComp (σs : ℕ → P) : ℕ → V → V
  | 0 => id
  | n + 1 => fun v => planComp σs n (A.T (σs n) v)

theorem planComp_succ (σs : ℕ → P) (n : ℕ) (v : V) :
    A.planComp σs (n + 1) v = A.planComp σs n (A.T (σs n) v) := rfl

/-- Each `planComp σs n` is order preserving. -/
theorem planComp_mono (σs : ℕ → P) (n : ℕ) : Monotone (A.planComp σs n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih => exact fun v w h => ih (A.mono (σs n) h)

variable [MetricSpace V]

variable (A) in
/-- **Assumption 3.1.1** (p. 103), with completeness of the metric kept as a separate hypothesis:
the metric is sup-nonexpansive, every `T_σ` is a contraction of modulus `λ ∈ (0, 1)`, and
`sup_σ d(v, T_σ v) < ∞` for every `v`. -/
structure Assumption311 (lam : ℝ) : Prop where
  /-- the metric is sup-nonexpansive -/
  supNonexp : IsSupNonexpansive (dist : V → V → ℝ)
  /-- `λ > 0` -/
  pos : 0 < lam
  /-- `λ < 1` -/
  lt_one : lam < 1
  /-- common contraction modulus -/
  contr : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ lam * dist v w
  /-- `sup_σ d(v, T_σ v) < ∞` -/
  bdd : ∀ v, BddAbove (range fun σ => dist v (A.T σ v))

/-- `planComp σs n` is Lipschitz with constant `λⁿ`. -/
theorem Assumption311.dist_planComp {lam : ℝ} (h : A.Assumption311 lam) (σs : ℕ → P) (n : ℕ)
    (v w : V) : dist (A.planComp σs n v) (A.planComp σs n w) ≤ lam ^ n * dist v w := by
  induction n generalizing v w with
  | zero => simp [planComp]
  | succ n ih =>
    rw [planComp_succ, planComp_succ, pow_succ, mul_assoc]
    exact (ih _ _).trans (mul_le_mul_of_nonneg_left (h.contr _ v w)
      (pow_nonneg h.pos.le n))

variable [CompleteSpace V]

/-- **Lemma 3.1.9 (i)** (p. 104): for every policy plan `σs` and every `v₀`, the limit
`lim_n T_{σ₀} ⋯ T_{σₙ} v₀` exists, and every other starting point `v` gives the same limit. -/
theorem Assumption311.exists_planValue {lam : ℝ} (h : A.Assumption311 lam) (σs : ℕ → P)
    (v₀ : V) : ∃ vbar, ∀ v, Tendsto (fun n => A.planComp σs n v) atTop (𝓝 vbar) := by
  obtain ⟨b, hb⟩ := h.bdd v₀
  have hcauchy : CauchySeq fun n => A.planComp σs n v₀ := by
    refine cauchySeq_of_le_geometric lam b h.lt_one fun n => ?_
    rw [planComp_succ]
    refine (h.dist_planComp σs n _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hb ⟨σs n, rfl⟩) (pow_nonneg h.pos.le n)
  obtain ⟨vbar, hvbar⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨vbar, fun v => tendsto_iff_dist_tendsto_zero.2 ?_⟩
  have hpow : Tendsto (fun n => lam ^ n * dist v v₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.pos.le h.lt_one).mul_const
      (dist v v₀)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => dist_triangle _
    (A.planComp σs n v₀) _) ?_
  simpa using (squeeze_zero (fun _ => dist_nonneg) (fun n => h.dist_planComp σs n v v₀)
    hpow).add (tendsto_iff_dist_tendsto_zero.1 hvbar)

variable (A) in
/-- The lifetime value (3.2) of a policy plan `σs` from terminal condition `v`. -/
noncomputable def planValue [Nonempty V] (σs : ℕ → P) (v : V) : V :=
  limUnder atTop fun n => A.planComp σs n v

/-- `T_{σ₀} ⋯ T_{σₙ} v → v_σ̄`. -/
theorem Assumption311.tendsto_planValue [Nonempty V] {lam : ℝ} (h : A.Assumption311 lam)
    (σs : ℕ → P) (v : V) : Tendsto (fun n => A.planComp σs n v) atTop (𝓝 (A.planValue σs v)) := by
  obtain ⟨vbar, hvbar⟩ := h.exists_planValue σs v
  exact tendsto_nhds_limUnder ⟨vbar, hvbar v⟩

/-- **Lemma 3.1.9 (i)** (p. 104): `v_σ̄` does not depend on the terminal condition. -/
theorem Assumption311.planValue_eq [Nonempty V] {lam : ℝ} (h : A.Assumption311 lam)
    (σs : ℕ → P) (v w : V) : A.planValue σs v = A.planValue σs w := by
  obtain ⟨vbar, hvbar⟩ := h.exists_planValue σs v
  exact tendsto_nhds_unique (h.tendsto_planValue σs v) (hvbar v) |>.trans
    (tendsto_nhds_unique (h.tendsto_planValue σs w) (hvbar w)).symm

/-- **Lemma 3.1.9 (ii)** (p. 104): every `T_σ` is continuous and globally stable on `V`, with
`v_σ = lim_j T_σʲ v` (3.3). -/
theorem Assumption311.continuous_globallyStable [Nonempty V] {lam : ℝ}
    (h : A.Assumption311 lam) (σ : P) : Continuous (A.T σ) ∧ GloballyStable (A.T σ) :=
  ⟨(LipschitzWith.of_dist_le_mul (K := ⟨lam, h.pos.le⟩) fun v w => h.contr σ v w).continuous,
    isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr σ⟩

/-- **Lemma 3.1.9 (iii)** (p. 104): if, in addition, `(V, 𝕋)` is semi-regular on a nonempty
`V₀`, some `v` satisfies `v = ⋁_σ T_σ v`. -/
theorem Assumption311.exists_solvesBellman [OrderClosedTopology V] {lam : ℝ}
    (h : A.Assumption311 lam) {V₀ : Set V} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ v, A.SolvesBellman v := by
  obtain ⟨⟨-, ⟨v, -, -, hb, -⟩, -⟩, -⟩ :=
    theorem_3_1_5 h.supNonexp h.pos.le h.lt_one h.contr hsr hne
  exact ⟨v, hb⟩

/-- **Theorem 3.1.10** (p. 105): if `(V, 𝕋)` is regular and Assumption 3.1.1 holds, the
fundamental optimality properties hold, and every policy plan `σ̄` is weakly dominated by a
stationary policy: `v_σ̄ ≼ v_σ` for some `σ`. -/
theorem theorem_3_1_10 [OrderClosedTopology V] [Nonempty V] {lam : ℝ} (hr : A.Regular)
    (h : A.Assumption311 lam) :
    A.FundamentalOptimality
        (isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr).wellPosed ∧
      ∀ σs : ℕ → P, ∃ σ, ∀ v, A.planValue σs v ≤
        A.vσ (isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr).wellPosed σ := by
  obtain ⟨hFO, -⟩ := theorem_3_1_5 h.supNonexp h.pos.le h.lt_one h.contr
    ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩ univ_nonempty
  refine ⟨hFO, fun σs => ?_⟩
  obtain ⟨vstar, σ, -, hσ, hvG, hb⟩ := hFO.exists_vstar
  have hfix : A.bellman vstar = vstar := (A.solvesBellman_iff hvG).1 hb
  have hle : ∀ n, A.planComp σs n vstar ≤ vstar := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [planComp_succ]
      exact (planComp_mono σs n ((A.T_le_bellman _ (hr vstar)).trans_eq hfix)).trans ih
  refine ⟨σ, fun v => ?_⟩
  rw [hσ, h.planValue_eq σs v vstar]
  exact le_of_tendsto' (h.tendsto_planValue σs vstar) hle

end ADP

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

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

namespace SargentStachurski.ADPsOnPospaces

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

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# MDPs with a countable state space

Sargent and Stachurski, *Dynamic Programming*, Volume 2, **Exercise 3.2.1** (p. 106).

The MDP `(Γ, r, β, P)` of §1.2.1.1 with state and action spaces that need not be finite, finite
nonempty feasible sets `Γ(x)`, a reward bounded on the feasible pairs and transition
probabilities `P(x, a, ·)` summing to one. The value space is `bX`, the bounded functions on `X`,
which are all measurable for the discrete σ-algebra.

* (i) `(bX, 𝕋_MDP)` is an ADP, with `T_σ v = r_σ + βP_σ v`;
* (ii) the fundamental optimality properties hold; and
* (iii) VFI, OPI and HPI all converge.

The proof applies Theorem 3.1.5 on the Banach lattice `bX` (the ADP is regular because the
feasible sets are finite), then Theorem 3.1.2.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- An MDP with general (countable) state and action spaces (Exercise 3.2.1): finite nonempty
feasible sets, a reward bounded on the feasible pairs, and summable transition probabilities. -/
structure CountableMDP (X A : Type*) where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  r_bdd : ∃ C, ∀ x, ∀ a ∈ Γ x, |r x a| ≤ C
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', 0 ≤ P x a x'
  P_sum : ∀ x, ∀ a ∈ Γ x, HasSum (P x a) 1

namespace CountableMDP

variable {X A : Type*} (M : CountableMDP X A)

/-- The feasible policies. -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

theorem nonempty_policy : Nonempty M.Policy := by
  choose f hf using fun x => M.Γ_nonempty x
  exact ⟨⟨f, hf⟩⟩

theorem summable_mul {x : X} {a : A} (ha : a ∈ M.Γ x) {v : X → ℝ} {C : ℝ}
    (hv : ∀ y, |v y| ≤ C) : Summable fun x' => v x' * M.P x a x' := by
  refine Summable.of_norm_bounded ((M.P_sum x a ha).summable.mul_left C) fun x' => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (M.P_nonneg x a ha x')]
  exact mul_le_mul_of_nonneg_right (hv x') (M.P_nonneg x a ha x')

/-- `|∑_{x'} v(x')P(x, a, x')| ≤ C` when `|v| ≤ C`. -/
theorem abs_tsum_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v : X → ℝ} {C : ℝ}
    (hv : ∀ y, |v y| ≤ C) : |∑' x', v x' * M.P x a x'| ≤ C := by
  have hC : HasSum (fun x' => C * M.P x a x') C := by
    simpa using (M.P_sum x a ha).mul_left C
  have hnC : HasSum (fun x' => -C * M.P x a x') (-C) := by
    simpa using (M.P_sum x a ha).mul_left (-C)
  refine abs_le.2 ⟨?_, ?_⟩
  · rw [← hnC.tsum_eq]
    exact hnC.summable.tsum_le_tsum (fun x' => mul_le_mul_of_nonneg_right
      (abs_le.1 (hv x')).1 (M.P_nonneg x a ha x')) (M.summable_mul ha hv)
  · rw [← hC.tsum_eq]
    exact (M.summable_mul ha hv).tsum_le_tsum (fun x' => mul_le_mul_of_nonneg_right
      (abs_le.1 (hv x')).2 (M.P_nonneg x a ha x')) hC.summable

/-- The value of action `a` at `x` given a bounded `v`. -/
noncomputable def Q (v : X → ℝ) (x : X) (a : A) : ℝ :=
  M.r x a + M.β * ∑' x', v x' * M.P x a x'

theorem Q_mono {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {C D : ℝ}
    (hv : ∀ y, |v y| ≤ C) (hw : ∀ y, |w y| ≤ D) (h : ∀ y, v y ≤ w y) :
    M.Q v x a ≤ M.Q w x a :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left ((M.summable_mul ha hv).tsum_le_tsum
    (fun x' => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg x a ha x'))
    (M.summable_mul ha hw)) M.β_nonneg)

theorem abs_Q_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {C D c : ℝ}
    (hv : ∀ y, |v y| ≤ C) (hw : ∀ y, |w y| ≤ D) (h : ∀ y, |v y - w y| ≤ c) :
    |M.Q v x a - M.Q w x a| ≤ M.β * c := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
  rw [← (M.summable_mul ha hv).tsum_sub (M.summable_mul ha hw)]
  simpa only [← sub_mul] using M.abs_tsum_le ha h

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]

/-- The policy operator `T_σ v = r_σ + βP_σ v` on `bX`. -/
noncomputable def Tσ (σ : M.Policy) (v : BM X) : BM X :=
  ⟨fun x => M.Q v.toFun x (σ.1 x), Measurable.of_discrete, by
    obtain ⟨C, hC⟩ := M.r_bdd
    refine ⟨C + M.β * ‖v‖, fun x => (abs_add_le _ _).trans (add_le_add (hC x _ (σ.2 x)) ?_)⟩
    rw [abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (M.abs_tsum_le (σ.2 x) (BM.abs_le_norm v)) M.β_nonneg⟩

/-- **Exercise 3.2.1 (i)**: `(bX, 𝕋_MDP)` is an ADP. -/
noncomputable def adp : ADP (BM X) M.Policy where
  T := M.Tσ
  mono σ v w h x := M.Q_mono (σ.2 x) (BM.abs_le_norm v) (BM.abs_le_norm w) h
  nonempty := M.nonempty_policy

/-- Each `T_σ` is a contraction of modulus `β` for the supremum norm. -/
theorem adp_contraction (σ : M.Policy) (v w : BM X) :
    dist (M.adp.T σ v) (M.adp.T σ w) ≤ M.β * dist v w :=
  BM.dist_le (mul_nonneg M.β_nonneg dist_nonneg) fun x =>
    M.abs_Q_sub_le (σ.2 x) (BM.abs_le_norm v) (BM.abs_le_norm w) (BM.abs_sub_le_dist v w)

/-- The ADP is regular: the feasible sets are finite. -/
theorem adp_regular : M.adp.Regular := fun v => by
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x) (M.Q v.toFun x)
    (M.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun τ x => hmax x _ (τ.2 x)⟩

/-- The ADP is globally stable (Banach's theorem). -/
theorem adp_isGloballyStable : M.adp.IsGloballyStable :=
  ADP.isGloballyStable_of_contraction ⟨0⟩ M.β_nonneg M.β_lt_one M.adp_contraction

/-- **Exercise 3.2.1** (p. 106): (ii) the fundamental optimality properties hold for `(bX, 𝕋_MDP)`
and (iii) VFI, OPI and HPI all converge. -/
theorem exercise_3_2_1 :
    M.adp.FundamentalOptimality M.adp_isGloballyStable.wellPosed ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isGloballyStable.wellPosed g vstar := by
  obtain ⟨hFO, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive M.β_nonneg M.β_lt_one
    M.adp_contraction ⟨isClosed_univ, fun v _ => M.adp_regular v, mapsTo_univ _ _⟩
    univ_nonempty
  obtain ⟨vstar, -, -, -, hvG, hb⟩ := hFO.exists_vstar
  exact ADP.theorem_3_1_2 M.adp_regular M.adp_isGloballyStable
    ((M.adp.solvesBellman_iff hvG).1 hb)

end CountableMDP

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings on the Banach lattice `bℝ₊`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.2 (pp. 108–109).

The optimal savings ADP `(bℝ₊, 𝕋_OS)` with policy operators (3.8), now on the Banach lattice
`bℝ₊` with the supremum norm.

* Each `T_σ` is globally stable (Lemma 1.3.1), and greedy policies are those of (3.10).
* **Proposition 3.2.1** (the strongly continuous case): given Lemma 1.3.2 (i) (greedy policies
  exist, which needs the continuous density of Assumption 1.3.1 and is proved in Chapter 6),
  Theorem 3.1.4 gives the fundamental optimality properties and convergence of VFI, OPI and HPI.
  **Remark 3.2.1**: Theorem 3.1.5 gives the same.
* **Exercise 3.2.7** (the weakly continuous case, `φ` any probability measure): for `v ∈ bcℝ₊` a
  `v`-greedy policy exists (the largest maximizer, shown measurable by a sequential compactness
  argument) and the Bellman operator maps `bcℝ₊` into itself.
* **Proposition 3.2.2**: by Theorem 3.1.5 with `V₀ = bcℝ₊`, the fundamental optimality properties
  hold, the value function is continuous, and VFI converges geometrically on `bcℝ₊`.
-/

open Set Function Filter Topology MeasureTheory

open scoped NNReal

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The policy operator (3.8) on `bℝ₊`. -/
noncomputable def TBM (σ : SavingsPolicy) (v : BM ℝ≥0) : BM ℝ≥0 :=
  ⟨S.Tσ σ.1 v.toFun, (S.Tσ_mapsTo σ.2.1 (BM.mem_bX v)).1, (S.Tσ_mapsTo σ.2.1 (BM.mem_bX v)).2⟩

/-- The optimal savings ADP `(bℝ₊, 𝕋_OS)` on the Banach lattice `bℝ₊`. -/
noncomputable def adpBM : ADP (BM ℝ≥0) SavingsPolicy where
  T := S.TBM
  mono σ v w h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg (BM.mem_bX v)
    (BM.mem_bX w) h
  nonempty := ⟨consumeAll⟩

/-- Lemma 1.3.1: the ADP is globally stable on `bℝ₊`. -/
theorem adpBM_isGloballyStable : S.adpBM.IsGloballyStable := fun σ =>
  BM.globallyStable_of_bX (fun _ => rfl) (S.Tσ_globallyStable σ.2.1)

/-- (3.10): `σ` is greedy for the ADP iff `σ(w)` maximizes (3.10) at every `w`. -/
theorem adpBM_isGreedy_iff (v : BM ℝ≥0) (σ : SavingsPolicy) :
    S.adpBM.IsGreedy v σ ↔ S.IsGreedy v.toFun σ := by
  constructor
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]
          exact hc
        · simp only [hx, ↓reduceIte]
          exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v.toFun w ≤ S.Tσ σ.1 v.toFun w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this
  · exact fun h τ w => h w _ (τ.2.2 w)

/-- On `V_G`, the ADP Bellman operator is (1.51). -/
theorem adpBM_bellman_apply {v : BM ℝ≥0} (hv : v ∈ S.adpBM.VG) (w : ℝ≥0) :
    (S.adpBM.bellman v).toFun w = S.bellmanOp v.toFun w := by
  have hg := (S.adpBM_isGreedy_iff v _).1 (S.adpBM.isGreedy_greedy hv)
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective v.bdd' w) ⟨(S.adpBM.greedy v).1 w, (S.adpBM.greedy v).2.2 w⟩

/-- The ADP is order bounded: with `|u| ≤ M`, the constant `M/(1 − β)` is mapped down by every
`T_σ`. -/
theorem adpBM_orderBounded : S.adpBM.OrderBounded := by
  have := S.φ_prob
  obtain ⟨M, hM0, hM⟩ := S.u_bdd.nonneg_bound
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  set K := M / (1 - S.β)
  have hK : M + S.β * K = K := by
    have : K * (1 - S.β) = M := div_mul_cancel₀ M h1β.ne'
    linarith
  refine ⟨BM.const K, fun σ w => ?_⟩
  change S.Tσ σ.1 (fun _ => K) w ≤ K
  simp only [Tσ, affineOp, rσ, Pσ, cont, integral_const, probReal_univ, one_smul]
  linarith [(abs_le.1 (hM (σ.1 w))).2]

/-- Each `T_σ` is a contraction of modulus `β` for the supremum norm. -/
theorem adpBM_contraction (σ : SavingsPolicy) (v w : BM ℝ≥0) :
    dist (S.adpBM.T σ v) (S.adpBM.T σ w) ≤ S.β * dist v w := by
  have := S.φ_prob
  refine BM.dist_le (mul_nonneg S.β_nonneg dist_nonneg) fun x => ?_
  change |S.u (σ.1 x) + S.β * S.cont v.toFun x (σ.1 x) -
    (S.u (σ.1 x) + S.β * S.cont w.toFun x (σ.1 x))| ≤ _
  have hsub : S.cont v.toFun x (σ.1 x) - S.cont w.toFun x (σ.1 x) =
      S.cont (v - w).toFun x (σ.1 x) := by
    simp only [cont, BM.sub_apply]
    exact (integral_sub (S.integrable_comp (BM.mem_bX v) _)
      (S.integrable_comp (BM.mem_bX w) _)).symm
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_nonneg, hsub]
  refine mul_le_mul_of_nonneg_left (S.abs_cont_le (fun y => ?_) _ _) S.β_nonneg
  rw [BM.sub_apply]
  exact BM.abs_sub_le_dist v w y

/-- **Proposition 3.2.1** (p. 108): given Lemma 1.3.2 (i) (greedy policies exist), the optimal
savings ADP obeys the fundamental optimality properties and VFI, OPI and HPI converge, by
Theorem 3.1.4 (`bℝ₊` is countably Dedekind complete, Corollary A.5.17). -/
theorem proposition_3_2_1 (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adpBM.FundamentalOptimality S.adpBM_isGloballyStable.wellPosed ∧
      ∃ vstar, S.adpBM.IsValueFunction vstar ∧ S.adpBM.VFIConverges vstar ∧
        ∀ g, S.adpBM.IsSelector g → S.adpBM.OPIConverges g vstar ∧
          S.adpBM.HPIConverges S.adpBM_isGloballyStable.wellPosed g vstar :=
  ADP.theorem_3_1_4 (fun v => (hgreedy v.toFun (BM.mem_bX v)).imp fun σ hσ =>
    (S.adpBM_isGreedy_iff v σ).2 hσ) S.adpBM_isGloballyStable S.adpBM_orderBounded
    BM.countablyDedekindComplete

/-- **Remark 3.2.1** (p. 108): Proposition 3.2.1 also follows from Theorem 3.1.5, which adds
geometric convergence of VFI. -/
theorem remark_3_2_1 (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adpBM.FundamentalOptimality (ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg
        S.β_lt_one S.adpBM_contraction).wellPosed ∧
      ∃ vstar, S.adpBM.VFIGeometric univ vstar := by
  obtain ⟨hFO, vstar, -, hgeo, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive S.β_nonneg
    S.β_lt_one S.adpBM_contraction ⟨isClosed_univ, fun v _ =>
      (hgreedy v.toFun (BM.mem_bX v)).imp fun σ hσ => (S.adpBM_isGreedy_iff v σ).2 hσ,
      mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨hFO, vstar, hgeo⟩

/-! ### The weakly continuous case -/

/-- For continuous bounded `v`, `(w, c) ↦ ∫ v(R(w − c) + y) φ(dy)` is continuous. -/
theorem continuous_cont {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous fun p : ℝ≥0 × ℝ≥0 => S.cont v.toFun p.1 p.2 := by
  have := S.φ_prob
  refine continuous_of_dominated (bound := fun _ => ‖v‖) (fun p => ?_) (fun p => ?_)
    (integrable_const _) (Eventually.of_forall fun y => ?_)
  · exact (v.measurable'.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _
  · exact hv.comp ((continuous_const.mul (continuous_fst.sub continuous_snd)).add
      continuous_const)

/-- For continuous bounded `v`, the objective `(w, c) ↦ u(c) + β ∫ v(R(w − c) + y) φ(dy)` is
continuous. -/
theorem continuous_objective {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous fun p : ℝ≥0 × ℝ≥0 => S.objective v.toFun p.1 p.2 :=
  (S.u_cont.comp continuous_snd).add (continuous_const.mul (S.continuous_cont hv))

/-- The maximizers of (3.10) at wealth `w`. -/
def argmaxSet (v : BM ℝ≥0) (w : ℝ≥0) : Set ℝ≥0 :=
  {c | c ≤ w ∧ ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c}

theorem argmaxSet_nonempty {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    (S.argmaxSet v w).Nonempty := by
  have hcpt : IsCompact (Icc (0 : ℝ≥0) w) := isCompact_Icc
  obtain ⟨c, hc, hmax⟩ := hcpt.exists_isMaxOn ⟨0, le_rfl, bot_le⟩
    ((S.continuous_objective hv).comp (continuous_const.prodMk continuous_id)).continuousOn
  exact ⟨c, hc.2, fun d hd => hmax ⟨bot_le, hd⟩⟩

theorem isClosed_argmaxSet {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    IsClosed (S.argmaxSet v w) := by
  have hO : Continuous fun c => S.objective v.toFun w c :=
    (S.continuous_objective hv).comp (continuous_const.prodMk continuous_id)
  have heq : {c | ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c} =
      ⋂ d, ⋂ (_ : d ≤ w), {c | S.objective v.toFun w d ≤ S.objective v.toFun w c} := by
    ext c
    simp
  have h2 : IsClosed {c | ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c} :=
    heq ▸ isClosed_iInter fun d => isClosed_iInter fun _ => isClosed_le continuous_const hO
  exact (isClosed_le continuous_id continuous_const).inter h2

/-- The largest maximizer of (3.10). -/
noncomputable def greedyBM (v : BM ℝ≥0) (w : ℝ≥0) : ℝ≥0 := sSup (S.argmaxSet v w)

theorem greedyBM_mem {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    S.greedyBM v w ∈ S.argmaxSet v w :=
  (S.isClosed_argmaxSet hv w).csSup_mem (S.argmaxSet_nonempty hv w) ⟨w, fun _ hc => hc.1⟩

/-- The largest maximizer is upper semicontinuous: `{w | a ≤ σ(w)}` is closed. -/
theorem isClosed_le_greedyBM {v : BM ℝ≥0} (hv : Continuous v.toFun) (a : ℝ≥0) :
    IsClosed {w | a ≤ S.greedyBM v w} := by
  refine isSeqClosed_iff_isClosed.1 fun ws w hws hlim => ?_
  have hO := S.continuous_objective hv
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  have hc : ∀ n, S.greedyBM v (ws n) ∈ Icc (0 : ℝ≥0) B := fun n =>
    ⟨bot_le, ((S.greedyBM_mem hv (ws n)).1).trans (hB ⟨n, rfl⟩)⟩
  obtain ⟨c, -, φ, hφ, hcφ⟩ := isCompact_Icc.tendsto_subseq hc
  have hwφ : Tendsto (ws ∘ φ) atTop (𝓝 w) := hlim.comp hφ.tendsto_atTop
  have hcw : c ≤ w := le_of_tendsto_of_tendsto' hcφ hwφ fun k =>
    (S.greedyBM_mem hv (ws (φ k))).1
  have hac : a ≤ c := ge_of_tendsto' hcφ fun k => hws (φ k)
  have hmem : c ∈ S.argmaxSet v w := by
    refine ⟨hcw, fun d hd => ?_⟩
    have hdk : Tendsto (fun k => min d (ws (φ k))) atTop (𝓝 d) := by
      have := (tendsto_const_nhds (x := d)).min hwφ
      rwa [min_eq_left hd] at this
    refine le_of_tendsto_of_tendsto' ((hO.tendsto (w, d)).comp (hwφ.prodMk_nhds hdk))
      ((hO.tendsto (w, c)).comp (hwφ.prodMk_nhds hcφ)) fun k => ?_
    exact (S.greedyBM_mem hv (ws (φ k))).2 _ (min_le_right _ _)
  exact hac.trans (le_csSup ⟨w, fun _ hc => hc.1⟩ hmem)

/-- The largest maximizer is a feasible (Borel) policy. -/
noncomputable def greedyPolicy {v : BM ℝ≥0} (hv : Continuous v.toFun) : SavingsPolicy :=
  ⟨S.greedyBM v, measurable_of_Ici fun a => (S.isClosed_le_greedyBM hv a).measurableSet,
    fun w => (S.greedyBM_mem hv w).1⟩

/-- For continuous `v`, the Bellman operator (1.51) is continuous in wealth. -/
theorem continuous_bellmanOp {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous (S.bellmanOp v.toFun) := by
  have hO := S.continuous_objective hv
  have heq : S.bellmanOp v.toFun = fun w =>
      sSup ((fun t => S.objective v.toFun w (t * w)) '' Icc (0 : ℝ≥0) 1) := by
    funext w
    simp only [bellmanOp, iSup]
    congr 1
    ext z
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      rcases eq_or_ne w 0 with rfl | hw
      · obtain rfl : c = 0 := le_antisymm hc bot_le
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      · refine ⟨c / w, ⟨bot_le, div_le_one_of_le₀ hc (bot_le)⟩, ?_⟩
        simp only [div_mul_cancel₀ c hw]
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t * w, mul_le_of_le_one_left (bot_le) ht.2⟩, rfl⟩
  rw [heq]
  exact isCompact_Icc.continuous_sSup (hO.comp (continuous_fst.prodMk
    (continuous_snd.mul continuous_fst)))

/-- **Exercise 3.2.7** (p. 109): if `v ∈ bcℝ₊`, then a `v`-greedy policy exists, and the Bellman
operator maps `bcℝ₊` into itself. -/
theorem exercise_3_2_7 {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    S.IsGreedy v.toFun (S.greedyPolicy hv) ∧ Continuous (S.adpBM.bellman v).toFun := by
  have hg : S.IsGreedy v.toFun (S.greedyPolicy hv) := fun w c hc =>
    (S.greedyBM_mem hv w).2 c hc
  refine ⟨hg, ?_⟩
  have hvG : v ∈ S.adpBM.VG := ⟨_, (S.adpBM_isGreedy_iff v _).2 hg⟩
  rw [funext (S.adpBM_bellman_apply hvG)]
  exact S.continuous_bellmanOp hv

/-- `bcℝ₊` is closed in `bℝ₊`: uniform limits of continuous functions are continuous. -/
theorem isClosed_bc : IsClosed {v : BM ℝ≥0 | Continuous v.toFun} := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  exact (BM.tendstoUniformly_of_tendsto hlim).continuous (Frequently.of_forall hvs)

/-- **Proposition 3.2.2** (p. 109): with `φ` an arbitrary probability measure, the optimal savings
ADP obeys the fundamental optimality properties, the value function is continuous, and VFI
converges geometrically on `bcℝ₊`, by Theorem 3.1.5 with `V₀ = bcℝ₊`. -/
theorem proposition_3_2_2 :
    S.adpBM.FundamentalOptimality (ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg
        S.β_lt_one S.adpBM_contraction).wellPosed ∧
      ∃ vstar, Continuous vstar.toFun ∧
        S.adpBM.VFIGeometric {v : BM ℝ≥0 | Continuous v.toFun} vstar := by
  obtain ⟨hFO, vstar, hv, hgeo, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive S.β_nonneg
    S.β_lt_one S.adpBM_contraction ⟨isClosed_bc, fun v hv =>
      ⟨_, (S.adpBM_isGreedy_iff v _).2 (S.exercise_3_2_7 hv).1⟩,
      fun v hv => (S.exercise_3_2_7 hv).2⟩ ⟨BM.const 0, continuous_const⟩
  exact ⟨hFO, vstar, hv, hgeo⟩

end OptimalSavings

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# No-discount optimal stopping

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.3 (pp. 110–116).

A controller watching a `P`-Markov state decides when to stop: stopping in state `x` costs
`e(x)`, continuing costs `c(x)`, with `e, c ∈ bX₊` and no discounting. A policy is a measurable
exit region `E` containing the certain exit region `Ē = {e ≤ c}` (3.14), (3.16). With
`K_E g = 𝟙_{Eᶜ} Pg` (3.20) the policy operator is `T_E g = 𝟙_E e + 𝟙_{Eᶜ}(c + Pg)` (3.18)–(3.19).

The probabilistic objects are expressed through these operators: `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x)` (the
computation in the proof of Lemma 3.2.6), so `𝔼_x τ̄ = ∑_{n ≥ 1} (K_Ēⁿ𝟙)(x)`, and the `σ`-loss
function (3.13) is `g_E = ∑ₜ K_Eᵗ h_E` with `h_E = 𝟙_E e + 𝟙_{Eᶜ} c`. Identifying these with the
path-space expectations is the Markov property, not formalised here.

* **Exercise A.2.1**: an asymptotically contracting map with a fixed point is globally stable.
* **Assumption 3.2.1**: `sup_x 𝔼_x τ̄ < ∞`.
* **Lemma 3.2.3**: `g_E` is finite and bounded; **Lemma 3.2.4**: `T_E g_E = g_E`.
* **Lemma 3.2.6** (`‖K_Eⁿ f‖ ≤ ‖f‖ sup_x ℙ_x{τ_E ≥ n}`), **Lemma 3.2.7**
  (`sup_x ℙ_x{τ_E ≥ n} → 0`), **Lemma 3.2.8** (asymptotic contraction) and **Proposition 3.2.5**
  (global stability on `bX₊`).
* The ADP `(bX₊, 𝕋)` is min-regular (§3.2.3.5) and its Bellman min-equation is (3.11).
* **Theorem 3.2.9**: the fundamental min-optimality properties hold, and min-VFI, min-OPI and
  min-HPI all converge (via Theorem 3.1.8).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- **Exercise A.2.1** (p. 346): an asymptotically contracting self-map with a fixed point is
globally stable. -/
theorem exercise_A_2_1 {V : Type*} [MetricSpace V] {S : V → V}
    (hS : ∀ u v, Tendsto (fun n => dist (S^[n] u) (S^[n] v)) atTop (𝓝 0)) {vbar : V}
    (hfix : S vbar = vbar) : GloballyStable S := by
  have hit : ∀ n, S^[n] vbar = vbar := fun n => iterate_fixed hfix n
  refine ⟨vbar, hfix, fun w hw => ?_, fun u => ?_⟩
  · have h := hS w vbar
    simp only [iterate_fixed hw, hit] at h
    exact dist_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h)
  · refine tendsto_iff_dist_tendsto_zero.2 ?_
    simpa only [hit] using hS u vbar

/-- The no-discount optimal stopping problem (§3.2.3.1): a stochastic kernel `P`, an exit cost
`e ∈ bX₊` and a flow cost `c ∈ bX₊`. -/
structure NoDiscountStopping (X : Type*) [MeasurableSpace X] where
  /-- the transition kernel -/
  P : Kernel X X
  /-- the exit cost -/
  e : BM X
  e_nonneg : 0 ≤ e
  /-- the flow cost -/
  c : BM X
  c_nonneg : 0 ≤ c

namespace NoDiscountStopping

variable {X : Type*} [MeasurableSpace X] (M : NoDiscountStopping X)

/-- The certain exit region `Ē = {e ≤ c}` (3.14). -/
def Ebar : Set X := {x | M.e.toFun x ≤ M.c.toFun x}

theorem measurableSet_Ebar : MeasurableSet M.Ebar :=
  measurableSet_le M.e.measurable' M.c.measurable'

/-- Policies (3.16): measurable exit regions `E ⊇ Ē` (the indicator of `E` is `σ ≥ σ̄`). -/
def Policy : Type _ := {E : Set X // MeasurableSet E ∧ M.Ebar ⊆ E}

/-- The lower bound policy `σ̄ = 𝟙{e ≤ c}`. -/
def barPolicy : M.Policy := ⟨M.Ebar, M.measurableSet_Ebar, subset_rfl⟩

variable [IsMarkovKernel M.P]

/-- The Markov operator `P` on `bX`. -/
noncomputable def Pop (g : BM X) : BM X :=
  ⟨markovOp M.P g.toFun, measurable_markovOp M.P g.measurable',
    ⟨‖g‖, abs_markovOp_le M.P (BM.abs_le_norm g)⟩⟩

/-- `K_E g = 𝟙_{Eᶜ} Pg` (3.20). -/
noncomputable def K (σ : M.Policy) (g : BM X) : BM X :=
  ⟨σ.1ᶜ.indicator (markovOp M.P g.toFun),
    (measurable_markovOp M.P g.measurable').indicator σ.2.1.compl,
    ⟨‖g‖, fun x => by
      by_cases hx : x ∈ σ.1ᶜ
      · rw [indicator_of_mem hx]
        exact abs_markovOp_le M.P (BM.abs_le_norm g) x
      · rw [indicator_of_notMem hx, abs_zero]
        exact norm_nonneg g⟩⟩

/-- The one-period cost `h_E = 𝟙_E e + 𝟙_{Eᶜ} c`. -/
noncomputable def hcost (σ : M.Policy) : BM X :=
  ⟨fun x => σ.1.indicator M.e.toFun x + σ.1ᶜ.indicator M.c.toFun x,
    (M.e.measurable'.indicator σ.2.1).add (M.c.measurable'.indicator σ.2.1.compl),
    ⟨‖M.e‖ + ‖M.c‖, fun x => by
      by_cases hx : x ∈ σ.1
      · rw [indicator_of_mem hx, indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]
        exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_right (norm_nonneg _))
      · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx), zero_add]
        exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_left (norm_nonneg _))⟩⟩

/-- The policy operator (3.19): `T_E g = h_E + K_E g`. -/
noncomputable def T (σ : M.Policy) (g : BM X) : BM X := M.hcost σ + M.K σ g

theorem K_apply_mem {σ : M.Policy} {x : X} (hx : x ∈ σ.1) (g : BM X) :
    (M.K σ g).toFun x = 0 :=
  indicator_of_notMem (notMem_compl_iff.2 hx) _

theorem K_apply_notMem {σ : M.Policy} {x : X} (hx : x ∉ σ.1) (g : BM X) :
    (M.K σ g).toFun x = markovOp M.P g.toFun x :=
  indicator_of_mem (mem_compl hx) _

/-- (3.18): `(T_E g)(x) = e(x)` on `E` and `c(x) + (Pg)(x)` off `E`. -/
theorem T_apply_mem {σ : M.Policy} {x : X} (hx : x ∈ σ.1) (g : BM X) :
    (M.T σ g).toFun x = M.e.toFun x := by
  simp only [T, BM.add_apply, hcost, M.K_apply_mem hx, indicator_of_mem hx,
    indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]

theorem T_apply_notMem {σ : M.Policy} {x : X} (hx : x ∉ σ.1) (g : BM X) :
    (M.T σ g).toFun x = M.c.toFun x + markovOp M.P g.toFun x := by
  simp only [T, BM.add_apply, hcost, M.K_apply_notMem hx, indicator_of_notMem hx,
    indicator_of_mem (mem_compl hx), zero_add]

/-! ### Linearity and positivity of `K_E` -/

theorem K_add (σ : M.Policy) (f g : BM X) : M.K σ (f + g) = M.K σ f + M.K σ g :=
  BM.ext fun x => by
    have h := congrFun (markovOp_add M.P (BM.mem_bX f) (BM.mem_bX g)) x
    simp only [K, BM.add_apply]
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
      exact h
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]

theorem K_smul (σ : M.Policy) (a : ℝ) (f : BM X) : M.K σ (a • f) = a • M.K σ f :=
  BM.ext fun x => by
    simp only [K, BM.smul_apply]
    have := markovOp_smul M.P a f.toFun
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      exact congrFun this x
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem K_sub (σ : M.Policy) (f g : BM X) : M.K σ (f - g) = M.K σ f - M.K σ g :=
  BM.ext fun x => by
    have h := congrFun (markovOp_sub M.P (BM.mem_bX f) (BM.mem_bX g)) x
    simp only [K, BM.sub_apply]
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
      exact h
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, sub_zero]

theorem K_mono (σ : M.Policy) {f g : BM X} (h : f ≤ g) : M.K σ f ≤ M.K σ g := fun x => by
  by_cases hx : x ∈ σ.1
  · rw [M.K_apply_mem hx, M.K_apply_mem hx]
  · rw [M.K_apply_notMem hx, M.K_apply_notMem hx]
    exact markovOp_mono M.P (BM.mem_bX f) (BM.mem_bX g) h x

theorem K_nonneg (σ : M.Policy) {f : BM X} (h : 0 ≤ f) : 0 ≤ M.K σ f := by
  have := M.K_mono σ h
  rwa [show M.K σ 0 = 0 from by simpa using M.K_smul σ 0 0] at this

theorem K_const_le (σ : M.Policy) {a : ℝ} (ha : 0 ≤ a) : M.K σ (BM.const a) ≤ BM.const a :=
  fun x => by
    by_cases hx : x ∈ σ.1
    · rw [M.K_apply_mem hx]
      exact ha
    · rw [M.K_apply_notMem hx]
      exact (congrFun (markovOp_const M.P a) x).le

/-- A larger exit region discounts less: `K_E f ≤ K_F f` for `f ≥ 0` and `F ⊆ E`. -/
theorem K_le_of_subset {σ τ : M.Policy} (hst : τ.1 ⊆ σ.1) {f : BM X} (hf : 0 ≤ f) :
    M.K σ f ≤ M.K τ f := fun x => by
  by_cases hx : x ∈ σ.1
  · rw [M.K_apply_mem hx]
    exact M.K_nonneg τ hf x
  · rw [M.K_apply_notMem hx, M.K_apply_notMem (fun h => hx (hst h))]

theorem iterate_K_mono (σ : M.Policy) (n : ℕ) : Monotone (M.K σ)^[n] :=
  Monotone.iterate (fun _ _ h => M.K_mono σ h) n

theorem iterate_K_nonneg (σ : M.Policy) (n : ℕ) {f : BM X} (h : 0 ≤ f) :
    0 ≤ (M.K σ)^[n] f := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [iterate_succ_apply']
    exact M.K_nonneg σ ih

theorem iterate_K_smul (σ : M.Policy) (n : ℕ) (a : ℝ) (f : BM X) :
    (M.K σ)^[n] (a • f) = a • (M.K σ)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ih, M.K_smul]

theorem iterate_K_sub (σ : M.Policy) (n : ℕ) (f g : BM X) :
    (M.K σ)^[n] (f - g) = (M.K σ)^[n] f - (M.K σ)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih, M.K_sub]

/-! ### Survival probabilities -/

/-- `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x)`. -/
noncomputable def surv (σ : M.Policy) (n : ℕ) : BM X := (M.K σ)^[n] (BM.const 1)

theorem surv_nonneg (σ : M.Policy) (n : ℕ) : 0 ≤ M.surv σ n :=
  M.iterate_K_nonneg σ n fun _ => zero_le_one

theorem surv_succ_le (σ : M.Policy) (n : ℕ) : M.surv σ (n + 1) ≤ M.surv σ n := by
  simp only [surv]
  rw [iterate_succ_apply]
  exact M.iterate_K_mono σ n (M.K_const_le σ zero_le_one)

theorem surv_anti (σ : M.Policy) : Antitone (M.surv σ) :=
  antitone_nat_of_succ_le (M.surv_succ_le σ)

/-- (3.17): every policy stops no later than the upper bound stopping time `τ̄`. -/
theorem surv_le_surv_bar (σ : M.Policy) (n : ℕ) : M.surv σ n ≤ M.surv M.barPolicy n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [surv] at ih ⊢
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (M.K_le_of_subset σ.2.2 (M.iterate_K_nonneg σ n fun _ => zero_le_one)).trans
      (M.K_mono _ ih)

/-- **Lemma 3.2.6** (p. 114), pointwise: `|(K_Eⁿ f)(x)| ≤ ‖f‖ ℙ_x{τ_E ≥ n}`. -/
theorem abs_iterate_K_le (σ : M.Policy) (n : ℕ) (f : BM X) (x : X) :
    |((M.K σ)^[n] f).toFun x| ≤ ‖f‖ * (M.surv σ n).toFun x := by
  have hup : f ≤ ‖f‖ • BM.const 1 := fun y => by
    simpa using (le_abs_self _).trans (BM.abs_le_norm f y)
  have hlo : -‖f‖ • BM.const 1 ≤ f := fun y => by
    simpa using neg_le_of_abs_le (BM.abs_le_norm f y)
  have h1 := M.iterate_K_mono σ n hup x
  have h2 := M.iterate_K_mono σ n hlo x
  rw [M.iterate_K_smul] at h1 h2
  simp only [BM.smul_apply] at h1 h2
  exact abs_le.2 ⟨by simpa [surv] using h2, by simpa [surv] using h1⟩

/-- **Lemma 3.2.6** (p. 114): `‖K_Eⁿ f‖ ≤ ‖f‖ · sup_x ℙ_x{τ_E ≥ n}`. -/
theorem lemma_3_2_6 (σ : M.Policy) (n : ℕ) (f : BM X) :
    ‖(M.K σ)^[n] f‖ ≤ ‖f‖ * ‖M.surv σ n‖ :=
  BM.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x =>
    (M.abs_iterate_K_le σ n f x).trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (BM.abs_le_norm _ x)) (norm_nonneg _))

/-- **Assumption 3.2.1** (p. 112): `sup_x 𝔼_x τ̄ < ∞`, with
`𝔼_x τ̄ = ∑_{n ≥ 1} ℙ_x{τ̄ ≥ n} = ∑_{n ≥ 1} (K_Ēⁿ𝟙)(x)`. -/
def Assumption321 : Prop :=
  ∃ C, ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C

/-- **Lemma 3.2.7** (p. 115): under Assumption 3.2.1, `sup_x ℙ_x{τ_E ≥ n} → 0` for every policy. -/
theorem lemma_3_2_7 (hA : M.Assumption321) (σ : M.Policy) :
    Tendsto (fun n => ‖M.surv σ n‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hA
  set C' := max C 0
  have hbound : ∀ n, 1 ≤ n → ‖M.surv σ n‖ ≤ C' / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine BM.norm_le (div_nonneg (le_max_right _ _) hn'.le) fun x => ?_
    rw [abs_of_nonneg (M.surv_nonneg σ n x), le_div_iff₀ hn']
    have hsum : (n : ℝ) * (M.surv M.barPolicy n).toFun x ≤
        ∑ k ∈ Finset.range n, (M.surv M.barPolicy (k + 1)).toFun x := by
      have : ∀ k ∈ Finset.range n, (M.surv M.barPolicy n).toFun x ≤
          (M.surv M.barPolicy (k + 1)).toFun x := fun k hk =>
        M.surv_anti M.barPolicy (Finset.mem_range.1 hk) x
      simpa using Finset.card_nsmul_le_sum _ _ _ this
    calc (M.surv σ n).toFun x * n ≤ (M.surv M.barPolicy n).toFun x * n :=
          mul_le_mul_of_nonneg_right (M.surv_le_surv_bar σ n x) hn'.le
      _ ≤ C' := by linarith [hC n x, le_max_left C 0]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨1, hbound⟩) ?_
  simpa using tendsto_const_div_atTop_nhds_zero_nat C'

/-- `T_E f − T_E g = K_E(f − g)`, so `T_Eⁿ f − T_Eⁿ g = K_Eⁿ(f − g)`. -/
theorem iterate_T_sub (σ : M.Policy) (n : ℕ) (f g : BM X) :
    (M.T σ)^[n] f - (M.T σ)^[n] g = (M.K σ)^[n] (f - g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ← ih, M.K_sub]
    simp only [T]
    abel

/-- **Lemma 3.2.8** (p. 116): under Assumption 3.2.1 each `T_E` is asymptotically contracting:
`‖T_Eⁿ f − T_Eⁿ g‖ ≤ ‖f − g‖ sup_x ℙ_x{τ_E ≥ n} → 0`. -/
theorem lemma_3_2_8 (hA : M.Assumption321) (σ : M.Policy) (f g : BM X) :
    Tendsto (fun n => dist ((M.T σ)^[n] f) ((M.T σ)^[n] g)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (by simpa using (M.lemma_3_2_7 hA σ).const_mul ‖f - g‖)
  rw [dist_eq_norm, M.iterate_T_sub]
  exact M.lemma_3_2_6 σ n (f - g)

theorem K_zero (σ : M.Policy) : M.K σ 0 = 0 := by simpa using M.K_smul σ 0 0

theorem K_sum (σ : M.Policy) (s : Finset ℕ) (f : ℕ → BM X) :
    M.K σ (∑ t ∈ s, f t) = ∑ t ∈ s, M.K σ (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [M.K_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, M.K_add, ih]

/-- `T_Eⁿ 0 = ∑_{t < n} K_Eᵗ h_E`. -/
theorem iterate_T_zero (σ : M.Policy) (n : ℕ) :
    (M.T σ)^[n] 0 = ∑ t ∈ Finset.range n, (M.K σ)^[t] (M.hcost σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, Finset.sum_range_succ']
    simp only [T, M.K_sum, iterate_zero, id]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun t _ => (iterate_succ_apply' _ t _).symm

theorem sum_apply (s : Finset ℕ) (f : ℕ → BM X) (x : X) :
    (∑ t ∈ s, f t).toFun x = ∑ t ∈ s, (f t).toFun x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BM.add_apply, ih]

omit [IsMarkovKernel M.P] in
theorem hcost_nonneg (σ : M.Policy) : 0 ≤ M.hcost σ := fun x =>
  add_nonneg (indicator_nonneg (fun y _ => M.e_nonneg y) x)
    (indicator_nonneg (fun y _ => M.c_nonneg y) x)

omit [IsMarkovKernel M.P] in
theorem norm_hcost_le (σ : M.Policy) : ‖M.hcost σ‖ ≤ ‖M.e‖ + ‖M.c‖ := by
  obtain ⟨C, hC⟩ := (M.hcost σ).bdd'
  refine BM.norm_le (add_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => ?_
  simp only [hcost]
  by_cases hx : x ∈ σ.1
  · rw [indicator_of_mem hx, indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]
    exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_right (norm_nonneg _))
  · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx), zero_add]
    exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- `∑_{t < n} ℙ_x{τ_E ≥ t} ≤ 1 + 𝔼_x τ̄`. -/
theorem sum_surv_le (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) (n : ℕ)
    (x : X) : ∑ t ∈ Finset.range n, (M.surv σ t).toFun x ≤ 1 + C := by
  have hC0 : 0 ≤ C := by simpa using hC 0 x
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
  | succ m =>
    rw [Finset.sum_range_succ']
    have h0 : (M.surv σ 0).toFun x = 1 := rfl
    have h1 : ∑ t ∈ Finset.range m, (M.surv σ (t + 1)).toFun x ≤
        ∑ t ∈ Finset.range m, (M.surv M.barPolicy (t + 1)).toFun x :=
      Finset.sum_le_sum fun t _ => M.surv_le_surv_bar σ (t + 1) x
    linarith [hC m x]

/-- The bound behind **Lemma 3.2.3**: `‖T_Eⁿ 0‖ ≤ (‖e‖ + ‖c‖)(1 + C)`. -/
theorem norm_iterate_T_zero_le (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) (n : ℕ) :
    ‖(M.T σ)^[n] 0‖ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) := by
  refine BM.norm_le (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (by positivity)) fun x => ?_
  rw [M.iterate_T_zero, sum_apply]
  calc |∑ t ∈ Finset.range n, ((M.K σ)^[t] (M.hcost σ)).toFun x|
      ≤ ∑ t ∈ Finset.range n, |((M.K σ)^[t] (M.hcost σ)).toFun x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range n, ‖M.hcost σ‖ * (M.surv σ t).toFun x :=
        Finset.sum_le_sum fun t _ => M.abs_iterate_K_le σ t _ x
    _ = ‖M.hcost σ‖ * ∑ t ∈ Finset.range n, (M.surv σ t).toFun x := by rw [Finset.mul_sum]
    _ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) := mul_le_mul (M.norm_hcost_le σ)
        ((M.sum_surv_le σ hC n x).trans (by linarith [le_max_left C 0]))
        (Finset.sum_nonneg fun t _ => M.surv_nonneg σ t x)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- `dist (T_E f) (T_E g) ≤ dist f g`. -/
theorem dist_T_le (σ : M.Policy) (f g : BM X) : dist (M.T σ f) (M.T σ g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  have h := M.lemma_3_2_6 σ 1 (f - g)
  have hs : ‖M.surv σ 1‖ ≤ 1 := BM.norm_le zero_le_one fun x => by
    rw [abs_of_nonneg (M.surv_nonneg σ 1 x)]
    exact M.K_const_le σ zero_le_one x
  have hT : M.T σ f - M.T σ g = M.K σ (f - g) := by
    simpa using M.iterate_T_sub σ 1 f g
  rw [hT]
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hs)

/-- The `σ`-loss function (3.13), as the limit of `T_Eⁿ 0 = ∑_{t < n} K_Eᵗ h_E`. -/
noncomputable def lossFn (σ : M.Policy) : BM X := limUnder atTop fun n => (M.T σ)^[n] 0

theorem tendsto_lossFn (hA : M.Assumption321) (σ : M.Policy) :
    Tendsto (fun n => (M.T σ)^[n] 0) atTop (𝓝 (M.lossFn σ)) := by
  obtain ⟨C, hC⟩ := hA
  set B := (‖M.e‖ + ‖M.c‖) * (1 + max C 0)
  have hsurv := (M.lemma_3_2_7 ⟨C, hC⟩ σ).const_mul B
  rw [mul_zero] at hsurv
  have hcauchy : CauchySeq fun n => (M.T σ)^[n] 0 := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hsurv.eventually (gt_mem_nhds hε))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [iterate_add_apply, dist_eq_norm, M.iterate_T_sub, sub_zero]
    exact ((M.lemma_3_2_6 σ N _).trans (mul_le_mul_of_nonneg_right
      (M.norm_iterate_T_zero_le σ hC m) (norm_nonneg _))).trans_lt (hN N le_rfl)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact tendsto_nhds_limUnder ⟨g, hg⟩

/-- **Lemma 3.2.4** (p. 112): `g_E` is a fixed point of `T_E`. -/
theorem lemma_3_2_4 (hA : M.Assumption321) (σ : M.Policy) :
    M.T σ (M.lossFn σ) = M.lossFn σ := by
  have hlim := M.tendsto_lossFn hA σ
  have hcont : Continuous (M.T σ) :=
    LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => by
      simpa using M.dist_T_le σ f g)
  have h1 : Tendsto (fun n => (M.T σ)^[n + 1] 0) atTop (𝓝 (M.T σ (M.lossFn σ))) := by
    simp only [iterate_succ_apply']
    exact (hcont.tendsto _).comp hlim
  exact tendsto_nhds_unique h1 (hlim.comp (tendsto_add_atTop_nat 1))

/-- **Lemma 3.2.3** (p. 112): under Assumption 3.2.1, `g_E` is bounded:
`‖g_E‖ ≤ (‖e‖ + ‖c‖)(1 + sup_x 𝔼_x τ̄)`. -/
theorem lemma_3_2_3 (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) :
    ‖M.lossFn σ‖ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) :=
  le_of_tendsto ((M.tendsto_lossFn ⟨C, hC⟩ σ).norm)
    (Eventually.of_forall (M.norm_iterate_T_zero_le σ hC))

/-- (3.13) in series form: `g_E(x) = ∑ₜ (K_Eᵗ h_E)(x)`. -/
theorem lossFn_hasSum (hA : M.Assumption321) (σ : M.Policy) (x : X) :
    HasSum (fun t => ((M.K σ)^[t] (M.hcost σ)).toFun x) ((M.lossFn σ).toFun x) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun t => M.iterate_K_nonneg σ t
    (M.hcost_nonneg σ) x) _).2 ?_
  have hpt : Tendsto (fun n => ((M.T σ)^[n] 0).toFun x) atTop (𝓝 ((M.lossFn σ).toFun x)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun n => by rw [Real.dist_eq]; exact BM.abs_sub_le_dist _ _ x)
      (tendsto_iff_dist_tendsto_zero.1 (M.tendsto_lossFn hA σ)))
  simpa only [M.iterate_T_zero, sum_apply] using hpt

/-- **Proposition 3.2.5** (p. 114), on `bX`: under Assumption 3.2.1 every `T_E` is globally stable,
with fixed point `g_E` (Lemma 3.2.8, Lemma 3.2.4 and Exercise A.2.1). -/
theorem proposition_3_2_5_bX (hA : M.Assumption321) (σ : M.Policy) : GloballyStable (M.T σ) :=
  exercise_A_2_1 (M.lemma_3_2_8 hA σ) (M.lemma_3_2_4 hA σ)

/-- A drift (Lyapunov) criterion for Assumption 3.2.1: if `W ≥ 0` is bounded and
`(PW)(x) + δ ≤ W(x)` off the certain exit region, then `𝔼_x τ̄ ≤ W(x)/δ ≤ ‖W‖/δ`. This plays the
role of the martingale exit-time bound (Theorem A.3.9) used in §3.2.4. -/
theorem assumption321_of_drift {W : BM X} (hW : 0 ≤ W) {δ : ℝ} (hδ : 0 < δ)
    (hdrift : ∀ x ∉ M.Ebar, markovOp M.P W.toFun x + δ ≤ W.toFun x) : M.Assumption321 := by
  have hKW : δ • M.K M.barPolicy (BM.const 1) + M.K M.barPolicy W ≤ W := fun x => by
    by_cases hx : x ∈ M.Ebar
    · simp only [BM.add_apply, BM.smul_apply, M.K_apply_mem (σ := M.barPolicy) hx, mul_zero,
        add_zero]
      exact hW x
    · simp only [BM.add_apply, BM.smul_apply, M.K_apply_notMem (σ := M.barPolicy) hx]
      have h1 : markovOp M.P (BM.const 1 : BM X).toFun x = 1 :=
        congrFun (markovOp_const M.P 1) x
      rw [h1, mul_one, add_comm]
      exact hdrift x hx
  have key : ∀ N, δ • ∑ n ∈ Finset.range N,
      (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) + (M.K M.barPolicy)^[N] W ≤ W := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hsplit : δ • ∑ n ∈ Finset.range (N + 1),
            (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) +
            (M.K M.barPolicy)^[N + 1] W =
          δ • M.K M.barPolicy (BM.const 1) + M.K M.barPolicy (δ • ∑ n ∈ Finset.range N,
            (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) +
            (M.K M.barPolicy)^[N] W) := by
        rw [Finset.sum_range_succ', M.K_add, M.K_smul, M.K_sum, iterate_succ_apply',
          iterate_zero, id, smul_add]
        simp only [iterate_succ_apply']
        abel
      rw [hsplit]
      exact (add_le_add le_rfl (M.K_mono _ ih)).trans hKW
  refine ⟨‖W‖ / δ, fun N x => ?_⟩
  have h1 := key N x
  have h2 : 0 ≤ ((M.K M.barPolicy)^[N] W).toFun x := M.iterate_K_nonneg M.barPolicy N hW x
  have hsurv : ∀ n, (M.surv M.barPolicy (n + 1)).toFun x =
      ((M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1))).toFun x := fun n => by
    simp only [surv]
    rw [iterate_succ_apply]
  simp only [BM.add_apply, BM.smul_apply, sum_apply] at h1
  rw [le_div_iff₀ hδ]
  simp only [hsurv]
  have h3 : W.toFun x ≤ ‖W‖ := (le_abs_self _).trans (BM.abs_le_norm W x)
  nlinarith

/-! ### The ADP on `bX₊` -/

theorem Pop_nonneg {g : BM X} (hg : 0 ≤ g) : 0 ≤ M.Pop g := fun x => by
  have := markovOp_mono M.P (const_mem_bX 0) (BM.mem_bX g) hg x
  rwa [markovOp_const] at this

theorem T_nonneg (σ : M.Policy) {g : BM X} (hg : 0 ≤ g) : 0 ≤ M.T σ g :=
  add_nonneg (M.hcost_nonneg σ) (M.K_nonneg σ hg)

theorem T_mono (σ : M.Policy) : Monotone (M.T σ) := fun _ _ h =>
  add_le_add le_rfl (M.K_mono σ h)

theorem lossFn_nonneg (hA : M.Assumption321) (σ : M.Policy) : 0 ≤ M.lossFn σ :=
  ge_of_tendsto' (M.tendsto_lossFn hA σ) fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact M.T_nonneg σ ih

/-- The no-discount optimal stopping ADP `(bX₊, 𝕋)` (§3.2.3.5). -/
noncomputable def adp : ADP {g : BM X // 0 ≤ g} M.Policy where
  T σ g := ⟨M.T σ g.1, M.T_nonneg σ g.2⟩
  mono σ _ _ h := M.T_mono σ h
  nonempty := ⟨M.barPolicy⟩

/-- **Proposition 3.2.5** (p. 114): under Assumption 3.2.1 every `T_E` is globally stable on
`bX₊`. -/
theorem proposition_3_2_5 (hA : M.Assumption321) : M.adp.IsGloballyStable := fun σ => by
  obtain ⟨u, hu, huniq, hlim⟩ := M.proposition_3_2_5_bX hA σ
  have hit : ∀ n (g : {g : BM X // 0 ≤ g}), ((M.adp.T σ)^[n] g).1 = (M.T σ)^[n] g.1 := by
    intro n
    induction n with
    | zero => exact fun g => rfl
    | succ n ih =>
      intro g
      rw [iterate_succ_apply', iterate_succ_apply', ← ih]
      rfl
  have hu0 : u = M.lossFn σ := (huniq _ (M.lemma_3_2_4 hA σ)).symm
  refine ⟨⟨u, hu0 ▸ M.lossFn_nonneg hA σ⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 (congrArg Subtype.val hw)), fun g => ?_⟩
  refine tendsto_subtype_rng.2 ?_
  simp only [hit]
  exact hlim g.1

/-- The `g`-min-greedy exit region `{e ≤ c + Pg}` (§3.2.3.5). -/
noncomputable def minGreedy (g : {g : BM X // 0 ≤ g}) : M.Policy :=
  ⟨{x | M.e.toFun x ≤ M.c.toFun x + markovOp M.P g.1.toFun x},
    measurableSet_le M.e.measurable' (M.c.measurable'.add (measurable_markovOp M.P
      g.1.measurable')),
    fun x hx => (show M.e.toFun x ≤ M.c.toFun x from hx).trans
      (le_add_of_nonneg_right (M.Pop_nonneg g.2 x))⟩

/-- (3.11): the min-greedy policy attains `min{e, c + Pg}`. -/
theorem T_minGreedy_apply (g : {g : BM X // 0 ≤ g}) (x : X) :
    (M.T (M.minGreedy g) g.1).toFun x =
      min (M.e.toFun x) (M.c.toFun x + markovOp M.P g.1.toFun x) := by
  by_cases hx : x ∈ (M.minGreedy g).1
  · rw [M.T_apply_mem hx, min_eq_left hx]
  · rw [M.T_apply_notMem hx, min_eq_right (le_of_lt (not_le.1 hx))]

/-- §3.2.3.5 (p. 114): the min-greedy exit region is `g`-min-greedy, so `(bX₊, 𝕋)` is
min-regular, and its Bellman min-operator is (3.11), `T▿g = min{e, c + Pg}`. -/
theorem isMinGreedy_minGreedy (g : {g : BM X // 0 ≤ g}) :
    M.adp.IsMinGreedy g (M.minGreedy g) := fun τ x => by
  change (M.T (M.minGreedy g) g.1).toFun x ≤ (M.T τ g.1).toFun x
  rw [M.T_minGreedy_apply]
  by_cases hx : x ∈ τ.1
  · rw [M.T_apply_mem hx]
    exact min_le_left _ _
  · rw [M.T_apply_notMem hx]
    exact min_le_right _ _

theorem adp_minRegular : M.adp.MinRegular := fun g => ⟨_, M.isMinGreedy_minGreedy g⟩

/-- `bX₊` is countably Dedekind complete. -/
theorem countablyDedekindComplete_nonneg :
    CountablyDedekindComplete {g : BM X // 0 ≤ g} := by
  intro A hne hc
  obtain ⟨a₀, ha₀⟩ := hne
  have h := BM.countablyDedekindComplete (Subtype.val '' A) ⟨a₀.1, a₀, ha₀, rfl⟩ (hc.image _)
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨l, hl⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := h.1 ⟨u.1, by rintro _ ⟨a, ha, rfl⟩; exact hu ha⟩
    have hs0 : 0 ≤ s := a₀.2.trans (hs.1 ⟨a₀, ha₀, rfl⟩)
    exact ⟨⟨s, hs0⟩, fun a ha => hs.1 ⟨a, ha, rfl⟩, fun w hw =>
      hs.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩
  · obtain ⟨i, hi⟩ := h.2 ⟨l.1, by rintro _ ⟨a, ha, rfl⟩; exact hl ha⟩
    have hi0 : 0 ≤ i := l.2.trans (hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hl ha))
    exact ⟨⟨i, hi0⟩, fun a ha => hi.1 ⟨a, ha, rfl⟩, fun w hw =>
      hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩

/-- The `σ`-value function of the ADP is the `σ`-loss function `g_E`. -/
theorem vσ_eq_lossFn (hA : M.Assumption321) (σ : M.Policy) :
    (M.adp.vσ (M.proposition_3_2_5 hA).wellPosed σ).1 = M.lossFn σ :=
  (congrArg Subtype.val (M.adp.eq_vσ (M.proposition_3_2_5 hA).wellPosed
    (σ := σ) (v := ⟨M.lossFn σ, M.lossFn_nonneg hA σ⟩)
    (Subtype.ext (M.lemma_3_2_4 hA σ)))).symm

/-- **Theorem 3.2.9** (p. 116): under Assumption 3.2.1, for the no-discount optimal stopping ADP
`(bX₊, 𝕋)`, (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI and
min-HPI all converge. -/
theorem theorem_3_2_9 (hA : M.Assumption321) :
    M.adp.MinFundamentalOptimality (M.proposition_3_2_5 hA).wellPosed ∧
      ∃ vstar, M.adp.IsMinValueFunction vstar ∧ M.adp.MinVFIConverges vstar ∧
        ∀ g, M.adp.IsMinSelector g → M.adp.MinOPIConverges g vstar ∧
          M.adp.MinHPIConverges (M.proposition_3_2_5 hA).wellPosed g vstar :=
  ADP.theorem_3_1_8 M.adp_minRegular (M.proposition_3_2_5 hA)
    ⟨⟨0, le_rfl⟩, fun σ => M.T_nonneg σ le_rfl⟩ countablyDedekindComplete_nonneg

end NoDiscountStopping

end SargentStachurski.ADPsOnPospaces

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential analysis revisited

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.4 (pp. 117–121).

The belief state `π` evolves by Bayes' rule (3.30), `π' = κ(π, Z)` with `Z` drawn from the
predictive density `ψ(π, ·)` (3.26). The kernel `P` is built on `X = [0, 1]`: the book's
`(0, 1)` is not invariant when the supports of `f₀` and `f₁` differ (`kappa_hits_zero`).

* The belief kernel `P(π, ·)` = law of `κ(π, Z)`, `Z ∼ ψ(π, z) dz`, with
  `(Pg)(π) = ∫ g(κ(π, z))ψ(π, z) dz` (3.26).
* Beliefs are a martingale, and the conditional variance is (3.32)–(3.33):
  `∫ (κ(π, z) − π)²ψ(π, z) dz ≥ π²(1 − π)²Δ(f₀, f₁)`, with `Δ` the triangular discrimination.
* **Lemma 3.2.11**: `Δ(f₀, f₁) > 0` when `f₀ ≠ f₁` on a set of positive measure.
* **Lemma 3.2.12**, in drift form: with `W(π) = 1 − π²`, `(PW)(π) + δ ≤ W(π)` on `(a, b)` for
  `δ = a²(1 − b)²Δ`. A drift bound gives `𝔼_π τ ≤ W(π)/δ ≤ 1/δ` (replacing the martingale
  bound of Theorem A.3.9).
* **Proposition 3.2.10**: when `f₀, f₁` are distinct, Assumption 3.2.1 holds for the sequential
  analysis stopping problem with exit cost `e(π) = min{πL₀, (1 − π)L₁}` (3.27), so the fundamental
  min-optimality properties hold and min-VFI, min-OPI and min-HPI converge.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- The belief space `X = [0, 1]`. -/
abbrev Belief : Type := ↥(Icc (0 : ℝ) 1)

/-- The sequential analysis problem (§1.4, §3.2.4.1): densities `f₀, f₁` on `ℝ`, losses
`L₀, L₁ > 0` and a sampling cost `c > 0`. -/
structure SeqAnalysis where
  /-- the density under hypothesis 0 -/
  f₀ : ℝ → ℝ
  /-- the density under hypothesis 1 -/
  f₁ : ℝ → ℝ
  f₀_nonneg : ∀ z, 0 ≤ f₀ z
  f₁_nonneg : ∀ z, 0 ≤ f₁ z
  f₀_meas : Measurable f₀
  f₁_meas : Measurable f₁
  f₀_int : Integrable f₀
  f₁_int : Integrable f₁
  f₀_one : ∫ z, f₀ z = 1
  f₁_one : ∫ z, f₁ z = 1
  /-- the loss from wrongly accepting `f₀` -/
  L₀ : ℝ
  /-- the loss from wrongly accepting `f₁` -/
  L₁ : ℝ
  /-- the cost of a draw -/
  c : ℝ
  L₀_pos : 0 < L₀
  L₁_pos : 0 < L₁
  c_pos : 0 < c

namespace SeqAnalysis

variable (S : SeqAnalysis)

/-- `ψ(π, z)`, nonnegative on `[0, 1]`. -/
theorem psi_nonneg (π : Belief) (z : ℝ) : 0 ≤ predDensity S.f₀ S.f₁ π.1 z :=
  add_nonneg (mul_nonneg (by linarith [π.2.2]) (S.f₀_nonneg z)) (mul_nonneg π.2.1 (S.f₁_nonneg z))

theorem measurable_psi : Measurable fun p : Belief × ℝ => predDensity S.f₀ S.f₁ p.1.1 p.2 :=
  ((measurable_const.sub (measurable_subtype_coe.comp measurable_fst)).mul
    (S.f₀_meas.comp measurable_snd)).add
    ((measurable_subtype_coe.comp measurable_fst).mul (S.f₁_meas.comp measurable_snd))

theorem integrable_psi (π : ℝ) : Integrable (predDensity S.f₀ S.f₁ π) :=
  (S.f₀_int.const_mul _).add (S.f₁_int.const_mul _)

/-- The predictive distribution `ψ(π, z) dz` as a kernel from `[0, 1]` to `ℝ`. -/
noncomputable def Q : Kernel Belief ℝ :=
  Kernel.withDensity (Kernel.const Belief volume)
    fun π z => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)

theorem measurable_density :
    Measurable (uncurry fun (π : Belief) (z : ℝ) => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)) :=
  ENNReal.measurable_ofReal.comp S.measurable_psi

theorem isMarkov_Q : IsMarkovKernel S.Q := by
  refine ⟨fun π => ⟨?_⟩⟩
  rw [Q, Kernel.withDensity_apply _ S.measurable_density, Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (S.integrable_psi π.1)
      (Eventually.of_forall (S.psi_nonneg π)),
    integral_predDensity S.f₀_int S.f₁_int S.f₀_one S.f₁_one, ENNReal.ofReal_one]

/-- Bayes' rule (3.30) as a map `[0, 1] × ℝ → [0, 1]`. -/
noncomputable def kappa (p : Belief × ℝ) : Belief :=
  ⟨bayesUpdate S.f₀ S.f₁ p.1.1 p.2, bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg p.1.2 p.2⟩

theorem measurable_kappa : Measurable S.kappa :=
  (((measurable_subtype_coe.comp measurable_fst).mul (S.f₁_meas.comp measurable_snd)).div
    S.measurable_psi).subtype_mk

/-- The belief kernel (3.26): `P(π, ·)` is the law of `κ(π, Z)` with `Z ∼ ψ(π, z) dz`. -/
noncomputable def P : Kernel Belief Belief :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ S.Q) S.kappa

theorem isMarkov_P : IsMarkovKernel S.P := by
  have := S.isMarkov_Q
  exact Kernel.IsMarkovKernel.map _ S.measurable_kappa

theorem P_apply (π : Belief) : S.P π = (S.Q π).map fun z => S.kappa (π, z) := by
  have := S.isMarkov_Q
  rw [P, Kernel.map_apply _ S.measurable_kappa, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.dirac_prod, Measure.map_map S.measurable_kappa measurable_prodMk_left]
  rfl

/-- (3.26): `(Pg)(π) = ∫ g(κ(π, z))ψ(π, z) dz` for bounded measurable `g`. -/
theorem integral_P {g : Belief → ℝ} (hg : Measurable g) (π : Belief) :
    ∫ x, g x ∂(S.P π) = ∫ z, g (S.kappa (π, z)) * predDensity S.f₀ S.f₁ π.1 z := by
  have hk : Measurable fun z => S.kappa (π, z) := S.measurable_kappa.comp measurable_prodMk_left
  rw [S.P_apply, integral_map hk.aemeasurable hg.aestronglyMeasurable, Q,
    Kernel.withDensity_apply _ S.measurable_density, Kernel.const_apply]
  have hd : Measurable fun z => (predDensity S.f₀ S.f₁ π.1 z).toNNReal :=
    (S.measurable_psi.comp measurable_prodMk_left).real_toNNReal
  rw [show (fun z => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)) =
      fun z => ((predDensity S.f₀ S.f₁ π.1 z).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hd]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (S.psi_nonneg π z), smul_eq_mul]
  ring

/-! ### The triangular discrimination -/

/-- The triangular discrimination `Δ(f₀, f₁) = ∫ (f₁ − f₀)²/(f₀ + f₁)` (the integrand is `0` where
`f₀ + f₁ = 0`). -/
noncomputable def triDisc : ℝ := ∫ z, (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z)

theorem triDisc_integrand_nonneg (z : ℝ) : 0 ≤ (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) :=
  div_nonneg (sq_nonneg _) (add_nonneg (S.f₀_nonneg z) (S.f₁_nonneg z))

theorem triDisc_integrand_le (z : ℝ) :
    (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) ≤ S.f₀ z + S.f₁ z := by
  have h0 := S.f₀_nonneg z
  have h1 := S.f₁_nonneg z
  rcases (add_nonneg h0 h1).eq_or_lt with h | h
  · rw [← h, div_zero]
  · rw [div_le_iff₀ h]
    nlinarith

theorem integrable_triDisc :
    Integrable fun z => (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) := by
  refine (S.f₀_int.add S.f₁_int).mono' (((S.f₁_meas.sub S.f₀_meas).pow_const 2).div
    (S.f₀_meas.add S.f₁_meas)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (S.triDisc_integrand_nonneg z)]
  exact S.triDisc_integrand_le z

theorem triDisc_nonneg : 0 ≤ S.triDisc := integral_nonneg S.triDisc_integrand_nonneg

/-- **Lemma 3.2.11** (p. 120): if `f₀` and `f₁` are distinct (not equal almost everywhere), the
triangular discrimination is positive. -/
theorem lemma_3_2_11 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) : 0 < S.triDisc := by
  refine (integral_pos_iff_support_of_nonneg S.triDisc_integrand_nonneg
    S.integrable_triDisc).2 ?_
  rw [Filter.EventuallyEq, ae_iff] at h
  refine (pos_iff_ne_zero.2 h).trans_le (measure_mono fun z hz => ?_)
  have hz' : S.f₀ z ≠ S.f₁ z := hz
  have hs : 0 < S.f₀ z + S.f₁ z := by
    rcases (add_nonneg (S.f₀_nonneg z) (S.f₁_nonneg z)).eq_or_lt with h0 | h0
    · exact absurd (by linarith [S.f₀_nonneg z, S.f₁_nonneg z]) hz'
    · exact h0
  exact (div_pos (pow_pos (abs_pos.2 (sub_ne_zero.2 hz'.symm)) 2 |>.trans_eq
    (sq_abs _)) hs).ne'

/-! ### Beliefs: martingale and conditional variance -/

theorem measurable_val : Measurable fun x : Belief => (x : ℝ) := measurable_subtype_coe

/-- Beliefs are a martingale (§3.2.4.2): `∫ π' P(π, dπ') = π`. -/
theorem integral_P_id (π : Belief) : ∫ x, (x : ℝ) ∂(S.P π) = π := by
  rw [S.integral_P measurable_val]
  exact integral_bayesUpdate_mul_predDensity S.f₀_nonneg S.f₁_nonneg S.f₁_one π.2

theorem integrable_bounded_mul_psi {h : ℝ → ℝ} (hh : Measurable h) (hb : ∀ z, |h z| ≤ 1)
    (π : Belief) : Integrable fun z => h z * predDensity S.f₀ S.f₁ π.1 z :=
  (S.integrable_psi π.1).bdd_mul hh.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)

theorem measurable_bayes (π : Belief) : Measurable (bayesUpdate S.f₀ S.f₁ π.1) :=
  (measurable_const.mul S.f₁_meas).div ((measurable_const.mul S.f₀_meas).add
    (measurable_const.mul S.f₁_meas))

theorem abs_bayes_le (π : Belief) (z : ℝ) : |bayesUpdate S.f₀ S.f₁ π.1 z| ≤ 1 := by
  obtain ⟨h0, h1⟩ := bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z
  rw [abs_le]
  constructor <;> linarith

/-- The conditional variance of beliefs:
`∫ π'² P(π, dπ') − π² = ∫ (κ(π, z) − π)²ψ(π, z) dz`. -/
theorem integral_P_sq (π : Belief) :
    ∫ x, (x : ℝ) ^ 2 ∂(S.P π) - (π : ℝ) ^ 2 =
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  have hκ := S.measurable_bayes π
  have hb := S.abs_bayes_le π
  rw [S.integral_P (measurable_val.pow_const 2)]
  have i1 := S.integrable_bounded_mul_psi (hκ.pow_const 2) (fun z => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb z)) π
  have i2 := S.integrable_bounded_mul_psi hκ hb π
  have i3 := S.integrable_psi π.1
  have hexp : (fun z => (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z) =
      fun z => (bayesUpdate S.f₀ S.f₁ π.1 z ^ 2 * predDensity S.f₀ S.f₁ π.1 z -
        2 * π * (bayesUpdate S.f₀ S.f₁ π.1 z * predDensity S.f₀ S.f₁ π.1 z)) +
          π ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
    funext z
    ring
  rw [hexp, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_bayesUpdate_mul_predDensity S.f₀_nonneg S.f₁_nonneg S.f₁_one π.2,
    integral_predDensity S.f₀_int S.f₁_int S.f₀_one S.f₁_one]
  · simp only [kappa]
    ring
  · exact i1
  · exact i2.const_mul _
  · exact i1.sub (i2.const_mul _)
  · exact i3.const_mul _

/-- (3.32)–(3.33) (p. 121): for `0 < π < 1`,
`∫ (κ(π, z) − π)²ψ(π, z) dz ≥ π²(1 − π)²Δ(f₀, f₁)`. -/
theorem variance_ge (π : Belief) (h0 : 0 < (π : ℝ)) (h1 : (π : ℝ) < 1) :
    (π : ℝ) ^ 2 * (1 - π) ^ 2 * S.triDisc ≤
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  rw [triDisc, ← integral_const_mul]
  refine integral_mono (S.integrable_triDisc.const_mul _)
    (S.integrable_bounded_mul_psi (((S.measurable_bayes π).sub measurable_const).pow_const 2)
      (fun z => ?_) π) fun z => ?_
  · obtain ⟨hk0, hk1⟩ := bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z
    have hp0 := π.2.1
    have hp1 := π.2.2
    simp only [Pi.sub_apply]
    rw [abs_of_nonneg (sq_nonneg _), sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  · have ha := S.f₀_nonneg z
    have hb := S.f₁_nonneg z
    simp only [bayesUpdate, predDensity]
    set a := S.f₀ z
    set b := S.f₁ z
    set p : ℝ := (π : ℝ)
    have hq : 0 ≤ 1 - p := by linarith
    have hqa : 0 ≤ (1 - p) * a := mul_nonneg hq ha
    have hpb : 0 ≤ p * b := mul_nonneg h0.le hb
    rcases (add_nonneg hqa hpb).eq_or_lt with hψ | hψ
    · have hA : (1 - p) * a = 0 := by linarith
      have hB : p * b = 0 := by linarith
      have ha0 : a = 0 := (mul_eq_zero.1 hA).resolve_left (sub_ne_zero.2 (ne_of_gt h1))
      have hb0 : b = 0 := (mul_eq_zero.1 hB).resolve_left h0.ne'
      simp [ha0, hb0]
    · have hle : (1 - p) * a + p * b ≤ a + b := by nlinarith
      have key : (p * b / ((1 - p) * a + p * b) - p) ^ 2 * ((1 - p) * a + p * b) =
          p ^ 2 * (1 - p) ^ 2 * ((b - a) ^ 2 / ((1 - p) * a + p * b)) := by
        field_simp
        ring
      rw [key]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) hψ hle)
        (by positivity)

/-! ### Lemma 3.2.12 in drift form -/

/-- The Lyapunov function `W(π) = 1 − π²`. -/
noncomputable def W : BM Belief :=
  ⟨fun x => 1 - (x : ℝ) ^ 2, measurable_const.sub (measurable_val.pow_const 2), ⟨1, fun x => by
    have h0 := x.2.1
    have h1 := x.2.2
    rw [abs_le]
    constructor <;> nlinarith⟩⟩

theorem W_nonneg : 0 ≤ W := fun x => by
  have h0 := x.2.1
  have h1 := x.2.2
  change 0 ≤ 1 - (x : ℝ) ^ 2
  nlinarith

/-- `(PW)(π) = 1 − π² − ∫ (κ(π, z) − π)²ψ(π, z) dz`. -/
theorem markovOp_W (π : Belief) :
    markovOp S.P W.toFun π = 1 - (π : ℝ) ^ 2 -
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  have := S.isMarkov_P
  have hsq : Integrable (fun x : Belief => (x : ℝ) ^ 2) (S.P π) :=
    Integrable.of_bound (measurable_val.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        have h0 := x.2.1
        have h1 := x.2.2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith)
  have h := S.integral_P_sq π
  simp only [markovOp, W]
  rw [integral_sub (integrable_const 1) hsq, integral_const, probReal_univ, one_smul]
  linarith

/-- **Lemma 3.2.12** (p. 120), drift form: for `0 < a ≤ π ≤ b < 1`,
`(PW)(π) + a²(1 − b)²Δ(f₀, f₁) ≤ W(π)`. With the drift criterion this bounds `𝔼_π τ` by
`W(π)/δ < 1/δ`, `δ = a²(1 − b)²Δ`. -/
theorem lemma_3_2_12 {a b : ℝ} (ha : 0 < a) (hb : b < 1) (π : Belief) (hπa : a ≤ π)
    (hπb : (π : ℝ) ≤ b) :
    markovOp S.P W.toFun π + a ^ 2 * (1 - b) ^ 2 * S.triDisc ≤ W.toFun π := by
  have hv := S.variance_ge π (ha.trans_le hπa) (hπb.trans_lt hb)
  rw [S.markovOp_W]
  have h1 : a ^ 2 * (1 - b) ^ 2 ≤ (π : ℝ) ^ 2 * (1 - π) ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ ha.le hπa 2) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (sq_nonneg _) (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_right h1 S.triDisc_nonneg
  change _ ≤ 1 - (π : ℝ) ^ 2
  linarith

/-! ### The stopping problem and Proposition 3.2.10 -/

/-- The exit cost (3.27): `e(π) = min{πL₀, (1 − π)L₁}`. -/
noncomputable def exitCost : BM Belief :=
  ⟨fun x => min ((x : ℝ) * S.L₀) ((1 - x) * S.L₁),
    (measurable_val.mul measurable_const).min ((measurable_const.sub measurable_val).mul
      measurable_const), ⟨S.L₀ + S.L₁, fun x => by
        have h0 := x.2.1
        have h1 := x.2.2
        have hL₀ := S.L₀_pos
        have hL₁ := S.L₁_pos
        rw [abs_of_nonneg (le_min (by positivity) (mul_nonneg (by linarith) hL₁.le))]
        exact (min_le_left _ _).trans (by nlinarith)⟩⟩

/-- The sequential analysis problem as a no-discount stopping problem (§3.2.4.1): exit cost
(3.27), constant flow cost `c` and the belief kernel (3.26). -/
noncomputable abbrev stopping : NoDiscountStopping Belief where
  P := S.P
  e := S.exitCost
  e_nonneg x := le_min (mul_nonneg x.2.1 S.L₀_pos.le) (mul_nonneg (by linarith [x.2.2])
    S.L₁_pos.le)
  c := BM.const S.c
  c_nonneg _ := S.c_pos.le

attribute [local instance] SeqAnalysis.isMarkov_P

/-- Off the certain exit region, `c/L₀ < π < 1 − c/L₁` (§3.2.4.2). -/
theorem bounds_of_notMem_Ebar {π : Belief} (h : π ∉ S.stopping.Ebar) :
    S.c / S.L₀ < π ∧ (π : ℝ) < 1 - S.c / S.L₁ := by
  have h' : ¬ (S.exitCost.toFun π ≤ S.c) := h
  rw [not_le] at h'
  have h : S.c < min ((π : ℝ) * S.L₀) ((1 - π) * S.L₁) := h'
  have h1 : S.c < π * S.L₀ := h.trans_le (min_le_left _ _)
  have h2 : S.c < (1 - π) * S.L₁ := h.trans_le (min_le_right _ _)
  constructor
  · rw [div_lt_iff₀ S.L₀_pos]
    exact h1
  · have : S.c / S.L₁ < 1 - π := by
      rw [div_lt_iff₀ S.L₁_pos]
      exact h2
    linarith

/-- §3.2.4.2: if `f₀` and `f₁` are distinct, Assumption 3.2.1 holds, with `sup_π 𝔼_π τ̄ ≤ 1/δ`,
`δ = (c/L₀)²(c/L₁)²Δ(f₀, f₁)`. -/
theorem assumption321 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) : S.stopping.Assumption321 := by
  have hΔ := S.lemma_3_2_11 h
  have ha : 0 < S.c / S.L₀ := div_pos S.c_pos S.L₀_pos
  have hb : 1 - S.c / S.L₁ < 1 := by linarith [div_pos S.c_pos S.L₁_pos]
  refine S.stopping.assumption321_of_drift W_nonneg
    (δ := (S.c / S.L₀) ^ 2 * (1 - (1 - S.c / S.L₁)) ^ 2 * S.triDisc)
    (by have : 0 < 1 - (1 - S.c / S.L₁) := by linarith
        positivity) fun π hπ => ?_
  obtain ⟨h1, h2⟩ := S.bounds_of_notMem_Ebar hπ
  exact S.lemma_3_2_12 ha hb π h1.le h2.le

/-- **Proposition 3.2.10** (p. 119): if `f₀` and `f₁` are distinct, then for the sequential
analysis ADP the fundamental min-optimality properties hold, and min-VFI, min-OPI and min-HPI
all converge. -/
theorem proposition_3_2_10 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) :
    S.stopping.adp.MinFundamentalOptimality
        (S.stopping.proposition_3_2_5 (S.assumption321 h)).wellPosed ∧
      ∃ vstar, S.stopping.adp.IsMinValueFunction vstar ∧ S.stopping.adp.MinVFIConverges vstar ∧
        ∀ g, S.stopping.adp.IsMinSelector g → S.stopping.adp.MinOPIConverges g vstar ∧
          S.stopping.adp.MinHPIConverges
            (S.stopping.proposition_3_2_5 (S.assumption321 h)).wellPosed g vstar :=
  S.stopping.theorem_3_2_9 (S.assumption321 h)

/-- (3.25) and (3.28) agree with the Bellman operator (1.58) of §1.4: the Bellman min-operator of
the stopping ADP is `min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`. -/
theorem minBellman_eq_seqBellman (g : {g : BM Belief // 0 ≤ g}) (π : Belief) :
    (S.stopping.T (S.stopping.minGreedy g) g.1).toFun π =
      seqBellman S.f₀ S.f₁ S.L₀ S.L₁ S.c
        (fun x => if h : x ∈ Icc (0 : ℝ) 1 then g.1.toFun ⟨x, h⟩ else 0) π := by
  rw [NoDiscountStopping.T_minGreedy_apply]
  have hint : ∫ z, g.1.toFun (S.kappa (π, z)) * predDensity S.f₀ S.f₁ π.1 z =
      ∫ z, (fun x => if h : x ∈ Icc (0 : ℝ) 1 then g.1.toFun ⟨x, h⟩ else 0)
        (bayesUpdate S.f₀ S.f₁ π.1 z) * predDensity S.f₀ S.f₁ π.1 z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    split_ifs with hz
    · rfl
    · exact absurd (bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z) hz
  simp only [seqBellman, markovOp]
  rw [S.integral_P g.1.measurable', hint, ← min_assoc]
  rfl

end SeqAnalysis

/-- **The belief space `(0, 1)` of §3.2.4.1 is not invariant.** With `f₀ = 𝟙_{[0, 1]}` and
`f₁ = 2 · 𝟙_{[0, 1/2]}` (both densities), every `π ∈ (0, 1)` and every `z ∈ (1/2, 1]` give
`ψ(π, z) > 0` and `κ(π, z) = 0`: from any interior belief the posterior jumps to `0` with
probability `(1 − π)/2 > 0`. -/
theorem kappa_hits_zero :
    ∃ f₀ f₁ : ℝ → ℝ, (∀ z, 0 ≤ f₀ z) ∧ (∀ z, 0 ≤ f₁ z) ∧ (∫ z, f₀ z = 1) ∧ (∫ z, f₁ z = 1) ∧
      ∀ π : ℝ, 0 < π → π < 1 → ∀ z ∈ Ioc (1 / 2 : ℝ) 1,
        0 < predDensity f₀ f₁ π z ∧ bayesUpdate f₀ f₁ π z = 0 := by
  refine ⟨(Icc (0 : ℝ) 1).indicator fun _ => 1, (Icc (0 : ℝ) (1 / 2)).indicator fun _ => 2,
    fun z => indicator_nonneg (fun _ _ => zero_le_one) z,
    fun z => indicator_nonneg (fun _ _ => zero_le_two) z, ?_, ?_, fun π h0 h1 z hz => ?_⟩
  · rw [integral_indicator_const (1 : ℝ) measurableSet_Icc, Real.volume_real_Icc]
    norm_num
  · rw [integral_indicator_const (2 : ℝ) measurableSet_Icc, Real.volume_real_Icc]
    norm_num
  · have hz1 : z ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    have hz2 : z ∉ Icc (0 : ℝ) (1 / 2) := fun h => absurd h.2 (not_le.2 hz.1)
    simp only [predDensity, bayesUpdate, indicator_of_mem hz1, indicator_of_notMem hz2,
      mul_zero, add_zero, zero_div, and_true, mul_one]
    linarith

end SargentStachurski.ADPsOnPospaces

set_option linter.style.longLine false
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.mk
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.nonneg
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.rowsum
#print axioms SargentStachurski.ADPsOnPospaces.IsDistribution
#print axioms SargentStachurski.ADPsOnPospaces.IsDistribution.mk
#print axioms SargentStachurski.ADPsOnPospaces.IsDistribution.nonneg
#print axioms SargentStachurski.ADPsOnPospaces.IsDistribution.sum_eq_one
#print axioms SargentStachurski.ADPsOnPospaces.mulVec_apply_eq
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.mul
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.pow
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.mulVec_const
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.GloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.mk
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.nonneg
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.lt_one
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.iterate_mem
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.ADPsOnPospaces.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.ADPsOnPospaces.fixedPt_le_of_le
#print axioms SargentStachurski.ADPsOnPospaces.le_fixedPt_of_le_apply
#print axioms SargentStachurski.ADPsOnPospaces.isContractionOn_of_blackwell
#print axioms SargentStachurski.ADPsOnPospaces.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.ADPsOnPospaces.IsBdd
#print axioms SargentStachurski.ADPsOnPospaces.IsSupContraction
#print axioms SargentStachurski.ADPsOnPospaces.IsUniformlyClosed
#print axioms SargentStachurski.ADPsOnPospaces.isBdd_const
#print axioms SargentStachurski.ADPsOnPospaces.IsBdd.sub
#print axioms SargentStachurski.ADPsOnPospaces.IsBdd.add
#print axioms SargentStachurski.ADPsOnPospaces.IsBdd.nonneg_bound
#print axioms SargentStachurski.ADPsOnPospaces.IsBdd.exists_dist
#print axioms SargentStachurski.ADPsOnPospaces.IsSupContraction.iterate
#print axioms SargentStachurski.ADPsOnPospaces.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.ADPsOnPospaces.IsSupContraction.exists_limit
#print axioms SargentStachurski.ADPsOnPospaces.IsSupContraction.globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.le_of_le_map_of_tendsto
#print axioms SargentStachurski.ADPsOnPospaces.le_of_map_le_of_tendsto
#print axioms SargentStachurski.ADPsOnPospaces.bX
#print axioms SargentStachurski.ADPsOnPospaces.isUniformlyClosed_bX
#print axioms SargentStachurski.ADPsOnPospaces.const_mem_bX
#print axioms SargentStachurski.ADPsOnPospaces.abs_max_sub_max_le
#print axioms SargentStachurski.ADPsOnPospaces.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.mk
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.V
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.T
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.β
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.β_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.β_lt_one
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.nonempty
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bdd
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.closed
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.mono
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.contraction
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.exists_greedy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_mem
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.T_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.eq_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.le_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_le
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.IsGreedy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.nonempty_policy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.greedy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.T_le_bellman
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_mono
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_contraction
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vstar
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vstar_mem
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.bellman_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.eq_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.IsOptimal
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.optimality
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.hpiPolicy
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.hpi_terminates
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.opi
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.opi_step
#print axioms SargentStachurski.ADPsOnPospaces.ContractingDP.tendsto_opi
#print axioms SargentStachurski.ADPsOnPospaces.markovOp
#print axioms SargentStachurski.ADPsOnPospaces.integrable_of_mem_bX
#print axioms SargentStachurski.ADPsOnPospaces.measurable_markovOp
#print axioms SargentStachurski.ADPsOnPospaces.abs_markovOp_le
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_mem_bX
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_mono
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_const
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_add
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_sub
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_smul
#print axioms SargentStachurski.ADPsOnPospaces.markovOp_sub_const
#print axioms SargentStachurski.ADPsOnPospaces.abs_markovOp_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.mk
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.add
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.smul
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.mono
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.abs_le
#print axioms SargentStachurski.ADPsOnPospaces.isMarkovLike_markovOp
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.sub
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.abs_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.iterate_mem
#print axioms SargentStachurski.ADPsOnPospaces.IsMarkovLike.abs_iterate_le
#print axioms SargentStachurski.ADPsOnPospaces.affineOp
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_mono
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_contraction
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_iterate_zero
#print axioms SargentStachurski.ADPsOnPospaces.affineOp_hasSum
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.mk
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Γ
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Γ_nonempty
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.r
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.β
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.β_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.β_lt_one
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.P
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.P_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.P_sum
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Policy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Q
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Tσ
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.isBdd_of_finite
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.abs_sum_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Q_mono
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.abs_Q_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Q_sub_const
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exists_greedy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.toDP
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.IsGreedy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.bellman_eq
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.bellman_contraction
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Pσ
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.rσ
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Tσ_eq_mulVec
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.abs_Pσ_mulVec_le
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.vσ_eq_inv
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.vσ_hasSum
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.abs_vσ_le
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.finite_policy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.theorem_1_2_1
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.theorem_1_2_2
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.vstar_le
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.IsLPFeasible
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.lp_solution
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.mk
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.u
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.u_cont
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.u_bdd
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.φ
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.φ_prob
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.β
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.β_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.β_lt_one
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.R
#print axioms SargentStachurski.ADPsOnPospaces.SavingsPolicy
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.cont
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.Pσ
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.rσ
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.Tσ
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.integrable_comp
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.abs_cont_le
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.isMarkovLike_Pσ
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.rσ_mem
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.Tσ_mapsTo
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.Tσ_globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.vσ_hasSum
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.abs_fixedPoint_le
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.objective
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.bellmanOp
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.bddAbove_objective
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.bellmanOp_contraction
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.IsGreedy
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.toDP
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.bellman_eq
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.dp_results
#print axioms SargentStachurski.ADPsOnPospaces.predDensity
#print axioms SargentStachurski.ADPsOnPospaces.bayesUpdate
#print axioms SargentStachurski.ADPsOnPospaces.bayesUpdate_mem_Icc
#print axioms SargentStachurski.ADPsOnPospaces.bayesUpdate_mul_predDensity
#print axioms SargentStachurski.ADPsOnPospaces.integral_predDensity
#print axioms SargentStachurski.ADPsOnPospaces.integral_bayesUpdate_mul_predDensity
#print axioms SargentStachurski.ADPsOnPospaces.seqBellman
#print axioms SargentStachurski.ADPsOnPospaces.seqBellman_mono
#print axioms SargentStachurski.ADPsOnPospaces.seqBellman_mem
#print axioms SargentStachurski.ADPsOnPospaces.OrderStable
#print axioms SargentStachurski.ADPsOnPospaces.IncreasesTo
#print axioms SargentStachurski.ADPsOnPospaces.DecreasesTo
#print axioms SargentStachurski.ADPsOnPospaces.StronglyOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.orderStable_of_up_down
#print axioms SargentStachurski.ADPsOnPospaces.StronglyOrderStable.orderStable
#print axioms SargentStachurski.ADPsOnPospaces.dualMap
#print axioms SargentStachurski.ADPsOnPospaces.orderStable_dual_iff
#print axioms SargentStachurski.ADPsOnPospaces.dualMap_iterate
#print axioms SargentStachurski.ADPsOnPospaces.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete.exists_least
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.ADPsOnPospaces.ChainComplete.orderStable
#print axioms SargentStachurski.ADPsOnPospaces.chainComplete_Icc
#print axioms SargentStachurski.ADPsOnPospaces.CountablyDedekindComplete
#print axioms SargentStachurski.ADPsOnPospaces.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.ADPsOnPospaces.CountablyDedekindComplete.dual
#print axioms SargentStachurski.ADPsOnPospaces.OrderContinuous
#print axioms SargentStachurski.ADPsOnPospaces.OrderContinuous.monotone
#print axioms SargentStachurski.ADPsOnPospaces.isLUB_range_succ_iff
#print axioms SargentStachurski.ADPsOnPospaces.tarski_kantorovich
#print axioms SargentStachurski.ADPsOnPospaces.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP
#print axioms SargentStachurski.ADPsOnPospaces.ADP.mk
#print axioms SargentStachurski.ADPsOnPospaces.ADP.T
#print axioms SargentStachurski.ADPsOnPospaces.ADP.mono
#print axioms SargentStachurski.ADPsOnPospaces.ADP.nonempty
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGreedy
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VG
#print axioms SargentStachurski.ADPsOnPospaces.ADP.WellPosed
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsFinite
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Regular
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsBellmanValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.SolvesBellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.ADPsOnPospaces.ADP.regular_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.greedy
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isGreedy_greedy
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.T_le_bellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.solvesBellman_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman_mono
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VU
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VSig
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.ADPsOnPospaces.ADP.vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.T_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.eq_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VSig_eq_range
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOptimal
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsValueFunction
#print axioms SargentStachurski.ADPsOnPospaces.ADP.BellmanPrinciple
#print axioms SargentStachurski.ADPsOnPospaces.ADP.FundamentalOptimality
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isOptimal_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.ADPsOnPospaces.ADP.exists_solves_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.ADPsOnPospaces.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsSelector
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.ADPsOnPospaces.ADP.howard
#print axioms SargentStachurski.ADPsOnPospaces.ADP.opt
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsSelector.T_eq
#print axioms SargentStachurski.ADPsOnPospaces.ADP.mem_VU_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.ADPsOnPospaces.ADP.iterate_mono_of_le
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman_le_opt
#print axioms SargentStachurski.ADPsOnPospaces.ADP.chain_2_9
#print axioms SargentStachurski.ADPsOnPospaces.ADP.mapsTo_VU
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman_le_of_le
#print axioms SargentStachurski.ADPsOnPospaces.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VFIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.OPIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.HPIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.opt_one
#print axioms SargentStachurski.ADPsOnPospaces.ADP.OPIConverges.vfi
#print axioms SargentStachurski.ADPsOnPospaces.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.ADPsOnPospaces.ADP.iterates_le_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VU_nonempty
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.ADPsOnPospaces.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.ADPsOnPospaces.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.ADPsOnPospaces.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.ADPsOnPospaces.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.ADPsOnPospaces.ADP.OrderBounded
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderContinuous
#print axioms SargentStachurski.ADPsOnPospaces.ADP.le_of_orderBounded
#print axioms SargentStachurski.ADPsOnPospaces.ADP.convergence_of_dedekind
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_dual
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsMinGreedy
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VGmin
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinRegular
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinOrderBounded
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsMinBellmanValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.SolvesMinBellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsMinValueFunction
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsMinOptimal
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinBellmanPrinciple
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinFundamentalOptimality
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isMinGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minRegular_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minOrderBounded_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isMinBellmanValue_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VGmin_eq
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_VSig
#print axioms SargentStachurski.ADPsOnPospaces.ADP.WellPosed.dual
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isMinValueFunction_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isMinOptimal_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_opt_howard
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minBellmanPrinciple_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minFundamentalOptimality_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VD
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinVFIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minVFIConverges_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsOrderStable.minFundamentalOptimality
#print axioms SargentStachurski.ADPsOnPospaces.isLUB_of_tendsto_bX
#print axioms SargentStachurski.ADPsOnPospaces.tendsto_of_isLUB_bX
#print axioms SargentStachurski.ADPsOnPospaces.countablyDedekindComplete_bX
#print axioms SargentStachurski.ADPsOnPospaces.tendsto_markovOp
#print axioms SargentStachurski.ADPsOnPospaces.consumeAll
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_wellPosed
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_isOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_regular_iff
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_bellman_apply
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.exercise_2_3_4
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_orderBounded
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_isOrderContinuous
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adp_optimality
#print axioms SargentStachurski.ADPsOnPospaces.isLUB_of_tendsto_subtype
#print axioms SargentStachurski.ADPsOnPospaces.isGLB_of_tendsto_subtype
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.nonempty_policy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_wellPosed
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_isOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_isOrderContinuous
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.rbar
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.abs_r_le_rbar
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_orderBounded
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_2_3_7
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_regular
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_bellman_apply
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.proposition_2_3_1
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Vhat
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.mem_Vhat_iff
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Tσ_mapsTo_Vhat
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adpHat
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.vσ_mem_Vhat
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adpHat_isStronglyOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adpHat_regular
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_2_3_10
#print axioms SargentStachurski.ADPsOnPospaces.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.ADPsOnPospaces.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.ADPsOnPospaces.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_2
#print axioms SargentStachurski.ADPsOnPospaces.ADP.corollary_3_1_3
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_4
#print axioms SargentStachurski.ADPsOnPospaces.IsSupNonexpansive
#print axioms SargentStachurski.ADPsOnPospaces.IsInfNonexpansive
#print axioms SargentStachurski.ADPsOnPospaces.isInfNonexpansive_iff
#print axioms SargentStachurski.ADPsOnPospaces.isSupNonexpansive_real
#print axioms SargentStachurski.ADPsOnPospaces.isSupNonexpansive_pi
#print axioms SargentStachurski.ADPsOnPospaces.ADP.lemma_A_5_21
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsSemiRegular
#print axioms SargentStachurski.ADPsOnPospaces.ADP.VFIGeometric
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_5
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsMinSelector
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinOPIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.MinHPIConverges
#print axioms SargentStachurski.ADPsOnPospaces.ADP.isMinSelector_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_opt_iterate
#print axioms SargentStachurski.ADPsOnPospaces.ADP.dual_howard_iterate
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minOPIConverges_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.minHPIConverges_iff
#print axioms SargentStachurski.ADPsOnPospaces.ADP.min_of_dual
#print axioms SargentStachurski.ADPsOnPospaces.ADP.IsGloballyStable.dual
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_6
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_8
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_7
#print axioms SargentStachurski.ADPsOnPospaces.vShapeOrder
#print axioms SargentStachurski.ADPsOnPospaces.vShapeDist
#print axioms SargentStachurski.ADPsOnPospaces.vShapeDist_metric
#print axioms SargentStachurski.ADPsOnPospaces.vShape_isLUB
#print axioms SargentStachurski.ADPsOnPospaces.vShape_sup_not_inf
#print axioms SargentStachurski.ADPsOnPospaces.ADP.planComp
#print axioms SargentStachurski.ADPsOnPospaces.ADP.planComp_succ
#print axioms SargentStachurski.ADPsOnPospaces.ADP.planComp_mono
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.mk
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.supNonexp
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.pos
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.lt_one
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.contr
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.bdd
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.dist_planComp
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.exists_planValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.planValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.tendsto_planValue
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.planValue_eq
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.continuous_globallyStable
#print axioms SargentStachurski.ADPsOnPospaces.ADP.Assumption311.exists_solvesBellman
#print axioms SargentStachurski.ADPsOnPospaces.ADP.theorem_3_1_10
#print axioms SargentStachurski.ADPsOnPospaces.BM
#print axioms SargentStachurski.ADPsOnPospaces.BM.mk
#print axioms SargentStachurski.ADPsOnPospaces.BM.toFun
#print axioms SargentStachurski.ADPsOnPospaces.BM.measurable'
#print axioms SargentStachurski.ADPsOnPospaces.BM.bdd'
#print axioms SargentStachurski.ADPsOnPospaces.BM.ext
#print axioms SargentStachurski.ADPsOnPospaces.BM.bddAbove
#print axioms SargentStachurski.ADPsOnPospaces.BM.const
#print axioms SargentStachurski.ADPsOnPospaces.BM.toFun_injective
#print axioms SargentStachurski.ADPsOnPospaces.BM.zero
#print axioms SargentStachurski.ADPsOnPospaces.BM.add
#print axioms SargentStachurski.ADPsOnPospaces.BM.neg
#print axioms SargentStachurski.ADPsOnPospaces.BM.sub
#print axioms SargentStachurski.ADPsOnPospaces.BM.smulReal
#print axioms SargentStachurski.ADPsOnPospaces.BM.nsmul
#print axioms SargentStachurski.ADPsOnPospaces.BM.zsmul
#print axioms SargentStachurski.ADPsOnPospaces.BM.addCommGroup
#print axioms SargentStachurski.ADPsOnPospaces.BM.supNorm
#print axioms SargentStachurski.ADPsOnPospaces.BM.abs_le_supNorm
#print axioms SargentStachurski.ADPsOnPospaces.BM.supNorm_le
#print axioms SargentStachurski.ADPsOnPospaces.BM.supNorm_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.BM.normedAddCommGroup
#print axioms SargentStachurski.ADPsOnPospaces.BM.add_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.sub_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.neg_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.zero_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.const_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.norm_def
#print axioms SargentStachurski.ADPsOnPospaces.BM.abs_le_norm
#print axioms SargentStachurski.ADPsOnPospaces.BM.norm_le
#print axioms SargentStachurski.ADPsOnPospaces.BM.abs_sub_le_dist
#print axioms SargentStachurski.ADPsOnPospaces.BM.dist_le
#print axioms SargentStachurski.ADPsOnPospaces.BM.module
#print axioms SargentStachurski.ADPsOnPospaces.BM.smul_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.normedSpace
#print axioms SargentStachurski.ADPsOnPospaces.BM.lattice
#print axioms SargentStachurski.ADPsOnPospaces.BM.le_def
#print axioms SargentStachurski.ADPsOnPospaces.BM.sup_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.inf_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.abs_apply
#print axioms SargentStachurski.ADPsOnPospaces.BM.isOrderedAddMonoid
#print axioms SargentStachurski.ADPsOnPospaces.BM.hasSolidNorm
#print axioms SargentStachurski.ADPsOnPospaces.BM.completeSpace
#print axioms SargentStachurski.ADPsOnPospaces.BM.countablyDedekindComplete
#print axioms SargentStachurski.ADPsOnPospaces.BM.isSupNonexpansive
#print axioms SargentStachurski.ADPsOnPospaces.BM.isInfNonexpansive
#print axioms SargentStachurski.ADPsOnPospaces.BM.mem_bX
#print axioms SargentStachurski.ADPsOnPospaces.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.ADPsOnPospaces.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.ADPsOnPospaces.BM.globallyStable_of_bX
#print axioms SargentStachurski.ADPsOnPospaces.globallyStable_of_supContraction
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.adp_isGloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.section_3_2_1_1
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.G
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.finite_G
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.pairOf
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Sσ
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.Sσ_mono
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.qadp
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_3_2_3
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_3_2_3_converse
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exists_qgreedy
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.qadp_regular
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_3_2_4
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_3_2_5
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.qadp_isGloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.FiniteMDP.exercise_3_2_6
#print axioms SargentStachurski.ADPsOnPospaces.exercise_3_2_3_converse_fails
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.mk
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Γ
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Γ_nonempty
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.r
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.r_bdd
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.β
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.β_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.β_lt_one
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.P
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.P_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.P_sum
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Policy
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.nonempty_policy
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.summable_mul
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.abs_tsum_le
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Q
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Q_mono
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.abs_Q_sub_le
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.Tσ
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.adp
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.adp_contraction
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.adp_regular
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.adp_isGloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.CountableMDP.exercise_3_2_1
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.TBM
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM_isGloballyStable
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM_isGreedy_iff
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM_bellman_apply
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM_orderBounded
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.adpBM_contraction
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.proposition_3_2_1
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.remark_3_2_1
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.continuous_cont
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.continuous_objective
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.argmaxSet
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.argmaxSet_nonempty
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.isClosed_argmaxSet
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.greedyBM
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.greedyBM_mem
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.isClosed_le_greedyBM
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.greedyPolicy
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.continuous_bellmanOp
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.exercise_3_2_7
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.isClosed_bc
#print axioms SargentStachurski.ADPsOnPospaces.OptimalSavings.proposition_3_2_2
#print axioms SargentStachurski.ADPsOnPospaces.exercise_A_2_1
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.mk
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.P
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.e
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.e_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.c
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.c_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.Ebar
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.measurableSet_Ebar
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.Policy
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.barPolicy
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.Pop
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.hcost
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_apply_mem
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_apply_notMem
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T_apply_mem
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T_apply_notMem
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_add
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_smul
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_sub
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_mono
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_const_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_le_of_subset
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_K_mono
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_K_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_K_smul
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_K_sub
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.surv
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.surv_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.surv_succ_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.surv_anti
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.surv_le_surv_bar
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.abs_iterate_K_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lemma_3_2_6
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.Assumption321
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lemma_3_2_7
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_T_sub
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lemma_3_2_8
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_zero
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.K_sum
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.iterate_T_zero
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.sum_apply
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.hcost_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.norm_hcost_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.sum_surv_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.norm_iterate_T_zero_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.dist_T_le
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lossFn
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.tendsto_lossFn
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lemma_3_2_4
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lemma_3_2_3
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lossFn_hasSum
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.proposition_3_2_5_bX
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.assumption321_of_drift
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.Pop_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T_mono
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.lossFn_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.adp
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.proposition_3_2_5
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.minGreedy
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.T_minGreedy_apply
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.isMinGreedy_minGreedy
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.adp_minRegular
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.countablyDedekindComplete_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.vσ_eq_lossFn
#print axioms SargentStachurski.ADPsOnPospaces.NoDiscountStopping.theorem_3_2_9
#print axioms SargentStachurski.ADPsOnPospaces.Belief
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.mk
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₀
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₁
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₀_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₁_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₀_meas
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₁_meas
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₀_int
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₁_int
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₀_one
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.f₁_one
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.L₀
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.L₁
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.c
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.L₀_pos
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.L₁_pos
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.c_pos
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.psi_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.measurable_psi
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integrable_psi
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.Q
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.measurable_density
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.isMarkov_Q
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.kappa
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.measurable_kappa
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.P
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.isMarkov_P
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.P_apply
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integral_P
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.triDisc
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.triDisc_integrand_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.triDisc_integrand_le
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integrable_triDisc
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.triDisc_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.lemma_3_2_11
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.measurable_val
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integral_P_id
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integrable_bounded_mul_psi
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.measurable_bayes
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.abs_bayes_le
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.integral_P_sq
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.variance_ge
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.W
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.W_nonneg
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.markovOp_W
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.lemma_3_2_12
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.exitCost
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.stopping
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.bounds_of_notMem_Ebar
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.assumption321
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.proposition_3_2_10
#print axioms SargentStachurski.ADPsOnPospaces.SeqAnalysis.minBellman_eq_seqBellman
#print axioms SargentStachurski.ADPsOnPospaces.kappa_hits_zero
