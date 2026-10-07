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
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.GiryMonad
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Volume 2, Chapter 4 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firm valuation on `bX`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.1.1 and §4.2.1.3 (pp. 133–136).

* §4.2.1.1: the firm ADP `(bX, 𝕋_FV)` with policy operators (4.10), the greedy policy (4.11),
  the Bellman equation (4.13), and **Proposition 4.2.1** by Theorem 4.1.3 with `e = 𝟙`, `λ = β`.
* §4.2.1.3: state-dependent discounting, `T_σ v = σs + (1 − σ)(π + Kv)` (4.14) with
  `(Kv)(x) = β(x) ∫ v(x')P(x, dx')`; the Bellman equation (4.15), and **Proposition 4.2.2**
  (**Exercise 4.2.1**) under Assumption 4.2.1 `ρ(K) < 1`, by Theorem 4.1.8.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnBanachSpace

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X : Type*} [MeasurableSpace X]

/-- `id` is an isometric order embedding of `bX` into itself. -/
theorem isIsoOrderEmbedding_id : BanachLattice.IsIsoOrderEmbedding (id : BM X → BM X) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

namespace FirmProblem

variable (F : FirmProblem X)

/-- The policy operator (4.10) on `bX`. -/
noncomputable def TBM (σ : FirmPolicy X) (v : BM X) : BM X :=
  ⟨F.Tσ σ.1 v.toFun, (F.Tσ_mapsTo σ.2 (BM.mem_bX v)).1, (F.Tσ_mapsTo σ.2 (BM.mem_bX v)).2⟩

/-- The firm valuation ADP `(bX, 𝕋_FV)` (§4.2.1.1). -/
noncomputable def adpBM : ADP (BM X) (FirmPolicy X) where
  T := F.TBM
  mono σ _ _ h := F.Tσ_mono σ.1 (BM.mem_bX _) (BM.mem_bX _) h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The `v`-greedy policy (4.11): sell when `s ≥ π + βPv`. -/
noncomputable def sellBM (v : BM X) : FirmPolicy X :=
  ⟨fun x => decide (F.profit x + F.β * markovOp F.P v.toFun x ≤ F.s),
    F.measurable_sellPolicy (BM.mem_bX v)⟩

theorem sellBM_isGreedy (v : BM X) : F.adpBM.IsGreedy v (F.sellBM v) := fun τ x =>
  (F.Tσ_le_max τ.1 v.toFun x).trans_eq (F.Tσ_sellPolicy v.toFun x).symm

theorem adpBM_regular : F.adpBM.Regular := fun v => ⟨_, F.sellBM_isGreedy v⟩

/-- (4.13): the Bellman operator is `Tv = s ∨ (π + βPv)`. -/
theorem adpBM_bellman_apply (v : BM X) (x : X) :
    (F.adpBM.bellman v).toFun x = max F.s (F.profit x + F.β * markovOp F.P v.toFun x) := by
  have h := F.adpBM.isGreedy_greedy (F.adpBM_regular v)
  rw [← F.Tσ_sellPolicy v.toFun x]
  exact le_antisymm (F.sellBM_isGreedy v _ x) (h (F.sellBM v) x)

/-- Blackwell's condition (4.4) with `e = 𝟙` and `λ = β`. -/
theorem blackwell (σ : FirmPolicy X) (v : BM X) (κ : ℝ) (hκ : 0 ≤ κ) :
    F.adpBM.T σ (v + κ • BM.const 1) ≤ F.adpBM.T σ v + (F.β * κ) • BM.const 1 := fun x => by
  have := F.isMarkov
  change F.Tσ σ.1 (v + κ • BM.const 1).toFun x ≤ F.Tσ σ.1 v.toFun x + F.β * κ * 1
  have hP : markovOp F.P (v + κ • BM.const 1).toFun x = markovOp F.P v.toFun x + κ := by
    have h1 := markovOp_add F.P (BM.mem_bX v) (const_mem_bX κ)
    have h2 : (v + κ • BM.const 1).toFun = v.toFun + fun _ => κ := by
      funext y
      simp only [BM.add_apply, BM.smul_apply, BM.const_apply, Pi.add_apply, mul_one]
    rw [h2, h1, markovOp_const]
    rfl
  simp only [Tσ, hP]
  split_ifs
  · nlinarith [F.β_nonneg]
  · nlinarith [F.β_nonneg]

/-- **Proposition 4.2.1** (p. 133): for the firm valuation ADP `(bX, 𝕋_FV)` the fundamental
optimality properties hold, VFI converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_1 [Nonempty X] :
    ∃ hw : F.adpBM.WellPosed, F.adpBM.FundamentalOptimality hw ∧ ∃ vstar,
      F.adpBM.VFIGeometric univ vstar ∧ F.adpBM.VFIConverges vstar ∧
        ∀ g, F.adpBM.IsSelector g → F.adpBM.OPIConverges g vstar ∧
          F.adpBM.HPIConverges hw g vstar := by
  have hsr : F.adpBM.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adpBM_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one F.adpBM F.β_nonneg F.β_lt_one F.blackwell hsr univ_nonempty
  have hT : ∀ σ v w, dist (F.adpBM.T σ v) (F.adpBM.T σ w) ≤ F.β * dist v w := fun σ v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one (F.adpBM.mono σ) F.β_nonneg
      (F.blackwell σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ F.β_nonneg F.β_lt_one hT
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adpBM_regular hgs
    ((F.adpBM.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adpBM_regular⟩

end FirmProblem

/-! ### State-dependent discounting -/

/-- The firm problem with state-dependent discounting (§4.2.1.3): a bounded nonnegative discount
function `β(x) = 1/(1 + r(x))`. -/
structure FirmSD (X : Type*) [MeasurableSpace X] where
  /-- the stochastic kernel of the state -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the profit function -/
  profit : BM X
  /-- the state-dependent discount factor -/
  βf : BM X
  βf_nonneg : 0 ≤ βf
  /-- the sale price -/
  s : ℝ

namespace FirmSD

variable (F : FirmSD X)

/-- The discount operator `(Kv)(x) = β(x) ∫ v(x')P(x, dx')`. -/
noncomputable def K : BM X →L[ℝ] BM X :=
  have := F.isMarkov
  BM.mulCLM F.βf ∘L BM.markovCLM F.P

theorem K_apply (v : BM X) (x : X) :
    (F.K v).toFun x = F.βf.toFun x * markovOp F.P v.toFun x := rfl

theorem K_isPositive : BanachLattice.IsPositiveOp F.K := by
  have := F.isMarkov
  exact fun v hv => BM.mulCLM_isPositive F.βf_nonneg _ (BM.markovCLM_isPositive F.P v hv)

/-- The indicator of continuing, `1 − σ`. -/
def cont (σ : FirmPolicy X) : BM X :=
  ⟨fun x => if σ.1 x then 0 else 1, Measurable.ite (σ.2 (measurableSet_singleton true))
    measurable_const measurable_const, ⟨1, fun x => by split_ifs <;> simp⟩⟩

/-- `r_σ = σs + (1 − σ)π`. -/
def rσ (σ : FirmPolicy X) : BM X :=
  ⟨fun x => if σ.1 x then F.s else F.profit.toFun x, Measurable.ite
    (σ.2 (measurableSet_singleton true)) measurable_const F.profit.measurable', by
      obtain ⟨C, hC⟩ := F.profit.bdd'
      exact ⟨max |F.s| C, fun x => by
        split_ifs
        · exact le_max_left _ _
        · exact (hC x).trans (le_max_right _ _)⟩⟩

/-- `K_σ = (1 − σ)K`. -/
noncomputable def Kσ (σ : FirmPolicy X) : BM X →L[ℝ] BM X := BM.mulCLM (cont σ) ∘L F.K

/-- The policy operator (4.14): `T_σ v = σs + (1 − σ)(π + Kv)`. -/
noncomputable def T (σ : FirmPolicy X) (v : BM X) : BM X := F.rσ σ + F.Kσ σ v

theorem T_apply (σ : FirmPolicy X) (v : BM X) (x : X) :
    (F.T σ v).toFun x = if σ.1 x then F.s else F.profit.toFun x + (F.K v).toFun x := by
  simp only [T, Kσ, BM.add_apply, ContinuousLinearMap.comp_apply, BM.mulCLM_apply, rσ, cont]
  split_ifs <;> simp

/-- The firm ADP with state-dependent discounting, `(bX, 𝕋_FV)`. -/
noncomputable def adp : ADP (BM X) (FirmPolicy X) where
  T := F.T
  mono σ v w h x := by
    rw [F.T_apply, F.T_apply]
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (F.K_isPositive.mono h x)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The `v`-greedy policy: sell when `s ≥ π + Kv`. -/
noncomputable def sell (v : BM X) : FirmPolicy X :=
  ⟨fun x => decide (F.profit.toFun x + (F.K v).toFun x ≤ F.s), measurable_to_bool (by
    have : (fun x => decide (F.profit.toFun x + (F.K v).toFun x ≤ F.s)) ⁻¹' {true} =
        {x | F.profit.toFun x + (F.K v).toFun x ≤ F.s} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le (F.profit + F.K v).measurable' measurable_const)⟩

theorem T_sell_apply (v : BM X) (x : X) :
    (F.T (F.sell v) v).toFun x = max F.s (F.profit.toFun x + (F.K v).toFun x) := by
  rw [F.T_apply]
  by_cases h : F.profit.toFun x + (F.K v).toFun x ≤ F.s
  · simp [sell, h]
  · simp only [sell, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

theorem sell_isGreedy (v : BM X) : F.adp.IsGreedy v (F.sell v) := fun τ x => by
  change (F.T τ v).toFun x ≤ (F.T (F.sell v) v).toFun x
  rw [F.T_sell_apply, F.T_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem adp_regular : F.adp.Regular := fun v => ⟨_, F.sell_isGreedy v⟩

/-- (4.15): the Bellman operator is `Tv = s ∨ (π + Kv)`. -/
theorem adp_bellman_apply (v : BM X) (x : X) :
    (F.adp.bellman v).toFun x = max F.s (F.profit.toFun x + (F.K v).toFun x) := by
  have h := F.adp.isGreedy_greedy (F.adp_regular v)
  rw [← F.T_sell_apply v x]
  exact le_antisymm (F.sell_isGreedy v _ x) (h (F.sell v) x)

/-- The ADP is additive: `T_σ v = r_σ + K_σ v` with `K_σ = (1 − σ)K` positive. -/
theorem isAdditive : BanachLattice.IsAdditive id F.adp F.rσ F.Kσ :=
  ⟨fun σ v hv => BM.mulCLM_isPositive (fun x => by simp only [cont]; split_ifs <;> norm_num) _
    (F.K_isPositive v hv), fun _ _ => rfl⟩

/-- `K_σ ≤ K` on the positive cone. -/
theorem Kσ_le_K (σ : FirmPolicy X) (h : BM X) (hh : 0 ≤ h) : F.Kσ σ h ≤ F.K h := fun x => by
  change (cont σ).toFun x * (F.K h).toFun x ≤ (F.K h).toFun x
  have := F.K_isPositive h hh x
  simp only [cont]
  split_ifs
  · simpa using this
  · simp

/-- **Proposition 4.2.2** (p. 136), **Exercise 4.2.1**: under Assumption 4.2.1, `ρ(K) < 1`, the
fundamental optimality properties hold for the firm ADP with state-dependent discounting, VFI
converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_2 (hρ : BanachLattice.specRad F.K < 1) :
    ∃ hw : F.adp.WellPosed, F.adp.FundamentalOptimality hw ∧ ∃ vstar,
      F.adp.VFIGeometric univ vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧ F.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 F.K_isPositive hρ
  have hsr : F.adp.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adp_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8 isIsoOrderEmbedding_id
    F.adp F.isAdditive hD F.Kσ_le_K hsr univ_nonempty
  have hgs : F.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 isIsoOrderEmbedding_id ⟨hD, fun v w =>
      (F.isAdditive.abs_sub σ v w).trans (F.Kσ_le_K σ _ (abs_nonneg _))⟩).1
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adp_regular hgs
    ((F.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adp_regular⟩

end FirmSD

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Structural estimation with state-dependent discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.3.2 (pp. 143–144).

`X` and `A` are finite and nonempty, `G = X × A`, and the Bellman equation is (4.23),
`g(x, a) = ∑_{x'} max_{a'} [r(x', a') + β(x')g(x', a')] P(x, a, x')`, with a state-dependent
discount factor `β(x) ≥ 0`.

* `ℝⁿ` with the supremum norm is a Banach lattice (its norm is a lattice norm).
* The policy operators `T̂_σ g = r̂_σ + K_σ g` with `K_σ` as in (4.25); the greedy policies (4.24),
  regularity, and the Bellman operator.
* **Proposition 4.2.5**: if `ρ(K_σ) < 1` for every `σ`, the fundamental optimality properties hold,
  VFI, OPI and HPI converge, and HPI converges in finitely many steps (Theorems 4.1.7 and 2.2.6).
* With a constant discount `β(x) ≤ b < 1`, `ρ(K_σ) ≤ b < 1` always holds.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnBanachSpace

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

/-- The finite structural estimation model of §4.2.3.2. -/
structure FiniteSE (X A : Type*) [Fintype X] [Fintype A] where
  /-- the reward -/
  r : X × A → ℝ
  /-- the state-dependent discount factor -/
  βf : X → ℝ
  βf_nonneg : ∀ x, 0 ≤ βf x
  /-- the transition probabilities from `G` to `X` -/
  P : X × A → X → ℝ
  P_nonneg : ∀ p x', 0 ≤ P p x'
  P_sum : ∀ p, ∑ x', P p x' = 1

namespace FiniteSE

variable {X A : Type*} [Fintype X] [Fintype A] (M : FiniteSE X A)

/-- `K_σ` (4.25): `(K_σ g)(x, a) = ∑_{x'} β(x')g(x', σ(x'))P(x, a, x')`, linear. -/
def Klin (σ : X → A) : (X × A → ℝ) →ₗ[ℝ] (X × A → ℝ) where
  toFun g p := ∑ x', M.βf x' * g (x', σ x') * M.P p x'
  map_add' g h := funext fun p => by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x' _ => by ring
  map_smul' c g := funext fun p => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring

/-- `K_σ` as a bounded linear operator. -/
noncomputable def K (σ : X → A) : (X × A → ℝ) →L[ℝ] (X × A → ℝ) :=
  LinearMap.toContinuousLinearMap (M.Klin σ)

theorem K_apply (σ : X → A) (g : X × A → ℝ) (p : X × A) :
    M.K σ g p = ∑ x', M.βf x' * g (x', σ x') * M.P p x' := rfl

theorem K_isPositive (σ : X → A) : BanachLattice.IsPositiveOp (M.K σ) := fun g hg p => by
  rw [M.K_apply]
  exact Finset.sum_nonneg fun x' _ =>
    mul_nonneg (mul_nonneg (M.βf_nonneg x') (hg _)) (M.P_nonneg p x')

/-- `r̂_σ(x, a) = ∑_{x'} r(x', σ(x'))P(x, a, x')`. -/
def rhat (σ : X → A) : X × A → ℝ := fun p => ∑ x', M.r (x', σ x') * M.P p x'

/-- The policy operators `T̂_σ g = r̂_σ + K_σ g`. -/
noncomputable def adp [Nonempty A] : ADP (X × A → ℝ) (X → A) where
  T σ g := M.rhat σ + M.K σ g
  mono σ _ _ h := add_le_add le_rfl ((M.K_isPositive σ).mono h)
  nonempty := ⟨fun _ => Classical.arbitrary A⟩

theorem adp_T_apply [Nonempty A] (σ : X → A) (g : X × A → ℝ) (p : X × A) :
    M.adp.T σ g p = ∑ x', (M.r (x', σ x') + M.βf x' * g (x', σ x')) * M.P p x' := by
  change M.rhat σ p + M.K σ g p = _
  rw [rhat, M.K_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- (4.24): a policy maximizing `r(x, ·) + β(x)g(x, ·)` at every state is `g`-greedy. -/
theorem isGreedy_of_argmax [Nonempty A] (g : X × A → ℝ) (σ : X → A)
    (hσ : ∀ x a, M.r (x, a) + M.βf x * g (x, a) ≤ M.r (x, σ x) + M.βf x * g (x, σ x)) :
    M.adp.IsGreedy g σ := fun τ p => by
  rw [M.adp_T_apply, M.adp_T_apply]
  exact Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hσ x' (τ x')) (M.P_nonneg p x')

theorem exists_argmax [Nonempty A] (g : X × A → ℝ) :
    ∃ σ : X → A, ∀ x a, M.r (x, a) + M.βf x * g (x, a) ≤ M.r (x, σ x) + M.βf x * g (x, σ x) := by
  choose σ _ hσ using fun x => Finset.exists_max_image Finset.univ
    (fun a => M.r (x, a) + M.βf x * g (x, a)) Finset.univ_nonempty
  exact ⟨σ, fun x a => hσ x a (Finset.mem_univ a)⟩

/-- §4.2.3.2: the ADP `(ℝ^G, 𝕋̂_SE)` is regular. -/
theorem adp_regular [Nonempty A] : M.adp.Regular := fun g => by
  obtain ⟨σ, hσ⟩ := M.exists_argmax g
  exact ⟨σ, M.isGreedy_of_argmax g σ hσ⟩

/-- (4.23): the Bellman operator is
`(T̂g)(x, a) = ∑_{x'} max_{a'} [r(x', a') + β(x')g(x', a')] P(x, a, x')`. -/
theorem adp_bellman_apply [Nonempty A] (g : X × A → ℝ) (p : X × A) :
    M.adp.bellman g p = ∑ x', (Finset.univ.sup' Finset.univ_nonempty fun a' =>
      M.r (x', a') + M.βf x' * g (x', a')) * M.P p x' := by
  obtain ⟨σ, hσ⟩ := M.exists_argmax g
  have hg := M.adp.isGreedy_greedy (M.adp_regular g)
  have heq : M.adp.bellman g = M.adp.T σ g :=
    le_antisymm (M.isGreedy_of_argmax g σ hσ _) (hg σ)
  rw [heq, M.adp_T_apply]
  refine Finset.sum_congr rfl fun x' _ => ?_
  congr 1
  exact le_antisymm (Finset.le_sup' (fun a' => M.r (x', a') + M.βf x' * g (x', a'))
    (Finset.mem_univ _)) (Finset.sup'_le _ _ fun a' _ => hσ x' a')

theorem isIsoOrderEmbedding_id :
    BanachLattice.IsIsoOrderEmbedding (id : (X × A → ℝ) → (X × A → ℝ)) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

theorem isAdditive [Nonempty A] : BanachLattice.IsAdditive id M.adp M.rhat M.K :=
  ⟨M.K_isPositive, fun _ _ => rfl⟩

/-- **Proposition 4.2.5** (p. 144): if `ρ(K_σ) < 1` for every `σ`, the fundamental optimality
properties hold for `(ℝ^G, 𝕋̂_SE)`, OPI, VFI and HPI all converge, and HPI converges in finitely
many steps. -/
theorem proposition_4_2_5 [Nonempty A] (hρ : ∀ σ, BanachLattice.specRad (M.K σ) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard hw g)^[n] v) := by
  have hfin : M.adp.IsFinite := finite_range _
  obtain ⟨hw, h12⟩ := BanachLattice.theorem_4_1_7 isIsoOrderEmbedding_id M.adp M.adp_regular
    hfin M.isAdditive hρ
  have hgs : M.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 isIsoOrderEmbedding_id
      ⟨BanachLattice.example_4_1_1 (M.K_isPositive σ) (hρ σ), M.isAdditive.abs_sub σ⟩).1
  exact ⟨hw, h12.1, h12.2,
    (ADP.fundamentalOptimality_of_finite hgs.isOrderStable M.adp_regular hfin).2⟩

/-- With `β(x) ≤ b < 1` everywhere, `‖K_σ‖ ≤ b`, so `ρ(K_σ) ≤ b < 1`: the condition of
Proposition 4.2.5 generalizes a constant discount factor below one. -/
theorem specRad_lt_one_of_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hβ : ∀ x, M.βf x ≤ b)
    (σ : X → A) : BanachLattice.specRad (M.K σ) < 1 := by
  refine ((BanachLattice.specRad_le_norm _).trans ?_).trans_lt hb1
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun g => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb0 (norm_nonneg g))).2 fun p => ?_
  rw [Real.norm_eq_abs, M.K_apply]
  calc |∑ x', M.βf x' * g (x', σ x') * M.P p x'|
      ≤ ∑ x', |M.βf x' * g (x', σ x') * M.P p x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', b * ‖g‖ * M.P p x' := Finset.sum_le_sum fun x' _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (M.βf_nonneg x'), abs_of_nonneg (M.P_nonneg p x')]
        refine mul_le_mul_of_nonneg_right (mul_le_mul (hβ x') ?_ (abs_nonneg _) hb0)
          (M.P_nonneg p x')
        exact (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm g _)
    _ = b * ‖g‖ := by rw [← Finset.mul_sum, M.P_sum, mul_one]

end FiniteSE

end SargentStachurski.ADPsOnBanachSpace

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

namespace SargentStachurski.ADPsOnBanachSpace

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

end SargentStachurski.ADPsOnBanachSpace

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firm valuation with unbounded rewards and a real option problem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.1.2 and §4.2.2 (pp. 134–140).

Both problems live in `L¹(ψ)` for a stationary distribution `ψ` of the state kernel `P`, with the
`ψ`-a.e. order.

* §4.2.1.2: the firm ADP `(L¹(ψ), 𝕋_FV)` with `T_σ v = σs + (1 − σ)(π + βPv)` and `π ∈ L¹(ψ)`. It is
  regular, `K_σ = (1 − σ)βP ≤ βP` and `‖βP‖ ≤ β < 1`, so Theorem 4.1.8 gives the claims of
  Proposition 4.2.1.
* §4.2.2: the real option ADP `(L¹(φ), 𝕋_RO)` with `T_σ v = −c + K(σq + (1 − σ)v)` (4.16),
  `(Kv)(x) = β(x) ∫ v(x')P(x, dx')` and `q = (I − K)⁻¹π`. **Exercise 4.2.2** (well-posedness and
  the lifetime values), **Exercise 4.2.3** (the greedy policy `𝟙{q ≥ v}`), the Bellman equation
  (4.18)–(4.19) and **Proposition 4.2.3** (via Theorem 4.1.8).
* (4.17) and the proof of Proposition 4.2.3 write the constant term as `−c + K_σ q`; it is
  `−c + K(σq)` (`RealOption.eq_4_17_misprint`).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnBanachSpace

variable {X : Type*} [MeasurableSpace X]

/-! ### Indicator functions of policies -/

/-- `σ` as a `{0, 1}`-valued function. -/
def polInd (σ : FirmPolicy X) (x : X) : ℝ := if σ.1 x then 1 else 0

/-- `1 − σ`. -/
def polCont (σ : FirmPolicy X) (x : X) : ℝ := if σ.1 x then 0 else 1

theorem measurable_polInd (σ : FirmPolicy X) : Measurable (polInd σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem measurable_polCont (σ : FirmPolicy X) : Measurable (polCont σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem abs_polInd_le (σ : FirmPolicy X) (x : X) : |polInd σ x| ≤ 1 := by
  simp only [polInd]; split_ifs <;> simp

theorem abs_polCont_le (σ : FirmPolicy X) (x : X) : |polCont σ x| ≤ 1 := by
  simp only [polCont]; split_ifs <;> simp

theorem polCont_nonneg (σ : FirmPolicy X) (x : X) : 0 ≤ polCont σ x := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polCont_le_one (σ : FirmPolicy X) (x : X) : polCont σ x ≤ 1 := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polInd_nonneg (σ : FirmPolicy X) (x : X) : 0 ≤ polInd σ x := by
  simp only [polInd]; split_ifs <;> norm_num

/-- `id` is an isometric order embedding of `L¹(ψ)` into itself. -/
theorem isIsoOrderEmbedding_id_L1 (ψ : Measure X) :
    BanachLattice.IsIsoOrderEmbedding (id : Lp ℝ 1 ψ → Lp ℝ 1 ψ) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

/-! ### Firm valuation in `L¹(ψ)` -/

/-- The firm problem with an integrable profit function (§4.2.1.2). -/
structure FirmL1 (X : Type*) [MeasurableSpace X] where
  /-- the state kernel -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- a stationary distribution -/
  ψ : Measure X
  isProb : IsProbabilityMeasure ψ
  stationary : ψ.bind P = ψ
  /-- the profit function `π ∈ L¹(ψ)` -/
  profit : Lp ℝ 1 ψ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the sale price -/
  s : ℝ

namespace FirmL1

variable (F : FirmL1 X)

/-- The Markov operator on `L¹(ψ)`. -/
noncomputable def Pop : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ :=
  have := F.isMarkov
  L1.markovCLM F.stationary

/-- The constant `s` as an element of `L¹(ψ)`. -/
noncomputable def sconst : Lp ℝ 1 F.ψ :=
  have := F.isProb
  (memLp_const F.s).toLp _

/-- The discount operator `D = βP`. -/
noncomputable def D : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ := F.β • F.Pop

/-- `r_σ = σs + (1 − σ)π`. -/
noncomputable def rσ (σ : FirmPolicy X) : Lp ℝ 1 F.ψ :=
  L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst +
    L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit

/-- `K_σ = (1 − σ)βP` (4.12). -/
noncomputable def Kσ (σ : FirmPolicy X) : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ :=
  L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) ∘L F.D

theorem D_isPositive : BanachLattice.IsPositiveOp F.D := fun v hv => by
  have := F.isMarkov
  have h := L1.markovCLM_isPositive F.stationary v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul F.β (F.Pop v), h] with x h1 h2
  change 0 ≤ (F.β • F.Pop v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg F.β_nonneg h2

theorem Kσ_isPositive (σ : FirmPolicy X) : BanachLattice.IsPositiveOp (F.Kσ σ) := fun v hv =>
  L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ) _
    (F.D_isPositive v hv)

theorem Kσ_le_D (σ : FirmPolicy X) (h : Lp ℝ 1 F.ψ) (hh : 0 ≤ h) : F.Kσ σ h ≤ F.D h :=
  L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ) (polCont_le_one σ)
    (F.D_isPositive h hh)

/-- `ρ(βP) ≤ ‖βP‖ ≤ β < 1` (Lemma A.5.32 gives `ρ(βP) = β`). -/
theorem specRad_D_lt_one : BanachLattice.specRad F.D < 1 := by
  have hD : ‖F.D‖ ≤ F.β := ContinuousLinearMap.opNorm_le_bound _ F.β_nonneg fun v => by
    change ‖F.β • F.Pop v‖ ≤ F.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg F.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((F.Pop.le_opNorm v).trans ?_) F.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le F.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)
  exact ((BanachLattice.specRad_le_norm _).trans hD).trans_lt F.β_lt_one

/-- The firm ADP `(L¹(ψ), 𝕋_FV)`. -/
noncomputable def adp : ADP (Lp ℝ 1 F.ψ) (FirmPolicy X) where
  T σ v := F.rσ σ + F.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl ((F.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- `T_σ v = σs + (1 − σ)(π + βPv)` almost everywhere. -/
theorem T_coeFn (σ : FirmPolicy X) (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.T σ v) =ᵐ[F.ψ] fun x => if σ.1 x then F.s else F.profit x + F.β * F.Pop v x := by
  have := F.isProb
  filter_upwards [Lp.coeFn_add (F.rσ σ) (F.Kσ σ v),
    Lp.coeFn_add (L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst)
      (L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) F.sconst,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) F.profit,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) (F.D v),
    Lp.coeFn_smul F.β (F.Pop v), (memLp_const (μ := F.ψ) F.s).coeFn_toLp]
    with x h1 h2 h3 h4 h5 h6 h7
  change (F.rσ σ + F.Kσ σ v) x = _
  rw [h1, Pi.add_apply]
  change (L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst +
    L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit) x +
    (L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) (F.D v)) x = _
  rw [h2, Pi.add_apply, h3, h4, h5]
  change polInd σ x * F.sconst x + polCont σ x * F.profit x + polCont σ x * (F.β • F.Pop v) x = _
  rw [h6, Pi.smul_apply, smul_eq_mul]
  change polInd σ x * ((memLp_const (μ := F.ψ) F.s).toLp _) x + _ + _ = _
  rw [h7]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- The `v`-greedy policy (4.11): sell when `s ≥ π + βPv`. -/
noncomputable def sell (v : Lp ℝ 1 F.ψ) : FirmPolicy X :=
  ⟨fun x => decide (F.profit x + F.β * F.Pop v x ≤ F.s), measurable_to_bool (by
    have : (fun x => decide (F.profit x + F.β * F.Pop v x ≤ F.s)) ⁻¹' {true} =
        {x | F.profit x + F.β * F.Pop v x ≤ F.s} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le ((Lp.stronglyMeasurable _).measurable.add
      (measurable_const.mul (Lp.stronglyMeasurable _).measurable)) measurable_const)⟩

theorem T_sell_coeFn (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.T (F.sell v) v) =ᵐ[F.ψ] fun x => max F.s (F.profit x + F.β * F.Pop v x) := by
  filter_upwards [F.T_coeFn (F.sell v) v] with x hx
  rw [hx]
  by_cases h : F.profit x + F.β * F.Pop v x ≤ F.s
  · simp [sell, h]
  · simp only [sell, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

theorem sell_isGreedy (v : Lp ℝ 1 F.ψ) : F.adp.IsGreedy v (F.sell v) := fun τ => by
  rw [← Lp.coeFn_le]
  filter_upwards [F.T_coeFn τ v, F.T_sell_coeFn v] with x h1 h2
  rw [h1, h2]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem adp_regular : F.adp.Regular := fun v => ⟨_, F.sell_isGreedy v⟩

/-- (4.13) in `L¹(ψ)`: the Bellman operator is `Tv = s ∨ (π + βPv)` almost everywhere. -/
theorem adp_bellman_coeFn (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.bellman v) =ᵐ[F.ψ] fun x => max F.s (F.profit x + F.β * F.Pop v x) := by
  have heq : F.adp.bellman v = F.adp.T (F.sell v) v :=
    le_antisymm (F.sell_isGreedy v _) (F.adp.isGreedy_greedy (F.adp_regular v) _)
  rw [heq]
  exact F.T_sell_coeFn v

theorem isAdditive : BanachLattice.IsAdditive id F.adp F.rσ F.Kσ :=
  ⟨F.Kσ_isPositive, fun _ _ => rfl⟩

/-- §4.2.1.2 (p. 135): the claims of Proposition 4.2.1 extend to `(L¹(ψ), 𝕋_FV)`, by
Theorem 4.1.8: the fundamental optimality properties hold, VFI converges (geometrically), and OPI
and HPI converge. -/
theorem optimality :
    ∃ hw : F.adp.WellPosed, F.adp.FundamentalOptimality hw ∧ ∃ vstar,
      F.adp.VFIGeometric univ vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧ F.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 F.D_isPositive F.specRad_D_lt_one
  have hsr : F.adp.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adp_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 F.ψ) F.adp F.isAdditive hD F.Kσ_le_D hsr univ_nonempty
  have hgs : F.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 F.ψ) ⟨hD, fun v w =>
      (F.isAdditive.abs_sub σ v w).trans (F.Kσ_le_D σ _ (abs_nonneg _))⟩).1
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adp_regular hgs
    ((F.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adp_regular⟩

end FirmL1

/-! ### A real option problem -/

/-- `(v ↦ a + Kv)ᵏ u − (v ↦ a + Kv)ᵏ w = Kᵏ(u − w)`. -/
theorem iterate_affine_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E)
    (K : E →L[ℝ] E) (k : ℕ) (u w : E) :
    (fun v => a + K v)^[k] u - (fun v => a + K v)^[k] w = (K ^ k) (u - w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', add_sub_add_left_eq_sub, ← map_sub, ih,
      pow_succ']
    rfl

/-- The real option problem (§4.2.2): Assumption 4.2.2, with a stationary distribution `φ`,
integrable `c` and `π`, and a bounded nonnegative measurable discount function `β`. -/
structure RealOption (X : Type*) [MeasurableSpace X] where
  /-- the state kernel -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the stationary distribution -/
  φ : Measure X
  isProb : IsProbabilityMeasure φ
  stationary : φ.bind P = φ
  /-- the development cost -/
  c : Lp ℝ 1 φ
  /-- the post-launch profit -/
  profit : Lp ℝ 1 φ
  /-- the discount function -/
  βf : X → ℝ
  βf_meas : Measurable βf
  βf_nonneg : ∀ x, 0 ≤ βf x
  /-- a bound on the discount function -/
  N : ℝ
  βf_le : ∀ x, βf x ≤ N

namespace RealOption

variable (R : RealOption X)

theorem abs_βf_le (x : X) : |R.βf x| ≤ R.N := by
  rw [abs_of_nonneg (R.βf_nonneg x)]
  exact R.βf_le x

/-- The discount operator `(Kv)(x) = β(x) ∫ v(x')P(x, dx')` on `L¹(φ)`. -/
noncomputable def K : Lp ℝ 1 R.φ →L[ℝ] Lp ℝ 1 R.φ :=
  L1.mulCLM R.φ R.βf_meas R.abs_βf_le ∘L L1.markovCLM R.stationary

theorem K_isPositive : BanachLattice.IsPositiveOp R.K := fun v hv =>
  L1.mulCLM_isPositive R.βf_meas R.abs_βf_le R.βf_nonneg _
    (L1.markovCLM_isPositive R.stationary v hv)

/-- Under Assumption 4.2.3, `q = π + Kq` has a solution, `q = (I − K)⁻¹π`. -/
theorem exists_q (hρ : BanachLattice.specRad R.K < 1) : ∃ q, q = R.profit + R.K q := by
  obtain ⟨k, hk, hlt⟩ := BanachLattice.exercise_A_4_2 hρ
  obtain ⟨-, q, hq, -⟩ := theorem_4_1_1 (S := fun v => R.profit + R.K v) hk (norm_nonneg _) hlt
    fun u w => by
      rw [dist_eq_norm, dist_eq_norm, iterate_affine_sub]
      exact (R.K ^ k).le_opNorm _
  exact ⟨q, hq.symm⟩

/-- The value of launching, `q = (I − K)⁻¹π`. -/
noncomputable def q (hρ : BanachLattice.specRad R.K < 1) : Lp ℝ 1 R.φ :=
  (R.exists_q hρ).choose

theorem q_eq (hρ : BanachLattice.specRad R.K < 1) : R.q hρ = R.profit + R.K (R.q hρ) :=
  (R.exists_q hρ).choose_spec

variable (hρ : BanachLattice.specRad R.K < 1)

/-- The constant term `r_σ = −c + K(σq)`. -/
noncomputable def rσ (σ : FirmPolicy X) : Lp ℝ 1 R.φ :=
  -R.c + R.K (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ))

/-- `K_σ f = K((1 − σ)f)`, `(K_σ f)(x) = β(x) ∫ f(x')(1 − σ(x'))P(x, dx')`. -/
noncomputable def Kσ (σ : FirmPolicy X) : Lp ℝ 1 R.φ →L[ℝ] Lp ℝ 1 R.φ :=
  R.K ∘L L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ)

/-- The real option ADP `(L¹(φ), 𝕋_RO)`. -/
noncomputable def adp : ADP (Lp ℝ 1 R.φ) (FirmPolicy X) where
  T σ v := R.rσ hρ σ + R.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl (R.K_isPositive.mono
    ((L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ)).mono h))
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (4.16): `T_σ v = −c + K(σq + (1 − σ)v)`. -/
theorem T_eq (σ : FirmPolicy X) (v : Lp ℝ 1 R.φ) :
    (R.adp hρ).T σ v = -R.c + R.K (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v) := by
  change R.rσ hρ σ + R.Kσ σ v = _
  rw [rσ, Kσ, map_add, ContinuousLinearMap.comp_apply, add_assoc]

theorem Kσ_isPositive (σ : FirmPolicy X) : BanachLattice.IsPositiveOp (R.Kσ σ) := fun v hv =>
  R.K_isPositive _ (L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ)
    (polCont_nonneg σ) v hv)

theorem Kσ_le_K (σ : FirmPolicy X) (h : Lp ℝ 1 R.φ) (hh : 0 ≤ h) : R.Kσ σ h ≤ R.K h :=
  R.K_isPositive.mono (L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ)
    (polCont_le_one σ) hh)

theorem isAdditive : BanachLattice.IsAdditive id (R.adp hρ) (R.rσ hρ) R.Kσ :=
  ⟨R.Kσ_isPositive, fun _ _ => rfl⟩

include hρ in
theorem isDiscountOperator : BanachLattice.IsDiscountOperator (R.K : Lp ℝ 1 R.φ → Lp ℝ 1 R.φ) :=
  BanachLattice.example_4_1_1 R.K_isPositive hρ

theorem isGloballyStable : (R.adp hρ).IsGloballyStable := fun σ =>
  (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 R.φ) ⟨R.isDiscountOperator hρ,
    fun v w => ((R.isAdditive hρ).abs_sub σ v w).trans (R.Kσ_le_K σ _ (abs_nonneg _))⟩).1

/-- `T_σⁿ 0 = ∑_{t < n} K_σᵗ r_σ`. -/
theorem iterate_T_zero (σ : FirmPolicy X) (n : ℕ) :
    ((R.adp hρ).T σ)^[n] 0 = ∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, Finset.sum_range_succ']
    change R.rσ hρ σ + R.Kσ σ (∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ)) = _
    rw [map_sum, add_comm]
    simp only [pow_succ', pow_zero]
    rfl

/-- **Exercise 4.2.2** (p. 139): `(L¹(φ), 𝕋_RO)` is well-posed, and the lifetime value of `σ` is
`v_σ = (I − K_σ)⁻¹(−c + K(σq)) = ∑ₜ K_σᵗ(−c + K(σq))`, the infinite sum being the limit of its
partial sums. -/
theorem exercise_4_2_2 :
    ∃ hw : (R.adp hρ).WellPosed, ∀ σ, Tendsto
      (fun n => ∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ)) atTop
      (𝓝 ((R.adp hρ).vσ hw σ)) := by
  refine ⟨(R.isGloballyStable hρ).wellPosed, fun σ => ?_⟩
  have := (R.isGloballyStable hρ).tendsto_vσ σ 0
  simpa only [R.iterate_T_zero hρ] using this

/-- **(4.17) is misprinted.** For the policy that launches everywhere, `K_σ = 0`, so the book's
`v_σ = (I − K_σ)⁻¹(−c + K_σ q)` would be `−c`. But `T_σ(−c) = −c + Kq`, so `−c` is the lifetime
value only when `Kq = 0`. The correct constant term is `−c + K(σq)` (`exercise_4_2_2`). -/
theorem eq_4_17_misprint (σ : FirmPolicy X) (hσ : ∀ x, σ.1 x = true) :
    R.Kσ σ = 0 ∧ ((R.adp hρ).T σ (-R.c + R.Kσ σ (R.q hρ)) = -R.c + R.Kσ σ (R.q hρ) ↔
      R.K (R.q hρ) = 0) := by
  have hcont : L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) = 0 :=
    ContinuousLinearMap.ext fun f => Lp.ext (by
      filter_upwards [L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) f,
        Lp.coeFn_zero ℝ 1 R.φ] with x h1 h2
      rw [h1, _root_.zero_apply, h2]
      simp [polCont, hσ x])
  have hind : L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) = R.q hρ :=
    Lp.ext (by
      filter_upwards [L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ)] with x h1
      rw [h1]
      simp [polInd, hσ x])
  have hKσ : R.Kσ σ = 0 := by rw [Kσ, hcont, ContinuousLinearMap.comp_zero]
  refine ⟨hKσ, ?_⟩
  rw [hKσ, _root_.zero_apply, add_zero]
  change R.rσ hρ σ + R.Kσ σ (-R.c) = -R.c ↔ _
  rw [hKσ, _root_.zero_apply, add_zero, rσ, hind]
  constructor
  · intro h
    simpa using h
  · intro h
    rw [h, add_zero]

/-- The launch policy `𝟙{q ≥ v}`. -/
noncomputable def launch (v : Lp ℝ 1 R.φ) : FirmPolicy X :=
  ⟨fun x => decide (v x ≤ R.q hρ x), measurable_to_bool (by
    have : (fun x => decide (v x ≤ R.q hρ x)) ⁻¹' {true} = {x | v x ≤ R.q hρ x} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le (Lp.stronglyMeasurable _).measurable
      (Lp.stronglyMeasurable _).measurable)⟩

/-- `σq + (1 − σ)v` is `q` where `σ` launches and `v` elsewhere. -/
theorem mix_coeFn (σ : FirmPolicy X) (v : Lp ℝ 1 R.φ) :
    ⇑(L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v) =ᵐ[R.φ]
        fun x => if σ.1 x then R.q hρ x else v x := by
  filter_upwards [Lp.coeFn_add (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ))
      (L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ),
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) v] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- For the launch policy, `σq + (1 − σ)v = q ∨ v`. -/
theorem mix_launch (v : Lp ℝ 1 R.φ) :
    L1.mulCLM R.φ (measurable_polInd (R.launch hρ v)) (abs_polInd_le _) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont (R.launch hρ v)) (abs_polCont_le _) v = R.q hρ ⊔ v :=
  Lp.ext (by
    filter_upwards [R.mix_coeFn hρ (R.launch hρ v) v, Lp.coeFn_sup (R.q hρ) v] with x h1 h2
    rw [h1, h2, Pi.sup_apply]
    by_cases h : v x ≤ R.q hρ x
    · simp [launch, h]
    · simp only [launch, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (max_eq_right (le_of_not_ge h)).symm)

/-- **Exercise 4.2.3** (p. 139): for `v ∈ L¹(φ)`, the policy `σ = 𝟙{q ≥ v}` is `v`-greedy. -/
theorem exercise_4_2_3 (v : Lp ℝ 1 R.φ) : (R.adp hρ).IsGreedy v (R.launch hρ v) := fun τ => by
  rw [R.T_eq, R.T_eq, R.mix_launch]
  refine add_le_add le_rfl (R.K_isPositive.mono ?_)
  rw [← Lp.coeFn_le]
  filter_upwards [R.mix_coeFn hρ τ v, Lp.coeFn_sup (R.q hρ) v] with x h1 h2
  rw [h1, h2, Pi.sup_apply]
  split_ifs
  · exact le_sup_left
  · exact le_sup_right

theorem adp_regular : (R.adp hρ).Regular := fun v => ⟨_, R.exercise_4_2_3 hρ v⟩

/-- (4.18)–(4.19): the Bellman operator is `Tv = −c + K(q ∨ v)`. -/
theorem adp_bellman (v : Lp ℝ 1 R.φ) : (R.adp hρ).bellman v = -R.c + R.K (R.q hρ ⊔ v) := by
  have heq : (R.adp hρ).bellman v = (R.adp hρ).T (R.launch hρ v) v :=
    le_antisymm (R.exercise_4_2_3 hρ v _) ((R.adp hρ).isGreedy_greedy (R.adp_regular hρ v) _)
  rw [heq, R.T_eq, R.mix_launch]

/-- **Proposition 4.2.3** (p. 140): under Assumptions 4.2.2 and 4.2.3, the fundamental optimality
properties hold for `(L¹(φ), 𝕋_RO)`, VFI converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_3 :
    ∃ hw : (R.adp hρ).WellPosed, (R.adp hρ).FundamentalOptimality hw ∧ ∃ vstar,
      (R.adp hρ).VFIGeometric univ vstar ∧ (R.adp hρ).VFIConverges vstar ∧
        ∀ g, (R.adp hρ).IsSelector g → (R.adp hρ).OPIConverges g vstar ∧
          (R.adp hρ).HPIConverges hw g vstar := by
  have hsr : (R.adp hρ).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => R.adp_regular hρ v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 R.φ) (R.adp hρ) (R.isAdditive hρ) (R.isDiscountOperator hρ)
    R.Kσ_le_K hsr univ_nonempty
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 (R.adp_regular hρ) (R.isGloballyStable hρ)
    (((R.adp hρ).solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv (R.adp_regular hρ)⟩

end RealOption

end SargentStachurski.ADPsOnBanachSpace

set_option linter.style.longLine false
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.rowsum
#print axioms SargentStachurski.ADPsOnBanachSpace.IsDistribution
#print axioms SargentStachurski.ADPsOnBanachSpace.IsDistribution.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.IsDistribution.nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.IsDistribution.sum_eq_one
#print axioms SargentStachurski.ADPsOnBanachSpace.mulVec_apply_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.mul
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.pow
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.mulVec_const
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.ADPsOnBanachSpace.GloballyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.iterate_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.ADPsOnBanachSpace.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.ADPsOnBanachSpace.fixedPt_le_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.le_fixedPt_of_le_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.isContractionOn_of_blackwell
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsBdd
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupContraction
#print axioms SargentStachurski.ADPsOnBanachSpace.IsUniformlyClosed
#print axioms SargentStachurski.ADPsOnBanachSpace.isBdd_const
#print axioms SargentStachurski.ADPsOnBanachSpace.IsBdd.sub
#print axioms SargentStachurski.ADPsOnBanachSpace.IsBdd.add
#print axioms SargentStachurski.ADPsOnBanachSpace.IsBdd.nonneg_bound
#print axioms SargentStachurski.ADPsOnBanachSpace.IsBdd.exists_dist
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupContraction.iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupContraction.exists_limit
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupContraction.globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.le_of_le_map_of_tendsto
#print axioms SargentStachurski.ADPsOnBanachSpace.le_of_map_le_of_tendsto
#print axioms SargentStachurski.ADPsOnBanachSpace.bX
#print axioms SargentStachurski.ADPsOnBanachSpace.isUniformlyClosed_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.const_mem_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_max_sub_max_le
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.V
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.T
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.β
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.β_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.β_lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.nonempty
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bdd
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.closed
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.mono
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.exists_greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.T_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.eq_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.le_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.IsGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.nonempty_policy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.T_le_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vstar_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.bellman_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.eq_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.IsOptimal
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.optimality
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.hpiPolicy
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.hpi_terminates
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.opi
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.opi_step
#print axioms SargentStachurski.ADPsOnBanachSpace.ContractingDP.tendsto_opi
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp
#print axioms SargentStachurski.ADPsOnBanachSpace.integrable_of_mem_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.measurable_markovOp
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_markovOp_le
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_mem_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_const
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_add
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_sub
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_smul
#print axioms SargentStachurski.ADPsOnBanachSpace.markovOp_sub_const
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_markovOp_sub_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.add
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.smul
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.mono
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.abs_le
#print axioms SargentStachurski.ADPsOnBanachSpace.isMarkovLike_markovOp
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.sub
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.abs_sub_le
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.iterate_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.IsMarkovLike.abs_iterate_le
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_iterate_zero
#print axioms SargentStachurski.ADPsOnBanachSpace.affineOp_hasSum
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.P
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.isMarkov
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.profit
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.profit_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.β
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.β_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.β_lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.s
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmPolicy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.isMarkovLike_P
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.valOp
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.valOp_mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.valOp_contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.valuation_globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.value
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.value_mem
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.value_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.value_hasSum
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_mapsTo
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.measurable_sellPolicy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_le_max
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.Tσ_sellPolicy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.toDP
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.bellman_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.IsGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.isGreedy_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.isGreedy_iff_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.abs_vσ_le
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.theorem_1_1_1
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.sellPolicy_optimal
#print axioms SargentStachurski.ADPsOnBanachSpace.OrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.IncreasesTo
#print axioms SargentStachurski.ADPsOnBanachSpace.DecreasesTo
#print axioms SargentStachurski.ADPsOnBanachSpace.StronglyOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.orderStable_of_up_down
#print axioms SargentStachurski.ADPsOnBanachSpace.StronglyOrderStable.orderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.dualMap
#print axioms SargentStachurski.ADPsOnBanachSpace.orderStable_dual_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.dualMap_iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete.exists_least
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.ADPsOnBanachSpace.ChainComplete.orderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.chainComplete_Icc
#print axioms SargentStachurski.ADPsOnBanachSpace.CountablyDedekindComplete
#print axioms SargentStachurski.ADPsOnBanachSpace.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.ADPsOnBanachSpace.CountablyDedekindComplete.dual
#print axioms SargentStachurski.ADPsOnBanachSpace.OrderContinuous
#print axioms SargentStachurski.ADPsOnBanachSpace.OrderContinuous.monotone
#print axioms SargentStachurski.ADPsOnBanachSpace.isLUB_range_succ_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.tarski_kantorovich
#print axioms SargentStachurski.ADPsOnBanachSpace.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.T
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.mono
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.nonempty
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VG
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.WellPosed
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsFinite
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.Regular
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsBellmanValue
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.SolvesBellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.regular_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isGreedy_greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.T_le_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isGreedy_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.solvesBellman_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VU
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VSig
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.T_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.eq_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VSig_eq_range
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOptimal
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsValueFunction
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.BellmanPrinciple
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.FundamentalOptimality
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isOptimal_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.exists_solves_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsSelector
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.howard
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.opt
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsSelector.T_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.mem_VU_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.iterate_mono_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman_le_opt
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.chain_2_9
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.mapsTo_VU
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman_le_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VFIConverges
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.OPIConverges
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.HPIConverges
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.opt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.OPIConverges.vfi
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.iterates_le_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VU_nonempty
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.OrderBounded
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsOrderContinuous
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.le_of_orderBounded
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.convergence_of_dedekind
#print axioms SargentStachurski.ADPsOnBanachSpace.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGloballyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.theorem_3_1_2
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.corollary_3_1_3
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.theorem_3_1_4
#print axioms SargentStachurski.ADPsOnBanachSpace.IsSupNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.IsInfNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.isInfNonexpansive_iff
#print axioms SargentStachurski.ADPsOnBanachSpace.isSupNonexpansive_real
#print axioms SargentStachurski.ADPsOnBanachSpace.isSupNonexpansive_pi
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.lemma_A_5_21
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.IsSemiRegular
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.VFIGeometric
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.theorem_3_1_5
#print axioms SargentStachurski.ADPsOnBanachSpace.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.ADPsOnBanachSpace.BM
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.toFun
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.measurable'
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.bdd'
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.ext
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.bddAbove
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.const
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.toFun_injective
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.zero
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.add
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.neg
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.sub
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.smulReal
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.nsmul
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.zsmul
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.addCommGroup
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.supNorm
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.abs_le_supNorm
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.supNorm_le
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.supNorm_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.normedAddCommGroup
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.add_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.sub_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.neg_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.zero_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.const_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.norm_def
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.abs_le_norm
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.norm_le
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.abs_sub_le_dist
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.dist_le
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.module
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.smul_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.normedSpace
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.lattice
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.le_def
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.sup_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.inf_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.abs_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.isOrderedAddMonoid
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.hasSolidNorm
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.completeSpace
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.countablyDedekindComplete
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.isSupNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.isInfNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mem_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.globallyStable_of_bX
#print axioms SargentStachurski.ADPsOnBanachSpace.pow_div_le_geometric
#print axioms SargentStachurski.ADPsOnBanachSpace.theorem_4_1_1
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsNormalizedOrderUnit
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsNormalizedOrderUnit.smul_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsNormalizedOrderUnit.le_add
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsNormalizedOrderUnit.norm_sub_le
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.isSupNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.isInfNonexpansive
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.isSupNonexpansive_subtype
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.lemma_4_1_2
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.lemma_4_1_2_subtype
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_3
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_3_univ
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsCertaintyEquivalent
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.exercise_4_1_2
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.exercise_4_1_2_subtype
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsDiscountOperator
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsDiscountOperator.exercise_4_1_3
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsDiscountOperator.iterate_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsDiscountOperator.iterate_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.specRad
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.exercise_A_4_2
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.specRad_le_norm
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsPositiveOp
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsPositiveOp.mono
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsPositiveOp.abs_le
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsPositiveOp.iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.example_4_1_1
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsIsoOrderEmbedding
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsOrderContraction
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsOrderContraction.iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_4
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.example_4_1_2
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.exercise_4_1_4
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_5
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.bellman_orderContraction
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_6
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsAdditive
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.IsAdditive.abs_sub
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_7
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_8
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.GloballyStableOn
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.DuConditions
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.abs_sub_le_of_mem_Icc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.norm_sub_le_of_mem_Icc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.iterate_mem_Icc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.du_concave
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.neg_mem_Icc_iff'
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.iterate_reflect
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.globallyStableOn_of_reflect
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.du_convex
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_10
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.lemma_4_1_9_concave
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.lemma_4_1_9_convex
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.lemma_4_1_9
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.extendIcc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.extendIcc_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.extendIcc_iterate
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.globallyStable_of_extendIcc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_10_subtype
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.countablyDedekindComplete_Icc
#print axioms SargentStachurski.ADPsOnBanachSpace.BanachLattice.theorem_4_1_11
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.posSMulMono
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.one_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.isNormalizedOrderUnit_one
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.markovLin
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.markovCLM
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.markovCLM_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.markovCLM_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.markovCLM_const
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mulLin
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mulCLM
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mulCLM_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.BM.mulCLM_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.sup'_add_const
#print axioms SargentStachurski.ADPsOnBanachSpace.harrisonKreps
#print axioms SargentStachurski.ADPsOnBanachSpace.exercise_4_1_1
#print axioms SargentStachurski.ADPsOnBanachSpace.isIsoOrderEmbedding_id
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.TBM
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.adpBM
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.sellBM
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.sellBM_isGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.adpBM_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.adpBM_bellman_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.blackwell
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmProblem.proposition_4_2_1
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.P
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.isMarkov
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.profit
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.βf
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.βf_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.s
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.K
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.K_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.K_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.cont
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.rσ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.Kσ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.T
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.T_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.adp
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.sell
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.T_sell_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.sell_isGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.adp_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.adp_bellman_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.isAdditive
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.Kσ_le_K
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmSD.proposition_4_2_2
#print axioms SargentStachurski.ADPsOnBanachSpace.argmaxSet
#print axioms SargentStachurski.ADPsOnBanachSpace.argmaxSet_nonempty
#print axioms SargentStachurski.ADPsOnBanachSpace.argmaxSel
#print axioms SargentStachurski.ADPsOnBanachSpace.argmaxSel_max
#print axioms SargentStachurski.ADPsOnBanachSpace.measurable_argmaxSel
#print axioms SargentStachurski.ADPsOnBanachSpace.SEPolicy
#print axioms SargentStachurski.ADPsOnBanachSpace.IsCEOperator
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.r
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.β
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.β_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.β_lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.M
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.H
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.H_mono
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.H_shift
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.adp
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.blackwell
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.greedySE
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.H_le_greedy
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.greedySE_isGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.adp_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.adp_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.PostAction.proposition_4_2_6
#print axioms SargentStachurski.ADPsOnBanachSpace.expectOp
#print axioms SargentStachurski.ADPsOnBanachSpace.integrable_BM
#print axioms SargentStachurski.ADPsOnBanachSpace.isCEOperator_expectOp
#print axioms SargentStachurski.ADPsOnBanachSpace.postActionEU
#print axioms SargentStachurski.ADPsOnBanachSpace.exercise_4_2_5
#print axioms SargentStachurski.ADPsOnBanachSpace.bellman_EU
#print axioms SargentStachurski.ADPsOnBanachSpace.proposition_4_2_4
#print axioms SargentStachurski.ADPsOnBanachSpace.riskSensitive
#print axioms SargentStachurski.ADPsOnBanachSpace.isCEOperator_riskSensitive
#print axioms SargentStachurski.ADPsOnBanachSpace.riskSensitive_optimality
#print axioms SargentStachurski.ADPsOnBanachSpace.hasSolidNorm_pi
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.r
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.βf
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.βf_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.P
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.P_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.P_sum
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.Klin
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.K
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.K_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.K_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.rhat
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.adp
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.adp_T_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.isGreedy_of_argmax
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.exists_argmax
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.adp_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.adp_bellman_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.isIsoOrderEmbedding_id
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.isAdditive
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.proposition_4_2_5
#print axioms SargentStachurski.ADPsOnBanachSpace.FiniteSE.specRad_lt_one_of_le
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.ae_ae_of_stationary
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.lintegral_stationary
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovFun
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.lintegral_markov_le
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.memLp_markovFun
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.ae_integrable
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovFun_congr
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovLin
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovLin_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovLin_norm_le
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovCLM
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovCLM_norm_le
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovCLM_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.markovCLM_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.memLp_mul
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulLin
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulLin_apply
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulCLM
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulCLM_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulCLM_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.L1.mulCLM_le_self
#print axioms SargentStachurski.ADPsOnBanachSpace.polInd
#print axioms SargentStachurski.ADPsOnBanachSpace.polCont
#print axioms SargentStachurski.ADPsOnBanachSpace.measurable_polInd
#print axioms SargentStachurski.ADPsOnBanachSpace.measurable_polCont
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_polInd_le
#print axioms SargentStachurski.ADPsOnBanachSpace.abs_polCont_le
#print axioms SargentStachurski.ADPsOnBanachSpace.polCont_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.polCont_le_one
#print axioms SargentStachurski.ADPsOnBanachSpace.polInd_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.isIsoOrderEmbedding_id_L1
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.P
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.isMarkov
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.ψ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.isProb
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.stationary
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.profit
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.β
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.β_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.β_lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.s
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.Pop
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.sconst
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.D
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.rσ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.Kσ
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.D_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.Kσ_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.Kσ_le_D
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.specRad_D_lt_one
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.adp
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.T_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.sell
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.T_sell_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.sell_isGreedy
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.adp_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.adp_bellman_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.isAdditive
#print axioms SargentStachurski.ADPsOnBanachSpace.FirmL1.optimality
#print axioms SargentStachurski.ADPsOnBanachSpace.iterate_affine_sub
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.mk
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.P
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.isMarkov
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.φ
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.isProb
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.stationary
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.c
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.profit
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.βf
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.βf_meas
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.βf_nonneg
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.N
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.βf_le
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.abs_βf_le
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.K
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.K_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.exists_q
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.q
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.q_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.rσ
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.Kσ
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.adp
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.T_eq
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.Kσ_isPositive
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.Kσ_le_K
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.isAdditive
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.isDiscountOperator
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.isGloballyStable
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.iterate_T_zero
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.exercise_4_2_2
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.eq_4_17_misprint
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.launch
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.mix_coeFn
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.mix_launch
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.exercise_4_2_3
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.adp_regular
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.adp_bellman
#print axioms SargentStachurski.ADPsOnBanachSpace.RealOption.proposition_4_2_3
