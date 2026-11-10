import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Function
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPCorrespondences`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`Correspondences.lean`), namespace renamed.

SLP §3.3, pp. 56–61, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`): lower and upper hemi-continuity on metric spaces (`IsLHC`, `IsUHC`),
the graph, Exercise 3.11a (`continuousAt_of_isUHC_singleton`) and Exercise 3.15
(`isCompact_graph`).
-/


namespace Miao.IncompleteMarkets

open Set Filter Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `Γ` is **lower hemi-continuous** at `x` (SLP p. 56). -/
def IsLHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ N, ∃ ys : ℕ → Y, (∀ n ≥ N, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is **upper hemi-continuous** at `x` (SLP p. 56; the book applies it to compact-valued
correspondences). -/
def IsUHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → Y, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ y ∈ Γ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- The graph `A = {(x, y) : y ∈ Γ(x)}`. -/
def graph (Γ : X → Set Y) : Set (X × Y) := {p | p.2 ∈ Γ p.1}

/-- **Ex 3.11a.** A single-valued u.h.c. correspondence is continuous. -/
theorem continuousAt_of_isUHC_singleton {f : X → Y} {x : X} (h : IsUHC (fun x => {f x}) x) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, hy, φ, -, hφ⟩ := h.2 (xs ∘ ns) (hxs.comp hns) (fun n => f (xs (ns n))) fun n => rfl
  rw [mem_singleton_iff] at hy
  exact ⟨φ, by rw [← hy]; exact hφ⟩

/-- **Ex 3.15.** A compact-valued u.h.c. correspondence on a compact space has a compact graph. -/
theorem isCompact_graph [CompactSpace X] {Γ : X → Set Y} (h : ∀ x, IsUHC Γ x) :
    IsCompact (graph Γ) := by
  refine IsSeqCompact.isCompact fun ps hps => ?_
  obtain ⟨x, -, ν, hν, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n => (ps n).1)
    fun _ => mem_univ _
  obtain ⟨y, hy, μ, hμ, hlim'⟩ := (h x).2 _ hlim (fun n => (ps (ν n)).2) fun n => hps (ν n)
  refine ⟨(x, y), hy, ν ∘ μ, hν.comp hμ, ?_⟩
  exact (Prod.tendsto_iff _ _).2 ⟨hlim.comp hμ.tendsto_atTop, hlim'⟩

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions: the Markov operator and the Feller property

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPTransitionFunctions`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`TransitionFunctions.lean`, excerpt), namespace
renamed.

SLP §8.1, pp. 212–220: the Markov operator `T` on real functions (`markovOpR`) and the Feller
property (`IsFeller`, p. 220). A transition function is a Mathlib Markov kernel `Kernel Z Z`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z] (κ : Kernel Z Z)

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Theorem of the Maximum

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPMaximum`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`Maximum.lean`), namespace renamed.

SLP §3.3, pp. 56–65, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`).

For `f : X × Y → ℝ` and a correspondence `Γ`, `h(x) = max_{y ∈ Γ(x)} f(x, y)` (`maxValue`) and
`G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}` (`argmax`).

* `theorem_3_6` (**Theorem of the Maximum**).
* `UniqueArgmax`, `argmaxFn`, `continuous_argmaxFn`, `lemma_3_7`, `theorem_3_8`: Lemma 3.7 and
  Theorem 3.8 for objectives with a unique maximizer. Chapter 3 proves them with `Γ`
  convex-valued in a normed space and `f(x, ·)` strictly concave; the proofs use only uniqueness
  of the maximizer, and Chapter 4 needs them on a convex subset of a normed space.
-/


namespace Miao.IncompleteMarkets

open Set Filter Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `h(x) = max_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def maxValue (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : ℝ :=
  sSup ((fun y => f (x, y)) '' Γ x)

/-- `G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}`. -/
def argmax (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : Set Y :=
  {y | y ∈ Γ x ∧ f (x, y) = maxValue f Γ x}

variable {f : X × Y → ℝ} {Γ : X → Set Y}

theorem continuousOn_section (hf : ContinuousOn f (graph Γ)) (x : X) :
    ContinuousOn (fun y => f (x, y)) (Γ x) :=
  hf.comp (Continuous.prodMk_right x).continuousOn fun _ hy => hy

/-- On a compact nonempty `Γ(x)` the maximum is attained. -/
theorem exists_argmax (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x))
    (hne : (Γ x).Nonempty) :
    ∃ y ∈ Γ x, f (x, y) = maxValue f Γ x ∧ ∀ z ∈ Γ x, f (x, z) ≤ f (x, y) := by
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn hne (continuousOn_section hf x)
  have hgr : IsGreatest ((fun y => f (x, y)) '' Γ x) (f (x, y)) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax hz⟩
  exact ⟨y, hy, hgr.csSup_eq.symm, fun z hz => hmax hz⟩

theorem le_maxValue (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x)) {z : Y}
    (hz : z ∈ Γ x) : f (x, z) ≤ maxValue f Γ x :=
  le_csSup ((hc.image_of_continuousOn (continuousOn_section hf x)).bddAbove) ⟨z, hz, rfl⟩

/-- Along a sequence in the graph converging to a graph point, `f` converges. -/
theorem tendsto_f_graph (hf : ContinuousOn f (graph Γ)) {xs : ℕ → X} {ys : ℕ → Y} {x : X} {y : Y}
    (hy : y ∈ Γ x) (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y)) {N : ℕ}
    (hmem : ∀ n ≥ N, ys n ∈ Γ (xs n)) :
    Tendsto (fun n => f (xs n, ys n)) atTop (𝓝 (f (x, y))) := by
  have hp : Tendsto (fun n => (xs n, ys n)) atTop (𝓝[graph Γ] (x, y)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Prod.tendsto_iff _ _).2 ⟨hxs, hys⟩,
      eventually_atTop.2 ⟨N, fun n hn => hmem n hn⟩⟩
  exact (hf (x, y) hy).tendsto.comp hp

/-- **Theorem 3.6 (Theorem of the Maximum).** If `f` is continuous on the graph and `Γ` is
compact-valued and continuous (l.h.c. and u.h.c.), then `h` is continuous and `G` is nonempty,
compact-valued and u.h.c. -/
theorem theorem_3_6 (hf : ContinuousOn f (graph Γ)) (hc : ∀ x, IsCompact (Γ x))
    (hl : ∀ x, IsLHC Γ x) (hu : ∀ x, IsUHC Γ x) :
    Continuous (maxValue f Γ) ∧
      ∀ x, (argmax f Γ x).Nonempty ∧ IsCompact (argmax f Γ x) ∧ IsUHC (argmax f Γ) x := by
  -- G is nonempty and compact
  have hGne : ∀ x, (argmax f Γ x).Nonempty := fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_argmax hf (hc x) (hu x).1
    exact ⟨y, hy, hval⟩
  have hGc : ∀ x, IsCompact (argmax f Γ x) := fun x => by
    have hcl : IsClosed (Γ x ∩ (fun y => f (x, y)) ⁻¹' {maxValue f Γ x}) :=
      (continuousOn_section hf x).preimage_isClosed_of_isClosed (hc x).isClosed isClosed_singleton
    exact (hc x).of_isClosed_subset hcl (fun y hy => hy.1)
  -- G is u.h.c.
  have hGu : ∀ x, IsUHC (argmax f Γ) x := fun x => by
    refine ⟨hGne x, fun xs hxs ys hys => ?_⟩
    obtain ⟨y, hy, ν, hν, hlim⟩ := (hu x).2 xs hxs ys fun n => (hys n).1
    refine ⟨y, ⟨hy, ?_⟩, ν, hν, hlim⟩
    refine le_antisymm (le_maxValue hf (hc x) hy) ?_
    obtain ⟨z, hz, hzval, -⟩ := exists_argmax hf (hc x) (hu x).1
    rw [← hzval]
    -- compare with a sequence converging to the maximizer `z`
    have hxν : Tendsto (xs ∘ ν) atTop (𝓝 x) := hxs.comp hν.tendsto_atTop
    obtain ⟨N, zs, hzs, hzlim⟩ := (hl x).2 z hz (xs ∘ ν) hxν
    have h1 := tendsto_f_graph hf hy hxν hlim (N := 0) fun n _ => (hys (ν n)).1
    have h2 := tendsto_f_graph hf hz hxν hzlim hzs
    refine le_of_tendsto_of_tendsto h2 h1 (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hyn := hys (ν n)
    simp only [Function.comp_apply]
    rw [hyn.2]
    exact le_maxValue hf (hc _) (hzs n hn)
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, fun x => ⟨hGne x, hGc x, hGu x⟩⟩
  -- h is continuous: every subsequence has a further subsequence along which `h → h(x)`
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  choose ys hys using fun n => hGne (xs (ns n))
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (hGu x).2 (xs ∘ ns) (hxs.comp hns) ys hys
  refine ⟨φ, ?_⟩
  have h1 := tendsto_f_graph hf hy.1 ((hxs.comp hns).comp hφ.tendsto_atTop) hlim (N := 0)
    fun n _ => (hys (φ n)).1
  rw [hy.2] at h1
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply]
  exact (hys (φ n)).2

/-! ### Unique maximizers: Lemma 3.7 and Theorem 3.8 -/

/-- The hypotheses of Lemma 3.7 with uniqueness of the maximizer in place of strict concavity. -/
structure UniqueArgmax (Γ : X → Set Y) (f : X × Y → ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cont : ContinuousOn f (graph Γ)
  unique : ∀ x, ∀ y₁ ∈ argmax f Γ x, ∀ y₂ ∈ argmax f Γ x, y₁ = y₂

variable [Nonempty Y]

/-- The maximizer `g(x) = argmax_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def argmaxFn (Γ : X → Set Y) (f : X × Y → ℝ) (x : X) : Y :=
  Classical.epsilon fun y => y ∈ argmax f Γ x

namespace UniqueArgmax

variable (h : UniqueArgmax Γ f)
include h

theorem argmaxFn_mem (x : X) : argmaxFn Γ f x ∈ argmax f Γ x := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax h.cont (h.compact x) (h.nonempty x)
  exact Classical.epsilon_spec (p := fun y => y ∈ argmax f Γ x) ⟨y, hy, hval⟩

theorem argmax_eq (x : X) : argmax f Γ x = {argmaxFn Γ f x} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h.argmaxFn_mem x, fun _ hy => h.unique x _ hy _
    (h.argmaxFn_mem x)⟩

/-- `f(x, y) < f(x, g(x))` for `y ≠ g(x)` in `Γ(x)`. -/
theorem lt_of_ne {x : X} {y : Y} (hy : y ∈ Γ x) (hne : y ≠ argmaxFn Γ f x) :
    f (x, y) < f (x, argmaxFn Γ f x) := by
  have hle : f (x, y) ≤ f (x, argmaxFn Γ f x) := by
    rw [(h.argmaxFn_mem x).2]
    exact le_maxValue h.cont (h.compact x) hy
  refine lt_of_le_of_ne hle fun heq => hne ?_
  have : y ∈ argmax f Γ x := ⟨hy, by rw [heq]; exact (h.argmaxFn_mem x).2⟩
  rw [h.argmax_eq x] at this
  exact this

/-- The maximizer is continuous (Theorem 3.6 with Ex 3.11a). -/
theorem continuous_argmaxFn : Continuous (argmaxFn Γ f) := by
  have h36 := theorem_3_6 h.cont h.compact h.lhc h.uhc
  refine continuous_iff_continuousAt.2 fun x => continuousAt_of_isUHC_singleton ?_
  have := (h36.2 x).2.2
  have heq : argmax f Γ = fun x => {argmaxFn Γ f x} := funext h.argmax_eq
  rwa [heq] at this

/-- **Lemma 3.7.** For each `ε > 0` and `x` there is `δ > 0` such that `y ∈ Γ(x)` and
`|f(x, g(x)) − f(x, y)| < δ` imply `ρ(g(x), y) < ε`. -/
theorem lemma_3_7 {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ δ > 0, ∀ y ∈ Γ x, |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f x
  set K := Γ x ∩ {y | ε ≤ dist g y}
  have hK : IsCompact K := (h.compact x).inter_right
    (isClosed_le continuous_const (continuous_const.dist continuous_id))
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hge
    have : y ∈ K := ⟨hy, not_lt.1 hge⟩
    rw [hK0] at this
    exact this
  have hcont : ContinuousOn (fun y => f (x, g) - f (x, y)) K :=
    continuousOn_const.sub ((continuousOn_section h.cont x).mono inter_subset_left)
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < f (x, g) - f (x, y₀) := by
    have hne : y₀ ≠ g := fun he => by
      have := hy₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    linarith [h.lt_of_ne hy₀.1 hne]
  refine ⟨f (x, g) - f (x, y₀), hpos, fun y hy hyδ => ?_⟩
  by_contra hge
  have hyK : y ∈ K := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin y hyK
  have habs := le_abs_self (f (x, g) - f (x, y))
  linarith

/-- **Lemma 3.7 (compact `X`).** If `X` is compact, `δ` can be chosen independently of `x`. -/
theorem lemma_3_7_uniform [CompactSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ∀ y ∈ Γ x,
      |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f
  have hg := h.continuous_argmaxFn
  set Aε := graph Γ ∩ {p : X × Y | ε ≤ dist (g p.1) p.2}
  have hA : IsCompact Aε := (isCompact_graph h.uhc).inter_right
    (isClosed_le continuous_const ((hg.comp continuous_fst).dist continuous_snd))
  rcases Aε.eq_empty_or_nonempty with hA0 | hAne
  · refine ⟨1, one_pos, fun x y hy _ => ?_⟩
    by_contra hge
    have : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
    rw [hA0] at this
    exact this
  have hcont : ContinuousOn (fun p : X × Y => f (p.1, g p.1) - f p) Aε := by
    refine ContinuousOn.sub ?_ (h.cont.mono inter_subset_left)
    exact h.cont.comp (continuous_fst.prodMk (hg.comp continuous_fst)).continuousOn
      fun p _ => (h.argmaxFn_mem p.1).1
  obtain ⟨p₀, hp₀, hmin⟩ := hA.exists_isMinOn hAne hcont
  have hpos : 0 < f (p₀.1, g p₀.1) - f p₀ := by
    have hne : p₀.2 ≠ g p₀.1 := fun he => by
      have := hp₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    have := h.lt_of_ne hp₀.1 hne
    linarith
  refine ⟨_, hpos, fun x y hy hyδ => ?_⟩
  by_contra hge
  have hyA : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin (x, y) hyA
  have habs := le_abs_self (f (x, g x) - f (x, y))
  linarith

end UniqueArgmax

/-- The shortfall bound behind Theorem 3.8: if `|f − fₙ| < δ/2` on the graph, then
`|f(x, g(x)) − f(x, gₙ(x))| < δ`. -/
theorem shortfall_lt {f fn : X × Y → ℝ} (hf : UniqueArgmax Γ f) (hfn : UniqueArgmax Γ fn)
    {δ : ℝ} (hclose : ∀ p ∈ graph Γ, |f p - fn p| < δ / 2) (x : X) :
    |f (x, argmaxFn Γ f x) - f (x, argmaxFn Γ fn x)| < δ := by
  set g := argmaxFn Γ f x
  set gn := argmaxFn Γ fn x
  have hg := hf.argmaxFn_mem x
  have hgn := hfn.argmaxFn_mem x
  have h1 : f (x, gn) ≤ f (x, g) := by rw [hg.2]; exact le_maxValue hf.cont (hf.compact x) hgn.1
  have h2 : fn (x, g) ≤ fn (x, gn) := by
    rw [hgn.2]; exact le_maxValue hfn.cont (hfn.compact x) hg.1
  have e1 := abs_lt.1 (hclose (x, g) hg.1)
  have e2 := abs_lt.1 (hclose (x, gn) hgn.1)
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- **Theorem 3.8.** If `fₙ → f` uniformly on the graph, each with a unique maximizer, then the
maximizers converge pointwise: `gₙ(x) → g(x)`. -/
theorem theorem_3_8 {fs : ℕ → X × Y → ℝ} (hf : UniqueArgmax Γ f)
    (hfs : ∀ n, UniqueArgmax Γ (fs n)) (hunif : TendstoUniformlyOn fs f atTop (graph Γ))
    (x : X) : Tendsto (fun n => argmaxFn Γ (fs n) x) atTop (𝓝 (argmaxFn Γ f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7 hε x
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine ⟨M, fun n hn => ?_⟩
  rw [dist_comm]
  refine hlem _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

/-- **Theorem 3.8 (compact `X`).** If `X` is compact the convergence is uniform. -/
theorem theorem_3_8_uniform [CompactSpace X] {fs : ℕ → X × Y → ℝ}
    (hf : UniqueArgmax Γ f) (hfs : ∀ n, UniqueArgmax Γ (fs n))
    (hunif : TendstoUniformlyOn fs f atTop (graph Γ)) :
    TendstoUniformly (fun n => argmaxFn Γ (fs n)) (argmaxFn Γ f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7_uniform hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine eventually_atTop.2 ⟨M, fun n hn x => ?_⟩
  refine hlem x _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Measurable Selection Theorem

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPSelection`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`Selection.lean`), namespace renamed.

SLP §7.3, pp. 183–184: measurable selections and Theorem 7.6, which the book cites from
Hildenbrand (1974). It is proved here by **lexicographic minimization**.

A nonempty compact-valued correspondence `Φ : X → ℝᵐ` is *measurable* (`IsMeasCorr`) when
`{x : Φ(x) ∩ F ≠ ∅}` is measurable for every closed `F`. A compact-valued u.h.c. correspondence
on a metric space is measurable, since these sets are closed (`isMeasCorr_of_uhc`). For a
measurable `Φ`, the least `i`-th coordinate `x ↦ min {yᵢ : y ∈ Φ(x)}` is measurable
(`measurable_minCoord`), and the points of `Φ(x)` attaining it again form a measurable
correspondence (`IsMeasCorr.refine`): the key identity expresses the lower inverse through
rational thresholds. Minimizing the coordinates one after the other leaves a single point
whose coordinates are measurable functions (`theorem_7_6`).
-/

namespace Miao.IncompleteMarkets

open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A **measurable selection** from `Γ` (SLP p. 183): a measurable `h` with `h(x) ∈ Γ(x)`. -/
def IsMeasurableSelection {Y : Type*} [MeasurableSpace Y] (Γ : X → Set Y) (h : X → Y) : Prop :=
  Measurable h ∧ ∀ x, h x ∈ Γ x

/-- A nonempty compact-valued correspondence whose lower inverses of closed sets are
measurable. -/
def IsMeasCorr (Φ : X → Set (Fin m → ℝ)) : Prop :=
  (∀ x, (Φ x).Nonempty ∧ IsCompact (Φ x)) ∧
    ∀ F : Set (Fin m → ℝ), IsClosed F → MeasurableSet {x | (Φ x ∩ F).Nonempty}

/-- The least `i`-th coordinate on `Φ(x)`. -/
noncomputable def minCoord (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : ℝ :=
  sInf ((fun y => y i) '' Φ x)

theorem minCoord_mem {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) (x : X) :
    ∃ y ∈ Φ x, y i = minCoord Φ i x := by
  have hK := ((hΦ.1 x).2.image (continuous_apply i))
  exact hK.sInf_mem ((hΦ.1 x).1.image _)

theorem minCoord_le {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) {x : X}
    {y : Fin m → ℝ} (hy : y ∈ Φ x) : minCoord Φ i x ≤ y i :=
  csInf_le ((hΦ.1 x).2.image (continuous_apply i)).bddBelow (mem_image_of_mem _ hy)

/-- The least coordinate is measurable: `{x : min yᵢ ≤ a} = {x : Φ(x) ∩ {yᵢ ≤ a} ≠ ∅}`. -/
theorem measurable_minCoord {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    Measurable (minCoord Φ i) := by
  refine measurable_of_Iic fun a => ?_
  change MeasurableSet {x | minCoord Φ i x ≤ a}
  have heq : {x | minCoord Φ i x ≤ a} = {x | (Φ x ∩ {y | y i ≤ a}).Nonempty} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
      exact ⟨y, hy, by rw [mem_ofPred_eq, hyi]; exact hx⟩
    · rintro ⟨y, hy, hya⟩
      exact (minCoord_le hΦ i hy).trans hya
  rw [heq]
  exact hΦ.2 _ (isClosed_le (continuous_apply i) continuous_const)

/-- The points of `Φ(x)` minimizing the `i`-th coordinate. -/
def refineCorr (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : Set (Fin m → ℝ) :=
  Φ x ∩ {y | y i = minCoord Φ i x}

/-- **The minimizers again form a measurable correspondence.** -/
theorem IsMeasCorr.refine {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    IsMeasCorr (refineCorr Φ i) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun F hF => ?_⟩
  · obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
    exact ⟨y, hy, hyi⟩
  · exact (hΦ.1 x).2.inter_right (isClosed_eq (continuous_apply i) continuous_const)
  · have heq : {x | (refineCorr Φ i x ∩ F).Nonempty} =
        ⋂ q : ℚ, ({x | (q : ℝ) ≤ minCoord Φ i x} ∪
          ⋃ n : ℕ, {x | (Φ x ∩ (F ∩ {y | y i ≤ q - 1 / ((n : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [refineCorr, mem_ofPred_eq, mem_iInter, mem_union, mem_iUnion]
      constructor
      · rintro ⟨y, ⟨hy, hyi⟩, hyF⟩ q
        by_cases hq : (q : ℝ) ≤ minCoord Φ i x
        · exact Or.inl hq
        · push Not at hq
          right
          rw [mem_ofPred_eq] at hyi
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hq)
          exact ⟨n, y, hy, hyF, by rw [mem_ofPred_eq, hyi]; linarith⟩
      · intro hx
        by_contra hne
        set K := Φ x ∩ F
        have hKc : IsCompact K := (hΦ.1 x).2.inter_right hF
        have hall : ∀ y ∈ K, minCoord Φ i x < y i := fun y hy => by
          refine lt_of_le_of_ne (minCoord_le hΦ i hy.1) fun h => hne ⟨y, ⟨hy.1, h.symm⟩, hy.2⟩
        by_cases hKe : K.Nonempty
        · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hKe (continuous_apply i).continuousOn
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (hall y₀ hy₀)
          rcases hx q with h | ⟨n, y, hy, hyF, hyq⟩
          · exact absurd h (not_le.2 hq1)
          · have : y₀ i ≤ y i := hmin ⟨hy, hyF⟩
            have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            rw [mem_ofPred_eq] at hyq
            linarith
        · obtain ⟨q, hq⟩ := exists_rat_gt (minCoord Φ i x)
          rcases hx q with h | ⟨n, y, hy, hyF, -⟩
          · exact absurd h (not_le.2 hq)
          · exact hKe ⟨y, hy, hyF⟩
    rw [heq]
    refine MeasurableSet.iInter fun q => ?_
    refine (measurableSet_le measurable_const (measurable_minCoord hΦ i)).union ?_
    exact MeasurableSet.iUnion fun n => hΦ.2 _
      (hF.inter (isClosed_le (continuous_apply i) continuous_const))

/-- The correspondences obtained by minimizing coordinates `0, 1, …, k − 1` in turn. -/
noncomputable def lexCorr (Γ : X → Set (Fin m → ℝ)) : ℕ → X → Set (Fin m → ℝ)
  | 0 => Γ
  | k + 1 => if h : k < m then refineCorr (lexCorr Γ k) ⟨k, h⟩ else lexCorr Γ k

theorem lexCorr_spec {Γ : X → Set (Fin m → ℝ)} (hΓ : IsMeasCorr Γ) (k : ℕ) :
    IsMeasCorr (lexCorr Γ k) ∧ (∀ x, lexCorr Γ k x ⊆ Γ x) ∧
      ∀ i : Fin m, (i : ℕ) < k → ∀ x, ∀ y ∈ lexCorr Γ k x, y i = minCoord (lexCorr Γ i) i x := by
  induction k with
  | zero => exact ⟨hΓ, fun _ => subset_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases hk : k < m
    · have hdef : lexCorr Γ (k + 1) = refineCorr (lexCorr Γ k) ⟨k, hk⟩ := by
        simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1.refine _, fun x => inter_subset_left.trans (h2 x), fun i hi x y hy => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact h3 i hlt x y hy.1
      · have : i = ⟨k, hk⟩ := Fin.ext heq
        subst this
        exact hy.2
    · have hdef : lexCorr Γ (k + 1) = lexCorr Γ k := by simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1, h2, fun i hi => h3 i ?_⟩
      have := i.2
      omega

/-- **A compact-valued u.h.c. correspondence is measurable**: for closed `F`, the set
`{x : Γ(x) ∩ F ≠ ∅}` is closed. -/
theorem isMeasCorr_of_uhc {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    IsMeasCorr Γ := by
  refine ⟨fun x => ⟨(hΓ x).1, hK x⟩, fun F hF => ?_⟩
  refine IsClosed.measurableSet (IsSeqClosed.isClosed fun xs x hxs hlim => ?_)
  choose ys hys using hxs
  obtain ⟨y, hy, φ, -, hφ⟩ := (hΓ x).2 xs hlim ys fun n => (hys n).1
  exact ⟨y, hy, hF.mem_of_tendsto hφ (Eventually.of_forall fun n => (hys (φ n)).2)⟩

/-- **Theorem 7.6 (Measurable Selection Theorem).** A nonempty compact-valued u.h.c.
correspondence `Γ` from a metric space `X` (with its Borel sets; the book's `X` is a Borel set
in `ℝˡ`) into `ℝᵐ` has a measurable selection. -/
theorem theorem_7_6 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    ∃ h : X → Fin m → ℝ, IsMeasurableSelection Γ h := by
  have hM := isMeasCorr_of_uhc hΓ hK
  obtain ⟨h1, h2, h3⟩ := lexCorr_spec hM m
  refine ⟨fun x (i : Fin m) => minCoord (lexCorr Γ i) i x, ?_, fun x => ?_⟩
  · exact measurable_pi_iff.2 fun i => measurable_minCoord (lexCorr_spec hM i).1 i
  · obtain ⟨y, hy⟩ := (h1.1 x).1
    have : y = fun (i : Fin m) => minCoord (lexCorr Γ i) i x := funext fun i => h3 i i.2 x y hy
    change (fun (i : Fin m) => minCoord (lexCorr Γ i) i x) ∈ Γ x
    rw [← this]
    exact h2 x hy

/-- **Theorem 7.6 with a target set `T`** (SLP's `T ⊆ ℝᵐ`): if `Γ(x) ⊆ T` for all `x`, the
selection is a measurable map into `T` with its subspace σ-algebra. -/
theorem theorem_7_6_subtype {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {T : Set (Fin m → ℝ)} {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x)
    (hK : ∀ x, IsCompact (Γ x)) (hT : ∀ x, Γ x ⊆ T) :
    ∃ h : X → T, Measurable h ∧ ∀ x, (h x : Fin m → ℝ) ∈ Γ x := by
  obtain ⟨h, hm, hmem⟩ := theorem_7_6 hΓ hK
  exact ⟨fun x => ⟨h x, hT x (hmem x)⟩, hm.subtype_mk, hmem⟩

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability of a concave function from below: Benveniste and Scheinkman

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPEnvelope`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`Envelope.lean`), namespace renamed.

SLP §4.2, pp. 83–86.

* `theorem_4_10` (**Benveniste–Scheinkman**): if `V` is concave on a convex `X`, `x₀ ∈ int X`, and
  a function `W` differentiable at `x₀` satisfies `W(x₀) = V(x₀)` and `W ≤ V` near `x₀`, then `V`
  is differentiable at `x₀` with `DV(x₀) = DW(x₀)`. The proof needs no subgradients: near `x₀`,
  `W(x₀ + h) − W(x₀) ≤ V(x₀ + h) − V(x₀) ≤ V(x₀) − V(x₀ − h) ≤ W(x₀) − W(x₀ − h)`, the middle
  step by concavity at the midpoint `x₀`. Concavity of `W` (assumed in the book) is not needed.
* `ex_4_5`: from the first-order condition `U′(f(x) − g(x)) = βv′(g(x))` with `U`, `f`, `v`
  strictly increasing, strictly concave and differentiable, `0 < g(x′) − g(x) < f(x′) − f(x)`
  for `x′ > x`.
-/


namespace Miao.IncompleteMarkets

open Filter Topology Asymptotics Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 4.10 (Benveniste and Scheinkman).** Let `V` be concave on a convex set `X`,
`x₀ ∈ int X`, and `W` differentiable at `x₀` with `W(x₀) = V(x₀)` and `W ≤ V` on a neighborhood
of `x₀`. Then `V` is differentiable at `x₀` and `DV(x₀) = DW(x₀)`. -/
theorem theorem_4_10 {X : Set E} {V W : E → ℝ} {x₀ : E} {W' : E →L[ℝ] ℝ}
    (hV : ConcaveOn ℝ X V) (hx₀ : X ∈ 𝓝 x₀) (hW : HasFDerivAt W W' x₀) (heq : W x₀ = V x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ V x) : HasFDerivAt V W' x₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hW ⊢
  set r : E → ℝ := fun h => W (x₀ + h) - W x₀ - W' h
  -- the remainder of `W` at `−h`
  have hr' : (fun h : E => r (-h)) =o[𝓝 0] fun h => h := by
    have := hW.comp_tendsto (show Tendsto (fun h : E => -h) (𝓝 0) (𝓝 0) by
      simpa using (continuous_neg (G := E)).tendsto 0)
    refine (this.trans_isBigO ?_)
    exact IsBigO.of_bound 1 (Eventually.of_forall fun h => by simp)
  -- `x₀ ± h ∈ X` and `W ≤ V` there, for `h` near `0`
  have hplus : ∀ᶠ h in 𝓝 (0 : E), x₀ + h ∈ X ∧ W (x₀ + h) ≤ V (x₀ + h) := by
    have hc : Tendsto (fun h : E => x₀ + h) (𝓝 0) (𝓝 x₀) := by
      simpa using (continuous_const_add x₀).tendsto (0 : E)
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hminus : ∀ᶠ h in 𝓝 (0 : E), x₀ - h ∈ X ∧ W (x₀ - h) ≤ V (x₀ - h) := by
    have hc : Tendsto (fun h : E => x₀ - h) (𝓝 0) (𝓝 x₀) := by
      simpa using ((continuous_const.sub continuous_id).tendsto (0 : E) (f := fun h : E => x₀ - h))
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hbound : ∀ᶠ h in 𝓝 (0 : E),
      ‖V (x₀ + h) - V x₀ - W' h‖ ≤ 1 * ‖‖r h‖ + ‖r (-h)‖‖ := by
    filter_upwards [hplus, hminus] with h hp hm
    have hx₀X : x₀ ∈ X := mem_of_mem_nhds hx₀
    -- concavity at the midpoint `x₀ = ½(x₀ + h) + ½(x₀ − h)`
    have hmid := hV.2 hp.1 hm.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • (x₀ + h) + (1 / 2 : ℝ) • (x₀ - h) = x₀ := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hmid
    have er : r (-h) = W (x₀ - h) - W x₀ + W' h := by
      simp only [r, map_neg, ← sub_eq_add_neg]; ring
    rw [er, one_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (r h))
      (abs_nonneg (W (x₀ - h) - W x₀ + W' h))), abs_le]
    have h1 := hp.2
    have h2 := hm.2
    constructor
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
  have hsum : (fun h : E => ‖r h‖ + ‖r (-h)‖) =o[𝓝 0] fun h => h :=
    hW.norm_left.add hr'.norm_left
  exact (IsBigO.of_bound 1 hbound).trans_isLittleO hsum

/-- **Exercise 4.5.** Let `U`, `f`, `v` be strictly increasing, strictly concave and
differentiable on `ℝ₊`, `0 < g(x) < f(x)`, and `U′(f(x) − g(x)) = βv′(g(x))` with `β > 0`. Then
`0 < g(x′) − g(x) < f(x′) − f(x)` for `0 ≤ x < x′`. -/
theorem ex_4_5 {U f v g : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ U c)
    (hv : StrictConcaveOn ℝ (Ici 0) v) (hvd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ v c)
    (hf : StrictMonoOn f (Ici 0)) (hg : ∀ x ∈ Ici (0 : ℝ), 0 < g x ∧ g x < f x)
    (hfoc : ∀ x ∈ Ici (0 : ℝ), deriv U (f x - g x) = β * deriv v (g x))
    {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    0 < g x' - g x ∧ g x' - g x < f x' - f x := by
  have hx' : 0 ≤ x' := hx.trans hxx'.le
  have hU' := hU.strictAntiOn_deriv hUd
  have hv' := hv.strictAntiOn_deriv hvd
  have hfx := hf hx hx' hxx'
  obtain ⟨g0, g1⟩ := hg x hx
  obtain ⟨g0', g1'⟩ := hg x' hx'
  have hc : (0 : ℝ) ≤ f x - g x := by linarith
  have hc' : (0 : ℝ) ≤ f x' - g x' := by linarith
  constructor
  · -- if `g(x′) ≤ g(x)` then consumption rises, contradicting the first-order condition
    by_contra hle
    push Not at hle
    have h1 : deriv v (g x) ≤ deriv v (g x') := hv'.antitoneOn g0'.le g0.le (by linarith)
    have h2 : f x - g x < f x' - g x' := by linarith
    have h3 := hU' hc hc' h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    nlinarith
  · -- if `g` rises by at least `f`, consumption falls, again a contradiction
    by_contra hle
    push Not at hle
    have h2 : f x' - g x' ≤ f x - g x := by linarith
    have h3 : deriv U (f x - g x) ≤ deriv U (f x' - g x') := hU'.antitoneOn hc' hc h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    have hgg : g x < g x' := by linarith
    have h4 := hv' g0.le g0'.le hgg
    nlinarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 9.5: integration preserves continuity, monotonicity and concavity

Copied from `EconomicDynamics/FiniteHorizonDP` (module `SLPLemma95`), namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (`Lemma95.lean`), namespace renamed.

SLP §9.2, pp. 260–262 and 268–269. The operator `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)` (`mop`) on
functions of an endogenous variable `w` and the shock `z`. **Assumption 9.5** asks that `M` map
bounded continuous functions to continuous ones (`PreservesBC`). **Lemma 9.5** proves this in the
book's two cases:

* (a) `Z` countable with all subsets measurable (`lemma_9_5_discrete`: any `Z` with the discrete
  topology whose open sets are measurable; countability is not needed), by dominated convergence;
* (b) `Z` compact and `Q` Feller (`lemma_9_5_compact`): `|Mf(w′, z′) − Mf(w, z)|` is at most
  `sup_{z″} |f(w′, z″) − f(w, z″)| + |Mf(w, z′) − Mf(w, z)|`; the first term vanishes because
  `w ↦ f(w, ·)` is continuous into `C(Z)` with the sup norm (the book's uniform continuity on
  `D × Z`), the second by the Feller property.

The bound `|Mf| ≤ sup |f|` is `abs_mop_le`; preservation of (strict) monotonicity and concavity is
stated for any combination `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` (`lemma_9_5_comb`,
`lemma_9_5_comb_strict`, `lemma_9_5_mono`, `lemma_9_5_strictMono`), the strict versions by
Exercises 7.18 and 7.24 (`integral_lt_integral_of_lt`).

**Lemma 9.5′** (`lemma_9_5'`): with `φ` continuous on `D × Z`, where `D` is the projection of the
graph of `Γ` on `X × Y` (Assumption 9.17), `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is
continuous on `D × Z`: apply Lemma 9.5 to `ψ(u, z′) = f[φ(u, z′), z′]` on `D × Z`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W Z : Type*} [MeasurableSpace Z]

/-- The Markov operator on functions of `(w, z)`: `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)`. -/
noncomputable def mop (Q : Kernel Z Z) (f : W × Z → ℝ) (p : W × Z) : ℝ := ∫ z', f (p.1, z') ∂Q p.2

/-- **Assumption 9.5** (in the form the proofs use): `M` maps the bounded continuous functions on
`W × Z` into continuous functions. -/
def PreservesBC (W : Type*) [TopologicalSpace W] [TopologicalSpace Z] (Q : Kernel Z Z) : Prop :=
  ∀ f : W × Z → ℝ, Continuous f → (∃ B, ∀ p, |f p| ≤ B) → Continuous (mop Q f)

/-- A bounded measurable function is integrable for a finite measure. -/
theorem integrable_of_abs_le {μ : Measure Z} [IsFiniteMeasure μ] {h : Z → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ z, |h z| ≤ B) : Integrable h μ :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)

/-- **Exercises 7.18 and 7.24.** For a probability measure, `f < g` everywhere implies
`∫ f < ∫ g`. -/
theorem integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {f g : Z → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hlt : ∀ z, f z < g z) :
    ∫ z, f z ∂μ < ∫ z, g z ∂μ := by
  have hpos : 0 < ∫ z, (g z - f z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (hlt z)).le) (hg.sub hf)]
    have : Function.support (fun z => g z - f z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (hlt z)).ne'
    rw [this, measure_univ]
    exact one_pos
  rw [integral_sub hg hf] at hpos
  linarith

variable [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z]

omit [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z] in
theorem abs_mop_le (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} {B : ℝ}
    (hB : ∀ p, |f p| ≤ B) (p : W × Z) : |mop Q f p| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := B) (f := fun z' => f (p.1, z'))
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
  rw [mop]
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem integrable_section (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) (w : W) (z : Z) : Integrable (fun z' => f (w, z')) (Q z) :=
  integrable_of_abs_le (hf.comp (Continuous.prodMk_right w)).measurable fun _ => hB _

/-- **Lemma 9.5 (a).** If `Z` is discrete (with its subsets measurable), `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_discrete [FirstCountableTopology W] [DiscreteTopology Z] (Q : Kernel Z Z)
    [IsMarkovKernel Q] : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  refine continuous_prod_of_discrete_right.2 fun z => ?_
  exact continuous_of_dominated (bound := fun _ => B)
    (fun w => (integrable_section Q hf hB w z).aestronglyMeasurable)
    (fun w => Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
    (integrable_const B) (Eventually.of_forall fun z' => hf.comp (Continuous.prodMk_left z'))

/-- **Lemma 9.5 (b).** If `Z` is compact and `Q` has the Feller property, `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_compact [CompactSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (hQ : IsFeller Q) : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨w, z⟩
  set g : C(W, C(Z, ℝ)) := (ContinuousMap.mk f hf).curry with hgdef
  set k : Z → ℝ := markovOpR Q fun z' => f (w, z') with hkdef
  have hk : Continuous k :=
    hQ _ (hf.comp (Continuous.prodMk_right w)) ⟨B, fun z' => hB _⟩
  have hdist : Tendsto (fun p : W × Z => dist (g p.1) (g w)) (𝓝 (w, z)) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((g.continuous.tendsto w).comp continuous_fst.continuousAt)
  have hA : Tendsto (fun p : W × Z => mop Q f p - k p.2) (𝓝 (w, z)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => ?_) hdist
    rw [mop, hkdef, markovOpR, ← integral_sub (integrable_section Q hf hB p.1 p.2)
      (integrable_section Q hf hB w p.2)]
    have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := dist (g p.1) (g w))
      (f := fun z' => f (p.1, z') - f (w, z')) (Eventually.of_forall fun z' => by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := g p.1) (g := g w) z')
    simpa [measureReal_def] using this
  have hB' : Tendsto (fun p : W × Z => k p.2) (𝓝 (w, z)) (𝓝 (k z)) :=
    (hk.tendsto z).comp continuous_snd.continuousAt
  have hsum := hA.add hB'
  rw [zero_add] at hsum
  have heq : (fun p : W × Z => mop Q f p - k p.2 + k p.2) = mop Q f :=
    funext fun p => sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

/-- **Lemma 9.5 (combinations).** If `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` for all `z′`,
then `θ (Mf)(w₀, z) + (1 − θ) (Mf)(w₁, z) ≤ (Mf)(w, z)`: concavity is preserved. -/
theorem lemma_9_5_comb (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hle : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') ≤ f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) ≤ mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_mono ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hle

/-- **Lemma 9.5 (strict combinations).** Strict concavity is preserved. -/
theorem lemma_9_5_comb_strict (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hlt : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') < f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) < mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_lt_integral_of_lt ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hlt

/-- **Lemma 9.5 (monotonicity).** If `f(·, z′)` is nondecreasing for every `z′`, so is
`(Mf)(·, z)`. -/
theorem lemma_9_5_mono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) (hmono : ∀ z', Monotone fun w => f (w, z'))
    (z : Z) : Monotone fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_mono (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

/-- **Lemma 9.5 (strict monotonicity).** -/
theorem lemma_9_5_strictMono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B)
    (hmono : ∀ z', StrictMono fun w => f (w, z')) (z : Z) :
    StrictMono fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_lt_integral_of_lt (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

omit [OpensMeasurableSpace Z] in
/-- **Lemma 9.5′.** Let `D ⊆ X × Y` (the projection of the graph of `Γ`), let `φ` be continuous on
`D × Z` (Assumption 9.17), and let `Q` satisfy Assumption 9.5 on `D × Z`. For bounded continuous
`f` on `X × Z`, `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on `D × Z`. -/
theorem lemma_9_5' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (D : Set (X × Y))
    {φ : X × Y × Z → X} (hφ : ContinuousOn (fun q : (X × Y) × Z => φ (q.1.1, q.1.2, q.2))
      (D ×ˢ univ)) (Q : Kernel Z Z) (hQ : PreservesBC D Q) {f : X × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) :
    ContinuousOn (fun q : (X × Y) × Z => ∫ z', f (φ (q.1.1, q.1.2, z'), z') ∂Q q.2)
      (D ×ˢ univ) := by
  set ψ : D × Z → ℝ := fun q => f (φ (q.1.1.1, q.1.1.2, q.2), q.2) with hψdef
  have hφ' : Continuous fun q : D × Z => φ (q.1.1.1, q.1.1.2, q.2) := by
    refine hφ.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun q => ⟨q.1.2, mem_univ _⟩
  have hψ : Continuous ψ := hf.comp (hφ'.prodMk continuous_snd)
  have hM := hQ ψ hψ ⟨B, fun _ => hB _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous fun q : (D ×ˢ (univ : Set Z)) => ((⟨q.1.1, q.2.1⟩ : D), q.1.2) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact (hM.comp hmap : _)

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The optimal control model of §6.4: Bellman equation and assumptions

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCSetting`), namespace renamed.

Miao, §6.4, pp. 172–178 (with §5.2.4, pp. 153–154). The state is `(x, z)`: an endogenous state
`x ∈ X ⊆ E` and an exogenous shock `z ∈ Z` with transition function `Q`; the action `a ∈ A ⊆ F`
is chosen in `Γ(x, z)`; the state moves by (5.14), `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})`; the
rewards are `u_t(x, z, a)` and the terminal reward `u_T(x, z)`.

* `OCModel`: the primitives `(X, A, Q, Γ, φ, (u_t), u_T, β, T)`. The functions are defined on the
  ambient spaces `E`, `F` (for the book `ℝ^{n_x}`, `ℝ^{n_a}`); only their values on `X`, `A`
  matter. The 1-D case of §6.6.2 is `E = F = ℝ` with `X` an interval.
* `OCModel.cont`, `OCModel.obj`, `OCModel.bellman`: the right side of the Bellman equation (6.29),
  `sup_{a ∈ Γ(x, z)} u_t(x, z, a) + β ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`.
* `OCModel.V`: the backward-induction sequence of (6.29) with `V_T = u_T`; `V_T_eq` and `V_succ`
  are the two equations. `OCModel.G`: the policy correspondence `G_t`. `OCModel.g`: a selection
  from `G_t` (the policy function `g_t` of p. 178 when `G_t` is single-valued).
* `OCModel.path`, `OCModel.bolza`: for a filtered probability space with adapted shocks
  `z_t`, the states generated by a plan through (5.14) and the Bolza objective (6.28);
  `OCModel.IsPlan`: adapted and feasible plans; `OCModel.policyPath`: the plan and states
  generated by the policy functions (p. 178).
* `Assumption641` … `Assumption6414`: Assumptions 6.4.1–6.4.14, with `Assumption643i` and
  `Assumption643ii` the two cases of Assumption 6.4.3. Convex combinations are written
  `θ • x + η • x′` with `θ, η > 0`, `θ + η = 1`, the book's `θ` and `1 − θ`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory

/-- The **optimal control model** of Miao §6.4 (p. 172, from §5.2.4): the state space
`X ⊆ E`, the action space `A ⊆ F`, the shock transition function `Q`, the feasibility
correspondence `Γ`, the state transition function `φ` of (5.14), the rewards `u_t` and `u_T`,
the discount factor `β` and the horizon `T`. -/
structure OCModel (E F Z : Type*) [MeasurableSpace Z] where
  X : Set E
  A : Set F
  Q : Kernel Z Z
  Γ : E → Z → Set F
  φ : E → F → Z → Z → E
  u : ℕ → E → Z → F → ℝ
  uT : E → Z → ℝ
  β : ℝ
  T : ℕ

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] (M : OCModel E F Z)

/-- The expected continuation value `∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` (the function `h` of
Lemma 6.4.1 for `f`). -/
noncomputable def cont (f : E → Z → ℝ) (x : E) (a : F) (z : Z) : ℝ :=
  ∫ z', f (M.φ x a z z') z' ∂M.Q z

/-- The objective of the Bellman equation (6.29) at date `t`:
`u_t(x, z, a) + β ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`. -/
noncomputable def obj (t : ℕ) (f : E → Z → ℝ) (x : E) (z : Z) (a : F) : ℝ :=
  M.u t x z a + M.β * M.cont f x a z

/-- The Bellman operator of (6.29): `(T_t f)(x, z) = sup_{a ∈ Γ(x, z)} obj_t(f)(x, z, a)`. -/
noncomputable def bellman (t : ℕ) (f : E → Z → ℝ) (x : E) (z : Z) : ℝ :=
  sSup (M.obj t f x z '' M.Γ x z)

/-- The value function `k` steps before the horizon: `W₀ = u_T`, `W_{k+1} = T_{T−k−1} W_k`. -/
noncomputable def W : ℕ → E → Z → ℝ
  | 0 => M.uT
  | k + 1 => M.bellman (M.T - (k + 1)) (W k)

/-- **The solution of the Bellman equation (6.29)** (Miao, p. 172) by backward induction:
`V_t = W_{T−t}`, so `V_T = u_T` and `V_t = T_t V_{t+1}` for `t < T`. -/
noncomputable def V (t : ℕ) : E → Z → ℝ := M.W (M.T - t)

/-- Miao, p. 172: the terminal condition `V_T = u_T`. -/
theorem V_T_eq : M.V M.T = M.uT := by
  simp only [V, Nat.sub_self, W]

/-- **The Bellman equation (6.29)** (Miao, p. 172): for `t < T`,
`V_t(x, z) = sup_{a ∈ Γ(x, z)} u_t(x, z, a) + β ∫ V_{t+1}(φ(x, a, z, z′), z′) Q(z, dz′)`. -/
theorem V_succ {t : ℕ} (ht : t < M.T) : M.V t = M.bellman t (M.V (t + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, M.T - t = k + 1 := ⟨M.T - t - 1, by omega⟩
  have h1 : M.T - (k + 1) = t := by omega
  have h2 : M.T - (t + 1) = k := by omega
  simp only [V, hk, W, h1, h2]

theorem V_succ_apply {t : ℕ} (ht : t < M.T) (x : E) (z : Z) :
    M.V t x z = sSup (M.obj t (M.V (t + 1)) x z '' M.Γ x z) := by
  rw [M.V_succ ht]
  rfl

/-- The **policy correspondence** `G_t` (Miao, p. 174): the maximizers in (6.29). -/
def G (t : ℕ) (x : E) (z : Z) : Set F :=
  {a | a ∈ M.Γ x z ∧ M.obj t (M.V (t + 1)) x z a = M.V t x z}

/-- A selection from `G_t`; when `G_t` is single-valued (Theorem 6.4.3) it is the **policy
function** `g_t` of Miao, p. 178. -/
noncomputable def g [Nonempty F] (t : ℕ) (x : E) (z : Z) : F :=
  Classical.epsilon fun a => a ∈ M.G t x z

theorem g_mem [Nonempty F] {t : ℕ} {x : E} {z : Z} (h : (M.G t x z).Nonempty) :
    M.g t x z ∈ M.G t x z :=
  Classical.epsilon_spec (p := fun a => a ∈ M.G t x z) h

/-! ### The control problem (6.28) on a filtered probability space -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The states generated from `x₀` by a plan `a` and the shocks `z` through the state transition
equation (5.14): `x₀` given, `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})`. -/
def path (z : ℕ → Ω → Z) (a : ℕ → Ω → F) (x₀ : E) : ℕ → Ω → E
  | 0 => fun _ => x₀
  | t + 1 => fun ω => M.φ (path z a x₀ t ω) (a t ω) (z t ω) (z (t + 1) ω)

/-- A **feasible plan** (Miao, p. 172): `a_t` is `ℱ_t`-measurable and `a_t ∈ Γ(x_t, z_t)` for
`t < T`. -/
def IsPlan [MeasurableSpace F] (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (x₀ : E)
    (a : ℕ → Ω → F) : Prop :=
  (∀ t, Measurable[ℱ t] (a t)) ∧ ∀ t < M.T, ∀ ω, a t ω ∈ M.Γ (M.path z a x₀ t ω) (z t ω)

/-- **The objective (6.28) in Bolza form** (Miao, p. 172):
`E[Σ_{t<T} βᵗ u_t(x_t, z_t, a_t) + β^T u_T(x_T, z_T)]`. -/
noncomputable def bolza (P : Measure Ω) (z : ℕ → Ω → Z) (a : ℕ → Ω → F) (x₀ : E) : ℝ :=
  ∫ ω, ((∑ t ∈ Finset.range M.T, M.β ^ t * M.u t (M.path z a x₀ t ω) (z t ω) (a t ω)) +
    M.β ^ M.T * M.uT (M.path z a x₀ M.T ω) (z M.T ω)) ∂P

/-- The plan and the states generated by the policy functions (Miao, p. 178):
`a_t = g_t(x_t, z_t)`, `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})`, `x₀` given. -/
noncomputable def policyPath [Nonempty F] (z : ℕ → Ω → Z) (x₀ : E) : ℕ → Ω → E
  | 0 => fun _ => x₀
  | t + 1 => fun ω => M.φ (policyPath z x₀ t ω) (M.g t (policyPath z x₀ t ω) (z t ω))
      (z t ω) (z (t + 1) ω)

/-- Miao, p. 178: the states generated by the policy functions are the states of the plan
`a_t = g_t(x_t, z_t)` under (5.14). -/
theorem policyPath_eq [Nonempty F] (z : ℕ → Ω → Z) (x₀ : E) (t : ℕ) :
    M.policyPath z x₀ t =
      M.path z (fun s ω => M.g s (M.policyPath z x₀ s ω) (z s ω)) x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext ω
    simp only [policyPath, path]
    rw [← ih]

/-! ### Assumptions 6.4.1–6.4.14 -/

/-- The correspondence `Γ` on the state space `X × Z` (as a subtype of `E × Z`). -/
def Γs (s : ↥(M.X ×ˢ (Set.univ : Set Z))) : Set F := M.Γ s.1.1 s.1.2

/-- The policy correspondence `G_t` on the state space `X × Z`. -/
def Gs (t : ℕ) (s : ↥(M.X ×ˢ (Set.univ : Set Z))) : Set F := M.G t s.1.1 s.1.2

/-- **Assumption 6.4.1** (Miao, p. 173): `X` is a convex Borel set. -/
def Assumption641 [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] : Prop :=
  Convex ℝ M.X ∧ MeasurableSet M.X

/-- **Assumption 6.4.2** (Miao, p. 173): `A` is a convex Borel set. -/
def Assumption642 [AddCommGroup F] [Module ℝ F] [MeasurableSpace F] : Prop :=
  Convex ℝ M.A ∧ MeasurableSet M.A

/-- **Assumption 6.4.3 (i)** (Miao, p. 173): `Z` is countable, with the discrete topology and
all subsets measurable. -/
def Assumption643i (Z' : Type*) [TopologicalSpace Z'] [MeasurableSpace Z'] : Prop :=
  Countable Z' ∧ DiscreteTopology Z' ∧ DiscreteMeasurableSpace Z'

/-- **Assumption 6.4.3 (ii)** (Miao, p. 173): `Z` is compact with its Borel sets and `Q` has the
Feller property. -/
def Assumption643ii [TopologicalSpace Z] : Prop :=
  CompactSpace Z ∧ BorelSpace Z ∧ IsFeller M.Q

/-- **Assumption 6.4.4** (Miao, p. 173): `Γ : X × Z → A` is nonempty, compact-valued and
continuous (l.h.c. and u.h.c.; `IsLHC` includes nonemptiness). -/
def Assumption644 [MetricSpace E] [MetricSpace F] [MetricSpace Z] : Prop :=
  (∀ x ∈ M.X, ∀ z, M.Γ x z ⊆ M.A) ∧
    ∀ s, IsCompact (M.Γs s) ∧ IsLHC M.Γs s ∧ IsUHC M.Γs s

/-- **Assumption 6.4.5** (Miao, p. 173): `φ : X × A × Z × Z → X` is continuous. -/
def Assumption645 [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z] : Prop :=
  (∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) ∧
    ContinuousOn (fun p : E × F × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
      (M.X ×ˢ M.A ×ˢ Set.univ)

/-- **Assumption 6.4.6** (Miao, p. 173): `u_t : X × Z × A → ℝ` (`t < T`) and `u_T : X × Z → ℝ`
are continuous. -/
def Assumption646 [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z] : Prop :=
  (∀ t < M.T, ContinuousOn (fun p : E × Z × F => M.u t p.1 p.2.1 p.2.2)
      (M.X ×ˢ Set.univ ×ˢ M.A)) ∧
    ContinuousOn (fun p : E × Z => M.uT p.1 p.2) (M.X ×ˢ Set.univ)

/-- **Assumption 6.4.7** (Miao, p. 175): `u_T(·, z)` and `u_t(·, z, a)` are strictly increasing
on `X`. -/
def Assumption647 [Preorder E] : Prop :=
  (∀ z, StrictMonoOn (fun x => M.uT x z) M.X) ∧
    ∀ t < M.T, ∀ z, ∀ a ∈ M.A, StrictMonoOn (fun x => M.u t x z a) M.X

/-- **Assumption 6.4.8** (Miao, p. 175): `Γ(·, z)` is increasing: `x ≤ x′` implies
`Γ(x, z) ⊆ Γ(x′, z)`. -/
def Assumption648 [Preorder E] : Prop :=
  ∀ z, ∀ x ∈ M.X, ∀ x' ∈ M.X, x ≤ x' → M.Γ x z ⊆ M.Γ x' z

/-- **Assumption 6.4.9** (Miao, p. 175): `φ(·, a, z, z′)` is increasing. -/
def Assumption649 [Preorder E] : Prop :=
  ∀ a ∈ M.A, ∀ z z', MonotoneOn (fun x => M.φ x a z z') M.X

/-- **Assumption 6.4.10** (Miao, p. 176): `u_T(·, z)` is strictly concave and `u_t(·, z, ·)` is
concave on `X × A`, strictly when `x ≠ x′`. -/
def Assumption6410 [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] : Prop :=
  (∀ z, StrictConcaveOn ℝ M.X fun x => M.uT x z) ∧
    ∀ t < M.T, ∀ z, ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η →
      θ + η = 1 →
      θ * M.u t x z a + η * M.u t x' z a' ≤ M.u t (θ • x + η • x') z (θ • a + η • a') ∧
      (x ≠ x' → θ * M.u t x z a + η * M.u t x' z a' < M.u t (θ • x + η • x') z (θ • a + η • a'))

/-- **Assumption 6.4.11** (Miao, p. 176): `a ∈ Γ(x, z)`, `a′ ∈ Γ(x′, z)` imply
`θa + (1 − θ)a′ ∈ Γ(θx + (1 − θ)x′, z)`. -/
def Assumption6411 [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] : Prop :=
  ∀ z, ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.Γ x z, ∀ a' ∈ M.Γ x' z, ∀ θ η : ℝ, 0 < θ → 0 < η →
    θ + η = 1 → θ • a + η • a' ∈ M.Γ (θ • x + η • x') z

/-- **Assumption 6.4.12** (Miao, p. 176): `φ(·, ·, z, z′)` is concave on `X × A` (for the order
of `E`; componentwise on `ℝ^{n_x}`). -/
def Assumption6412 [AddCommGroup E] [Module ℝ E] [PartialOrder E] [AddCommGroup F]
    [Module ℝ F] : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η →
    θ + η = 1 → θ • M.φ x a z z' + η • M.φ x' a' z z' ≤ M.φ (θ • x + η • x') (θ • a + η • a') z z'

/-- **Assumption 6.4.13** (Miao, p. 178): `u_T(·, z)` is differentiable on `int X` and
`u_t(·, z, ·)` is continuously differentiable on `int(X × A)`. -/
def Assumption6413 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  (∀ z, DifferentiableOn ℝ (fun x => M.uT x z) (interior M.X)) ∧
    ∀ t < M.T, ∀ z, ContDiffOn ℝ 1 (fun p : E × F => M.u t p.1 z p.2) (interior (M.X ×ˢ M.A))

/-- **Assumption 6.4.14** (Miao, p. 178): `φ(·, ·, z, z′)` is differentiable on `int(X × A)`. -/
def Assumption6414 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  ∀ z z', DifferentiableOn ℝ (fun p : E × F => M.φ p.1 p.2 z z') (interior (M.X ×ˢ M.A))

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 6.4.1: the expected continuation value is continuous

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCLemma641`), namespace renamed.

Miao, §6.4, p. 174. For continuous `f : X × Z → ℝ`,
`h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z`. The book refers
to SLP Lemmas 9.5 and 9.5′.

* `lemma_6_4_1_compact`: case (ii) of Assumption 6.4.3 (`Z` compact, `Q` Feller), for every
  continuous `f`, bounded or not. It rests on `continuous_mop_of_compact`, SLP's Lemma 9.5(b)
  (`lemma_9_5_compact`) without the bound on `f`: on a compact `Z` each section `f(w, ·)` is
  bounded, which is all the proof needs.
* `lemma_6_4_1_countable`: case (i) (`Z` discrete with all subsets measurable), for **bounded**
  continuous `f`, by SLP's `lemma_9_5'` and `lemma_9_5_discrete` applied with the action
  `(a, z)`, since here `φ` also depends on the current shock. Countability of `Z` is not needed.
* **Correction.** In case (i) the lemma is false for unbounded `f`
  (`lemma_6_4_1_countable_counterexample`): with `Z = ℕ`, `Q(z, {n}) = 2^{-(n+1)}`, `φ = x` and
  `f(x, n) = 2^{n+1} max(0, 1 − |(n+1)x − 1|)`, each `f(x, ·)` vanishes off a finite set, yet
  `h(1/(m+1)) ≥ 1` for all `m` while `h(0) = 0`. Theorem 6.4.1 in case (i) therefore needs
  bounded rewards (`OCExistence`).
* `ExpCont P`: the conclusion of Lemma 6.4.1 (continuity and integrability of the sections) for
  the functions `f` with property `P`; `expCont_compact` (all `f`) and `expCont_countable`
  (bounded `f`) are the two cases. The later theorems are proved for any `P`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

variable {Z : Type*} [MeasurableSpace Z]

/-- SLP's Lemma 9.5(b) without the bound: if `Z` is compact and `Q` is Feller, then for every
continuous `f : W × Z → ℝ` the sections `f(w, ·)` are integrable and
`(w, z) ↦ ∫ f(w, z′) Q(z, dz′)` is continuous. -/
theorem continuous_mop_of_compact {W : Type*} [TopologicalSpace W] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {f : W × Z → ℝ} (hf : Continuous f) :
    Continuous (mop Q f) ∧ ∀ w z, Integrable (fun z' => f (w, z')) (Q z) := by
  have hsec : ∀ w, Continuous fun z' => f (w, z') := fun w => hf.comp (Continuous.prodMk_right w)
  have hbdd : ∀ w, ∃ B, ∀ z', |f (w, z')| ≤ B := fun w => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hsec w).continuousOn
    exact ⟨B, fun z' => by rw [← Real.norm_eq_abs]; exact hB z' (Set.mem_univ _)⟩
  have hint : ∀ w z, Integrable (fun z' => f (w, z')) (Q z) := fun w z =>
    integrable_of_abs_le (hsec w).measurable (hbdd w).choose_spec
  refine ⟨?_, hint⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨w, z⟩
  set g : C(W, C(Z, ℝ)) := (ContinuousMap.mk f hf).curry with hgdef
  set k : Z → ℝ := markovOpR Q fun z' => f (w, z') with hkdef
  have hk : Continuous k := hQ _ (hsec w) (hbdd w)
  have hdist : Tendsto (fun p : W × Z => dist (g p.1) (g w)) (𝓝 (w, z)) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((g.continuous.tendsto w).comp continuous_fst.continuousAt)
  have hA : Tendsto (fun p : W × Z => mop Q f p - k p.2) (𝓝 (w, z)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => ?_) hdist
    rw [mop, hkdef, markovOpR, ← integral_sub (hint p.1 p.2) (hint w p.2)]
    have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := dist (g p.1) (g w))
      (f := fun z' => f (p.1, z') - f (w, z')) (Eventually.of_forall fun z' => by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := g p.1) (g := g w) z')
    simpa [measureReal_def] using this
  have hB' : Tendsto (fun p : W × Z => k p.2) (𝓝 (w, z)) (𝓝 (k z)) :=
    (hk.tendsto z).comp continuous_snd.continuousAt
  have hsum := hA.add hB'
  rw [zero_add] at hsum
  have heq : (fun p : W × Z => mop Q f p - k p.2 + k p.2) = mop Q f :=
    funext fun p => sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

namespace OCModel

variable {E F : Type*} (M : OCModel E F Z)

/-- The conclusion of Lemma 6.4.1 for the functions `f` with property `P`: the sections
`z′ ↦ f(φ(x, a, z, z′), z′)` are integrable and `h(x, a, z)` is continuous on `X × A × Z`. -/
def ExpCont [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    (P : (E → Z → ℝ) → Prop) : Prop :=
  ∀ f, P f → ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ) →
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z)

/-- **Lemma 6.4.1** (Miao, p. 174), case (ii) of Assumption 6.4.3: if `Z` is compact and `Q`
is Feller, then for every continuous `f` on `X × Z` the function
`h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z` (and its
integrands are integrable). No bound on `f` is needed. -/
theorem lemma_6_4_1_compact [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] [IsMarkovKernel M.Q] (hQ : IsFeller M.Q)
    (h645 : M.Assumption645) {f : E → Z → ℝ}
    (hf : ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ)) :
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z) := by
  set S := M.X ×ˢ M.A ×ˢ (Set.univ : Set Z)
  -- the composite integrand on `S × Z`
  have hφc : Continuous fun q : S × Z => M.φ q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2 := by
    refine h645.2.comp_continuous (Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst).fst
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst).snd.fst
        (Continuous.prodMk (continuous_subtype_val.comp continuous_fst).snd.snd
          continuous_snd))) fun q => ?_
    exact ⟨q.1.2.1, q.1.2.2.1, Set.mem_univ _⟩
  have hψ : Continuous fun q : S × Z => f (M.φ q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2) q.2 := by
    refine hf.comp_continuous (hφc.prodMk continuous_snd) fun q => ⟨?_, Set.mem_univ _⟩
    exact h645.1 _ q.1.2.1 _ q.1.2.2.1 _ _
  obtain ⟨hM, hint⟩ := continuous_mop_of_compact M.Q hQ hψ
  refine ⟨?_, fun x hx a ha z => hint ⟨(x, a, z), hx, ha, Set.mem_univ _⟩ z⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact hM.comp (continuous_id.prodMk (continuous_subtype_val.snd.snd))

/-- `ExpCont` holds for all functions in case (ii) of Assumption 6.4.3 (Lemma 6.4.1). -/
theorem expCont_compact [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] [IsMarkovKernel M.Q] (hQ : IsFeller M.Q)
    (h645 : M.Assumption645) : M.ExpCont fun _ => True := fun _ _ hf =>
  M.lemma_6_4_1_compact hQ h645 hf

/-- **Lemma 6.4.1** (Miao, p. 174), case (i) of Assumption 6.4.3, for bounded `f`: if `Z` has the
discrete topology and all its subsets are measurable, then for every bounded continuous `f` on
`X × Z`, `h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z`. The
proof applies SLP's Lemma 9.5′ (`lemma_9_5'`) with the action `(a, z)` and Lemma 9.5(a). -/
theorem lemma_6_4_1_countable [MetricSpace E] [MetricSpace F] [MetricSpace Z] [DiscreteTopology Z]
    [DiscreteMeasurableSpace Z] [IsMarkovKernel M.Q] (h645 : M.Assumption645) {f : E → Z → ℝ}
    (hf : ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ)) {B : ℝ}
    (hB : ∀ x ∈ M.X, ∀ z, |f x z| ≤ B) :
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z) := by
  -- SLP's state space `↥X`, action space `↥A × Z`, law of motion `φ′`
  let φ' : ↥M.X × (↥M.A × Z) × Z → ↥M.X := fun q =>
    ⟨M.φ q.1 q.2.1.1 q.2.1.2 q.2.2, h645.1 _ q.1.2 _ q.2.1.1.2 _ _⟩
  let f' : ↥M.X × Z → ℝ := fun p => f p.1 p.2
  have hf' : Continuous f' :=
    hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨p.1.2, Set.mem_univ _⟩
  have hφ' : ContinuousOn (fun q : (↥M.X × (↥M.A × Z)) × Z => φ' (q.1.1, q.1.2, q.2))
      (Set.univ ×ˢ Set.univ) := by
    refine Continuous.continuousOn (Continuous.subtype_mk ?_ _)
    refine h645.2.comp_continuous ((continuous_subtype_val.comp continuous_fst.fst).prodMk
      ((continuous_subtype_val.comp continuous_fst.snd.fst).prodMk
        (continuous_fst.snd.snd.prodMk continuous_snd))) fun q => ?_
    exact ⟨q.1.1.2, q.1.2.1.2, Set.mem_univ _⟩
  have hQ : PreservesBC (↥(Set.univ : Set (↥M.X × (↥M.A × Z)))) M.Q :=
    lemma_9_5_discrete M.Q
  have h95 := lemma_9_5' (Set.univ : Set (↥M.X × (↥M.A × Z))) hφ' M.Q hQ hf'
    (B := B) fun p => hB _ p.1.2 _
  refine ⟨?_, fun x hx a ha z => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hmap : Continuous fun w : ↥(M.X ×ˢ M.A ×ˢ (Set.univ : Set Z)) =>
        (((⟨w.1.1, w.2.1⟩ : ↥M.X), ((⟨w.1.2.1, w.2.2.1⟩ : ↥M.A), w.1.2.2)), w.1.2.2) := by
      refine Continuous.prodMk (Continuous.prodMk ?_ (Continuous.prodMk ?_
        continuous_subtype_val.snd.snd)) continuous_subtype_val.snd.snd
      · exact continuous_subtype_val.fst.subtype_mk _
      · exact continuous_subtype_val.snd.fst.subtype_mk _
    rw [continuousOn_iff_continuous_domRestrict] at h95
    exact h95.comp (hmap.subtype_mk fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)
  · exact integrable_of_abs_le Measurable.of_discrete fun z' =>
      hB _ (h645.1 x hx a ha z z') z'

/-- `ExpCont` holds for the bounded functions in case (i) of Assumption 6.4.3 (Lemma 6.4.1). -/
theorem expCont_countable [MetricSpace E] [MetricSpace F] [MetricSpace Z] [DiscreteTopology Z]
    [DiscreteMeasurableSpace Z] [IsMarkovKernel M.Q] (h645 : M.Assumption645) :
    M.ExpCont fun f => ∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B := fun _ ⟨_, hB⟩ hf =>
  M.lemma_6_4_1_countable h645 hf hB

end OCModel

/-- The tent `ψ(s) = max(0, 1 − |s − 1|)` used in the counterexample. -/
noncomputable def oc_tent (s : ℝ) : ℝ := max 0 (1 - |s - 1|)

/-- The unbounded continuous function of the counterexample:
`f(x, n) = 2^{n+1} ψ((n + 1)x)`. -/
noncomputable def oc_spike (x : ℝ) (n : ℕ) : ℝ := 2 ^ (n + 1) * oc_tent ((n + 1) * x)

theorem oc_tent_eq_zero {s : ℝ} (hs : s ≤ 0 ∨ 2 ≤ s) : oc_tent s = 0 := by
  have : 1 ≤ |s - 1| := by
    rcases hs with hs | hs
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp only [oc_tent]
  exact max_eq_left (by linarith)

theorem oc_tent_nonneg (s : ℝ) : 0 ≤ oc_tent s := le_max_left _ _

theorem oc_tent_le_one (s : ℝ) : oc_tent s ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg (s - 1)])

theorem oc_spike_bound (x : ℝ) (n : ℕ) : |oc_spike x n| ≤ 2 ^ (⌈2 / x⌉₊ + 1) := by
  rw [oc_spike, abs_of_nonneg (mul_nonneg (by positivity) (oc_tent_nonneg _))]
  rcases le_or_gt x 0 with hx | hx
  · rw [oc_tent_eq_zero (Or.inl (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx))]
    simp
  rcases lt_or_ge n ⌈2 / x⌉₊ with hn | hn
  · calc (2 : ℝ) ^ (n + 1) * oc_tent ((n + 1) * x) ≤ 2 ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (oc_tent_le_one _) (by positivity)
      _ ≤ 2 ^ (⌈2 / x⌉₊ + 1) := by
          rw [mul_one]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  · have h1 : 2 / x ≤ (n : ℝ) := (Nat.ceil_le.1 hn)
    have h2 : 2 ≤ ((n : ℝ) + 1) * x := by
      have := (div_le_iff₀ hx).1 h1
      nlinarith
    rw [oc_tent_eq_zero (Or.inr h2)]
    simp

/-- The success probability `1/2` of the geometric law in the counterexample. -/
noncomputable def oc_half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The model of the counterexample: `X = A = ℝ`, `Z = ℕ`, `Q(z, ·)` geometric with
`Q(z, {n}) = 2^{-(n+1)}`, `φ(x, a, z, z′) = x`. -/
noncomputable def oc_spikeModel : OCModel ℝ ℝ ℕ :=
  ⟨Set.univ, Set.univ, Kernel.const ℕ (geometricMeasure oc_half), fun _ _ => Set.univ,
    fun x _ _ _ => x, fun _ _ _ _ => 0, fun _ _ => 0, 1, 1⟩

/-- **Counterexample to Lemma 6.4.1 in case (i) for unbounded `f`** (Miao, p. 174). Take
`X = A = ℝ`, `Z = ℕ` with `Q(z, {n}) = 2^{-(n+1)}` (the geometric law), `φ(x, a, z, z′) = x` and
the continuous `f(x, n) = 2^{n+1} max(0, 1 − |(n + 1)x − 1|)`. Assumptions 6.4.1, 6.4.2, 6.4.3(i)
and 6.4.5 hold and every integrand is integrable (each `f(x, ·)` is bounded), but `h` is not
continuous: `h(1/(m+1), a, z) ≥ 1` for all `m` while `h(0, a, z) = 0`. -/
theorem lemma_6_4_1_countable_counterexample :
    ∃ (M : OCModel ℝ ℝ ℕ) (f : ℝ → ℕ → ℝ), IsMarkovKernel M.Q ∧ M.Assumption641 ∧
      M.Assumption642 ∧ OCModel.Assumption643i ℕ ∧ M.Assumption645 ∧
      ContinuousOn (fun p : ℝ × ℕ => f p.1 p.2) (M.X ×ˢ Set.univ) ∧
      (∀ x a z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z)) ∧
      ¬ ContinuousOn (fun p : ℝ × ℝ × ℕ => M.cont f p.1 p.2.1 p.2.2)
        (M.X ×ˢ M.A ×ˢ Set.univ) := by
  have hp : oc_half ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    norm_num [oc_half] at this
  have hQ : ∀ z, oc_spikeModel.Q z = geometricMeasure oc_half := fun z => Kernel.const_apply _ _
  have hint : ∀ x, Integrable (oc_spike x) (geometricMeasure oc_half) := fun x =>
    integrable_of_abs_le Measurable.of_discrete (oc_spike_bound x)
  have hcont : ∀ x a z, oc_spikeModel.cont oc_spike x a z =
      ∫ n, oc_spike x n ∂geometricMeasure oc_half := fun x a z => by
    simp only [OCModel.cont, hQ]
    rfl
  have hX : oc_spikeModel.X = Set.univ := rfl
  have hA : oc_spikeModel.A = Set.univ := rfl
  have h641 : oc_spikeModel.Assumption641 := ⟨(by rw [hX]; exact convex_univ),
    (by rw [hX]; exact MeasurableSet.univ)⟩
  have h642 : oc_spikeModel.Assumption642 := ⟨(by rw [hA]; exact convex_univ),
    (by rw [hA]; exact MeasurableSet.univ)⟩
  have h645 : oc_spikeModel.Assumption645 :=
    ⟨fun _ _ _ _ _ _ => by rw [hX]; exact Set.mem_univ _, continuous_fst.continuousOn⟩
  refine ⟨oc_spikeModel, oc_spike, ⟨fun z => by rw [hQ]; infer_instance⟩, h641, h642,
    ⟨inferInstance, inferInstance, inferInstance⟩, h645, ?_, fun x a z => by
      rw [hQ]; exact hint x, ?_⟩
  · refine Continuous.continuousOn (continuous_prod_of_discrete_right.2 fun n => ?_)
    simp only [oc_spike, oc_tent]
    fun_prop
  · intro hc
    rw [hX, hA, Set.univ_prod_univ, Set.univ_prod_univ, continuousOn_univ] at hc
    -- along `x_m = 1/(m+1) → 0`, `h(x_m) ≥ 1`, but `h(0) = 0`
    have h0 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1), (0 : ℝ), (0 : ℕ))) atTop
        (𝓝 (0, 0, 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.prodMk_nhds tendsto_const_nhds
    have hlim := (hc.tendsto _).comp h0
    have hzero : oc_spikeModel.cont oc_spike 0 0 0 = 0 := by
      rw [hcont]
      have : ∀ n, oc_spike 0 n = 0 := fun n => by
        simp only [oc_spike, mul_zero, oc_tent_eq_zero (le_refl (0 : ℝ) |> Or.inl)]
      simp [this]
    have hone : ∀ m : ℕ, 1 ≤ oc_spikeModel.cont oc_spike (1 / ((m : ℝ) + 1)) 0 0 := fun m => by
      rw [hcont]
      have hle := setIntegral_le_integral (s := {m}) (hint (1 / ((m : ℝ) + 1)))
        (Eventually.of_forall fun n => mul_nonneg (by positivity) (oc_tent_nonneg _))
      rw [integral_singleton, geometricMeasure_real_singleton hp] at hle
      refine le_trans (le_of_eq ?_) hle
      have hm : ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) = 1 := by field_simp
      simp only [oc_spike, hm, oc_tent, sub_self, abs_zero, sub_zero, oc_half, smul_eq_mul]
      rw [max_eq_right zero_le_one, mul_one, pow_succ]
      norm_num
      have : ((1 : ℝ) / 2) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
      linear_combination -this
    have := ge_of_tendsto hlim (Eventually.of_forall hone)
    simp only at this
    rw [hzero] at this
    norm_num at this

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.1: existence

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCExistence`), namespace renamed.

Miao, §6.4, pp. 174–175. Under Assumptions 6.4.1–6.4.6, the solution `V_t` of the Bellman
equation (6.29) is continuous and the policy correspondence `G_t` is nonempty, compact-valued
and upper hemicontinuous, by backward induction with Lemma 6.4.1 and the Theorem of the Maximum
(SLP Theorem 3.6, `theorem_3_6`); each `G_t` then has a measurable selection (SLP Theorem 7.6,
`theorem_7_6`).

* `theorem_6_4_1`: the induction for any class `P` of functions for which Lemma 6.4.1 holds
  (`ExpCont P`) and which contains every `V_t`.
* `theorem_6_4_1_compact`: case (ii) of Assumption 6.4.3 (`Z` compact, `Q` Feller).
* `theorem_6_4_1_countable`: case (i) (`Z` discrete). **Correction:** here Lemma 6.4.1 needs
  bounded functions (`lemma_6_4_1_countable_counterexample`), so we add that the rewards are
  bounded on `X × Z × A`; then every `V_t` is bounded (`V_bounded`).
* `theorem_6_4_1_selection`: for actions in `ℝ^m`, each `G_t` has a measurable selection.
* `objS`, `Gs_eq_argmax`: the objective on `(X × Z) × A` and `G_t` as its argmax correspondence.

Assumptions 6.4.1–6.4.2 (convexity) and 5.1.2 (`β ∈ (0, 1)`) are not used. The state space
`X × Z` is the subtype `↥(X ×ˢ univ)` of `E × Z`; `E`, `F`, `Z` are metric spaces (the book's
Borel sets in Euclidean spaces).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] (M : OCModel E F Z)

/-- The objective of (6.29) on the graph of `Γ`, as a function on `(X × Z) × A`. -/
noncomputable def objS (t : ℕ) (f : E → Z → ℝ) (p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F) : ℝ :=
  M.obj t f p.1.1.1 p.1.1.2 p.2

theorem maxValue_objS (t : ℕ) (f : E → Z → ℝ) (s : ↥(M.X ×ˢ (Set.univ : Set Z))) :
    maxValue (M.objS t f) M.Γs s = M.bellman t f s.1.1 s.1.2 := rfl

theorem V_eq_maxValue {t : ℕ} (ht : t < M.T) (s : ↥(M.X ×ˢ (Set.univ : Set Z))) :
    M.V t s.1.1 s.1.2 = maxValue (M.objS t (M.V (t + 1))) M.Γs s := by
  rw [maxValue_objS, M.V_succ ht]

/-- `G_t` is the argmax correspondence of the objective (6.29). -/
theorem Gs_eq_argmax {t : ℕ} (ht : t < M.T) :
    M.Gs t = argmax (M.objS t (M.V (t + 1))) M.Γs := by
  funext s
  ext a
  change a ∈ M.Γ s.1.1 s.1.2 ∧ M.obj t (M.V (t + 1)) s.1.1 s.1.2 a = M.V t s.1.1 s.1.2 ↔
    a ∈ M.Γs s ∧ M.objS t (M.V (t + 1)) (s, a) = maxValue (M.objS t (M.V (t + 1))) M.Γs s
  rw [← M.V_eq_maxValue ht]
  rfl

/-- The bound `|∫ f| ≤ C` for a probability measure and `|f| ≤ C`. -/
theorem oc_abs_integral_le {μ : Measure Z} [IsProbabilityMeasure μ] {f : Z → ℝ} {C : ℝ}
    (hf : ∀ z, |f z| ≤ C) : |∫ z, f z ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := C) (f := f)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf z)
  simpa [Real.norm_eq_abs, measureReal_def] using this

variable [MetricSpace E] [MetricSpace F] [MetricSpace Z]

/-- The objective of (6.29) is continuous on the graph of `Γ` when `u_t` is continuous and the
continuation value `h` of Lemma 6.4.1 is. -/
theorem continuousOn_objS (h644 : M.Assumption644) {t : ℕ}
    (hu : ContinuousOn (fun p : E × Z × F => M.u t p.1 p.2.1 p.2.2) (M.X ×ˢ Set.univ ×ˢ M.A))
    {f : E → Z → ℝ}
    (hc : ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ)) :
    ContinuousOn (M.objS t f) (graph M.Γs) := by
  have hA : ∀ p ∈ graph M.Γs, p.2 ∈ M.A := fun p hp => h644.1 _ p.1.2.1 _ hp
  have h1 : ContinuousOn (fun p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F =>
      M.u t p.1.1.1 p.1.1.2 p.2) (graph M.Γs) :=
    hu.comp ((continuous_subtype_val.comp continuous_fst).fst.prodMk
      ((continuous_subtype_val.comp continuous_fst).snd.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨p.1.2.1, Set.mem_univ _, hA p hp⟩
  have h2 : ContinuousOn (fun p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F =>
      M.cont f p.1.1.1 p.2 p.1.1.2) (graph M.Γs) :=
    hc.comp ((continuous_subtype_val.comp continuous_fst).fst.prodMk
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst).snd)).continuousOn
      fun p hp => ⟨p.1.2.1, hA p hp, Set.mem_univ _⟩
  exact h1.add (continuousOn_const.mul h2)

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), for any class `P` of functions for which the
conclusion of Lemma 6.4.1 holds and which contains every `V_t`. Under Assumptions 6.4.4 and
6.4.6, each `V_t` is continuous on `X × Z` (`t ≤ T`) and each `G_t` (`t < T`) is nonempty,
compact-valued and upper hemicontinuous. -/
theorem theorem_6_4_1 (P : (E → Z → ℝ) → Prop) (hE : M.ExpCont P)
    (hP : ∀ t ≤ M.T, P (M.V t)) (h644 : M.Assumption644) (h646 : M.Assumption646) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have hcpt : ∀ s, IsCompact (M.Γs s) := fun s => (h644.2 s).1
  have hl : ∀ s, IsLHC M.Γs s := fun s => (h644.2 s).2.1
  have hu : ∀ s, IsUHC M.Γs s := fun s => (h644.2 s).2.2
  -- the step: continuity of `V_{t+1}` gives the Theorem of the Maximum at `t`
  have hstep : ∀ t < M.T,
      ContinuousOn (fun p : E × Z => M.V (t + 1) p.1 p.2) (M.X ×ˢ Set.univ) →
      ContinuousOn (M.objS t (M.V (t + 1))) (graph M.Γs) := fun t ht hV =>
    M.continuousOn_objS h644 (h646.1 t ht) (hE _ (hP (t + 1) ht) hV).1
  have hcont : ∀ k ≤ M.T,
      ContinuousOn (fun p : E × Z => M.V (M.T - k) p.1 p.2) (M.X ×ˢ Set.univ) := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, M.V_T_eq]; exact h646.2
    | succ k ih =>
      intro hk
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      have hV := ih (by omega)
      rw [← he] at hV
      have h36 := theorem_3_6 (hstep _ ht hV) hcpt hl hu
      rw [continuousOn_iff_continuous_domRestrict]
      refine h36.1.congr fun s => ?_
      exact (M.V_eq_maxValue ht s).symm
  have hcont' : ∀ t ≤ M.T,
      ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ) := fun t ht => by
    have := hcont (M.T - t) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self ht] at this
  refine ⟨hcont', fun t ht s => ?_⟩
  rw [M.Gs_eq_argmax ht]
  exact (theorem_3_6 (hstep t ht (hcont' (t + 1) ht)) hcpt hl hu).2 s

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), case (ii) of Assumption 6.4.3: if `Z` is
compact and `Q` is Feller, then under Assumptions 6.4.4–6.4.6 every `V_t` is continuous and
every `G_t` is nonempty, compact-valued and u.h.c. -/
theorem theorem_6_4_1_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  exact M.theorem_6_4_1 _ (M.expCont_compact h643.2.2 h645) (fun _ _ => trivial) h644 h646

/-- With bounded rewards, every `V_t` is bounded on `X × Z` (Assumptions 6.4.4–6.4.5). -/
theorem V_bounded [IsMarkovKernel M.Q] (h644 : M.Assumption644)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    ∀ t ≤ M.T, ∃ C, ∀ x ∈ M.X, ∀ z, |M.V t x z| ≤ C := by
  have key : ∀ k ≤ M.T, ∃ C, ∀ x ∈ M.X, ∀ z, |M.V (M.T - k) x z| ≤ C := by
    intro k
    induction k with
    | zero => intro _; exact ⟨B, fun x hx z => by rw [Nat.sub_zero, M.V_T_eq]; exact huT x hx z⟩
    | succ k ih =>
      intro hk
      obtain ⟨C, hC⟩ := ih (by omega)
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      refine ⟨B + |M.β| * C, fun x hx z => ?_⟩
      rw [M.V_succ_apply ht]
      have hobj : ∀ a ∈ M.Γ x z, |M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z a| ≤
          B + |M.β| * C := fun a ha => by
        have haA := h644.1 x hx z ha
        have hcont : |M.cont (M.V (M.T - (k + 1) + 1)) x a z| ≤ C := by
          rw [he]
          exact oc_abs_integral_le fun z' => hC _ (h645X x hx a haA z z') z'
        refine (abs_add_le _ _).trans (add_le_add (hu _ ht x hx z a haA) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hcont (abs_nonneg _)
      have hne : (M.Γ x z).Nonempty := (h644.2 ⟨(x, z), hx, Set.mem_univ _⟩).2.1.1
      have hS : (M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z '' M.Γ x z).Nonempty :=
        hne.image _
      have hbdd : BddAbove (M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z '' M.Γ x z) :=
        ⟨B + |M.β| * C, by rintro _ ⟨a, ha, rfl⟩; exact (abs_le.1 (hobj a ha)).2⟩
      obtain ⟨a, ha⟩ := hne
      rw [abs_le]
      constructor
      · exact (abs_le.1 (hobj a ha)).1.trans (le_csSup hbdd ⟨a, ha, rfl⟩)
      · exact csSup_le hS (by rintro _ ⟨b, hb, rfl⟩; exact (abs_le.1 (hobj b hb)).2)
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), case (i) of Assumption 6.4.3, corrected: if `Z`
is discrete with all subsets measurable and the rewards are **bounded** on `X × Z × A`, then
under Assumptions 6.4.4–6.4.6 every `V_t` is continuous and every `G_t` is nonempty,
compact-valued and u.h.c. (Without the bound Lemma 6.4.1 fails:
`lemma_6_4_1_countable_counterexample`.) -/
theorem theorem_6_4_1_countable [IsMarkovKernel M.Q] (h643 : Assumption643i Z)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  exact M.theorem_6_4_1 _ (M.expCont_countable h645) (M.V_bounded h644 h645.1 hu huT) h644 h646

/-- **Measurable selections** (Miao, p. 175): with actions in `ℝ^m`, under the hypotheses of
`theorem_6_4_1` each `G_t` has a measurable selection (SLP Theorem 7.6), so Theorem 6.3.2
applies. -/
theorem theorem_6_4_1_selection {m : ℕ} [MeasurableSpace E] [BorelSpace (E × Z)]
    (M : OCModel E (Fin m → ℝ) Z) (P : (E → Z → ℝ) → Prop) (hE : M.ExpCont P)
    (hP : ∀ t ≤ M.T, P (M.V t)) (h644 : M.Assumption644) (h646 : M.Assumption646) :
    ∀ t < M.T, ∃ g : ↥(M.X ×ˢ (Set.univ : Set Z)) → Fin m → ℝ,
      Measurable g ∧ ∀ s, g s ∈ M.Gs t s := by
  intro t ht
  have h := (M.theorem_6_4_1 P hE hP h644 h646).2 t ht
  exact theorem_7_6 (fun s => (h s).2.2) fun s => (h s).2.1

/-! ### The standing hypotheses -/

/-- The **standing hypotheses** of §6.4 for a class `P` of functions: Lemma 6.4.1 holds on `P`
(`ExpCont P`), every `V_t` lies in `P`, and Assumptions 6.4.4–6.4.6 hold. They hold in case (ii)
of Assumption 6.4.3 with `P = True` (`Standing.of_compact`) and in case (i) with bounded rewards
and `P` = bounded (`Standing.of_countable`). -/
structure Standing (P : (E → Z → ℝ) → Prop) : Prop where
  expCont : M.ExpCont P
  memP : ∀ t ≤ M.T, P (M.V t)
  a644 : M.Assumption644
  a645 : M.Assumption645
  a646 : M.Assumption646

/-- Case (ii) of Assumption 6.4.3 gives the standing hypotheses with `P = True`. -/
theorem Standing.of_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) :
    M.Standing fun _ => True := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  exact ⟨M.expCont_compact h643.2.2 h645, fun _ _ => trivial, h644, h645, h646⟩

/-- Case (i) of Assumption 6.4.3 with bounded rewards gives the standing hypotheses with `P` the
bounded functions. -/
theorem Standing.of_countable [IsMarkovKernel M.Q] (h643 : Assumption643i Z)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    M.Standing fun f => ∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B := by
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  exact ⟨M.expCont_countable h645, M.V_bounded h644 h645.1 hu huT, h644, h645, h646⟩

variable {M} {P : (E → Z → ℝ) → Prop}

/-- Under the standing hypotheses every `V_t` is continuous (Theorem 6.4.1). -/
theorem Standing.contV (h : M.Standing P) {t : ℕ} (ht : t ≤ M.T) :
    ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ) :=
  (M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).1 t ht

/-- The integrands `z′ ↦ V_{t+1}(φ(x, a, z, z′), z′)` are integrable. -/
theorem Standing.integrable (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    {a : F} (ha : a ∈ M.A) (z : Z) :
    Integrable (fun z' => M.V (t + 1) (M.φ x a z z') z') (M.Q z) :=
  (h.expCont _ (h.memP (t + 1) ht) (h.contV ht)).2 x hx a ha z

/-- The objective of (6.29) is continuous on the graph of `Γ`. -/
theorem Standing.continuousOn_objS (h : M.Standing P) {t : ℕ} (ht : t < M.T) :
    ContinuousOn (M.objS t (M.V (t + 1))) (graph M.Γs) :=
  M.continuousOn_objS h.a644 (h.a646.1 t ht) (h.expCont _ (h.memP (t + 1) ht) (h.contV ht)).1

/-- Every feasible action does at most as well as `V_t`: `obj_t(x, z, a) ≤ V_t(x, z)`. -/
theorem Standing.obj_le_V (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    {z : Z} {a : F} (ha : a ∈ M.Γ x z) : M.obj t (M.V (t + 1)) x z a ≤ M.V t x z := by
  have := le_maxValue (h.continuousOn_objS ht) (h.a644.2 ⟨(x, z), hx, Set.mem_univ _⟩).1
    (x := ⟨(x, z), hx, Set.mem_univ _⟩) ha
  rwa [← M.V_eq_maxValue ht] at this

/-- `G_t(x, z)` is nonempty (Theorem 6.4.1). -/
theorem Standing.G_nonempty (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    (z : Z) : (M.G t x z).Nonempty :=
  ((M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).2 t ht ⟨(x, z), hx, Set.mem_univ _⟩).1

/-- The selection `g_t(x, z)` lies in `G_t(x, z)`. -/
theorem Standing.g_mem [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E}
    (hx : x ∈ M.X) (z : Z) : M.g t x z ∈ M.G t x z :=
  M.g_mem (h.G_nonempty ht hx z)

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.2: monotonicity

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCMonotone`), namespace renamed.

Miao, §6.4, pp. 175–176. Under Assumptions 6.4.1–6.4.9, `V_t(·, z)` is strictly increasing on
`X` for every `z` and `t = 0, 1, …, T` (`theorem_6_4_2`), by backward induction: with `a*`
attaining `V_t(x, z)` and `x < x′`,
`V_t(x, z) = u_t(x, z, a*) + β E V_{t+1} < u_t(x′, z, a*) + β E V_{t+1} ≤ V_t(x′, z)`, using
Assumptions 6.4.7 and 6.4.9 for the strict inequality and `a* ∈ Γ(x′, z)` (Assumption 6.4.8)
for the second.

The order on `E` is any partial order (componentwise on `ℝ^{n_x}`); "strictly increasing" is
`StrictMonoOn`. The proof needs `β ≥ 0` rather than all of Assumption 5.1.2, and does not use
Assumptions 6.4.1–6.4.2. The standing hypotheses (`Standing`) carry Assumptions 6.4.3–6.4.6.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] [MetricSpace E] [MetricSpace F] [MetricSpace Z]
  {M : OCModel E F Z} {P : (E → Z → ℝ) → Prop}

/-- **Theorem 6.4.2 (Monotonicity)** (Miao, p. 175). Under the standing hypotheses
(Assumptions 6.4.3–6.4.6), Assumptions 6.4.7–6.4.9 and `β ≥ 0`, `V_t(·, z)` is strictly
increasing on `X` for each `z ∈ Z` and `t = 0, 1, …, T`. -/
theorem theorem_6_4_2 [PartialOrder E] (h : M.Standing P) (h647 : M.Assumption647)
    (h648 : M.Assumption648) (h649 : M.Assumption649) (hβ : 0 ≤ M.β) :
    ∀ t ≤ M.T, ∀ z, StrictMonoOn (fun x => M.V t x z) M.X := by
  have key : ∀ k ≤ M.T, ∀ z, StrictMonoOn (fun x => M.V (M.T - k) x z) M.X := by
    intro k
    induction k with
    | zero => intro _ z; rw [Nat.sub_zero, M.V_T_eq]; exact h647.1 z
    | succ k ih =>
      intro hk z x hx x' hx' hxx'
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      set t := M.T - (k + 1)
      obtain ⟨a, haΓ, hval⟩ := h.G_nonempty ht hx z
      have haA := h.a644.1 x hx z haΓ
      have ha' : a ∈ M.Γ x' z := h648 z x hx x' hx' hxx'.le haΓ
      -- the continuation value is nondecreasing in `x`
      have hcont : M.cont (M.V (t + 1)) x a z ≤ M.cont (M.V (t + 1)) x' a z := by
        refine integral_mono (h.integrable ht hx haA z) (h.integrable ht hx' haA z) fun z' => ?_
        have hmono := (ih (by omega) z').monotoneOn
        rw [he]
        exact hmono (h.a645.1 x hx a haA z z') (h.a645.1 x' hx' a haA z z')
          (h649 a haA z z' hx hx' hxx'.le)
      have hu := h647.2 t ht z a haA hx hx' hxx'
      change M.V t x z < M.V t x' z
      rw [← hval]
      refine lt_of_lt_of_le ?_ (h.obj_le_V ht hx' ha')
      simp only [obj]
      exact add_lt_add_of_lt_of_le hu (mul_le_mul_of_nonneg_left hcont hβ)
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.3: concavity and the policy function

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCConcave`), namespace renamed.

Miao, §6.4, pp. 176–178. Under Assumptions 6.4.1–6.4.12, `V_t(·, z)` is strictly concave and
`G_t` is a single-valued continuous function `g_t`.

* `CompConcave f`: `θ f(φ(x, a, z, z′), z′) + η f(φ(x′, a′, z, z′), z′) ≤
  f(φ(θx + ηx′, θa + ηa′, z, z′), z′)`, the property of `V_{t+1}` the induction needs. It holds
  when `f(·, z′)` is concave and nondecreasing and `φ` is concave (`compConcave_of_mono`; the
  book's remark that "we need `u_T` to be monotonic", p. 177), and when `f(·, z′)` is concave and
  `φ` is affine (`compConcave_of_affine`), with no monotonicity.
* `concave_core`: `V_t(·, z)` is strictly concave for all `t ≤ T` whenever every `V_{t+1}` that
  is strictly concave has `CompConcave`. **Strict concavity of `V_t` is correct as stated**: the
  strictness comes from `u_t`, strict in `x` by Assumption 6.4.10.
* `theorem_6_4_3_concave`: strict concavity under the book's Assumptions 6.4.1–6.4.12
  (monotonicity from Theorem 6.4.2).
* **Correction** (`theorem_6_4_3_counterexample`): `G_t` need not be single-valued. Assumption
  6.4.10 is strict only in `x`; if neither `u_t` nor `φ` depends on `a`, every feasible action is
  optimal although Assumptions 6.4.1–6.4.12 and 5.1.2 hold. `theorem_6_4_3` adds that
  `φ(x, ·, z, z′)` is one-to-one on `A` (true for `φ = a`) and uses `β > 0`; then `G_t = {g_t}`
  and `g_t` is continuous (`G_eq_singleton_core`, `continuousOn_g_core`).
* `theorem_6_4_3_affine`: the same conclusions with Assumptions 6.4.7–6.4.9 dropped when `φ` is
  affine in `(x, a)`; `theorem_6_4_3_phi_eq_a` is the case `φ(x, a, z, z′) = a` of p. 180.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F]
  (M : OCModel E F Z)

/-- The composite `f(φ(·, ·, z, z′), z′)` is concave on `X × A`. -/
def CompConcave (f : E → Z → ℝ) : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    θ * f (M.φ x a z z') z' + η * f (M.φ x' a' z z') z' ≤
      f (M.φ (θ • x + η • x') (θ • a + η • a') z z') z'

/-- The composite `f(φ(x, ·, z, z′), z′)` is strictly concave on `A` for each `x`. -/
def CompStrictA (f : E → Z → ℝ) : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, a ≠ a' → ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    θ * f (M.φ x a z z') z' + η * f (M.φ x a' z z') z' < f (M.φ x (θ • a + η • a') z z') z'

/-- `φ(·, ·, z, z′)` is affine on `X × A`. -/
def PhiAffine : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    M.φ (θ • x + η • x') (θ • a + η • a') z z' = θ • M.φ x a z z' + η • M.φ x' a' z z'

/-- `φ(x, ·, z, z′)` is one-to-one on `A`. -/
def PhiInjA : Prop := ∀ z z', ∀ x ∈ M.X, Set.InjOn (fun a => M.φ x a z z') M.A

variable {M}

omit [MetricSpace Z] in
/-- Miao, p. 177: with `φ` concave (Assumption 6.4.12) and `f(·, z′)` concave and nondecreasing,
the composite `f(φ(·, ·, z, z′), z′)` is concave. -/
theorem compConcave_of_mono [PartialOrder E] (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (h6412 : M.Assumption6412)
    {f : E → Z → ℝ} (hc : ∀ z', ConcaveOn ℝ M.X fun x => f x z')
    (hm : ∀ z', MonotoneOn (fun x => f x z') M.X) : M.CompConcave f := by
  intro z z' x hx x' hx' a ha a' ha' θ η hθ hη hs
  have hp := h645X x hx a ha z z'
  have hp' := h645X x' hx' a' ha' z z'
  have hq := h645X _ (h641.1 hx hx' hθ.le hη.le hs) _ (h642.1 ha ha' hθ.le hη.le hs) z z'
  have hmid := h641.1 hp hp' hθ.le hη.le hs
  refine le_trans ?_ (hm z' hmid hq (h6412 z z' x hx x' hx' a ha a' ha' θ η hθ hη hs))
  exact (hc z').2 hp hp' hθ.le hη.le hs

omit [MetricSpace Z] in
/-- With `φ` concave, `φ(x, ·, z, z′)` one-to-one and `f(·, z′)` strictly concave and
nondecreasing, `f(φ(x, ·, z, z′), z′)` is strictly concave. -/
theorem compStrictA_of_mono [PartialOrder E] (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (h6412 : M.Assumption6412)
    (hinj : M.PhiInjA) {f : E → Z → ℝ} (hc : ∀ z', StrictConcaveOn ℝ M.X fun x => f x z')
    (hm : ∀ z', MonotoneOn (fun x => f x z') M.X) : M.CompStrictA f := by
  intro z z' x hx a ha a' ha' hne θ η hθ hη hs
  have hp := h645X x hx a ha z z'
  have hp' := h645X x hx a' ha' z z'
  have hq := h645X x hx _ (h642.1 ha ha' hθ.le hη.le hs) z z'
  have hmid := h641.1 hp hp' hθ.le hη.le hs
  have hφne : M.φ x a z z' ≠ M.φ x a' z z' := fun he => hne (hinj z z' x hx ha ha' he)
  have hle := h6412 z z' x hx x hx a ha a' ha' θ η hθ hη hs
  rw [Convex.combo_self hs] at hle
  exact lt_of_lt_of_le ((hc z').2 hp hp' hφne hθ hη hs) (hm z' hmid hq hle)

omit [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F] in
/-- With `φ` affine and `f(·, z′)` concave, the composite is concave; no monotonicity needed. -/
theorem compConcave_of_affine
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (haff : M.PhiAffine)
    {f : E → Z → ℝ} (hc : ∀ z', ConcaveOn ℝ M.X fun x => f x z') : M.CompConcave f := by
  intro z z' x hx x' hx' a ha a' ha' θ η hθ hη hs
  rw [haff z z' x hx x' hx' a ha a' ha' θ η hθ hη hs]
  exact (hc z').2 (h645X x hx a ha z z') (h645X x' hx' a' ha' z z') hθ.le hη.le hs

omit [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F] in
/-- With `φ` affine and one-to-one in `a`, and `f(·, z′)` strictly concave, the composite is
strictly concave in `a`. -/
theorem compStrictA_of_affine (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X)
    (haff : M.PhiAffine) (hinj : M.PhiInjA) {f : E → Z → ℝ}
    (hc : ∀ z', StrictConcaveOn ℝ M.X fun x => f x z') : M.CompStrictA f := by
  intro z z' x hx a ha a' ha' hne θ η hθ hη hs
  have h := haff z z' x hx x hx a ha a' ha' θ η hθ hη hs
  rw [Convex.combo_self hs] at h
  rw [h]
  exact (hc z').2 (h645X x hx a ha z z') (h645X x hx a' ha' z z')
    (fun he => hne (hinj z z' x hx ha ha' he)) hθ hη hs

variable {P : (E → Z → ℝ) → Prop}

/-- Concavity passes through the expectation: from `CompConcave f`,
`θ h(x, a, z) + η h(x′, a′, z) ≤ h(θx + ηx′, θa + ηa′, z)` for the integrals `h`. -/
theorem cont_comb (h : M.Standing P) (h641 : M.Assumption641) (h642 : M.Assumption642) {t : ℕ}
    (ht : t < M.T) (hcc : M.CompConcave (M.V (t + 1))) {x x' : E} (hx : x ∈ M.X)
    (hx' : x' ∈ M.X) {a a' : F} (ha : a ∈ M.A) (ha' : a' ∈ M.A) (z : Z) {θ η : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hs : θ + η = 1) :
    θ * M.cont (M.V (t + 1)) x a z + η * M.cont (M.V (t + 1)) x' a' z ≤
      M.cont (M.V (t + 1)) (θ • x + η • x') (θ • a + η • a') z := by
  have i1 := h.integrable ht hx ha z
  have i2 := h.integrable ht hx' ha' z
  have i3 := h.integrable ht (h641.1 hx hx' hθ.le hη.le hs) (h642.1 ha ha' hθ.le hη.le hs) z
  simp only [cont]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul θ)
    (i2.const_mul η)]
  exact integral_mono ((i1.const_mul θ).add (i2.const_mul η)) i3
    fun z' => hcc z z' x hx x' hx' a ha a' ha' θ η hθ hη hs

/-- **The concavity step of Theorem 6.4.3** (Miao, pp. 176–177): if every strictly concave
`V_{t+1}` has the composite-concavity property, then `V_t(·, z)` is strictly concave on `X` for
all `t ≤ T`. -/
theorem concave_core (h : M.Standing P) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 ≤ M.β)
    (hCC : ∀ t < M.T, (∀ z, StrictConcaveOn ℝ M.X fun x => M.V (t + 1) x z) →
      M.CompConcave (M.V (t + 1))) :
    ∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z := by
  have key : ∀ k ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V (M.T - k) x z := by
    intro k
    induction k with
    | zero => intro _ z; rw [Nat.sub_zero, M.V_T_eq]; exact h6410.1 z
    | succ k ih =>
      intro hk z
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      set t := M.T - (k + 1)
      have hV : ∀ z, StrictConcaveOn ℝ M.X fun x => M.V (t + 1) x z := by
        rw [he]; exact ih (by omega)
      have hcc := hCC t ht hV
      refine ⟨h641.1, fun x hx x' hx' hne θ η hθ hη hs => ?_⟩
      obtain ⟨a, haΓ, hval⟩ := h.G_nonempty ht hx z
      obtain ⟨a', haΓ', hval'⟩ := h.G_nonempty ht hx' z
      have haA := h.a644.1 x hx z haΓ
      have haA' := h.a644.1 x' hx' z haΓ'
      have hθΓ := h6411 z x hx x' hx' a haΓ a' haΓ' θ η hθ hη hs
      have hxθ := h641.1 hx hx' hθ.le hη.le hs
      have hu := (h6410.2 t ht z x hx x' hx' a haA a' haA' θ η hθ hη hs).2 hne
      have hc := cont_comb h h641 h642 ht hcc hx hx' haA haA' z hθ hη hs
      simp only [smul_eq_mul]
      rw [← hval, ← hval']
      refine lt_of_lt_of_le ?_ (h.obj_le_V ht hxθ hθΓ)
      simp only [obj]
      nlinarith [mul_le_mul_of_nonneg_left hc hβ]
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

omit [MeasurableSpace E] in
/-- **Single-valuedness of `G_t`** (Miao, p. 177, corrected): if `β > 0` and every `V_{t+1}` gives
a composite strictly concave in `a`, then each `G_t(x, z)` has at most one element. -/
theorem G_subsingleton_core [IsMarkovKernel M.Q] (h : M.Standing P) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 < M.β)
    (hSA : ∀ t < M.T, M.CompStrictA (M.V (t + 1))) :
    ∀ t < M.T, ∀ x ∈ M.X, ∀ z, (M.G t x z).Subsingleton := by
  intro t ht x hx z a ⟨haΓ, hva⟩ b ⟨hbΓ, hvb⟩
  by_contra hne
  have haA := h.a644.1 x hx z haΓ
  have hbA := h.a644.1 x hx z hbΓ
  have hh : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hmΓ := h6411 z x hx x hx a haΓ b hbΓ (1 / 2) (1 / 2) hpos hpos hh
  rw [Convex.combo_self hh] at hmΓ
  have hu := (h6410.2 t ht z x hx x hx a haA b hbA (1 / 2) (1 / 2) hpos hpos hh).1
  rw [Convex.combo_self hh] at hu
  -- the continuation value is strictly concave in `a`
  have hc : (1 / 2) * M.cont (M.V (t + 1)) x a z + (1 / 2) * M.cont (M.V (t + 1)) x b z <
      M.cont (M.V (t + 1)) x ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) z := by
    have i1 := h.integrable ht hx haA z
    have i2 := h.integrable ht hx hbA z
    have i3 := h.integrable ht hx (h642.1 haA hbA hpos.le hpos.le hh) z
    simp only [cont]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    exact integral_lt_integral_of_lt ((i1.const_mul _).add (i2.const_mul _)) i3
      fun z' => hSA t ht z z' x hx a haA b hbA hne _ _ hpos hpos hh
  have hle := h.obj_le_V ht hx hmΓ
  simp only [obj] at hle hva hvb
  nlinarith [mul_lt_mul_of_pos_left hc hβ]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] in
/-- `G_t(x, z) = {g_t(x, z)}` when `G_t` is single-valued. -/
theorem G_eq_singleton_core [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E}
    (hx : x ∈ M.X) {z : Z} (hsub : (M.G t x z).Subsingleton) : M.G t x z = {M.g t x z} :=
  hsub.eq_singleton_of_mem (h.g_mem ht hx z)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] in
/-- A single-valued u.h.c. policy correspondence is a continuous function (SLP Ex 3.11a):
`g_t` is continuous on `X × Z`. -/
theorem continuousOn_g_core [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hsub : ∀ x ∈ M.X, ∀ z, (M.G t x z).Subsingleton) :
    ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hG := (M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).2 t ht
  have heq : M.Gs t = fun s => {M.g t s.1.1 s.1.2} := funext fun s =>
    G_eq_singleton_core h ht s.2.1 (hsub _ s.2.1 _)
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro s
  have hu := (hG s).2.2
  rw [heq] at hu
  exact continuousAt_of_isUHC_singleton hu

/-- **Theorem 6.4.3 (Concavity)** (Miao, p. 176), strict concavity of `V_t`: under Assumptions
6.4.1–6.4.12 (with the standing hypotheses for 6.4.3–6.4.6) and `β ≥ 0`, `V_t(·, z)` is strictly
concave on `X` for every `z` and `t ≤ T`. -/
theorem theorem_6_4_3_concave [PartialOrder E] (h : M.Standing P) (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (hβ : 0 ≤ M.β) :
    ∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z := by
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ
  refine concave_core h h641 h642 h6410 h6411 hβ fun t ht hV => ?_
  exact compConcave_of_mono h641 h642 h.a645.1 h6412 (fun z' => (hV z').concaveOn)
    fun z' => (hmono (t + 1) ht z').monotoneOn

/-- **Theorem 6.4.3 (Concavity)** (Miao, p. 176), corrected. Under Assumptions 6.4.1–6.4.12, with
`β > 0` and `φ(x, ·, z, z′)` one-to-one on `A`: `V_t(·, z)` is strictly concave for `t ≤ T`, and
for `t < T` the policy correspondence is a single-valued continuous function,
`G_t(x, z) = {g_t(x, z)}`. -/
theorem theorem_6_4_3 [PartialOrder E] [Nonempty F] [IsMarkovKernel M.Q] (h : M.Standing P)
    (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (hβ : 0 < M.β) (hinj : M.PhiInjA) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hconc := theorem_6_4_3_concave h h641 h642 h647 h648 h649 h6410 h6411 h6412 hβ.le
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ.le
  have hsub := G_subsingleton_core h h642 h6410 h6411 hβ fun t ht =>
    compStrictA_of_mono h641 h642 h.a645.1 h6412 hinj (hconc (t + 1) ht)
      fun z' => (hmono (t + 1) ht z').monotoneOn
  exact ⟨hconc, fun t ht x hx z => G_eq_singleton_core h ht hx (hsub t ht x hx z),
    fun t ht => continuousOn_g_core h ht (hsub t ht)⟩

/-- **Theorem 6.4.3 without monotonicity** (Miao, p. 180): if `φ` is affine in `(x, a)` and
one-to-one in `a`, the conclusions hold without Assumptions 6.4.7–6.4.9 and 6.4.12. -/
theorem theorem_6_4_3_affine [Nonempty F] [IsMarkovKernel M.Q] (h : M.Standing P)
    (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (hβ : 0 < M.β) (haff : M.PhiAffine) (hinj : M.PhiInjA) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hconc := concave_core h h641 h642 h6410 h6411 hβ.le fun t _ hV =>
    compConcave_of_affine h.a645.1 haff fun z' => (hV z').concaveOn
  have hsub := G_subsingleton_core h h642 h6410 h6411 hβ fun t ht =>
    compStrictA_of_affine h.a645.1 haff hinj (hconc (t + 1) ht)
  exact ⟨hconc, fun t ht x hx z => G_eq_singleton_core h ht hx (hsub t ht x hx z),
    fun t ht => continuousOn_g_core h ht (hsub t ht)⟩

/-- **Theorem 6.4.3 for `φ(x, a, z, z′) = a`** (Miao, p. 180): when the action is next period's
state, Assumptions 6.4.7–6.4.9 can be dispensed with. -/
theorem theorem_6_4_3_phi_eq_a [Nonempty E] {M : OCModel E E Z} [IsMarkovKernel M.Q]
    (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 < M.β) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  refine theorem_6_4_3_affine h h641 h642 h6410 h6411 hβ
    (fun z z' x _ x' _ a _ a' _ θ η _ _ _ => ?_) (fun z z' x _ a _ a' _ he => ?_)
  · simp only [hφ]
  · simpa only [hφ] using he

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two facts about concave functions of one variable

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCDiffTools`), namespace renamed.

Tools for Theorem 6.4.4 (Miao, §6.4, pp. 178–180).

* `oc_hasDerivAt_integral_concave`: **differentiation under `∫ Q(z, dz′)`**. If each
  `F(·, z′)` is concave on a ball around `x₀`, bounded there by a constant, and differentiable
  at `x₀`, then `∫ F(·, z′) μ(dz′)` is differentiable at `x₀` with derivative
  `∫ ∂F(x₀, z′)/∂x μ(dz′)`. A concave function bounded by `C` on `B(x₀, r)` is `4C/r`-Lipschitz
  on `B(x₀, r/2)` (Mathlib's `ConcaveOn.lipschitzOnWith_of_abs_le`), which gives the domination;
  the derivative is measurable as a limit of difference quotients.
* `oc_continuousOn_deriv_of_concave`: a concave function differentiable on an open set has a
  **continuous derivative** there. For `y` near `x₀` the derivative `f′(y)` lies between
  `f′(x₀)` and the slope of `f` between `y` and `2y − x₀`, which tends to `f′(x₀)`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology Metric

/-- **Differentiation under the integral sign for concave integrands.** Let `μ` be a probability
measure, each `F(·, z)` concave on `B(x₀, r)` with `|F(y, z)| ≤ C` there, each `F(y, ·)`
integrable for `y ∈ B(x₀, r)`, and `∂F(x₀, z)/∂x = F′(z)`. Then `F′` is integrable and
`x ↦ ∫ F(x, z) μ(dz)` has derivative `∫ F′ dμ` at `x₀`. -/
theorem oc_hasDerivAt_integral_concave {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    [IsProbabilityMeasure μ] {F : ℝ → Z → ℝ} {F' : Z → ℝ} {x₀ r C : ℝ} (hr : 0 < r)
    (hconc : ∀ z, ConcaveOn ℝ (ball x₀ r) fun y => F y z)
    (hbd : ∀ y ∈ ball x₀ r, ∀ z, |F y z| ≤ C)
    (hint : ∀ y ∈ ball x₀ r, Integrable (F y) μ)
    (hd : ∀ z, HasDerivAt (fun y => F y z) (F' z) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun y => ∫ z, F y z ∂μ) (∫ z, F' z ∂μ) x₀ := by
  set K : ℝ := 2 * C / (r / 2)
  have hlip : ∀ z, LipschitzOnWith (Real.nnabs K) (fun y => F y z) (ball x₀ (r / 2)) := by
    intro z
    have h := (hconc z).lipschitzOnWith_of_abs_le (ε := r / 2) (by positivity)
      fun y hy => hbd y hy z
    rw [show r - r / 2 = r / 2 by ring] at h
    refine h.weaken ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal', Real.coe_nnabs]
    exact max_le (le_abs_self K) (abs_nonneg K)
  -- the derivative is measurable: a limit of difference quotients
  set δ : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlt : ∀ n, δ n < r := fun n => by
    have : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  have hδmem : ∀ n, x₀ + δ n ∈ ball x₀ r := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos (hδpos n)]
    exact hδlt n
  have hδlim : Tendsto (fun n => x₀ + δ n) atTop (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto δ atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        exact h1.const_div_atTop r
      simpa using (tendsto_const_nhds (x := x₀)).add this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hδpos n]
  have hF'm : AEStronglyMeasurable F' μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n z => slope (fun y => F y z) x₀ (x₀ + δ n)) (fun n => ?_)
      (ae_of_all _ fun z => (hasDerivAt_iff_tendsto_slope.1 (hd z)).comp hδlim)
    simp only [slope_def_field]
    exact (((hint _ (hδmem n)).sub (hint x₀ (mem_ball_self hr))).div_const _).aestronglyMeasurable
  exact hasDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ (half_pos hr))
    (Eventually.mono (ball_mem_nhds x₀ hr) fun y hy => (hint y hy).aestronglyMeasurable)
    (hint x₀ (mem_ball_self hr)) hF'm (ae_of_all _ hlip) (integrable_const K) (ae_of_all _ hd)

/-- The slope of `f` between `y` and `2y − x₀`, written through slopes from `x₀`. -/
theorem oc_slope_double (f : ℝ → ℝ) {x₀ y : ℝ} (hy : y ≠ x₀) :
    slope f y (2 * y - x₀) = 2 * slope f x₀ (2 * y - x₀) - slope f x₀ y := by
  have h1 : y - x₀ ≠ 0 := sub_ne_zero.2 hy
  have h2 : 2 * y - x₀ - x₀ ≠ 0 := by
    intro h; apply h1; linarith
  have h3 : 2 * y - x₀ - y ≠ 0 := by
    intro h; apply h1; linarith
  simp only [slope_def_field]
  field_simp
  ring

/-- **A concave function differentiable on an open set is continuously differentiable there.** -/
theorem oc_continuousOn_deriv_of_concave {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hc : ConcaveOn ℝ U f) (hd : ∀ x ∈ U, DifferentiableAt ℝ f x) :
    ContinuousOn (deriv f) U := by
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  set d := deriv f x₀
  have hslope : Tendsto (slope f x₀) (𝓝[≠] x₀) (𝓝 d) :=
    hasDerivAt_iff_tendsto_slope.1 (hd x₀ hx₀).hasDerivAt
  have hmap : Tendsto (fun y => 2 * y - x₀) (𝓝[≠] x₀) (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => 2 * y - x₀) (𝓝 x₀) (𝓝 (2 * x₀ - x₀)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto x₀
      rw [show 2 * x₀ - x₀ = x₀ by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
      intro h; apply hy; linarith
  have hq : Tendsto (fun y => slope f y (2 * y - x₀)) (𝓝[≠] x₀) (𝓝 d) := by
    have := ((hslope.comp hmap).const_mul 2).sub hslope
    rw [show 2 * d - d = d by ring] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (oc_slope_double f hy).symm
  -- `f′(y)` lies between `f′(x₀)` and the slope from `y` to `2y − x₀`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hanti := hc.antitoneOn_deriv hd
  have hnear : ∀ᶠ y in 𝓝[≠] x₀, |deriv f y - d| ≤ |slope f y (2 * y - x₀) - d| := by
    have hb : ball x₀ (ε / 2) ∈ 𝓝[≠] x₀ :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by linarith))
    filter_upwards [hb, self_mem_nhdsWithin] with y hy hne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
    rw [mem_ball, Real.dist_eq] at hy
    have hyU : y ∈ U := hball (by rw [mem_ball, Real.dist_eq]; linarith)
    have hwU : 2 * y - x₀ ∈ U := hball (by
      rw [mem_ball, Real.dist_eq, show 2 * y - x₀ - x₀ = 2 * (y - x₀) by ring, abs_mul]
      norm_num; linarith)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `2y − x₀ < y < x₀`
      have h1 : d ≤ deriv f y := hanti hyU hx₀ hlt.le
      have h2 : deriv f y ≤ slope f (2 * y - x₀) y :=
        hc.deriv_le_slope hwU hyU (by linarith) (hd y hyU)
      rw [slope_comm] at h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · -- `x₀ < y < 2y − x₀`
      have h1 : deriv f y ≤ d := hanti hx₀ hyU hgt.le
      have h2 : slope f y (2 * y - x₀) ≤ deriv f y :=
        hc.slope_le_deriv hyU hwU (by linarith) (hd y hyU)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hq0 : Tendsto (fun y => |slope f y (2 * y - x₀) - d|) (𝓝[≠] x₀) (𝓝 0) := by
    have := (hq.sub_const d).abs
    simpa using this
  have h0 : Tendsto (fun y => deriv f y - d) (𝓝[≠] x₀) (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hnear) hq0
  simpa using h0.add_const d

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.4: differentiability, the envelope condition and the Euler equations

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCDifferentiable`), namespace renamed.

Miao, §6.4, pp. 178–180, for one-dimensional states and actions (`X, A ⊆ ℝ`; the book's
`n_x = n_a = 1`, the case of §6.5 and §6.6.2). The value functions are differentiable on `int X`
with the **envelope condition** (6.31)–(6.32) (`envRHS`), the **first-order condition** (6.33)
(`focRHS`) holds, and for `φ(x, a, z, z′) = a` these give the **Euler equations** of p. 180.

The proof is the book's: Benveniste–Scheinkman (SLP Theorem 4.10, `theorem_4_10`) applied to
`W(y) = u_t(y, z, a_t) + β ∫ V_{t+1}(φ(y, a_t, z, z′), z′) Q(z, dz′) ≤ V_t(y, z)`. **Corrections**
to the hypotheses, each needed by that argument:

* **Differentiating under `∫ Q(z, dz′)`** in (6.31) and (6.33) needs a domination. We use
  concavity: `y ↦ V_{t+1}(φ(y, a, z, z′), z′)` is concave (`CompConcave`), hence Lipschitz near
  `x_t` with a constant fixed by a uniform bound on `V_{t+1}(φ(y, b, z, z′), z′)` for `(y, b)`
  near `(x_t, a_t)` (`LocBounded`, `oc_hasDerivAt_integral_concave`). `LocBounded` holds when
  `Z` is compact (`locBounded_of_compact`), and when the `V_t` are bounded (case (i)).
* **Interiority must hold at every interior state, and the next state must be interior**
  (`InteriorPolicy`): the book assumes `x_t ∈ int X` and `g_t(x_t, z_t) ∈ int Γ(x_t, z_t)` at the
  point only, but (6.31) and (6.33) use the derivative of `V_{t+1}` at
  `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})`, which needs `x_{t+1} ∈ int X` and the induction
  hypothesis there.
* `g_t(x_t, z_t) ∈ int Γ(x_t, z_t)` gives `g_t(x_t, z_t) ∈ Γ(x, z_t)` for `x` near `x_t` only
  because `Γ` is convex-valued (Assumption 6.4.11) and l.h.c. (`eventually_mem_Γ`).
* (6.31) is stated for `t = 1, …, T − 1` but holds, and is used, for `t = 0` too.
* `V_t(·, z)` is continuously differentiable on `int X` because a differentiable concave function
  of one variable is (`oc_continuousOn_deriv_of_concave`); for `t = T` this needs only that
  `u_T(·, z)` is differentiable, as Assumption 6.4.13 says.

Main results: `theorem_6_4_4` (Assumptions 6.4.1–6.4.14), `theorem_6_4_4_phi_eq_a` and
`euler_equations` (`φ = a`, without Assumptions 6.4.7–6.4.9), built on `theorem_6_4_4_core`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology Metric

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] [MetricSpace Z] (M : OCModel ℝ ℝ Z)

/-- The right side of the **envelope condition (6.31)** at the action `a`:
`∂u_t(x, z, a)/∂x + β ∫ ∂V_{t+1}(φ(x, a, z, z′), z′)/∂x · ∂φ(x, a, z, z′)/∂x Q(z, dz′)`. -/
noncomputable def envRHS (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) : ℝ :=
  deriv (fun y => M.u t y z a) x + M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
    deriv (fun y => M.φ y a z z') x ∂M.Q z

/-- The right side of the **first-order condition (6.33)** at the action `a`:
`∂u_t(x, z, a)/∂a + β ∫ ∂V_{t+1}(φ(x, a, z, z′), z′)/∂x · ∂φ(x, a, z, z′)/∂a Q(z, dz′)`. -/
noncomputable def focRHS (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) : ℝ :=
  deriv (fun b => M.u t x z b) a + M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
    deriv (fun b => M.φ x b z z') a ∂M.Q z

/-- The domination hypothesis for (6.31) and (6.33): near an interior `(x, a)`,
`V_{t+1}(φ(y, b, z, z′), z′)` is bounded uniformly in `z′`. -/
def LocBounded : Prop :=
  ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A, ∃ r > 0, ∃ C,
    ∀ y ∈ ball x r, ∀ b ∈ ball a r, ∀ z', |M.V (t + 1) (M.φ y b z z') z'| ≤ C

/-- The interiority hypothesis of Theorem 6.4.4, corrected: at every interior state the policy
is interior to `Γ` and every next state is interior to `X`. -/
def InteriorPolicy : Prop :=
  ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
    M.g t x z ∈ interior (M.Γ x z) ∧ ∀ z', M.φ x (M.g t x z) z z' ∈ interior M.X

/-- The partial derivatives used in Theorem 6.4.4 exist on the interiors (they follow from
Assumptions 6.4.13–6.4.14, `partials_of`). -/
structure Partials : Prop where
  uT : ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.uT y z) x
  ux : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun y => M.u t y z a) x
  ua : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun b => M.u t x z b) a
  φx : ∀ z z', ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun y => M.φ y a z z') x
  φa : ∀ z z', ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun b => M.φ x b z z') a

variable {M}

omit [MetricSpace Z] in
/-- Assumptions 6.4.13 and 6.4.14 give the partial derivatives. -/
theorem partials_of (h6413 : M.Assumption6413) (h6414 : M.Assumption6414) : M.Partials := by
  have hopen : IsOpen (interior (M.X ×ˢ M.A)) := isOpen_interior
  have hmem : ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A → (x, a) ∈ interior (M.X ×ˢ M.A) :=
    fun hx ha => by rw [interior_prod_eq]; exact ⟨hx, ha⟩
  have hu : ∀ t < M.T, ∀ z, ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A →
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 z p.2) (x, a) := fun t ht z x a hx ha =>
    ((h6413.2 t ht z).differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds (hmem hx ha))
  have hφ : ∀ z z', ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A →
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 z z') (x, a) := fun z z' x a hx ha =>
    (h6414 z z').differentiableAt (hopen.mem_nhds (hmem hx ha))
  refine ⟨fun z x hx => (h6413.1 z).differentiableAt (isOpen_interior.mem_nhds hx),
    fun t ht z x hx a ha => ?_, fun t ht z x hx a ha => ?_, fun z z' x hx a ha => ?_,
    fun z z' x hx a ha => ?_⟩
  · exact (hu t ht z hx ha).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, a)) x)
  · exact (hu t ht z hx ha).comp a (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (x, b)) a)
  · exact (hφ z z' hx ha).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, a)) x)
  · exact (hφ z z' hx ha).comp a (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (x, b)) a)

omit [MeasurableSpace Z] [MetricSpace Z] in
/-- A concavity inequality with positive weights gives `ConcaveOn`. -/
theorem oc_concaveOn_of_pos {s : Set ℝ} (hs : Convex ℝ s) {f : ℝ → ℝ}
    (h : ∀ y₁ ∈ s, ∀ y₂ ∈ s, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
      θ * f y₁ + η * f y₂ ≤ f (θ * y₁ + η * y₂)) : ConcaveOn ℝ s f := by
  refine ⟨hs, fun y₁ hy₁ y₂ hy₂ θ η hθ hη hsum => ?_⟩
  simp only [smul_eq_mul]
  rcases hθ.eq_or_lt with rfl | hθ'
  · have : η = 1 := by linarith
    subst this; simp
  rcases hη.eq_or_lt with rfl | hη'
  · have : θ = 1 := by linarith
    subst this; simp
  exact h y₁ hy₁ y₂ hy₂ θ η hθ' hη' hsum

/-- **`g_t(x, z) ∈ int Γ(x, z)` gives `g_t(x, z) ∈ Γ(y, z)` for `y` near `x`** (Miao, p. 179),
for the convex-valued (Assumption 6.4.11) l.h.c. (Assumption 6.4.4) correspondence `Γ`. -/
theorem eventually_mem_Γ (h644 : M.Assumption644) (h6411 : M.Assumption6411) {x : ℝ}
    (hx : x ∈ interior M.X) {z : Z} {a : ℝ} (ha : a ∈ interior (M.Γ x z)) :
    ∀ᶠ y in 𝓝 x, y ∈ M.X ∧ a ∈ M.Γ y z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  have hb0 : a - ε / 2 ∈ M.Γ x z := hball (by
    rw [mem_ball, Real.dist_eq, show a - ε / 2 - a = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]; linarith)
  have hc0 : a + ε / 2 ∈ M.Γ x z := hball (by
    rw [mem_ball, Real.dist_eq, show a + ε / 2 - a = ε / 2 by ring, abs_of_pos (half_pos hε)]
    linarith)
  have hxX : M.X ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ M.X ∧ a ∉ M.Γ y z :=
    (hne.and_eventually hxX).mono fun y ⟨h1, h2⟩ => ⟨h2, fun h => h1 ⟨h2, h⟩⟩
  obtain ⟨ys, hys, hmem⟩ := exists_seq_forall_of_frequently hfreq
  let s0 : ↥(M.X ×ˢ (Set.univ : Set Z)) := ⟨(x, z), mem_of_mem_nhds hxX, Set.mem_univ _⟩
  let ss : ℕ → ↥(M.X ×ˢ (Set.univ : Set Z)) := fun n => ⟨(ys n, z), (hmem n).1, Set.mem_univ _⟩
  have hss : Tendsto ss atTop (𝓝 s0) :=
    tendsto_subtype_rng.2 (hys.prodMk_nhds tendsto_const_nhds)
  obtain ⟨N1, bs, hbs, hblim⟩ := (h644.2 s0).2.1.2 _ hb0 ss hss
  obtain ⟨N2, cs, hcs, hclim⟩ := (h644.2 s0).2.1.2 _ hc0 ss hss
  have e1 : ∀ᶠ n in atTop, bs n < a := hblim.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ n in atTop, a < cs n := hclim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2, hb, hc⟩ :=
    ((eventually_ge_atTop N1).and ((eventually_ge_atTop N2).and (e1.and e2))).exists
  have hbΓ : bs n ∈ M.Γ (ys n) z := hbs n hn1
  have hcΓ : cs n ∈ M.Γ (ys n) z := hcs n hn2
  have hd : 0 < cs n - bs n := by linarith
  have hθ : 0 < (cs n - a) / (cs n - bs n) := div_pos (by linarith) hd
  have hη : 0 < (a - bs n) / (cs n - bs n) := div_pos (by linarith) hd
  have hs : (cs n - a) / (cs n - bs n) + (a - bs n) / (cs n - bs n) = 1 := by
    field_simp; ring
  have hcomb : ((cs n - a) / (cs n - bs n)) • bs n + ((a - bs n) / (cs n - bs n)) • cs n = a := by
    simp only [smul_eq_mul]; field_simp; ring
  have := h6411 z (ys n) (hmem n).1 (ys n) (hmem n).1 (bs n) hbΓ (cs n) hcΓ _ _ hθ hη hs
  rw [Convex.combo_self hs, hcomb] at this
  exact (hmem n).2 this

variable {P : (ℝ → Z → ℝ) → Prop}

/-- Differentiating the continuation value in `x` under `∫ Q(z, dz′)` (the second term of
(6.31)). -/
theorem hasDerivAt_cont_x [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials) {x : ℝ}
    (hx : x ∈ interior M.X) {a : ℝ} (ha : a ∈ interior M.A) (z : Z)
    (hnext : ∀ z', M.φ x a z z' ∈ interior M.X)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y) :
    HasDerivAt (fun y => M.cont (M.V (t + 1)) y a z)
      (∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
        deriv (fun y => M.φ y a z z') x ∂M.Q z) x := by
  obtain ⟨r₀, hr₀, C, hC⟩ := hbd t ht z x hx a ha
  obtain ⟨ε, hε, hεX⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hr : 0 < min r₀ ε := lt_min hr₀ hε
  have hsub : ∀ y ∈ ball x (min r₀ ε), y ∈ M.X := fun y hy =>
    hεX (ball_subset_ball (min_le_right _ _) hy)
  have haA : a ∈ M.A := interior_subset ha
  refine (oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun y z' => M.V (t + 1) (M.φ y a z z') z') hr (fun z' => ?_)
    (fun y hy z' => hC y (ball_subset_ball (min_le_left _ _) hy) a (mem_ball_self hr₀) z')
    (fun y hy => h.integrable ht (hsub y hy) haA z) (fun z' => ?_)).2
  · refine oc_concaveOn_of_pos (convex_ball _ _) fun y₁ hy₁ y₂ hy₂ θ η hθ hη hs => ?_
    have := hcc z z' y₁ (hsub y₁ hy₁) y₂ (hsub y₂ hy₂) a haA a haA θ η hθ hη hs
    rwa [Convex.combo_self hs, smul_eq_mul, smul_eq_mul] at this
  · exact (hD z' _ (hnext z')).hasDerivAt.comp x (hpar.φx z z' x hx a ha).hasDerivAt

/-- Differentiating the continuation value in `a` under `∫ Q(z, dz′)` (the second term of
(6.33)). -/
theorem hasDerivAt_cont_a [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials) {x : ℝ}
    (hx : x ∈ interior M.X) {a : ℝ} (ha : a ∈ interior M.A) (z : Z)
    (hnext : ∀ z', M.φ x a z z' ∈ interior M.X)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y) :
    HasDerivAt (fun b => M.cont (M.V (t + 1)) x b z)
      (∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
        deriv (fun b => M.φ x b z z') a ∂M.Q z) a := by
  obtain ⟨r₀, hr₀, C, hC⟩ := hbd t ht z x hx a ha
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  have hr : 0 < min r₀ ε := lt_min hr₀ hε
  have hsub : ∀ b ∈ ball a (min r₀ ε), b ∈ M.A := fun b hb =>
    hεA (ball_subset_ball (min_le_right _ _) hb)
  have hxX : x ∈ M.X := interior_subset hx
  refine (oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun b z' => M.V (t + 1) (M.φ x b z z') z') hr (fun z' => ?_)
    (fun b hb z' => hC x (mem_ball_self hr₀) b (ball_subset_ball (min_le_left _ _) hb) z')
    (fun b hb => h.integrable ht hxX (hsub b hb) z) (fun z' => ?_)).2
  · refine oc_concaveOn_of_pos (convex_ball _ _) fun b₁ hb₁ b₂ hb₂ θ η hθ hη hs => ?_
    have := hcc z z' x hxX x hxX b₁ (hsub b₁ hb₁) b₂ (hsub b₂ hb₂) θ η hθ hη hs
    rwa [Convex.combo_self hs, smul_eq_mul, smul_eq_mul] at this
  · exact (hD z' _ (hnext z')).hasDerivAt.comp a (hpar.φa z z' x hx a ha).hasDerivAt

/-- **The envelope condition (6.31)** at a date `t < T`, given differentiability of `V_{t+1}` on
`int X` (Miao, p. 179, by Benveniste–Scheinkman). -/
theorem envelope_step [IsMarkovKernel M.Q] (h : M.Standing P) (h6411 : M.Assumption6411)
    {t : ℕ} (ht : t < M.T) (hconc : ∀ z, ConcaveOn ℝ M.X fun x => M.V t x z)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y)
    (z : Z) {x : ℝ} (hx : x ∈ interior M.X) :
    HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x := by
  obtain ⟨hgΓ, hnext⟩ := hint t ht z x hx
  have hgA : M.g t x z ∈ interior M.A := interior_mono (h.a644.1 x (interior_subset hx) z) hgΓ
  have hW : HasDerivAt (fun y => M.obj t (M.V (t + 1)) y z (M.g t x z))
      (M.envRHS t x z (M.g t x z)) x :=
    (hpar.ux t ht z x hx _ hgA).hasDerivAt.add
      ((hasDerivAt_cont_x h ht hcc hbd hpar hx hgA z hnext hD).const_mul M.β)
  have heq : M.obj t (M.V (t + 1)) x z (M.g t x z) = M.V t x z :=
    (h.g_mem ht (interior_subset hx) z).2
  have hle : ∀ᶠ y in 𝓝 x, M.obj t (M.V (t + 1)) y z (M.g t x z) ≤ M.V t y z :=
    (eventually_mem_Γ h.a644 h6411 hx hgΓ).mono fun y ⟨hyX, hyΓ⟩ => h.obj_le_V ht hyX hyΓ
  rw [hasDerivAt_iff_hasFDerivAt] at hW ⊢
  exact theorem_4_10 (hconc z) (mem_interior_iff_mem_nhds.1 hx) hW heq hle

/-- **The first-order condition (6.33)** at a date `t < T` (Miao, p. 179): the derivative of the
objective of (6.29) in `a` vanishes at the interior maximizer `a_t = g_t(x_t, z_t)`. -/
theorem foc_step [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y)
    (z : Z) {x : ℝ} (hx : x ∈ interior M.X) : M.focRHS t x z (M.g t x z) = 0 := by
  obtain ⟨hgΓ, hnext⟩ := hint t ht z x hx
  have hgA : M.g t x z ∈ interior M.A := interior_mono (h.a644.1 x (interior_subset hx) z) hgΓ
  have hd : HasDerivAt (fun b => M.obj t (M.V (t + 1)) x z b) (M.focRHS t x z (M.g t x z))
      (M.g t x z) :=
    (hpar.ua t ht z x hx _ hgA).hasDerivAt.add
      ((hasDerivAt_cont_a h ht hcc hbd hpar hx hgA z hnext hD).const_mul M.β)
  have hmax : IsLocalMax (fun b => M.obj t (M.V (t + 1)) x z b) (M.g t x z) := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hgΓ] with b hb
    rw [(h.g_mem ht (interior_subset hx) z).2]
    exact h.obj_le_V ht (interior_subset hx) hb
  exact hmax.hasDerivAt_eq_zero hd

/-- **Theorem 6.4.4 (Differentiability)** (Miao, pp. 178–180), for one-dimensional states and
actions, in the form the proof uses. Suppose the standing hypotheses, Assumption 6.4.11, `V_t(·, z)`
concave for `t ≤ T`, every composite `V_{t+1}(φ(·, ·, z, z′), z′)` concave, the domination
`LocBounded`, the partial derivatives `Partials` and the interiority `InteriorPolicy`. Then for
`x ∈ int X`:
* `V_t(·, z)` is differentiable for `t ≤ T`, with derivative continuous on `int X`;
* (6.31) for `t = 0, 1, …, T − 1`: `V_t′(x, z) = envRHS t x z (g_t(x, z))`;
* (6.32): `V_T′(x, z) = ∂u_T(x, z)/∂x`;
* (6.33) for `t = 0, 1, …, T − 1`: `focRHS t x z (g_t(x, z)) = 0`. -/
theorem theorem_6_4_4_core [IsMarkovKernel M.Q] (h : M.Standing P) (h6411 : M.Assumption6411)
    (hconc : ∀ t ≤ M.T, ∀ z, ConcaveOn ℝ M.X fun x => M.V t x z)
    (hCC : ∀ t < M.T, M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have hTd : ∀ z, ∀ x ∈ interior M.X,
      HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x := fun z x hx => by
    rw [M.V_T_eq]; exact (hpar.uT z x hx).hasDerivAt
  have key : ∀ k ≤ M.T, ∀ z, ∀ x ∈ interior M.X,
      DifferentiableAt ℝ (fun y => M.V (M.T - k) y z) x := by
    intro k
    induction k with
    | zero => intro _ z x hx; rw [Nat.sub_zero]; exact (hTd z x hx).differentiableAt
    | succ k ih =>
      intro hk z x hx
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      have hD : ∀ z', ∀ y ∈ interior M.X,
          DifferentiableAt ℝ (fun y => M.V (M.T - (k + 1) + 1) y z') y := by
        rw [he]; exact ih (by omega)
      exact (envelope_step h h6411 ht (hconc _ ht.le) (hCC _ ht) hbd hpar hint hD z
        hx).differentiableAt
  have hdiff : ∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X,
      DifferentiableAt ℝ (fun y => M.V t y z) x := fun t ht => by
    have := key (M.T - t) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self ht] at this
  refine ⟨hdiff, fun t ht z => ?_, fun t ht z x hx => ?_, hTd, fun t ht z x hx => ?_⟩
  · have hc := hconc t ht z
    exact oc_continuousOn_deriv_of_concave isOpen_interior
      (hc.subset interior_subset hc.1.interior) (hdiff t ht z)
  · exact envelope_step h h6411 ht (hconc t ht.le) (hCC t ht) hbd hpar hint
      (hdiff (t + 1) ht) z hx
  · exact foc_step h ht (hCC t ht) hbd hpar hint (hdiff (t + 1) ht) z hx

/-- `LocBounded` holds when `Z` is compact: `V_{t+1}(φ(y, b, z, z′), z′)` is continuous on the
compact set `B̄(x, r) × B̄(a, r) × Z ⊆ X × A × Z`. -/
theorem locBounded_of_compact [CompactSpace Z] (h : M.Standing P) : M.LocBounded := by
  intro t ht z x hx a ha
  obtain ⟨ε, hε, hεX⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  set r := min ε δ / 2
  have hm : 0 < min ε δ := lt_min hε hδ
  have hrdef : r = min ε δ / 2 := rfl
  have hr : 0 < r := by positivity
  have hrε : closedBall x r ⊆ M.X := fun y hy =>
    hεX (closedBall_subset_ball (by have := min_le_left ε δ; linarith) hy)
  have hrδ : closedBall a r ⊆ M.A := fun b hb =>
    hδA (closedBall_subset_ball (by have := min_le_right ε δ; linarith) hb)
  set K := closedBall x r ×ˢ closedBall a r ×ˢ (Set.univ : Set Z)
  have hK : IsCompact K := (isCompact_closedBall x r).prod
    ((isCompact_closedBall a r).prod isCompact_univ)
  have hφc : ContinuousOn (fun q : ℝ × ℝ × Z => M.φ q.1 q.2.1 z q.2.2) K :=
    h.a645.2.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk
      (continuous_const.prodMk continuous_snd.snd))).continuousOn
      fun q hq => ⟨hrε hq.1, hrδ hq.2.1, Set.mem_univ _⟩
  have hc : ContinuousOn (fun q : ℝ × ℝ × Z => M.V (t + 1) (M.φ q.1 q.2.1 z q.2.2) q.2.2) K :=
    (h.contV ht).comp (hφc.prodMk continuous_snd.snd.continuousOn) fun q hq =>
      ⟨h.a645.1 _ (hrε hq.1) _ (hrδ hq.2.1) _ _, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨r, hr, C, fun y hy b hb z' => ?_⟩
  have := hC (y, b, z') ⟨ball_subset_closedBall hy, ball_subset_closedBall hb, Set.mem_univ _⟩
  rwa [Real.norm_eq_abs] at this

/-- **Theorem 6.4.4 (Differentiability)** (Miao, p. 178), corrected, for `X, A ⊆ ℝ`. Under
Assumptions 6.4.1–6.4.14 (the standing hypotheses carrying 6.4.3–6.4.6), `β ≥ 0`, the
domination `LocBounded` (automatic for compact `Z`, `locBounded_of_compact`) and the interiority
`InteriorPolicy`: each `V_t(·, z)` is continuously differentiable on `int X`, the envelope
condition (6.31) holds for `t = 0, …, T − 1`, (6.32) holds, and the first-order condition (6.33)
holds for `t = 0, …, T − 1`. -/
theorem theorem_6_4_4 [IsMarkovKernel M.Q] (h : M.Standing P) (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (h6413 : M.Assumption6413) (h6414 : M.Assumption6414)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have hconc := theorem_6_4_3_concave h h641 h642 h647 h648 h649 h6410 h6411 h6412 hβ
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ
  refine theorem_6_4_4_core h h6411 (fun t ht z => (hconc t ht z).concaveOn) (fun t ht => ?_)
    hbd (partials_of h6413 h6414) hint
  exact compConcave_of_mono h641 h642 h.a645.1 h6412 (fun z' => (hconc (t + 1) ht z').concaveOn)
    fun z' => (hmono (t + 1) ht z').monotoneOn

/-- **Theorem 6.4.4 for `φ(x, a, z, z′) = a`** (Miao, p. 180): Assumptions 6.4.7–6.4.9 (and
6.4.12, 6.4.14) can be dispensed with. The conclusions are those of `theorem_6_4_4`. -/
theorem theorem_6_4_4_phi_eq_a [IsMarkovKernel M.Q] (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (h6413 : M.Assumption6413)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have haff : M.PhiAffine := fun z z' x _ x' _ a _ a' _ θ η _ _ _ => by simp only [hφ]
  have h6414 : M.Assumption6414 := fun z z' => by
    simp only [hφ]
    exact differentiable_snd.differentiableOn
  have hconc := concave_core h h641 h642 h6410 h6411 hβ fun t _ hV =>
    compConcave_of_affine h.a645.1 haff fun z' => (hV z').concaveOn
  exact theorem_6_4_4_core h h6411 (fun t ht z => (hconc t ht z).concaveOn)
    (fun t ht => compConcave_of_affine h.a645.1 haff fun z' => (hconc (t + 1) ht z').concaveOn)
    hbd (partials_of h6413 h6414) hint

/-- **The Euler equations** (Miao, p. 180): when `φ(x, a, z, z′) = a`, so that `x_{t+1} = a_t =
g_t(x_t, z_t)`, the first-order and envelope conditions combine into
`0 = ∂u_t(x_t, z_t, x_{t+1})/∂a + β E_t ∂u_{t+1}(x_{t+1}, z_{t+1}, x_{t+2})/∂x` for
`t = 0, …, T − 2`, with `x_{t+2} = g_{t+1}(x_{t+1}, z_{t+1})`, and
`0 = ∂u_{T−1}(x_{T−1}, z_{T−1}, x_T)/∂a + β E_{T−1} ∂u_T(x_T, z_T)/∂x`. -/
theorem euler_equations [IsMarkovKernel M.Q] (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (h6413 : M.Assumption6413)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t, t + 1 < M.T → ∀ z, ∀ x ∈ interior M.X,
      0 = deriv (fun b => M.u t x z b) (M.g t x z) + M.β * ∫ z',
        deriv (fun y => M.u (t + 1) y z' (M.g (t + 1) (M.g t x z) z')) (M.g t x z) ∂M.Q z) ∧
    ∀ t, t + 1 = M.T → ∀ z, ∀ x ∈ interior M.X,
      0 = deriv (fun b => M.u t x z b) (M.g t x z) + M.β * ∫ z',
        deriv (fun y => M.uT y z') (M.g t x z) ∂M.Q z := by
  obtain ⟨-, -, henv, hT, hfoc⟩ :=
    theorem_6_4_4_phi_eq_a h hφ h641 h642 h6410 h6411 h6413 hβ hbd hint
  have hdφa : ∀ x b z z', deriv (fun b' => M.φ x b' z z') b = 1 := fun x b z z' => by
    simp only [hφ, deriv_id'']
  have hdφx : ∀ y a z z', deriv (fun y' => M.φ y' a z z') y = 0 := fun y a z z' => by
    simp only [hφ, deriv_const']
  have hnext : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ z', M.g t x z ∈ interior M.X :=
    fun t ht z x hx z' => by simpa only [hφ] using (hint t ht z x hx).2 z'
  have hfoc' : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, 0 = deriv (fun b => M.u t x z b) (M.g t x z) +
      M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.g t x z) ∂M.Q z := fun t ht z x hx => by
    have := hfoc t ht z x hx
    simp only [focRHS, hφ, deriv_id'', mul_one] at this
    exact this.symm
  refine ⟨fun t ht z x hx => ?_, fun t ht z x hx => ?_⟩
  · rw [hfoc' t (by omega) z x hx]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    have := (henv (t + 1) ht z' _ (hnext t (by omega) z x hx z')).deriv
    simp only [envRHS, hdφx, mul_zero, integral_zero, add_zero] at this
    exact this
  · rw [hfoc' t (by omega) z x hx]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    have := (hT z' _ (hnext t (by omega) z x hx z')).deriv
    rw [← ht] at this
    exact this

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.5: the Maximum Principle

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCMaxPrinciple`), namespace renamed.

Miao, §6.5, pp. 180–183, with `X = A = ℝ` and `Γ(x, z) = A` (p. 180). The stochastic setting is a
probability space `(Ω, P)` with a filtration `(ℱ_t)` to which the shocks `z_t` are adapted; a
plan is an adapted process `(a_t)`, its states `x_t` follow (5.14) (`OCModel.path`), and the
objective is the Bolza form (6.28) (`OCModel.bolza`). `E_t` is the conditional expectation
`P[· | ℱ_t]` (Mathlib's `condExp`), so `E_t` conditions on the history of shocks; under the
Markov property (`IsMarkovCond`) it reduces to integration against `Q(z_t, ·)`.

* `Ha`, `Hx`: the derivatives of the Hamiltonian (6.37), `∂H_t/∂a = ∂u_t/∂a + β E_t[μ_{t+1} ∂φ/∂a]`
  and `∂H_t/∂x = ∂u_t/∂x + β E_t[μ_{t+1} ∂φ/∂x]`, the derivative taken inside `E_t` as in the
  book; `hamiltonian` is (6.37) itself. `MaxPrinciple`: the system (6.36), (6.38) (= (6.34)) and
  (6.39) (= (6.35)) along the states (5.14) of a plan.
* **Theorem 6.5.1** (`theorem_6_5_1`): a plan satisfying the system is optimal. **Departures.**
  (1) The book's hypothesis "`H_t(·, ·, z_t, μ_{t+1})` is concave" involves `E_t` of a function of
  the arguments, which is not well defined at the random arguments `(x_t, a_t)` the proof
  substitutes; we assume the pathwise Hamiltonian (`pathHam`)
  `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` concave in `(x, a)` for every `ω`, which is
  what the sufficient conditions of p. 183 give (`OCMaxPrincipleLinks`). (2) The telescoping
  needs integrability of the rewards and of `μ_{t+1}(x*_{t+1} − x_{t+1})`,
  `(x*_t − x_t) ∂u_t/∂x`, … for the optimal and the competing plan (`MPIntegrable`);
  optimality is among the plans for which these hold. (3) `β ≥ 0` is used.
* `oc_tangent_le`, `oc_supergradient`: tangent-line inequalities for differentiable concave
  functions on `ℝ` and `ℝ²`; `path_measurable`: the states of an adapted plan are adapted.

The sufficient conditions of p. 183, the link with dynamic programming and the deterministic
case (6.40) are in `OCMaxPrincipleLinks`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### Two tangent-line inequalities for concave functions -/

/-- A differentiable concave function lies below its tangent line. -/
theorem oc_tangent_le {f : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ f) {p : ℝ}
    (hd : DifferentiableAt ℝ f p) (q : ℝ) : f q ≤ f p + deriv f p * (q - p) := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have := hc.slope_le_deriv (Set.mem_univ p) (Set.mem_univ q) hpq hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.deriv_le_slope (Set.mem_univ q) (Set.mem_univ p) hqp hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- **The supergradient inequality on `ℝ²`**: a concave function differentiable at `p` satisfies
`h(q) ≤ h(p) + (q₁ − p₁) ∂₁h(p) + (q₂ − p₂) ∂₂h(p)`. -/
theorem oc_supergradient {h : ℝ × ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ h) {p : ℝ × ℝ}
    (hd : DifferentiableAt ℝ h p) (q : ℝ × ℝ) :
    h q ≤ h p + (q.1 - p.1) * deriv (fun y => h (y, p.2)) p.1 +
      (q.2 - p.2) * deriv (fun b => h (p.1, b)) p.2 := by
  set L := fderiv ℝ h p
  have hL : HasFDerivAt h L p := hd.hasFDerivAt
  have h1 : deriv (fun y => h (y, p.2)) p.1 = L (1, 0) := by
    have : HasDerivAt (fun y : ℝ => (y, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hL.comp_hasDerivAt p.1 this).deriv
  have h2 : deriv (fun b => h (p.1, b)) p.2 = L (0, 1) := by
    have : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hL.comp_hasDerivAt p.2 this).deriv
  -- restrict to the segment from `p` to `q`
  set g : ℝ → ℝ := h ∘ AffineMap.lineMap p q
  have hgc : ConcaveOn ℝ Set.univ g := by
    have := hc.comp_affineMap (AffineMap.lineMap p q)
    rwa [Set.preimage_univ] at this
  have hgd : HasDerivAt g (L (q - p)) 0 := by
    have hl : HasDerivAt (AffineMap.lineMap p q : ℝ → ℝ × ℝ) (q - p) 0 :=
      AffineMap.hasDerivAt_lineMap
    have hL0 : HasFDerivAt h L (AffineMap.lineMap p q (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]; exact hL
    exact hL0.comp_hasDerivAt 0 hl
  have ht := oc_tangent_le hgc hgd.differentiableAt 1
  simp only [g, Function.comp_apply, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
    hgd.deriv, sub_zero, mul_one] at ht
  have hdec : q - p = (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) + (q.2 - p.2) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at ht
  rw [h1, h2]
  linarith

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}
  (M : OCModel ℝ ℝ Z) (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z)

/-- The states of an adapted plan are adapted when `φ` is measurable. -/
theorem path_measurable (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    {a : ℕ → Ω → ℝ} (ha : ∀ t, Measurable[ℱ t] (a t)) (x₀ : ℝ) :
    ∀ t, Measurable[ℱ t] (M.path z a x₀ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hle : ℱ t ≤ ℱ (t + 1) := ℱ.mono (Nat.le_succ t)
    exact hφm.comp ((ih.mono hle le_rfl).prodMk ((ha t |>.mono hle le_rfl).prodMk
      ((hz t |>.mono hle le_rfl).prodMk (hz (t + 1)))))

/-- `∂H_t/∂a` along a plan, (6.34)/(6.38): `∂u_t(x_t, z_t, a_t)/∂a +
β E_t[μ_{t+1} ∂φ(x_t, a_t, z_t, z_{t+1})/∂a]`. -/
noncomputable def Ha (μ x a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  deriv (fun b => M.u t (x t ω) (z t ω) b) (a t ω) + M.β * (P[fun ω' => μ (t + 1) ω' *
    deriv (fun b => M.φ (x t ω') b (z t ω') (z (t + 1) ω')) (a t ω') | ℱ t]) ω

/-- `∂H_t/∂x` along a plan, (6.35)/(6.39): `∂u_t(x_t, z_t, a_t)/∂x +
β E_t[μ_{t+1} ∂φ(x_t, a_t, z_t, z_{t+1})/∂x]`. -/
noncomputable def Hx (μ x a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  deriv (fun y => M.u t y (z t ω) (a t ω)) (x t ω) + M.β * (P[fun ω' => μ (t + 1) ω' *
    deriv (fun y => M.φ y (a t ω') (z t ω') (z (t + 1) ω')) (x t ω') | ℱ t]) ω

/-- **The Hamiltonian (6.37)** (Miao, p. 181) at a deterministic `(x, a)`:
`H_t(x, a, z_t, μ_{t+1}) = u_t(x, z_t, a) + β E_t[μ_{t+1} φ(x, a, z_t, z_{t+1})]`. -/
noncomputable def hamiltonian (μ : ℕ → Ω → ℝ) (t : ℕ) (x a : ℝ) : Ω → ℝ := fun ω =>
  M.u t x (z t ω) a + M.β * (P[fun ω' => μ (t + 1) ω' * M.φ x a (z t ω') (z (t + 1) ω') | ℱ t]) ω

/-- The **pathwise Hamiltonian** `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` at `ω`. -/
def pathHam (μ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (p : ℝ × ℝ) : ℝ :=
  M.u t p.1 (z t ω) p.2 + M.β * (μ (t + 1) ω * M.φ p.1 p.2 (z t ω) (z (t + 1) ω))

/-- **The Maximum Principle system** (Miao, pp. 181–182): along the states `x` of the plan `a`,
(6.38) `∂H_t/∂a = 0` (`t < T`), (6.39) `∂H_t/∂x = μ_t` (`1 ≤ t < T`) and (6.36)
`μ_T = ∂u_T(x_T, z_T)/∂x`, almost surely. -/
structure MaxPrinciple (μ x a : ℕ → Ω → ℝ) : Prop where
  foc_a : ∀ t < M.T, M.Ha P ℱ z μ x a t =ᵐ[P] 0
  foc_x : ∀ t, 1 ≤ t → t < M.T → μ t =ᵐ[P] M.Hx P ℱ z μ x a t
  terminal : μ M.T =ᵐ[P] fun ω => deriv (fun y => M.uT y (z M.T ω)) (x M.T ω)

/-- The integrability needed for the telescoping in the proof of Theorem 6.5.1, for the
candidate `(xs, as)` with multipliers `μ` and a competing plan `(x, a)`. -/
structure MPIntegrable (μ xs as x a : ℕ → Ω → ℝ) : Prop where
  u_s : ∀ t < M.T, Integrable (fun ω => M.u t (xs t ω) (z t ω) (as t ω)) P
  u_c : ∀ t < M.T, Integrable (fun ω => M.u t (x t ω) (z t ω) (a t ω)) P
  uT_s : Integrable (fun ω => M.uT (xs M.T ω) (z M.T ω)) P
  uT_c : Integrable (fun ω => M.uT (x M.T ω) (z M.T ω)) P
  μΔ : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) P
  ux : ∀ t < M.T,
    Integrable (fun ω => (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω)) P
  φx : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P
  φxΔ : ∀ t < M.T, Integrable (fun ω => (xs t ω - x t ω) * (μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) P
  ua : ∀ t < M.T,
    Integrable (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω)) P
  φa : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P
  φaΔ : ∀ t < M.T, Integrable (fun ω => (as t ω - a t ω) * (μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω))) P
  uTx : Integrable (fun ω => (xs M.T ω - x M.T ω) * deriv (fun y => M.uT y (z M.T ω)) (xs M.T ω)) P

variable {M P ℱ z}

/-- `E[Δ W] = E[Δ E_t W]` for `ℱ_t`-measurable `Δ` (the tower property used in the proof). -/
theorem oc_integral_mul_condExp [IsFiniteMeasure P] {t : ℕ} {Δ W : Ω → ℝ}
    (hΔ : StronglyMeasurable[ℱ t] Δ) (hΔW : Integrable (fun ω => Δ ω * W ω) P)
    (hW : Integrable W P) :
    Integrable (fun ω => Δ ω * (P[W | ℱ t]) ω) P ∧
      ∫ ω, Δ ω * W ω ∂P = ∫ ω, Δ ω * (P[W | ℱ t]) ω ∂P := by
  have hpull : P[fun ω => Δ ω * W ω | ℱ t] =ᵐ[P] fun ω => Δ ω * (P[W | ℱ t]) ω :=
    condExp_mul_of_stronglyMeasurable_left hΔ hΔW hW
  refine ⟨integrable_condExp.congr hpull, ?_⟩
  rw [← integral_condExp (ℱ.le t)]
  exact integral_congr_ae hpull

/-- **Theorem 6.5.1 (sufficiency of the Maximum Principle)** (Miao, p. 182), with `X = A = ℝ` and
`Γ = A`, so that every adapted plan is feasible. Let the plan `as` with states `xs` (5.14) and
multipliers `μ` satisfy (6.36), (6.38) and (6.39); let the pathwise Hamiltonian
`u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` be concave in `(x, a)` and `u_T(·, z)` be
concave; let Assumptions 6.4.13–6.4.14 hold and `β ≥ 0`. Then for every adapted plan `a` with the
integrability `MPIntegrable`, the objective (6.28) of `a` is at most that of `as`. -/
theorem theorem_6_5_1 [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hX : M.X = Set.univ) (hA : M.A = Set.univ) (h6413 : M.Assumption6413)
    (h6414 : M.Assumption6414) (hβ : 0 ≤ M.β) (x₀ : ℝ) {μ as a : ℕ → Ω → ℝ}
    (has : ∀ t, Measurable[ℱ t] (as t)) (ha : ∀ t, Measurable[ℱ t] (a t))
    (hmp : M.MaxPrinciple P ℱ z μ (M.path z as x₀) as)
    (hH : ∀ t < M.T, ∀ ω, ConcaveOn ℝ Set.univ (M.pathHam z μ t ω))
    (huT : ∀ z', ConcaveOn ℝ Set.univ fun x => M.uT x z')
    (hint : M.MPIntegrable P z μ (M.path z as x₀) as (M.path z a x₀) a) :
    M.bolza P z a x₀ ≤ M.bolza P z as x₀ := by
  set xs := M.path z as x₀ with hxsdef
  set x := M.path z a x₀ with hxdef
  have hU : interior (M.X ×ˢ M.A) = Set.univ := by
    rw [hX, hA, Set.univ_prod_univ, interior_univ]
  have hud : ∀ t < M.T, ∀ z0 (p : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 z0 p.2) p := fun t ht z0 p => by
    have := (h6413.2 t ht z0).differentiableOn one_ne_zero
    rw [hU] at this
    exact this.differentiableAt Filter.univ_mem
  have hφd : ∀ z0 z1 (p : ℝ × ℝ), DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 z0 z1) p :=
    fun z0 z1 p => by
      have := h6414 z0 z1
      rw [hU] at this
      exact this.differentiableAt Filter.univ_mem
  have huTd : ∀ z0 (y : ℝ), DifferentiableAt ℝ (fun y => M.uT y z0) y := fun z0 y => by
    have := h6413.1 z0
    rw [hX, interior_univ] at this
    exact this.differentiableAt Filter.univ_mem
  have hxs : ∀ t, Measurable[ℱ t] (xs t) := M.path_measurable ℱ z hz hφm has x₀
  have hx : ∀ t, Measurable[ℱ t] (x t) := M.path_measurable ℱ z hz hφm ha x₀
  set c : ℕ → ℝ := fun t => ∫ ω, μ t ω * (xs t ω - x t ω) ∂P with hcdef
  have hc0 : c 0 = 0 := by simp [c, xs, x, path]
  -- the period-`t` inequality
  have hper : ∀ t < M.T, c t - M.β * c (t + 1) ≤
      (∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) - ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P := by
    intro t ht
    -- pathwise: the supergradient inequality for the pathwise Hamiltonian
    have hpath : ∀ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) +
        M.β * ((xs t ω - x t ω) * (μ (t + 1) ω *
          deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) +
        ((as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)))) ≤
        M.u t (xs t ω) (z t ω) (as t ω) - M.u t (x t ω) (z t ω) (a t ω) +
          M.β * (μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) := by
      intro ω
      set p : ℝ × ℝ := (xs t ω, as t ω)
      have hdH : DifferentiableAt ℝ (M.pathHam z μ t ω) p :=
        (hud t ht _ p).add ((hφd _ _ p).const_mul _ |>.const_mul _)
      have hsg := oc_supergradient (hH t ht ω) hdH (x t ω, a t ω)
      have hdx : deriv (fun y => M.pathHam z μ t ω (y, p.2)) p.1 =
          deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) + M.β * (μ (t + 1) ω *
            deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) := by
        have h1 : DifferentiableAt ℝ (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) := by
          have hg := hud t ht (z t ω) p
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        have h2 : DifferentiableAt ℝ (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω) := by
          have hg := hφd (z t ω) (z (t + 1) ω) p
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      have hda : deriv (fun b => M.pathHam z μ t ω (p.1, b)) p.2 =
          deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) + M.β * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) := by
        have h1 : DifferentiableAt ℝ (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) := by
          have hg := hud t ht (z t ω) p
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        have h2 : DifferentiableAt ℝ (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
          have hg := hφd (z t ω) (z (t + 1) ω) p
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      rw [hdx, hda] at hsg
      have e1 : xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω) := rfl
      have e2 : x (t + 1) ω = M.φ (x t ω) (a t ω) (z t ω) (z (t + 1) ω) := rfl
      simp only [pathHam, p] at hsg
      rw [e1, e2]
      nlinarith [hsg]
    -- integrate
    have hΔx : StronglyMeasurable[ℱ t] fun ω => xs t ω - x t ω :=
      ((hxs t).sub (hx t)).stronglyMeasurable
    have hΔa : StronglyMeasurable[ℱ t] fun ω => as t ω - a t ω :=
      ((has t).sub (ha t)).stronglyMeasurable
    obtain ⟨iX, eX⟩ := oc_integral_mul_condExp hΔx (hint.φxΔ t ht) (hint.φx t ht)
    obtain ⟨iA, eA⟩ := oc_integral_mul_condExp hΔa (hint.φaΔ t ht) (hint.φa t ht)
    have hmono := integral_mono (((hint.ux t ht).add ((hint.φxΔ t ht).const_mul M.β)).add
      ((hint.ua t ht).add ((hint.φaΔ t ht).const_mul M.β)))
      (((hint.u_s t ht).sub (hint.u_c t ht)).add ((hint.μΔ t ht).const_mul M.β)) hpath
    rw [integral_add' ((hint.ux t ht).add ((hint.φxΔ t ht).const_mul M.β))
        ((hint.ua t ht).add ((hint.φaΔ t ht).const_mul M.β)),
      integral_add' (hint.ux t ht) ((hint.φxΔ t ht).const_mul M.β),
      integral_add' (hint.ua t ht) ((hint.φaΔ t ht).const_mul M.β),
      integral_add' ((hint.u_s t ht).sub (hint.u_c t ht)) ((hint.μΔ t ht).const_mul M.β),
      integral_sub' (hint.u_s t ht) (hint.u_c t ht), integral_const_mul, integral_const_mul,
      integral_const_mul, eX, eA] at hmono
    -- the `a`-terms vanish by (6.38)
    have hAzero : (∫ ω, (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) ∂P)
        + M.β * ∫ ω, (as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω ∂P = 0 := by
      rw [← integral_const_mul, ← integral_add (hint.ua t ht) (iA.const_mul M.β)]
      have : (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
            deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω)) =ᵐ[P]
          fun _ => (0 : ℝ) := by
        filter_upwards [hmp.foc_a t ht] with ω hω
        simp only [Ha, Pi.zero_apply] at hω
        linear_combination (as t ω - a t ω) * hω
      rw [integral_congr_ae this, integral_zero]
    -- the `x`-terms are `c t` by (6.39), or vanish at `t = 0`
    have hXc : (∫ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) ∂P)
        + M.β * ∫ ω, (xs t ω - x t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun y => M.φ y (as t ω') (z t ω') (z (t + 1) ω')) (xs t ω') | ℱ t]) ω ∂P =
          c t := by
      rw [← integral_const_mul, ← integral_add (hint.ux t ht) (iX.const_mul M.β)]
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · rw [hc0]
        have : ∀ ω, xs 0 ω - x 0 ω = 0 := fun ω => by simp [xs, x, path]
        simp [this]
      · refine integral_congr_ae ?_
        filter_upwards [hmp.foc_x t ht1 ht] with ω hω
        simp only [Hx] at hω
        rw [hω]
        ring
    linarith [hmono]
  -- the terminal inequality
  have hterm : c M.T ≤ (∫ ω, M.uT (xs M.T ω) (z M.T ω) ∂P) - ∫ ω, M.uT (x M.T ω) (z M.T ω) ∂P := by
    have hpath : ∀ ω, (xs M.T ω - x M.T ω) * deriv (fun y => M.uT y (z M.T ω)) (xs M.T ω) ≤
        M.uT (xs M.T ω) (z M.T ω) - M.uT (x M.T ω) (z M.T ω) := fun ω => by
      have := oc_tangent_le (huT (z M.T ω)) (huTd _ (xs M.T ω)) (x M.T ω)
      nlinarith [this]
    have hmono := integral_mono hint.uTx (hint.uT_s.sub hint.uT_c) hpath
    rw [integral_sub' hint.uT_s hint.uT_c] at hmono
    refine le_trans (le_of_eq ?_) hmono
    refine integral_congr_ae ?_
    filter_upwards [hmp.terminal] with ω hω
    rw [hω]
    ring
  -- assemble: `D ≥ Σ βᵗ (c_t − β c_{t+1}) + β^T c_T = c_0 = 0`
  have hbolza : ∀ (b : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ),
      (∀ t < M.T, Integrable (fun ω => M.u t (y t ω) (z t ω) (b t ω)) P) →
      Integrable (fun ω => M.uT (y M.T ω) (z M.T ω)) P →
      ∫ ω, ((∑ t ∈ Finset.range M.T, M.β ^ t * M.u t (y t ω) (z t ω) (b t ω)) +
        M.β ^ M.T * M.uT (y M.T ω) (z M.T ω)) ∂P =
      (∑ t ∈ Finset.range M.T, M.β ^ t * ∫ ω, M.u t (y t ω) (z t ω) (b t ω) ∂P) +
        M.β ^ M.T * ∫ ω, M.uT (y M.T ω) (z M.T ω) ∂P := fun b y hi hT => by
    have hi' : ∀ t ∈ Finset.range M.T,
        Integrable (fun ω => M.β ^ t * M.u t (y t ω) (z t ω) (b t ω)) P :=
      fun t htm => (hi t (Finset.mem_range.1 htm)).const_mul _
    rw [integral_add (integrable_finsetSum _ hi') (hT.const_mul _), integral_finsetSum _ hi',
      integral_const_mul]
    simp only [integral_const_mul]
  have hs := hbolza as xs hint.u_s hint.uT_s
  have hc := hbolza a x hint.u_c hint.uT_c
  simp only [bolza]
  rw [hs, hc]
  have htel : (∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1))) + M.β ^ M.T * c M.T =
      c 0 := by
    have h1 : ∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1)) =
        ∑ t ∈ Finset.range M.T, (M.β ^ t * c t - M.β ^ (t + 1) * c (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by ring
    rw [h1, Finset.sum_range_sub' (fun t => M.β ^ t * c t) M.T]
    simp
  have hsum : (∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1))) ≤
      ∑ t ∈ Finset.range M.T, M.β ^ t * ((∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) -
        ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P) :=
    Finset.sum_le_sum fun t htm =>
      mul_le_mul_of_nonneg_left (hper t (Finset.mem_range.1 htm)) (pow_nonneg hβ t)
  have hT := mul_le_mul_of_nonneg_left hterm (pow_nonneg hβ M.T)
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum hT ⊢
  rw [hc0] at htel
  simp only [mul_sub, Finset.sum_sub_distrib] at htel
  linarith

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.5: concave Hamiltonians, dynamic programming, deterministic transitions

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCMaxPrincipleLinks`), namespace renamed.

Miao, §6.5, pp. 183–184.

* **Sufficient conditions for a concave Hamiltonian** (p. 183): the pathwise Hamiltonian
  `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` is concave in `(x, a)` if `u_t` and `φ` are
  concave and `β μ_{t+1} ≥ 0` (`pathHam_concave_of_concave`), or if `φ` is affine, whatever the
  sign of `μ_{t+1}` (`pathHam_concave_of_affine`).
* **The link `μ_t = ∂V_t(x_t, z_t)/∂x`** (p. 183). `IsMarkovCond`: `E_t` of a function of
  `(X_t, A_t, z_t, z_{t+1})`, `X_t, A_t` `ℱ_t`-measurable, is the integral against `Q(z_t, ·)`.
  With `μ_{t+1} = ∂V_{t+1}(x_{t+1}, z_{t+1})/∂x`, `∂H_t/∂a` is the right side of (6.33) and
  `∂H_t/∂x` that of (6.31) along the path (`link_6_38_6_33`, `link_6_39_6_31`), so
  (6.38) ⇔ (6.33) and (6.39) ⇔ (6.31). `maxPrinciple_of_dp`: the states generated by the policy
  functions, with `μ_t = ∂V_t(x_t, z_t)/∂x`, satisfy the Maximum Principle system whenever
  Theorem 6.4.4's conclusions hold along the path.
* **Deterministic transitions** (p. 184): if `x_{t+1} = φ(x_t, a_t, z_t)` and
  `λ_t = β E_t μ_{t+1}`, (6.34) becomes `∂u_t/∂a + λ_t ∂φ/∂a = 0` (`eq_6_40_a`), (6.35) at
  `t + 1` gives `λ_t = β E_t ∂u_{t+1}/∂x + β E_t[λ_{t+1} ∂φ/∂x]` (`eq_6_40_b`), and (6.36)
  gives `λ_{T−1} = β E_{T−1} ∂u_T(x_T, z_T)/∂x` (`eq_6_40_terminal`). **Correction:** the book
  prints `λ_{T−1} = E_{T−1}[u_T(x_T, z_T)]`, without the derivative and without `β`; with it the
  first-order system can be inconsistent (`eq_6_40_terminal_misprint`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}
  {M : OCModel ℝ ℝ Z} {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **Concave Hamiltonian, first sufficient condition** (Miao, p. 183): `u_t(·, z, ·)` concave,
`φ(·, ·, z, z′)` concave and `β μ_{t+1} ≥ 0`. -/
theorem pathHam_concave_of_concave {μ : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hu : ConcaveOn ℝ Set.univ fun p : ℝ × ℝ => M.u t p.1 (z t ω) p.2)
    (hφ : ConcaveOn ℝ Set.univ fun p : ℝ × ℝ => M.φ p.1 p.2 (z t ω) (z (t + 1) ω))
    (hβ : 0 ≤ M.β) (hμ : 0 ≤ μ (t + 1) ω) : ConcaveOn ℝ Set.univ (M.pathHam z μ t ω) := by
  have h := hu.add ((hφ.smul hμ).smul hβ)
  refine h.congr fun p _ => ?_
  simp only [pathHam, Pi.add_apply, smul_eq_mul]

/-- **Concave Hamiltonian, second sufficient condition** (Miao, p. 183): if `φ(·, ·, z, z′)` is
affine, the sign of `μ_{t+1}` does not matter. -/
theorem pathHam_concave_of_affine {μ : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hu : ConcaveOn ℝ Set.univ fun p : ℝ × ℝ => M.u t p.1 (z t ω) p.2)
    (hφ : ∀ p q : ℝ × ℝ, ∀ θ η : ℝ, θ + η = 1 →
      M.φ (θ • p + η • q).1 (θ • p + η • q).2 (z t ω) (z (t + 1) ω) =
        θ * M.φ p.1 p.2 (z t ω) (z (t + 1) ω) + η * M.φ q.1 q.2 (z t ω) (z (t + 1) ω)) :
    ConcaveOn ℝ Set.univ (M.pathHam z μ t ω) := by
  have hl : ConcaveOn ℝ Set.univ fun p : ℝ × ℝ =>
      M.β * (μ (t + 1) ω * M.φ p.1 p.2 (z t ω) (z (t + 1) ω)) := by
    refine ⟨convex_univ, fun p _ q _ θ η _ _ hs => ?_⟩
    simp only [smul_eq_mul]
    rw [hφ p q θ η hs]
    nlinarith
  exact hu.add hl

/-- **The Markov property** in the form used to evaluate `E_t`: for measurable `G` and
`ℱ_t`-measurable `X_t`, `A_t`, `E_t[G(X_t, A_t, z_t, z_{t+1})] = ∫ G(X_t, A_t, z_t, z′) Q(z_t, dz′)`
almost surely. -/
def IsMarkovCond (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (Q : Kernel Z Z) :
    Prop :=
  ∀ t (G : ℝ × ℝ × Z × Z → ℝ), Measurable G → ∀ X A : Ω → ℝ, Measurable[ℱ t] X →
    Measurable[ℱ t] A → Integrable (fun ω => G (X ω, A ω, z t ω, z (t + 1) ω)) P →
    P[fun ω => G (X ω, A ω, z t ω, z (t + 1) ω) | ℱ t] =ᵐ[P]
      fun ω => ∫ z', G (X ω, A ω, z t ω, z') ∂Q (z t ω)

/-- **(6.38) is (6.33)** (Miao, p. 183): if `μ_{t+1} = ∂V_{t+1}(x_{t+1}, z_{t+1})/∂x` and `E_t` is
integration against `Q(z_t, ·)`, then along the path `∂H_t/∂a` equals the right side of the
first-order condition (6.33). -/
theorem link_6_38_6_33 (hM : IsMarkovCond P ℱ z M.Q) {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hμ : ∀ ω, μ (t + 1) ω = deriv (fun y => M.V (t + 1) y (z (t + 1) ω)) (xs (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => M.V (t + 1) y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun b => M.φ p.1 b p.2.2.1 p.2.2.2) p.2.1)
    (hI : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P) :
    M.Ha P ℱ z μ xs as t =ᵐ[P] fun ω => M.focRHS t (xs t ω) (z t ω) (as t ω) := by
  have heq : (fun ω => μ (t + 1) ω * deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω))
      (as t ω)) = fun ω => deriv (fun y => M.V (t + 1) y (z (t + 1) ω))
        (M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω)) *
        deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
    funext ω; rw [hμ, hstate]
  rw [heq] at hI
  have hc := hM t _ hG (xs t) (as t) hxs has hI
  filter_upwards [hc] with ω hω
  simp only [Ha, focRHS]
  rw [heq, hω]

/-- **(6.39) is (6.31)** (Miao, p. 183): with `μ_{t+1} = ∂V_{t+1}(x_{t+1}, z_{t+1})/∂x`, along the
path `∂H_t/∂x` equals the right side of the envelope condition (6.31). -/
theorem link_6_39_6_31 (hM : IsMarkovCond P ℱ z M.Q) {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hμ : ∀ ω, μ (t + 1) ω = deriv (fun y => M.V (t + 1) y (z (t + 1) ω)) (xs (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => M.V (t + 1) y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun y => M.φ y p.2.1 p.2.2.1 p.2.2.2) p.1)
    (hI : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P) :
    M.Hx P ℱ z μ xs as t =ᵐ[P] fun ω => M.envRHS t (xs t ω) (z t ω) (as t ω) := by
  have heq : (fun ω => μ (t + 1) ω * deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω))
      (xs t ω)) = fun ω => deriv (fun y => M.V (t + 1) y (z (t + 1) ω))
        (M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω)) *
        deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω) := by
    funext ω; rw [hμ, hstate]
  rw [heq] at hI
  have hc := hM t _ hG (xs t) (as t) hxs has hI
  filter_upwards [hc] with ω hω
  simp only [Hx, envRHS]
  rw [heq, hω]

/-- **Dynamic programming gives the Maximum Principle** (Miao, p. 183). Let `xs` be the states
generated by the policy functions, `as_t = g_t(xs_t, z_t)`, staying in `int X`, and let the
conclusions of Theorem 6.4.4 hold (`henv`, `hTd`, `hfoc`). Then the shadow values
`μ_t = ∂V_t(x_t, z_t)/∂x` satisfy (6.36), (6.38) and (6.39), given the Markov property and the
measurability and integrability of the integrands. -/
theorem maxPrinciple_of_dp (hM : IsMarkovCond P ℱ z M.Q) {xs as : ℕ → Ω → ℝ}
    (hxs : ∀ t, Measurable[ℱ t] (xs t)) (has : ∀ t, Measurable[ℱ t] (as t))
    (hstate : ∀ t ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hpol : ∀ t ω, as t ω = M.g t (xs t ω) (z t ω))
    (hin : ∀ t ω, xs t ω ∈ interior M.X)
    (henv : ∀ t < M.T, ∀ z', ∀ x ∈ interior M.X,
      HasDerivAt (fun y => M.V t y z') (M.envRHS t x z' (M.g t x z')) x)
    (hTd : ∀ z', ∀ x ∈ interior M.X,
      HasDerivAt (fun y => M.V M.T y z') (deriv (fun y => M.uT y z') x) x)
    (hfoc : ∀ t < M.T, ∀ z', ∀ x ∈ interior M.X, M.focRHS t x z' (M.g t x z') = 0)
    (hGa : ∀ t, Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => M.V (t + 1) y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun b => M.φ p.1 b p.2.2.1 p.2.2.2) p.2.1)
    (hGx : ∀ t, Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => M.V (t + 1) y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun y => M.φ y p.2.1 p.2.2.1 p.2.2.2) p.1)
    (hIa : ∀ t, Integrable (fun ω => deriv (fun y => M.V (t + 1) y (z (t + 1) ω)) (xs (t + 1) ω) *
      deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P)
    (hIx : ∀ t, Integrable (fun ω => deriv (fun y => M.V (t + 1) y (z (t + 1) ω)) (xs (t + 1) ω) *
      deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P) :
    M.MaxPrinciple P ℱ z (fun t ω => deriv (fun y => M.V t y (z t ω)) (xs t ω)) xs as := by
  refine ⟨fun t ht => ?_, fun t _ ht => ?_, ?_⟩
  · refine (link_6_38_6_33 hM (hxs t) (has t) (hstate t) (fun _ => rfl) (hGa t)
      (hIa t)).trans (Eventually.of_forall fun ω => ?_)
    simp only [Pi.zero_apply]
    rw [hpol t ω]
    exact hfoc t ht _ _ (hin t ω)
  · refine EventuallyEq.trans (Eventually.of_forall fun ω => ?_)
      (link_6_39_6_31 hM (hxs t) (has t) (hstate t) (fun _ => rfl) (hGx t) (hIx t)).symm
    simp only
    rw [hpol t ω]
    exact (henv t ht _ _ (hin t ω)).deriv
  · exact Eventually.of_forall fun ω => (hTd _ _ (hin M.T ω)).deriv

/-! ### Deterministic transitions: (6.40) -/

/-- The multiplier of (6.40), `λ_t = β E_t μ_{t+1}` (Miao, p. 184). -/
noncomputable def lam (P : Measure Ω) (ℱ : Filtration ℕ m0) (β : ℝ) (μ : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => β * (P[μ (t + 1) | ℱ t]) ω

/-- **(6.40), first equation** (Miao, p. 184): when `∂φ(x_t, a_t, z_t)/∂a` is `ℱ_t`-measurable
(as it is when `φ` does not depend on `z_{t+1}`), `∂H_t/∂a = ∂u_t/∂a + λ_t ∂φ/∂a`; hence (6.34)
is `∂u_t/∂a + λ_t ∂φ/∂a = 0`. -/
theorem eq_6_40_a [IsFiniteMeasure P] {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hφa : StronglyMeasurable[ℱ t]
      fun ω => deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω))
    (hI : Integrable (fun ω => deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) *
      μ (t + 1) ω) P) (hμ : Integrable (μ (t + 1)) P) :
    M.Ha P ℱ z μ xs as t =ᵐ[P] fun ω => deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
      lam P ℱ M.β μ t ω * deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hφa hI hμ
  have hcomm : (fun ω => μ (t + 1) ω * deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω))
      (as t ω)) = (fun ω => deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) *
        μ (t + 1) := funext fun ω => mul_comm _ _
  filter_upwards [hpull] with ω hω
  simp only [Ha, lam]
  rw [hcomm, hω]
  simp only [Pi.mul_apply]
  ring

/-- **(6.40), second equation** (Miao, p. 184): if (6.35) holds at `t + 1 < T` and
`∂φ(x_{t+1}, a_{t+1}, z_{t+1})/∂x` is `ℱ_{t+1}`-measurable, then
`λ_t = β E_t[∂u_{t+1}/∂x] + β E_t[λ_{t+1} ∂φ/∂x]`. -/
theorem eq_6_40_b [IsFiniteMeasure P] {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (h635 : μ (t + 1) =ᵐ[P] M.Hx P ℱ z μ xs as (t + 1))
    (hφx : StronglyMeasurable[ℱ (t + 1)]
      fun ω => deriv (fun y => M.φ y (as (t + 1) ω) (z (t + 1) ω) (z (t + 2) ω)) (xs (t + 1) ω))
    (hI : Integrable (fun ω => deriv (fun y => M.φ y (as (t + 1) ω) (z (t + 1) ω) (z (t + 2) ω))
      (xs (t + 1) ω) * μ (t + 2) ω) P) (hμ : Integrable (μ (t + 2)) P)
    (hux : Integrable (fun ω => deriv (fun y => M.u (t + 1) y (z (t + 1) ω) (as (t + 1) ω))
      (xs (t + 1) ω)) P)
    (hlφ : Integrable (fun ω => lam P ℱ M.β μ (t + 1) ω *
      deriv (fun y => M.φ y (as (t + 1) ω) (z (t + 1) ω) (z (t + 2) ω)) (xs (t + 1) ω)) P) :
    lam P ℱ M.β μ t =ᵐ[P] fun ω =>
      M.β * (P[fun ω' => deriv (fun y => M.u (t + 1) y (z (t + 1) ω') (as (t + 1) ω'))
        (xs (t + 1) ω') | ℱ t]) ω +
      M.β * (P[fun ω' => lam P ℱ M.β μ (t + 1) ω' *
        deriv (fun y => M.φ y (as (t + 1) ω') (z (t + 1) ω') (z (t + 2) ω')) (xs (t + 1) ω') |
          ℱ t]) ω := by
  -- `μ_{t+1} = ∂u_{t+1}/∂x + λ_{t+1} ∂φ/∂x`
  have hpull := condExp_mul_of_stronglyMeasurable_left hφx hI hμ
  have hμeq : μ (t + 1) =ᵐ[P] (fun ω =>
      deriv (fun y => M.u (t + 1) y (z (t + 1) ω) (as (t + 1) ω)) (xs (t + 1) ω)) +
      fun ω => lam P ℱ M.β μ (t + 1) ω *
        deriv (fun y => M.φ y (as (t + 1) ω) (z (t + 1) ω) (z (t + 2) ω)) (xs (t + 1) ω) := by
    have hcomm : (fun ω => μ (t + 1 + 1) ω * deriv (fun y => M.φ y (as (t + 1) ω) (z (t + 1) ω)
        (z (t + 1 + 1) ω)) (xs (t + 1) ω)) = (fun ω => deriv (fun y => M.φ y (as (t + 1) ω)
          (z (t + 1) ω) (z (t + 2) ω)) (xs (t + 1) ω)) * μ (t + 2) :=
      funext fun ω => mul_comm _ _
    filter_upwards [h635, hpull] with ω h1 h2
    rw [h1]
    simp only [Hx, lam, Pi.add_apply]
    rw [hcomm, h2]
    simp only [Pi.mul_apply]
    ring
  have hc := condExp_congr_ae (m := ℱ t) hμeq
  have hadd := condExp_add hux hlφ (ℱ t)
  filter_upwards [hc, hadd] with ω h1 h2
  change M.β * (P[μ (t + 1) | ℱ t]) ω = _
  rw [h1, h2, Pi.add_apply, mul_add]

/-- **(6.40), terminal condition, corrected** (Miao, p. 184): from (6.36),
`λ_{T−1} = β E_{T−1}[∂u_T(x_T, z_T)/∂x]`. -/
theorem eq_6_40_terminal {μ xs as : ℕ → Ω → ℝ} {t : ℕ} (ht : t + 1 = M.T)
    (hmp : M.MaxPrinciple P ℱ z μ xs as) :
    lam P ℱ M.β μ t =ᵐ[P] fun ω => M.β *
      (P[fun ω' => deriv (fun y => M.uT y (z (t + 1) ω')) (xs (t + 1) ω') | ℱ t]) ω := by
  have h := hmp.terminal
  rw [← ht] at h
  filter_upwards [condExp_congr_ae (m := ℱ t) h] with ω hω
  simp only [lam]
  rw [hω]

/-- **The printed terminal condition of (6.40) is wrong** (Miao, p. 184). Take one period,
`x₁ = φ(x₀, a₀) = a₀`, `u₀(a) = −a²/2`, `u₁(x) = x + 1` and `β = 1/2`. The objective
`J(a) = u₀(a) + β u₁(a)` is maximized at `a* = 1/2`, where (6.40) holds with the corrected
`λ₀ = β u₁′(x₁) = 1/2`; but the printed system `u₀′(a) + λ₀ = 0`, `λ₀ = u₁(x₁)` has no solution,
and the variant `λ₀ = u₁′(x₁)` without `β` gives `a = 1`, which is not optimal. -/
theorem eq_6_40_terminal_misprint :
    let J : ℝ → ℝ := fun a => -a ^ 2 / 2 + 1 / 2 * (a + 1)
    (∀ a, J a ≤ J (1 / 2)) ∧ (-(1 / 2 : ℝ) + 1 / 2 * deriv (fun x : ℝ => x + 1) (1 / 2) = 0) ∧
      (¬ ∃ a lam : ℝ, -a + lam = 0 ∧ lam = a + 1) ∧ J 1 < J (1 / 2) := by
  intro J
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · simp only [J]; nlinarith [sq_nonneg (a - 1 / 2)]
  · have : deriv (fun x : ℝ => x + 1) (1 / 2) = 1 := by
      rw [deriv_add_const, deriv_id'']
    rw [this]; norm_num
  · rintro ⟨a, l, h1, h2⟩
    linarith
  · simp only [J]; norm_num

end OCModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The consumption-saving problem of §6.6.2: the model and existence

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSModel`), namespace renamed.

Miao, §6.6.2, pp. 186–188, and Exercises 6–7, p. 190. The consumer's cash on hand `x ≥ 0` is
split into consumption `c = x − s` and saving `s ∈ [0, x]`; next period's cash on hand is
`x′ = ρ(z′) s + w(z′)` where `z′` is next period's shock, drawn from `Q(z, ·)`. With
`ρ ≡ R` and `w(y) = y − rb` this is the book's `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`
(`cash_on_hand`, with `r = R − 1`); iid income is the constant kernel `Q(z, ·) = μ`
(`isFeller_const`); Exercise 6 is a general (Feller) kernel; Exercise 7 (Phelps) is
`ρ(z′) = R′`, `w ≡ y`.

* `CSModel`: the primitives `(u, β, Q, ρ, w)`.
* `CSModel.toOC T`: the problem as an optimal control model of §6.4 (`OCModel`) with horizon `T`:
  `X = A = [0, ∞)`, `Γ(x, z) = [0, x]`, `φ(x, s, z, z′) = ρ(z′)s + w(z′)`,
  `u_t(x, z, s) = u(max(x − s, 0))` (`= u(x − s)` on `Γ`), `u_T(x, z) = u(x)`.
* `CSModel.v n`: the time-to-go value functions `v_0 = u`,
  `v_n(x, z) = max_{s ∈ [0, x]} u(x − s) + β ∫ v_{n−1}(ρ(z′)s + w(z′), z′) Q(z, dz′)`
  (`v_zero`, `v_succ`); `V_t = v_{T−t}` for every horizon (`V_eq`).
* `CSModel.sav n`, `CSModel.cons n`: the saving and consumption policies `s_n`, `g_n`, with
  `s_0 = 0` and `g_0(x) = x`.
* `CSModel.Basic`: the standing hypotheses. They give the standing hypotheses of §6.4 (case (ii)
  of Assumption 6.4.3, `standing`), hence by **Theorem 6.4.1** every `v_n` is continuous on
  `[0, ∞) × Z` and the maximum is attained by `s_n` (`contV`, `sav_mem`, `obj_le`).

**Departures.** (1) The book's `u′′ < 0`, `u′ > 0`, `u′(0+) = ∞` make the logarithm admissible,
but consumption `c = 0` is feasible (`s = x`), so we need `u` finite and continuous on `[0, ∞)`
(`Basic.u_cont`). (2) For the first-order condition at `s = 0` and the Inada argument the next
cash on hand must stay away from `0`: `w > 0` (for the book, the cash floor `y_min − rb > 0`).
(3) **Theorem 6.4.3 does not apply** to this model: Assumption 6.4.10 asks `u_t(·, z, ·)` to be
strictly concave whenever `x ≠ x′`, but `u(x − s)` is constant along `x − s = c`
(`not_assumption6410`). Nor do Assumptions 6.4.7 and 6.4.13: `u_t` must be defined on all of
`X × A`, and by the Inada condition no concave differentiable extension of `u(x − s)` to `s > x`
exists. The properties of §6.6.2 are therefore proved directly (`CSProperties`,
`CSDifferentiable`), using Theorem 6.4.1 for existence and continuity.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-- The **consumption-saving model** of Miao §6.6.2 (p. 187) in cash-on-hand form: utility `u`,
discount factor `β`, shock transition `Q`, and next period's cash on hand
`x′ = ρ(z′) s + w(z′)` after saving `s`. -/
structure CSModel (Z : Type*) [MeasurableSpace Z] where
  u : ℝ → ℝ
  β : ℝ
  Q : Kernel Z Z
  ρ : Z → ℝ
  w : Z → ℝ

/-- Miao, p. 187: with `x_t = R a_t + y_t + b`, `â_{t+1} = a_{t+1} + b` and `r = R − 1`, the
budget `c_t + a_{t+1} = R a_t + y_t` becomes `c_t + â_{t+1} = x_t`, and
`x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`; the borrowing limit `a_{t+1} ≥ −b` is `â_{t+1} ≥ 0`. -/
theorem cash_on_hand (R b a a' y y' c : ℝ) (hbud : c + a' = R * a + y) :
    c + (a' + b) = R * a + y + b ∧
      R * a' + y' + b = R * ((R * a + y + b) - c) + y' - (R - 1) * b ∧
      (-b ≤ a' ↔ 0 ≤ a' + b) := by
  refine ⟨by linarith, ?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have : a' = R * a + y - c := by linarith
  subst this
  ring

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- The consumption-saving problem as an optimal control model of §6.4 with horizon `T`. -/
def toOC (T : ℕ) : OCModel ℝ ℝ Z where
  X := Set.Ici 0
  A := Set.Ici 0
  Q := M.Q
  Γ := fun x _ => Set.Icc 0 x
  φ := fun _ s _ z' => M.ρ z' * s + M.w z'
  u := fun _ x _ s => M.u (max (x - s) 0)
  uT := fun x _ => M.u x
  β := M.β
  T := T

/-- The **time-to-go value functions** `v_n` of Miao, p. 188. -/
noncomputable def v (n : ℕ) : ℝ → Z → ℝ := (M.toOC 0).W n

/-- The objective of the time-to-go Bellman equation:
`u(x − s) + β ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)`. -/
noncomputable def obj (n : ℕ) (x : ℝ) (z : Z) (s : ℝ) : ℝ :=
  M.u (max (x - s) 0) + M.β * ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z

/-- Miao, p. 188: `v_0 = u`. -/
theorem v_zero (x : ℝ) (z : Z) : M.v 0 x z = M.u x := rfl

/-- **The time-to-go Bellman equation** (Miao, p. 188):
`v_{n+1}(x, z) = sup_{s ∈ [0, x]} u(x − s) + β ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)`. -/
theorem v_succ (n : ℕ) (x : ℝ) (z : Z) :
    M.v (n + 1) x z = sSup (M.obj n x z '' Set.Icc 0 x) := rfl

/-- The value functions of `toOC T` do not depend on the horizon. -/
theorem W_eq (T n : ℕ) : (M.toOC T).W n = M.v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OCModel.W]
    rw [ih]
    rfl

/-- Miao, p. 188: the value function of §6.4 at date `t` is the time-to-go value function with
`n = T − t`. -/
theorem V_eq (T t : ℕ) : (M.toOC T).V t = M.v (T - t) := M.W_eq T (T - t)

/-- The **saving policy** `s_n` (Miao, p. 188): `s_0 = 0`, and for `n ≥ 1` the selection `g_0`
from the policy correspondence of `toOC n`. -/
noncomputable def sav : ℕ → ℝ → Z → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => (M.toOC (n + 1)).g 0

/-- The **consumption policy** `g_n(x) = x − s_n(x)` (Miao, p. 188). -/
noncomputable def cons (n : ℕ) (x : ℝ) (z : Z) : ℝ := x - M.sav n x z

/-- **Exercise 6.5**, second property (Miao, p. 188): `g_0(x) = x` and `s_0(x) = 0`. -/
theorem ex_6_5_g0_s0 (x : ℝ) (z : Z) : M.cons 0 x z = x ∧ M.sav 0 x z = 0 :=
  ⟨sub_zero x, rfl⟩

/-- On the feasible set the reward is `u(x − s)`. -/
theorem obj_eq (n : ℕ) {x : ℝ} (z : Z) {s : ℝ} (hs : s ≤ x) :
    M.obj n x z s = M.u (x - s) + M.β * ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z := by
  rw [obj, max_eq_left (sub_nonneg.2 hs)]

/-- Membership in the policy correspondence of `toOC (n + 1)` at date `0`. -/
theorem mem_G (n : ℕ) (x : ℝ) (z : Z) (s : ℝ) :
    s ∈ (M.toOC (n + 1)).G 0 x z ↔ s ∈ Set.Icc 0 x ∧ M.obj n x z s = M.v (n + 1) x z := by
  have h1 : (M.toOC (n + 1)).V (0 + 1) = M.v n := by rw [V_eq]; simp
  have h0 : (M.toOC (n + 1)).V 0 = M.v (n + 1) := by rw [V_eq]; simp
  simp only [OCModel.G, h1, h0]
  rfl

variable [MetricSpace Z]

/-- The **standing hypotheses** for §6.6.2: `β > 0`; `u` continuous, strictly increasing and
strictly concave on `[0, ∞)`; `ρ` and `w` continuous and positive (the cash floor); `Q` Feller. -/
structure Basic : Prop where
  β_pos : 0 < M.β
  u_cont : ContinuousOn M.u (Set.Ici 0)
  u_mono : StrictMonoOn M.u (Set.Ici 0)
  u_conc : StrictConcaveOn ℝ (Set.Ici 0) M.u
  ρ_cont : Continuous M.ρ
  ρ_pos : ∀ z, 0 < M.ρ z
  w_cont : Continuous M.w
  w_pos : ∀ z, 0 < M.w z
  feller : IsFeller M.Q

variable {M}

/-- `Γ(x, z) = [0, x]` is compact-valued and continuous on `X = [0, ∞)`
(Assumption 6.4.4). -/
theorem assumption644 (T : ℕ) : (M.toOC T).Assumption644 := by
  refine ⟨fun x _ _ => Set.Icc_subset_Ici_self, fun p => ?_⟩
  have hx0 : 0 ≤ p.1.1 := p.2.1
  have hne : (Set.Icc (0 : ℝ) p.1.1).Nonempty := ⟨0, le_rfl, hx0⟩
  have hfst : ∀ ps : ℕ → ↥((M.toOC T).X ×ˢ (Set.univ : Set Z)), Tendsto ps atTop (𝓝 p) →
      Tendsto (fun n => (ps n).1.1) atTop (𝓝 p.1.1) := fun ps hps =>
    ((continuous_fst.comp continuous_subtype_val).tendsto p).comp hps
  refine ⟨isCompact_Icc, ⟨hne, fun y hy ps hps => ?_⟩, ⟨hne, fun ps hps ys hys => ?_⟩⟩
  · refine ⟨0, fun n => min y (ps n).1.1, fun n _ => ⟨le_min hy.1 (ps n).2.1, min_le_right _ _⟩,
      ?_⟩
    have := (tendsto_const_nhds (x := y)).min (hfst ps hps)
    rwa [min_eq_left hy.2] at this
  · obtain ⟨B, hB⟩ := (hfst ps hps).bddAbove_range
    have hmem : ∀ n, ys n ∈ Set.Icc 0 B := fun n =>
      ⟨(hys n).1, (hys n).2.trans (hB ⟨n, rfl⟩)⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    refine ⟨y, ⟨ge_of_tendsto' hlim fun n => (hys (φ n)).1, ?_⟩, φ, hφ, hlim⟩
    exact le_of_tendsto_of_tendsto' hlim ((hfst ps hps).comp hφ.tendsto_atTop)
      fun n => (hys (φ n)).2

/-- The state transition `ρ(z′)s + w(z′)` maps `X × A` into `X` and is continuous
(Assumption 6.4.5). -/
theorem assumption645 (h : M.Basic) (T : ℕ) : (M.toOC T).Assumption645 := by
  refine ⟨fun x _ a ha z z' => ?_, ?_⟩
  · change 0 ≤ M.ρ z' * a + M.w z'
    exact add_nonneg (mul_nonneg (h.ρ_pos z').le ha) (h.w_pos z').le
  · change ContinuousOn (fun p : ℝ × ℝ × Z × Z => M.ρ p.2.2.2 * p.2.1 + M.w p.2.2.2) _
    exact ((h.ρ_cont.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      (continuous_fst.comp continuous_snd) |>.add
      (h.w_cont.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))).continuousOn

/-- The rewards `u(max(x − s, 0))` and `u(x)` are continuous (Assumption 6.4.6). -/
theorem assumption646 (h : M.Basic) (T : ℕ) : (M.toOC T).Assumption646 := by
  refine ⟨fun t _ => ?_, ?_⟩
  · change ContinuousOn (fun p : ℝ × Z × ℝ => M.u (max (p.1 - p.2.2) 0)) _
    have hc : Continuous fun p : ℝ × Z × ℝ => max (p.1 - p.2.2) 0 :=
      (continuous_fst.sub (continuous_snd.comp continuous_snd)).max continuous_const
    refine h.u_cont.comp hc.continuousOn fun p _ => ?_
    exact Set.mem_Ici.2 (le_max_right _ _)
  · change ContinuousOn (fun p : ℝ × Z => M.u p.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ)
    exact h.u_cont.comp continuous_fst.continuousOn fun p hp => hp.1

/-- An iid shock, the constant kernel `Q(z, ·) = μ`, is Feller. -/
theorem isFeller_const (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsFeller (Kernel.const Z μ) := by
  intro f _ _
  have : markovOpR (Kernel.const Z μ) f = fun _ => ∫ z', f z' ∂μ := by
    funext z
    simp only [markovOpR, Kernel.const_apply]
  rw [this]
  exact continuous_const

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- **The theory of §6.4 applies** (Theorem 6.4.1): for a compact shock space and a Feller `Q`,
`toOC T` satisfies the standing hypotheses of §6.4. -/
theorem standing (h : M.Basic) (T : ℕ) :
    (M.toOC T).Standing fun _ => True :=
  have : IsMarkovKernel (M.toOC T).Q := ‹IsMarkovKernel M.Q›
  OCModel.Standing.of_compact _ ⟨inferInstance, inferInstance, h.feller⟩ (assumption644 T)
    (assumption645 h T) (assumption646 h T)

/-- **Theorem 6.4.1 for §6.6.2** (Miao, p. 188): every `v_n` is continuous on `[0, ∞) × Z`. -/
theorem contV (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.v n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  have := (standing h n).contV (t := 0) (Nat.zero_le _)
  rwa [V_eq, Nat.sub_zero] at this

/-- The next-period continuation integrand is integrable whenever the next states are in
`[0, ∞)`. -/
theorem integrable_next (h : M.Basic) (n : ℕ) {s : ℝ} (hs : ∀ z', 0 ≤ M.ρ z' * s + M.w z')
    (z : Z) : Integrable (fun z' => M.v n (M.ρ z' * s + M.w z') z') (M.Q z) := by
  have hc : Continuous fun z' => M.v n (M.ρ z' * s + M.w z') z' := by
    exact (contV h n).comp_continuous (f := fun z' => (M.ρ z' * s + M.w z', z'))
      (((h.ρ_cont.mul continuous_const).add h.w_cont).prodMk continuous_id)
      fun z' => Set.mk_mem_prod (hs z') (Set.mem_univ _)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact integrable_of_abs_le hc.measurable fun z' => by
    have := hB z' (Set.mem_univ _)
    rwa [Real.norm_eq_abs] at this

/-- Every feasible saving does at most as well as `v_{n+1}` (Theorem 6.4.1). -/
theorem obj_le (h : M.Basic) (n : ℕ) {x : ℝ} {z : Z} {s : ℝ} (hs : s ∈ Set.Icc 0 x) :
    M.obj n x z s ≤ M.v (n + 1) x z := by
  have hx : x ∈ (M.toOC (n + 1)).X := hs.1.trans hs.2
  have := (standing h (n + 1)).obj_le_V (t := 0) (Nat.succ_pos _) hx (z := z) hs
  have h1 : (M.toOC (n + 1)).V (0 + 1) = M.v n := by rw [V_eq]; simp
  have h0 : (M.toOC (n + 1)).V 0 = M.v (n + 1) := by rw [V_eq]; simp
  rw [h1, h0] at this
  exact this

/-- **Existence of the optimal saving policy** (Theorem 6.4.1; Miao, p. 188): `s_{n+1}(x, z)`
is feasible and attains `v_{n+1}(x, z)`. -/
theorem sav_mem (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    M.sav (n + 1) x z ∈ Set.Icc 0 x ∧ M.obj n x z (M.sav (n + 1) x z) = M.v (n + 1) x z :=
  (M.mem_G n x z _).1 ((standing h (n + 1)).g_mem (t := 0) (Nat.succ_pos _) hx z)

/-- `v_{n+1}(x, z)` is the maximum of the objective over `[0, x]`. -/
theorem isMaxOn_sav (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    IsMaxOn (M.obj n x z) (Set.Icc 0 x) (M.sav (n + 1) x z) := fun s hs => by
  change M.obj n x z s ≤ M.obj n x z (M.sav (n + 1) x z)
  rw [(sav_mem h n hx z).2]
  exact obj_le h n hs

end CSModel

/-- **Theorem 6.4.3 does not apply to §6.6.2** (Miao, p. 188): Assumption 6.4.10 fails for
the reward `u(x − s)` whatever `u` is, since it is constant along `x − s = 1`. -/
theorem CSModel.not_assumption6410 {Z : Type*} [MeasurableSpace Z] [Nonempty Z] (M : CSModel Z)
    (T : ℕ) (hT : 0 < T) : ¬ (M.toOC T).Assumption6410 := by
  intro h
  obtain ⟨z⟩ := (inferInstance : Nonempty Z)
  have hX : ∀ x : ℝ, 0 ≤ x → x ∈ (M.toOC T).X := fun x hx => hx
  have := (h.2 0 hT z 1 (hX 1 one_pos.le) 2 (hX 2 two_pos.le) 0 (hX 0 le_rfl) 1
    (hX 1 one_pos.le) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  change 1 / 2 * M.u (max (1 - 0) 0) + 1 / 2 * M.u (max (2 - 1) 0) <
    M.u (max ((1 / 2 : ℝ) • (1 : ℝ) + (1 / 2 : ℝ) • 2 - ((1 / 2 : ℝ) • 0 + (1 / 2 : ℝ) • 1)) 0)
    at this
  norm_num at this
  linarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.6.2: monotonicity, concavity and the policy functions

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSProperties`), namespace renamed.

Miao, §6.6.2, p. 188 and Exercise 5, p. 189, the properties that need no derivatives. Under the
standing hypotheses `CSModel.Basic`:

* `strictMonoOn_v`: `v_n(·, z)` is strictly increasing on `[0, ∞)`;
* `strictConcaveOn_v`: `v_n(·, z)` is strictly concave on `[0, ∞)` (the book's "inherits the
  basic properties of `u`"; proved directly since Theorem 6.4.3 does not apply,
  `CSModel.not_assumption6410`);
* `sav_unique`: the maximizer is unique, so `s_n` and `g_n` are the policy functions;
* `continuousOn_sav`, `continuousOn_cons`: `s_n`, `g_n` are continuous on `[0, ∞) × Z`
  (single-valued u.h.c. policy, `continuousOn_g_core`);
* `monotoneOn_sav`, `monotoneOn_cons`: `s_n(·, z)` and `g_n(·, z)` are (weakly) increasing, by
  an exchange argument (strict concavity of `u` for `s_n`, of the continuation value for `g_n`);
  no differentiability is used, so these also hold without the Inada condition
  (Exercise 10).

The continuation value `ev n z s = ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)` is strictly concave on
`[0, ∞)` (`strictConcaveOn_ev`). `cs_exchange` is the exchange inequality for strictly concave
functions.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-- The exchange inequality: if `f` is strictly concave, `a < b < d` and `a + d = b + c`, then
`f(a) + f(d) < f(b) + f(c)`. -/
theorem cs_exchange {S : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ S f) {a b c d : ℝ}
    (ha : a ∈ S) (hd : d ∈ S) (hab : a < b) (hbd : b < d)
    (hs : a + d = b + c) : f a + f d < f b + f c := by
  have had : a < d := hab.trans hbd
  have hda : 0 < d - a := sub_pos.2 had
  set θ := (d - b) / (d - a) with hθ
  set η := (b - a) / (d - a) with hη
  have hθp : 0 < θ := div_pos (sub_pos.2 hbd) hda
  have hηp : 0 < η := div_pos (sub_pos.2 hab) hda
  have hsum : θ + η = 1 := by rw [hθ, hη, ← add_div]; field_simp; ring
  have hb : θ * a + η * d = b := by rw [hθ, hη]; field_simp; ring
  have hc : η * a + θ * d = c := by
    have : η * a + θ * d = (θ + η) * (a + d) - (θ * a + η * d) := by ring
    rw [this, hsum, hb]; linarith
  have h1 := hf.2 ha hd had.ne hθp hηp hsum
  have h2 := hf.2 ha hd had.ne hηp hθp (by linarith)
  simp only [smul_eq_mul] at h1 h2
  rw [hb] at h1
  rw [hc] at h2
  have key : θ * f a + η * f d + (η * f a + θ * f d) = f a + f d := by
    linear_combination (f a + f d) * hsum
  linarith

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- The **continuation value** `∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)` after saving `s`. -/
noncomputable def ev (n : ℕ) (z : Z) (s : ℝ) : ℝ :=
  ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z

theorem obj_eq_ev (n : ℕ) {x : ℝ} (z : Z) {s : ℝ} (hs : s ≤ x) :
    M.obj n x z s = M.u (x - s) + M.β * M.ev n z s :=
  M.obj_eq n z hs

variable {M} [MetricSpace Z]

/-- The next states after saving `s ≥ 0` are in `[0, ∞)`. -/
theorem next_nonneg (h : M.Basic) {s : ℝ} (hs : 0 ≤ s) (z' : Z) : 0 ≤ M.ρ z' * s + M.w z' :=
  add_nonneg (mul_nonneg (h.ρ_pos z').le hs) (h.w_pos z').le

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- Strict concavity of `v_n(·, z′)` for every `z′` makes the continuation value strictly
concave on `[0, ∞)`. -/
theorem strictConcaveOn_ev (h : M.Basic) {n : ℕ}
    (hv : ∀ z', StrictConcaveOn ℝ (Set.Ici 0) fun x => M.v n x z') (z : Z) :
    StrictConcaveOn ℝ (Set.Ici 0) (M.ev n z) := by
  refine ⟨convex_Ici 0, fun s₁ hs₁ s₂ hs₂ hne θ η hθ hη hsum => ?_⟩
  have i1 := integrable_next h n (next_nonneg h hs₁) z
  have i2 := integrable_next h n (next_nonneg h hs₂) z
  have hs₃ : (0 : ℝ) ≤ θ • s₁ + η • s₂ :=
    (convex_Ici 0) hs₁ hs₂ hθ.le hη.le hsum
  have i3 := integrable_next h n (next_nonneg h hs₃) z
  simp only [smul_eq_mul, ev]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul θ)
    (i2.const_mul η)]
  refine integral_lt_integral_of_lt ((i1.const_mul θ).add (i2.const_mul η)) i3 fun z' => ?_
  have hp₁ := next_nonneg h hs₁ z'
  have hp₂ := next_nonneg h hs₂ z'
  have hne' : M.ρ z' * s₁ + M.w z' ≠ M.ρ z' * s₂ + M.w z' := fun he =>
    hne (mul_left_cancel₀ (h.ρ_pos z').ne' (by linarith))
  have := (hv z').2 hp₁ hp₂ hne' hθ hη hsum
  simp only [smul_eq_mul] at this
  have heq : θ * (M.ρ z' * s₁ + M.w z') + η * (M.ρ z' * s₂ + M.w z') =
      M.ρ z' * (θ * s₁ + η * s₂) + M.w z' := by
    linear_combination M.w z' * hsum
  rw [heq] at this
  exact this

/-- **`v_n(·, z)` is strictly increasing** on `[0, ∞)` (Miao, p. 188). -/
theorem strictMonoOn_v (h : M.Basic) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => M.v n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact h.u_mono
  | succ n =>
    intro x hx x' hx' hxx'
    obtain ⟨hmem, hval⟩ := sav_mem h n hx z
    set s := M.sav (n + 1) x z
    have hs' : s ∈ Set.Icc 0 x' := ⟨hmem.1, hmem.2.trans hxx'.le⟩
    change M.v (n + 1) x z < M.v (n + 1) x' z
    rw [← hval]
    refine lt_of_lt_of_le ?_ (obj_le h n hs')
    rw [M.obj_eq_ev _ _ hmem.2, M.obj_eq_ev _ _ hs'.2]
    have : M.u (x - s) < M.u (x' - s) := h.u_mono (sub_nonneg.2 hmem.2)
      (sub_nonneg.2 hs'.2) (by linarith)
    linarith

/-- **`v_n(·, z)` is strictly concave** on `[0, ∞)` (Miao, p. 188), for every `n` and `z`. -/
theorem strictConcaveOn_v (h : M.Basic) (n : ℕ) :
    ∀ z, StrictConcaveOn ℝ (Set.Ici 0) fun x => M.v n x z := by
  induction n with
  | zero => intro z; exact h.u_conc
  | succ n ih =>
    intro z
    have hev := strictConcaveOn_ev h ih z
    refine ⟨convex_Ici 0, fun x₁ hx₁ x₂ hx₂ hne θ η hθ hη hsum => ?_⟩
    obtain ⟨hm₁, hv₁⟩ := sav_mem h n hx₁ z
    obtain ⟨hm₂, hv₂⟩ := sav_mem h n hx₂ z
    set s₁ := M.sav (n + 1) x₁ z
    set s₂ := M.sav (n + 1) x₂ z
    simp only [smul_eq_mul]
    have hs : s₁ ∈ Set.Ici (0 : ℝ) := hm₁.1
    have hs₂ : s₂ ∈ Set.Ici (0 : ℝ) := hm₂.1
    have hc₁ : x₁ - s₁ ∈ Set.Ici (0 : ℝ) := sub_nonneg.2 hm₁.2
    have hc₂ : x₂ - s₂ ∈ Set.Ici (0 : ℝ) := sub_nonneg.2 hm₂.2
    have hfeas : θ * s₁ + η * s₂ ∈ Set.Icc 0 (θ * x₁ + η * x₂) :=
      ⟨by nlinarith [hm₁.1, hm₂.1], by nlinarith [hm₁.2, hm₂.2]⟩
    have hle := obj_le h n (z := z) hfeas
    rw [M.obj_eq_ev _ _ hfeas.2] at hle
    rw [← hv₁, ← hv₂, M.obj_eq_ev _ _ hm₁.2, M.obj_eq_ev _ _ hm₂.2]
    have hcomb : θ * x₁ + η * x₂ - (θ * s₁ + η * s₂) = θ * (x₁ - s₁) + η * (x₂ - s₂) := by ring
    rw [hcomb] at hle
    have hβ := h.β_pos
    by_cases hss : s₁ = s₂
    · have hcne : x₁ - s₁ ≠ x₂ - s₂ := fun he => hne (by rw [hss] at he; linarith)
      have hu := h.u_conc.2 hc₁ hc₂ hcne hθ hη hsum
      simp only [smul_eq_mul] at hu
      have hevs : θ * M.ev n z s₁ + η * M.ev n z s₂ = M.ev n z (θ * s₁ + η * s₂) := by
        have hθη : θ * s₁ + η * s₁ = s₁ := by rw [← add_mul, hsum, one_mul]
        rw [← hss, ← add_mul, hsum, one_mul, hθη]
      nlinarith
    · have hu := h.u_conc.concaveOn.2 hc₁ hc₂ hθ.le hη.le hsum
      have he := hev.2 hs hs₂ hss hθ hη hsum
      simp only [smul_eq_mul] at hu he
      nlinarith

/-- **The optimal saving is unique** (Miao, p. 188): any feasible `s` attaining `v_{n+1}(x, z)` is
`s_{n+1}(x, z)`. -/
theorem sav_unique (h : M.Basic) (n : ℕ) {x : ℝ} {z : Z} {s : ℝ} (hs : s ∈ Set.Icc 0 x)
    (hval : M.obj n x z s = M.v (n + 1) x z) : s = M.sav (n + 1) x z := by
  have hx : 0 ≤ x := hs.1.trans hs.2
  obtain ⟨hm, hv⟩ := sav_mem h n hx z
  set s' := M.sav (n + 1) x z
  by_contra hne
  have hh : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hev := (strictConcaveOn_ev h (strictConcaveOn_v h n) z).2 hs.1 hm.1 hne hp hp hh
  have hu := h.u_conc.concaveOn.2 (sub_nonneg.2 hs.2 : x - s ∈ Set.Ici (0 : ℝ))
    (sub_nonneg.2 hm.2 : x - s' ∈ Set.Ici (0 : ℝ)) hp.le hp.le hh
  simp only [smul_eq_mul] at hev hu
  have hfeas : 1 / 2 * s + 1 / 2 * s' ∈ Set.Icc 0 x :=
    ⟨by linarith [hs.1, hm.1], by linarith [hs.2, hm.2]⟩
  have hle := obj_le h n (z := z) hfeas
  rw [M.obj_eq_ev _ _ hfeas.2] at hle
  rw [M.obj_eq_ev _ _ hs.2] at hval
  rw [M.obj_eq_ev _ _ hm.2] at hv
  have : x - (1 / 2 * s + 1 / 2 * s') = 1 / 2 * (x - s) + 1 / 2 * (x - s') := by ring
  rw [this] at hle
  nlinarith [h.β_pos]

/-- The policy correspondence of `toOC (n + 1)` at date `0` is single-valued. -/
theorem G_subsingleton (h : M.Basic) (n : ℕ) :
    ∀ x ∈ (M.toOC (n + 1)).X, ∀ z, ((M.toOC (n + 1)).G 0 x z).Subsingleton := by
  intro x _ z a ha b hb
  rw [mem_G] at ha hb
  rw [sav_unique h n ha.1 ha.2, sav_unique h n hb.1 hb.2]

/-- **`s_n` is continuous** on `[0, ∞) × Z` (Miao, p. 188; Theorem 6.4.3's continuity of the
single-valued policy). -/
theorem continuousOn_sav (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.sav n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  cases n with
  | zero => exact continuousOn_const
  | succ n =>
    have : IsMarkovKernel (M.toOC (n + 1)).Q := ‹IsMarkovKernel M.Q›
    exact OCModel.continuousOn_g_core (standing h (n + 1)) (Nat.succ_pos n) (G_subsingleton h n)

/-- **`g_n` is continuous** on `[0, ∞) × Z` (Miao, p. 188). -/
theorem continuousOn_cons (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.cons n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) :=
  continuous_fst.continuousOn.sub (continuousOn_sav h n)

/-- `0 ≤ s_n(x) ≤ x` for `x ≥ 0`. -/
theorem sav_mem' (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    M.sav n x z ∈ Set.Icc 0 x := by
  cases n with
  | zero => exact ⟨le_rfl, hx⟩
  | succ n => exact (sav_mem h n hx z).1

/-- **`s_n(·, z)` is increasing** (weakly) on `[0, ∞)` (Miao, p. 188), by the exchange argument
with the strict concavity of `u`. -/
theorem monotoneOn_sav (h : M.Basic) (n : ℕ) (z : Z) :
    MonotoneOn (fun x => M.sav n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact fun _ _ _ _ _ => le_rfl
  | succ n =>
    intro x hx x' hx' hxx'
    change M.sav (n + 1) x z ≤ M.sav (n + 1) x' z
    rcases hxx'.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨hm, hv⟩ := sav_mem h n hx z
    obtain ⟨hm', hv'⟩ := sav_mem h n hx' z
    set s := M.sav (n + 1) x z
    set s' := M.sav (n + 1) x' z
    by_contra hcon
    push Not at hcon
    have hf1 : s' ∈ Set.Icc 0 x := ⟨hm'.1, by linarith [hm.2]⟩
    have hf2 : s ∈ Set.Icc 0 x' := ⟨hm.1, by linarith [hm.2]⟩
    have h1 := obj_le h n (z := z) hf1
    have h2 := obj_le h n (z := z) hf2
    rw [← hv, M.obj_eq_ev _ _ hf1.2, M.obj_eq_ev _ _ hm.2] at h1
    rw [← hv', M.obj_eq_ev _ _ hf2.2, M.obj_eq_ev _ _ hm'.2] at h2
    have hx := cs_exchange h.u_conc (sub_nonneg.2 hm.2 : x - s ∈ Set.Ici (0 : ℝ))
      (sub_nonneg.2 hm'.2 : x' - s' ∈ Set.Ici (0 : ℝ)) (b := x - s') (c := x' - s)
      (by linarith) (by linarith) (by ring)
    linarith

/-- **`g_n(·, z)` is increasing** (weakly) on `[0, ∞)` (Miao, p. 188), by the exchange argument
with the strict concavity of the continuation value. -/
theorem monotoneOn_cons (h : M.Basic) (n : ℕ) (z : Z) :
    MonotoneOn (fun x => M.cons n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact fun _ _ _ _ h => by simpa [cons, sav] using h
  | succ n =>
    intro x hx x' hx' hxx'
    change M.cons (n + 1) x z ≤ M.cons (n + 1) x' z
    rcases hxx'.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨hm, hv⟩ := sav_mem h n hx z
    obtain ⟨hm', hv'⟩ := sav_mem h n hx' z
    simp only [cons]
    set s := M.sav (n + 1) x z
    set s' := M.sav (n + 1) x' z
    by_contra hcon
    push Not at hcon
    have hev := strictConcaveOn_ev h (strictConcaveOn_v h n) z
    -- at `x` consume `x' − s'`, at `x'` consume `x − s`
    have hf1 : x - (x' - s') ∈ Set.Icc 0 x := ⟨by linarith [hm.1], by linarith [hm'.2]⟩
    have hf2 : x' - (x - s) ∈ Set.Icc 0 x' := ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have h1 := obj_le h n (z := z) hf1
    have h2 := obj_le h n (z := z) hf2
    rw [← hv, M.obj_eq_ev _ _ hf1.2, M.obj_eq_ev _ _ hm.2] at h1
    rw [← hv', M.obj_eq_ev _ _ hf2.2, M.obj_eq_ev _ _ hm'.2] at h2
    have h3 : x - (x - (x' - s')) = x' - s' := by ring
    have h4 : x' - (x' - (x - s)) = x - s := by ring
    rw [h3] at h1
    rw [h4] at h2
    have hx := cs_exchange hev (hm.1 : s ∈ Set.Ici (0 : ℝ)) (hm'.1 : s' ∈ Set.Ici (0 : ℝ))
      (b := x - (x' - s')) (c := x' - (x - s)) (by linarith) (by linarith) (by ring)
    nlinarith [h.β_pos]

end CSModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.6.2: the Inada condition, the envelope and first-order conditions, and comparisons

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSDifferentiable`), namespace renamed.

Miao, §6.6.2, pp. 188–189 and Exercise 5, p. 189. Add to `CSModel.Basic` that `u` is
differentiable on `(0, ∞)` with `u′(0+) = ∞` (`CSModel.Smooth`). Then for `x > 0`:

* `cons_pos`: `g_n(x, z) > 0` (the Inada condition; `w > 0` bounds the continuation slope);
* `hasDerivAt_v`, `continuousOn_deriv_v`: **`v_n(·, z)` is `C¹` on `(0, ∞)`** with the envelope
  condition `v_n′(x) = u′(g_n(x))` (Benveniste–Scheinkman, `theorem_4_10`);
* `hasDerivAt_ev`: the continuation value has derivative
  `evd = ∫ v_n′(ρ(z′)s + w(z′), z′) ρ(z′) Q(z, dz′)` for `s ≥ 0`
  (`oc_hasDerivAt_integral_concave`);
* `foc`: **the first-order condition** `u′(g_{n+1}(x)) ≥ β evd_n(s_{n+1}(x))`, with equality if
  `s_{n+1}(x) > 0`; for `ρ ≡ R` this is the book's
  `v_n′(x) = u′(g_n(x)) ≥ βR E v_{n−1}′(Rs_n(x) + y − rb)`;
* `strictMonoOn_cons`: `g_n(·, z)` is **strictly** increasing; `s_n(·, z)` is only weakly
  increasing: `exists_sav_eq_zero` (the constraint binds for small `x`) and
  `not_strictMonoOn_sav`;
* `cons_succ_le`, `sav_le_sav_succ`, `deriv_v_le`: **`g_n` is decreasing in `n`, `s_n` and
  `v_n′` are increasing in `n`** (weakly; `exists_cons_succ_eq` shows strictness fails);
* `cons_ge_low`, `cons_le_high`: **`c_t(x; y_max) ≥ c_t(x) ≥ c_t(x; y_min)`** (p. 189), for
  `ρ ≡ R`, where `detModel z₀` is the model whose shock is `z₀` every period; this holds for
  Markov shocks too, and needs no assumption on `u′′′`.

`cs_compare` is the comparison lemma behind the last two items.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology Metric

/-- **Comparison of first-order conditions.** Let `du` be antitone on `(0, ∞)`, `s₁, s₂ < x`,
`du(x − s₁) = D₁(s₁)` if `s₁ > 0`, `D₂(s₂) ≤ du(x − s₂)`, `D₁(s₁) ≤ D₂(s₁)` and `D₂` strictly
decreasing on `[0, ∞)`. Then `s₁ ≤ s₂`. -/
theorem cs_compare {du D₁ D₂ : ℝ → ℝ} (hdu : AntitoneOn du (Set.Ioi 0)) {x s₁ s₂ : ℝ}
    (hs₁ : s₁ < x) (hs₂ : 0 ≤ s₂) (hs₂x : s₂ < x) (hfoc₁ : 0 < s₁ → du (x - s₁) = D₁ s₁)
    (hfoc₂ : D₂ s₂ ≤ du (x - s₂)) (hD : D₁ s₁ ≤ D₂ s₁) (hanti : StrictAntiOn D₂ (Set.Ici 0)) :
    s₁ ≤ s₂ := by
  by_contra hcon
  push Not at hcon
  have h1 : 0 < s₁ := hs₂.trans_lt hcon
  have h2 := hanti (Set.mem_Ici.2 hs₂) (Set.mem_Ici.2 h1.le) hcon
  have h3 := hdu (Set.mem_Ioi.2 (sub_pos.2 hs₁)) (Set.mem_Ioi.2 (sub_pos.2 hs₂x))
    (by linarith : x - s₁ ≤ x - s₂)
  have h4 := hfoc₁ h1
  linarith

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- Differentiability and the **Inada condition** (Miao, p. 187): `u` is differentiable on
`(0, ∞)` and `u′(c) → ∞` as `c → 0+`. -/
structure Smooth : Prop where
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ M.u c
  inada : Tendsto (deriv M.u) (𝓝[>] 0) atTop

/-- The derivative of the continuation value:
`∫ v_n′(ρ(z′)s + w(z′), z′) ρ(z′) Q(z, dz′)`. -/
noncomputable def evd (n : ℕ) (z : Z) (s : ℝ) : ℝ :=
  ∫ z', deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z' ∂M.Q z

/-- The model whose shock is `z₀` in every period (`Q(z, ·) = δ_{z₀}`): for §6.6.2 with
`z₀ = y_min` or `y_max`, the deterministic problems behind `c_t(x; y_min)`, `c_t(x; y_max)`. -/
noncomputable def detModel (z₀ : Z) : CSModel Z :=
  { M with Q := Kernel.const Z (Measure.dirac z₀) }

variable {M} [MetricSpace Z]

/-- `u′` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_deriv_u (h : M.Basic) (hs : M.Smooth) :
    StrictAntiOn (deriv M.u) (Set.Ioi 0) :=
  (h.u_conc.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun c hc => hs.u_diff c hc

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- **The Inada condition makes consumption interior** (Miao, p. 188): `g_n(x, z) > 0` for
`x > 0`. -/
theorem cons_pos (h : M.Basic) (hs : M.Smooth) (n : ℕ) {x : ℝ} (hx : 0 < x) (z : Z) :
    0 < M.cons n x z := by
  cases n with
  | zero => simpa [cons, sav] using hx
  | succ n =>
    obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
    simp only [cons]
    set s := M.sav (n + 1) x z
    rcases hm.2.lt_or_eq with hlt | heq
    · exact sub_pos.2 hlt
    exfalso
    have hev := (strictConcaveOn_ev h (strictConcaveOn_v h n) z).concaveOn
    set K := (M.ev n z (x / 2) - M.ev n z 0) / (x / 2 - 0)
    have hβ := h.β_pos
    obtain ⟨ε, hεu, hε⟩ : ∃ ε, M.β * K < deriv M.u ε ∧ ε ∈ Set.Ioo 0 (x / 2) :=
      ((hs.inada.eventually (eventually_gt_atTop (M.β * K))).and
        (Ioo_mem_nhdsGT (half_pos hx))).exists
    have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
    have hx2 : x / 2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (half_pos hx).le
    have hxε : x - ε ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hε.2])
    have h1 := hev.slope_anti_adjacent hx2 (Set.mem_Ici.2 hx.le) (by linarith [hε.2] :
      x / 2 < x - ε) (by linarith [hε.1] : x - ε < x)
    have h2 := hev.slope_anti_adjacent h0 hxε (half_pos hx) (by linarith [hε.2] :
      x / 2 < x - ε)
    have hxx : x - (x - ε) = ε := by ring
    rw [hxx] at h1
    have hslope : M.ev n z x - M.ev n z (x - ε) ≤ K * ε :=
      (div_le_iff₀ hε.1).1 (h1.trans h2)
    have hu := h.u_conc.concaveOn.deriv_le_slope h0 (Set.mem_Ici.2 hε.1.le) hε.1
      (hs.u_diff ε hε.1)
    rw [slope_def_field, sub_zero] at hu
    have hu' : ε * deriv M.u ε ≤ M.u ε - M.u 0 := by
      rw [le_div_iff₀ hε.1] at hu
      linarith
    have hfeas : x - ε ∈ Set.Icc 0 x := ⟨hxε, by linarith [hε.1]⟩
    have hle := obj_le h n (z := z) hfeas
    rw [← hv, M.obj_eq_ev _ _ hfeas.2, M.obj_eq_ev _ _ hm.2, hxx, heq, sub_self] at hle
    have e1 : M.β * (M.ev n z x - M.ev n z (x - ε)) ≤ M.β * (K * ε) :=
      mul_le_mul_of_nonneg_left hslope hβ.le
    have e2 : ε * (M.β * K) < ε * deriv M.u ε := mul_lt_mul_of_pos_left hεu hε.1
    nlinarith

/-- **The envelope condition** (Miao, p. 188): for `x > 0`, `v_n(·, z)` is differentiable at `x`
with `v_n′(x) = u′(g_n(x))`. -/
theorem hasDerivAt_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => M.v n y z) (deriv M.u (M.cons n x z)) x := by
  cases n with
  | zero =>
    have : M.cons 0 x z = x := sub_zero x
    rw [this]
    exact (hs.u_diff x hx).hasDerivAt
  | succ n =>
    obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
    have hc := cons_pos h hs (n + 1) hx z
    simp only [cons] at hc ⊢
    set s := M.sav (n + 1) x z
    have hsx : s < x := by linarith
    have hW : HasDerivAt (fun y => M.u (y - s) + M.β * M.ev n z s) (deriv M.u (x - s)) x := by
      have h1 := (hs.u_diff (x - s) hc).hasDerivAt.comp x ((hasDerivAt_id' x).sub_const s)
      have h2 := h1.add_const (M.β * M.ev n z s)
      rw [mul_one] at h2
      exact h2
    have heq : M.u (x - s) + M.β * M.ev n z s = M.v (n + 1) x z := by
      rw [← hv, M.obj_eq_ev _ _ hm.2]
    have hle : ∀ᶠ y in 𝓝 x, M.u (y - s) + M.β * M.ev n z s ≤ M.v (n + 1) y z := by
      filter_upwards [eventually_gt_nhds hsx] with y hy
      have hfeas : s ∈ Set.Icc 0 y := ⟨hm.1, hy.le⟩
      have := obj_le h n (z := z) hfeas
      rwa [M.obj_eq_ev _ _ hy.le] at this
    rw [hasDerivAt_iff_hasFDerivAt] at hW ⊢
    exact theorem_4_10 (strictConcaveOn_v h (n + 1) z).concaveOn (Ici_mem_nhds hx) hW heq hle

/-- `v_n′(x) = u′(g_n(x))` for `x > 0`. -/
theorem deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => M.v n y z) x = deriv M.u (M.cons n x z) :=
  (hasDerivAt_v h hs n z hx).deriv

/-- **`v_n(·, z)` is continuously differentiable on `(0, ∞)`** (Miao, p. 188). -/
theorem continuousOn_deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ContinuousOn (deriv fun y => M.v n y z) (Set.Ioi 0) :=
  oc_continuousOn_deriv_of_concave isOpen_Ioi
    ((strictConcaveOn_v h n z).concaveOn.subset Set.Ioi_subset_Ici_self (convex_Ioi 0))
    fun _ hx => (hasDerivAt_v h hs n z hx).differentiableAt

/-- `v_n′(·, z)` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictAntiOn (deriv fun y => M.v n y z) (Set.Ioi 0) :=
  ((strictConcaveOn_v h n z).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun _ hx => (hasDerivAt_v h hs n z hx).differentiableAt

/-- **Differentiating the continuation value** under `∫ Q(z, dz′)` at `s ≥ 0`. -/
theorem hasDerivAt_ev (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {s : ℝ} (hs0 : 0 ≤ s) :
    Integrable (fun z' => deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z') (M.Q z) ∧
      HasDerivAt (M.ev n z) (M.evd n z s) s := by
  have : Nonempty Z := ⟨z⟩
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.ρ_cont.continuousOn
  obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty h.w_cont.continuousOn
  set m := M.w z₀
  have hm : 0 < m := h.w_pos z₀
  set B' := max B 1
  have hB' : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r := m / (2 * B')
  have hr : 0 < r := by positivity
  have hBr : B' * r = m / 2 := by simp only [r]; field_simp
  have key : ∀ y, |y - s| ≤ r → ∀ z', m / 2 ≤ M.ρ z' * y + M.w z' := by
    intro y hy z'
    have hρ := h.ρ_pos z'
    have hρB : M.ρ z' ≤ B' := by
      have := hB z' (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hlo : -r ≤ y - s := (abs_le.1 hy).1
    have e1 : M.ρ z' * (-r) ≤ M.ρ z' * (y - s) := mul_le_mul_of_nonneg_left hlo hρ.le
    have e2 : M.ρ z' * r ≤ B' * r := mul_le_mul_of_nonneg_right hρB hr.le
    have e4 : 0 ≤ M.ρ z' * s := mul_nonneg hρ.le hs0
    have e5 : M.ρ z' * y = M.ρ z' * s + M.ρ z' * (y - s) := by ring
    have e6 : M.ρ z' * (-r) = -(M.ρ z' * r) := mul_neg _ _
    have hw : m ≤ M.w z' := (isMinOn_iff.1 hz₀) z' (Set.mem_univ _)
    linarith
  have hball : ∀ y ∈ ball s r, ∀ z', 0 ≤ M.ρ z' * y + M.w z' := fun y hy z' => by
    have : |y - s| ≤ r := by rw [mem_ball, Real.dist_eq] at hy; exact hy.le
    linarith [key y this z']
  -- the uniform bound
  set K := closedBall s r ×ˢ (Set.univ : Set Z)
  have hK : IsCompact K := (isCompact_closedBall s r).prod isCompact_univ
  have hcK : ContinuousOn (fun q : ℝ × Z => M.v n (M.ρ q.2 * q.1 + M.w q.2) q.2) K := by
    refine ContinuousOn.comp (g := fun p : ℝ × Z => M.v n p.1 p.2)
      (f := fun q : ℝ × Z => (M.ρ q.2 * q.1 + M.w q.2, q.2)) (contV h n)
      (Continuous.continuousOn ?_) fun q hq => ⟨?_, Set.mem_univ _⟩
    · exact ((h.ρ_cont.comp continuous_snd).mul continuous_fst |>.add
        (h.w_cont.comp continuous_snd)).prodMk continuous_snd
    · have : |q.1 - s| ≤ r := by
        have := hq.1
        rw [mem_closedBall, Real.dist_eq] at this
        exact this
      exact Set.mem_Ici.2 (by linarith [key q.1 this q.2])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcK
  have hres := oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun y z' => M.v n (M.ρ z' * y + M.w z') z')
    (F' := fun z' => deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z') (C := C) hr
    (fun z' => ?_) (fun y hy z' => ?_) (fun y hy => integrable_next h n (hball y hy) z)
    (fun z' => ?_)
  · exact hres
  · refine ⟨convex_ball s r, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
    have := (strictConcaveOn_v h n z').concaveOn.2 (Set.mem_Ici.2 (hball y₁ hy₁ z'))
      (Set.mem_Ici.2 (hball y₂ hy₂ z')) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have heq : a * (M.ρ z' * y₁ + M.w z') + b * (M.ρ z' * y₂ + M.w z') =
        M.ρ z' * (a * y₁ + b * y₂) + M.w z' := by linear_combination M.w z' * hab
    rwa [heq] at this
  · have := hC (y, z') ⟨ball_subset_closedBall hy, Set.mem_univ _⟩
    rwa [Real.norm_eq_abs] at this
  · have hp : 0 < M.ρ z' * s + M.w z' := by
      have := key s (by rw [sub_self, abs_zero]; exact hr.le) z'
      linarith
    have hlin : HasDerivAt (fun y => M.ρ z' * y + M.w z') (M.ρ z') s := by
      have := ((hasDerivAt_id' s).const_mul (M.ρ z')).add_const (M.w z')
      rwa [mul_one] at this
    exact (hasDerivAt_v h hs n z' hp).differentiableAt.hasDerivAt.comp s hlin

/-- The derivative of the continuation value is strictly decreasing on `[0, ∞)`. -/
theorem strictAntiOn_evd (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictAntiOn (M.evd n z) (Set.Ici 0) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  refine integral_lt_integral_of_lt (hasDerivAt_ev h hs n z hs₂).1 (hasDerivAt_ev h hs n z hs₁).1
    fun z' => ?_
  have hρ := h.ρ_pos z'
  have hp₁ : 0 < M.ρ z' * s₁ + M.w z' := by
    have := mul_nonneg hρ.le (Set.mem_Ici.1 hs₁); linarith [h.w_pos z']
  have hp₂ : 0 < M.ρ z' * s₂ + M.w z' := by
    have := mul_nonneg hρ.le (Set.mem_Ici.1 hs₂); linarith [h.w_pos z']
  have hpp : M.ρ z' * s₁ + M.w z' < M.ρ z' * s₂ + M.w z' := by
    have := mul_lt_mul_of_pos_left hlt hρ; linarith
  exact mul_lt_mul_of_pos_right (strictAntiOn_deriv_v h hs n z' hp₁ hp₂ hpp) hρ

/-- **The first-order condition** (Miao, p. 188): for `x > 0`,
`u′(g_{n+1}(x)) ≥ β ∫ v_n′(ρ(z′)s_{n+1}(x) + w(z′), z′) ρ(z′) Q(z, dz′)`, with equality if
`s_{n+1}(x) > 0`. -/
theorem foc (h : M.Basic) (hs : M.Smooth) (n : ℕ) {x : ℝ} (hx : 0 < x) (z : Z) :
    M.β * M.evd n z (M.sav (n + 1) x z) ≤ deriv M.u (M.cons (n + 1) x z) ∧
      (0 < M.sav (n + 1) x z →
        deriv M.u (M.cons (n + 1) x z) = M.β * M.evd n z (M.sav (n + 1) x z)) := by
  obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
  have hc := cons_pos h hs (n + 1) hx z
  simp only [cons] at hc ⊢
  set s := M.sav (n + 1) x z
  have hsx : s < x := by linarith
  have hf : HasDerivAt (fun s' => M.u (x - s') + M.β * M.ev n z s')
      (deriv M.u (x - s) * -1 + M.β * M.evd n z s) s := by
    have h1 := (hs.u_diff (x - s) hc).hasDerivAt.comp s ((hasDerivAt_id' s).const_sub x)
    exact h1.add ((hasDerivAt_ev h hs n z hm.1).2.const_mul M.β)
  have hmax : ∀ s' ∈ Set.Icc 0 x,
      M.u (x - s') + M.β * M.ev n z s' ≤ M.u (x - s) + M.β * M.ev n z s := fun s' hs' => by
    have := obj_le h n (z := z) hs'
    rw [← hv, M.obj_eq_ev _ _ hs'.2, M.obj_eq_ev _ _ hm.2] at this
    exact this
  refine ⟨?_, fun hpos => ?_⟩
  · have hsl := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE s)
    have hle : deriv M.u (x - s) * -1 + M.β * M.evd n z s ≤ 0 := by
      refine le_of_tendsto hsl ?_
      filter_upwards [Ioo_mem_nhdsGT hsx] with y hy
      rw [slope_def_field]
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.2 (hmax y ⟨hm.1.trans hy.1.le, hy.2.le⟩)) (sub_pos.2 hy.1).le
    linarith
  · have hloc : IsLocalMax (fun s' => M.u (x - s') + M.β * M.ev n z s') s := by
      filter_upwards [Ioo_mem_nhds hpos hsx] with y hy
      exact hmax y ⟨hy.1.le, hy.2.le⟩
    have := hloc.hasDerivAt_eq_zero hf
    linarith

/-- **`g_n(·, z)` is strictly increasing** on `[0, ∞)` (Miao, p. 188). -/
theorem strictMonoOn_cons (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => M.cons n x z) (Set.Ici 0) := by
  intro x hx x' hx' hlt
  change M.cons n x z < M.cons n x' z
  have hx'0 : 0 < x' := lt_of_le_of_lt hx hlt
  rcases (Set.mem_Ici.1 hx).lt_or_eq with hx0 | hx0
  swap
  · subst hx0
    have h0 : M.sav n 0 z = 0 := by
      have := sav_mem' h n le_rfl z
      exact le_antisymm this.2 this.1
    have := cons_pos h hs n hx'0 z
    simp only [cons, h0, sub_zero]
    exact this
  cases n with
  | zero => simpa [cons, sav] using hlt
  | succ n =>
    by_contra hcon
    push Not at hcon
    have hc := cons_pos h hs (n + 1) hx0 z
    have hc' := cons_pos h hs (n + 1) hx'0 z
    obtain ⟨f1, -⟩ := foc h hs n hx0 z
    obtain ⟨-, f2⟩ := foc h hs n hx'0 z
    have hm := sav_mem h n hx z
    simp only [cons] at hcon hc hc' f1 f2
    have hss : M.sav (n + 1) x z < M.sav (n + 1) x' z := by linarith
    have hpos : 0 < M.sav (n + 1) x' z := lt_of_le_of_lt hm.1.1 hss
    have e := strictAntiOn_evd h hs n z (Set.mem_Ici.2 hm.1.1) (Set.mem_Ici.2 hpos.le) hss
    have e' := mul_lt_mul_of_pos_left e h.β_pos
    have hu : deriv M.u (x - M.sav (n + 1) x z) ≤ deriv M.u (x' - M.sav (n + 1) x' z) :=
      (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc) hcon
    linarith [f2 hpos]

/-- **The borrowing constraint binds near `0`** (Miao, p. 188): for each `n` there is `x̄ > 0`
with `s_{n+1}(x) = 0` on `(0, x̄]`. -/
theorem exists_sav_eq_zero (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, M.sav (n + 1) x z = 0 := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hs.inada.eventually (eventually_gt_atTop (M.β * M.evd n z 0)))
  have hδ0 : 0 < δ := hδ
  refine ⟨δ / 2, half_pos hδ0, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  obtain ⟨hm, -⟩ := sav_mem h n hx0.le z
  by_contra hne
  have hpos : 0 < M.sav (n + 1) x z := lt_of_le_of_ne hm.1 (Ne.symm hne)
  have hc := cons_pos h hs (n + 1) hx0 z
  have f := (foc h hs n hx0 z).2 hpos
  simp only [cons] at hc f
  have e := strictAntiOn_evd h hs n z (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
  have e' := mul_lt_mul_of_pos_left e h.β_pos
  have hux : M.β * M.evd n z 0 < deriv M.u x := hsub ⟨hx0, by linarith [hx.2]⟩
  have hu : deriv M.u x ≤ deriv M.u (x - M.sav (n + 1) x z) :=
    (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hx0)
      (by linarith : x - M.sav (n + 1) x z ≤ x)
  linarith

/-- **`s_n(·, z)` is not strictly increasing** for `n ≥ 1` (correction to "increasing",
p. 188): it vanishes on an interval `[0, x̄]`. -/
theorem not_strictMonoOn_sav (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ¬ StrictMonoOn (fun x => M.sav (n + 1) x z) (Set.Ici 0) := by
  intro hmono
  obtain ⟨xb, hxb, hzero⟩ := exists_sav_eq_zero h hs n z
  have := hmono (Set.mem_Ici.2 (half_pos hxb).le) (Set.mem_Ici.2 hxb.le) (half_lt_self hxb)
  simp only [hzero (xb / 2) ⟨half_pos hxb, (half_lt_self hxb).le⟩,
    hzero xb ⟨hxb, le_rfl⟩, lt_self_iff_false] at this

/-- The continuation derivatives are ordered when the value derivatives are. -/
theorem evd_le_evd (h : M.Basic) (hs : M.Smooth) {n k : ℕ} (z : Z) {s : ℝ} (hs0 : 0 ≤ s)
    (hd : ∀ z', ∀ p, 0 < p → deriv (fun y => M.v n y z') p ≤ deriv (fun y => M.v k y z') p) :
    M.evd n z s ≤ M.evd k z s := by
  refine integral_mono (hasDerivAt_ev h hs n z hs0).1 (hasDerivAt_ev h hs k z hs0).1
    fun z' => ?_
  have hp : 0 < M.ρ z' * s + M.w z' := by
    have := mul_nonneg (h.ρ_pos z').le hs0; linarith [h.w_pos z']
  exact mul_le_mul_of_nonneg_right (hd z' _ hp) (h.ρ_pos z').le

/-- **`g_n(x)` is decreasing in `n`** (Miao, p. 188): `g_{n+1}(x, z) ≤ g_n(x, z)` for `x > 0`. -/
theorem cons_succ_le (h : M.Basic) (hs : M.Smooth) :
    ∀ n, ∀ z, ∀ x, 0 < x → M.cons (n + 1) x z ≤ M.cons n x z := by
  intro n
  induction n with
  | zero =>
    intro z x hx
    have := (sav_mem h 0 hx.le z).1.1
    simp only [cons, sav] at this ⊢
    linarith
  | succ n ih =>
    intro z x hx
    have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
    have hd : ∀ z', ∀ p, 0 < p →
        deriv (fun y => M.v n y z') p ≤ deriv (fun y => M.v (n + 1) y z') p := by
      intro z' p hp
      rw [deriv_v h hs n z' hp, deriv_v h hs (n + 1) z' hp]
      exact hu (Set.mem_Ioi.2 (cons_pos h hs (n + 1) hp z')) (Set.mem_Ioi.2 (cons_pos h hs n hp z'))
        (ih z' p hp)
    have hc₁ := cons_pos h hs (n + 1) hx z
    have hc₂ := cons_pos h hs (n + 2) hx z
    have hm₂ := (sav_mem h (n + 1) hx.le z).1
    have f1 := (foc h hs n hx z).2
    have f2 := (foc h hs (n + 1) hx z).1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * M.evd n z s)
      (D₂ := fun s => M.β * M.evd (n + 1) z s) hu (by linarith) hm₂.1 (by linarith) f1 f2
      (mul_le_mul_of_nonneg_left (evd_le_evd h hs z (sav_mem h n hx.le z).1.1 hd) h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd h hs (n + 1) z ha hb hab)
        h.β_pos)
    linarith

/-- **`s_n(x)` is increasing in `n`** (Miao, p. 188). -/
theorem sav_le_sav_succ (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    M.sav n x z ≤ M.sav (n + 1) x z := by
  have := cons_succ_le h hs n z x hx
  simp only [cons] at this
  linarith

/-- **`v_n′(x)` is increasing in `n`** (Miao, p. 188). -/
theorem deriv_v_le (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => M.v n y z) x ≤ deriv (fun y => M.v (n + 1) y z) x := by
  rw [deriv_v h hs n z hx, deriv_v h hs (n + 1) z hx]
  exact (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 (cons_pos h hs (n + 1) hx z))
    (Set.mem_Ioi.2 (cons_pos h hs n hx z)) (cons_succ_le h hs n z x hx)

/-- **The monotonicity in `n` is not strict** (correction to "decreasing", p. 188): there is
`x > 0` with `g_{n+2}(x, z) = g_{n+1}(x, z)`, and `g_1(x, z) = g_0(x, z) = x`. -/
theorem exists_cons_succ_eq (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    (∃ x > 0, M.cons (n + 2) x z = M.cons (n + 1) x z) ∧ ∃ x > 0, M.cons 1 x z = M.cons 0 x z := by
  obtain ⟨a, ha, hza⟩ := exists_sav_eq_zero h hs n z
  obtain ⟨b, hb, hzb⟩ := exists_sav_eq_zero h hs (n + 1) z
  obtain ⟨c, hc, hzc⟩ := exists_sav_eq_zero h hs 0 z
  refine ⟨⟨min a b, lt_min ha hb, ?_⟩, ⟨c, hc, ?_⟩⟩
  · simp only [cons, hza (min a b) ⟨lt_min ha hb, min_le_left _ _⟩,
      hzb (min a b) ⟨lt_min ha hb, min_le_right _ _⟩]
  · have h1 : M.sav 1 c z = 0 := hzc c ⟨hc, le_rfl⟩
    change c - M.sav 1 c z = c - M.sav 0 c z
    rw [h1]
    rfl


omit [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q] in
/-- The deterministic model `detModel z₀` satisfies the standing hypotheses. -/
theorem Basic.detModel (h : M.Basic) (z₀ : Z) : (M.detModel z₀).Basic :=
  ⟨h.β_pos, h.u_cont, h.u_mono, h.u_conc, h.ρ_cont, h.ρ_pos, h.w_cont, h.w_pos,
    isFeller_const (Measure.dirac z₀)⟩

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q] in
/-- The deterministic model's kernel is Markov. -/
theorem isMarkovKernel_detModel (z₀ : Z) : IsMarkovKernel (M.detModel z₀).Q := by
  change IsMarkovKernel (Kernel.const Z (Measure.dirac z₀))
  infer_instance

omit [CompactSpace Z] [IsMarkovKernel M.Q] in
/-- For the deterministic model the continuation derivative is evaluated at the shock `z₀`. -/
theorem evd_detModel (z₀ : Z) (n : ℕ) (z : Z) (s : ℝ) :
    (M.detModel z₀).evd n z s =
      deriv (fun y => (M.detModel z₀).v n y z₀) (M.ρ z₀ * s + M.w z₀) * M.ρ z₀ := by
  change ∫ z', deriv (fun y => (M.detModel z₀).v n y z') (M.ρ z' * s + M.w z') * M.ρ z'
    ∂(Kernel.const Z (Measure.dirac z₀) z) = _
  rw [Kernel.const_apply, integral_dirac]

/-- **The comparison with the lowest income** (Miao, p. 189), for `ρ ≡ R`:
`c_t(x) ≥ c_t(x; y_min)`, where `c_t(x; y_min)` is consumption in the model whose shock is `z₀`
every period and `w(z₀) ≤ w(z′)` for all `z′` (for §6.6.2, `z₀ = y_min`). It holds for every
current shock `z` of the stochastic model (so also for Markov shocks, Exercise 6). -/
theorem cons_ge_low (h : M.Basic) (hs : M.Smooth) {R : ℝ} (hR : ∀ z, M.ρ z = R) {z₀ : Z}
    (hw : ∀ z', M.w z₀ ≤ M.w z') :
    ∀ n, ∀ z z'', ∀ x, 0 < x → (M.detModel z₀).cons n x z'' ≤ M.cons n x z := by
  have := isMarkovKernel_detModel (M := M) z₀
  have hD := h.detModel z₀
  have hDs : (M.detModel z₀).Smooth := ⟨hs.u_diff, hs.inada⟩
  have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
  have hR0 : 0 < R := hR z₀ ▸ h.ρ_pos z₀
  intro n
  induction n with
  | zero => intro z z'' x _; exact le_rfl
  | succ n ih =>
    intro z z'' x hx
    have hc₁ := cons_pos h hs (n + 1) hx z
    have hc₂ := cons_pos hD hDs (n + 1) hx z''
    have hm₁ := (sav_mem h n hx.le z).1
    have hm₂ := (sav_mem hD n hx.le z'').1
    have f1 := (foc h hs n hx z).2
    have f2 := (foc hD hDs n hx z'').1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    set s₁ := M.sav (n + 1) x z
    have hp₀ : 0 < R * s₁ + M.w z₀ := by
      have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z₀]
    set c := deriv (fun y => (M.detModel z₀).v n y z₀) (R * s₁ + M.w z₀) * R
    have hle : M.evd n z s₁ ≤ (M.detModel z₀).evd n z'' s₁ := by
      rw [evd_detModel, hR z₀]
      change M.evd n z s₁ ≤ c
      have hpt : ∀ z', deriv (fun y => M.v n y z') (M.ρ z' * s₁ + M.w z') * M.ρ z' ≤ c := by
        intro z'
        rw [hR z']
        refine mul_le_mul_of_nonneg_right ?_ hR0.le
        have hp' : 0 < R * s₁ + M.w z' := by linarith [hw z']
        have e1 := (strictAntiOn_deriv_v h hs n z').antitoneOn (Set.mem_Ioi.2 hp₀)
          (Set.mem_Ioi.2 hp') (by linarith [hw z'] : R * s₁ + M.w z₀ ≤ R * s₁ + M.w z')
        refine e1.trans ?_
        rw [deriv_v h hs n z' hp₀, deriv_v hD hDs n z₀ hp₀]
        exact hu (Set.mem_Ioi.2 (cons_pos hD hDs n hp₀ z₀)) (Set.mem_Ioi.2 (cons_pos h hs n hp₀ z'))
          (ih z' z₀ _ hp₀)
      calc M.evd n z s₁ ≤ ∫ _, c ∂M.Q z :=
            integral_mono (hasDerivAt_ev h hs n z hm₁.1).1 (integrable_const c) hpt
        _ = c := by simp only [integral_const, probReal_univ, one_smul]
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * M.evd n z s)
      (D₂ := fun s => M.β * (M.detModel z₀).evd n z'' s) hu (by linarith) hm₂.1 (by linarith)
      f1 f2 (mul_le_mul_of_nonneg_left hle h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd hD hDs n z'' ha hb hab)
        h.β_pos)
    linarith

/-- **The comparison with the highest income** (Miao, p. 189), for `ρ ≡ R`:
`c_t(x; y_max) ≥ c_t(x)`, where `c_t(x; y_max)` is consumption in the model whose shock is `z₁`
every period and `w(z′) ≤ w(z₁)` for all `z′` (for §6.6.2, `z₁ = y_max`). -/
theorem cons_le_high (h : M.Basic) (hs : M.Smooth) {R : ℝ} (hR : ∀ z, M.ρ z = R) {z₁ : Z}
    (hw : ∀ z', M.w z' ≤ M.w z₁) :
    ∀ n, ∀ z z'', ∀ x, 0 < x → M.cons n x z ≤ (M.detModel z₁).cons n x z'' := by
  have := isMarkovKernel_detModel (M := M) z₁
  have hD := h.detModel z₁
  have hDs : (M.detModel z₁).Smooth := ⟨hs.u_diff, hs.inada⟩
  have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
  have hR0 : 0 < R := hR z₁ ▸ h.ρ_pos z₁
  intro n
  induction n with
  | zero => intro z z'' x _; exact le_rfl
  | succ n ih =>
    intro z z'' x hx
    have hc₁ := cons_pos hD hDs (n + 1) hx z''
    have hc₂ := cons_pos h hs (n + 1) hx z
    have hm₁ := (sav_mem hD n hx.le z'').1
    have hm₂ := (sav_mem h n hx.le z).1
    have f1 := (foc hD hDs n hx z'').2
    have f2 := (foc h hs n hx z).1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    set s₁ := (M.detModel z₁).sav (n + 1) x z''
    have hp₁ : 0 < R * s₁ + M.w z₁ := by
      have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z₁]
    set c := deriv (fun y => (M.detModel z₁).v n y z₁) (R * s₁ + M.w z₁) * R
    have hle : (M.detModel z₁).evd n z'' s₁ ≤ M.evd n z s₁ := by
      rw [evd_detModel, hR z₁]
      change c ≤ M.evd n z s₁
      have hpt : ∀ z', c ≤ deriv (fun y => M.v n y z') (M.ρ z' * s₁ + M.w z') * M.ρ z' := by
        intro z'
        rw [hR z']
        refine mul_le_mul_of_nonneg_right ?_ hR0.le
        have hp' : 0 < R * s₁ + M.w z' := by
          have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z']
        have e1 := (strictAntiOn_deriv_v h hs n z').antitoneOn (Set.mem_Ioi.2 hp')
          (Set.mem_Ioi.2 hp₁) (by linarith [hw z'] : R * s₁ + M.w z' ≤ R * s₁ + M.w z₁)
        refine le_trans ?_ e1
        rw [deriv_v h hs n z' hp₁, deriv_v hD hDs n z₁ hp₁]
        exact hu (Set.mem_Ioi.2 (cons_pos h hs n hp₁ z')) (Set.mem_Ioi.2 (cons_pos hD hDs n hp₁ z₁))
          (ih z' z₁ _ hp₁)
      calc c = ∫ _, c ∂M.Q z := by simp only [integral_const, probReal_univ, one_smul]
        _ ≤ M.evd n z s₁ := integral_mono (integrable_const c) (hasDerivAt_ev h hs n z hm₁.1).1 hpt
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * (M.detModel z₁).evd n z'' s)
      (D₂ := fun s => M.β * M.evd n z s) hu (by linarith) hm₂.1 (by linarith)
      f1 f2 (mul_le_mul_of_nonneg_left hle h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd h hs n z ha hb hab)
        h.β_pos)
    linarith

end CSModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 6.5–6.7: the consumption-saving problem with iid income, Markov income and
# random returns

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSExercises`), namespace renamed.

Miao, §6.6.2, pp. 186–189 and Exercises 5–7, pp. 189–190, as instances of `CSModel`.

* `bookModel`: §6.6.2 with iid income `y ∈ [y_min, y_max]` drawn from `μ`, cash on hand
  `x′ = R s + y′ − rb`, `r = R − 1`. The standing hypotheses hold when `u` is continuous,
  strictly increasing and strictly concave on `[0, ∞)`, `β, R > 0` and `y_min − rb > 0`
  (`bookModel_basic`). With iid income the value functions do not depend on the current shock
  (`v_indep`), so the state is `x` alone, as the book says.
* **Exercise 6.5** (the properties of p. 188 and the comparison of p. 189): `ex_6_5_value`,
  `ex_6_5_v_deriv_mono`, `ex_6_5_policy_x`, `ex_6_5_policy_n`, `ex_6_5_foc`, `ex_6_5_compare`;
  the corrections `ex_6_5_sav_not_strict` and `ex_6_5_n_not_strict`.
* **Exercise 6.6** (`markovModel`, `ex_6_6`): Markov income on a compact state space with a Feller
  transition `Q`; the state is `(x, z)` and all the properties hold for each current income
  state, including the comparisons with the lowest and highest income paths.
* **Exercise 6.7** (Phelps 1962; `phelpsModel`, `ex_6_7`): `b = 0`, constant income `y > 0`,
  iid gross return `R′ ∈ [R_min, R_max]`, `R_min > 0`, so `x′ = R′ s + y`. All the properties
  except the comparisons hold.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z]

/-- With iid shocks (`Q(z, ·)` independent of `z`) the value functions do not depend on the
current shock (Miao, p. 188: one state variable `x_t` instead of `(a_t, y_t)`). -/
theorem v_indep (M : CSModel Z) (hQ : ∀ z z', M.Q z = M.Q z') (n : ℕ) (x : ℝ) (z z' : Z) :
    M.v n x z = M.v n x z' := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [v_succ, v_succ]
    congr 2
    funext s
    simp only [obj, hQ z z']

end CSModel

/-- **The consumption-saving model of §6.6.2** (Miao, p. 187): iid income `y` with distribution
`μ` on `[y_min, y_max]`, `x′ = R s + y′ − rb` with `r = R − 1`. -/
noncomputable def bookModel (u : ℝ → ℝ) (β R b ymin ymax : ℝ) (μ : Measure (Set.Icc ymin ymax)) :
    CSModel (Set.Icc ymin ymax) where
  u := u
  β := β
  Q := Kernel.const _ μ
  ρ := fun _ => R
  w := fun y => y.1 - (R - 1) * b

/-- The assumptions on `u` in §6.6.2 (p. 187), in the form used here: continuous, strictly
increasing and strictly concave on `[0, ∞)`, differentiable on `(0, ∞)`, `u′(0+) = ∞`. -/
structure CSUtility (u : ℝ → ℝ) : Prop where
  cont : ContinuousOn u (Set.Ici 0)
  mono : StrictMonoOn u (Set.Ici 0)
  conc : StrictConcaveOn ℝ (Set.Ici 0) u
  diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  inada : Tendsto (deriv u) (𝓝[>] 0) atTop

variable {u : ℝ → ℝ} {β R b ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}

/-- The kernel of `bookModel` is Markov. -/
theorem bookModel_isMarkovKernel [IsProbabilityMeasure μ] :
    IsMarkovKernel (bookModel u β R b ymin ymax μ).Q := by
  change IsMarkovKernel (Kernel.const _ μ)
  infer_instance

/-- §6.6.2 satisfies the standing hypotheses when `β, R > 0` and `y_min − rb > 0`. -/
theorem bookModel_basic [IsProbabilityMeasure μ] (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) : (bookModel u β R b ymin ymax μ).Basic where
  β_pos := hβ
  u_cont := hu.cont
  u_mono := hu.mono
  u_conc := hu.conc
  ρ_cont := continuous_const
  ρ_pos := fun _ => hR
  w_cont := continuous_subtype_val.sub continuous_const
  w_pos := fun y => by
    change 0 < y.1 - (R - 1) * b
    linarith [y.2.1]
  feller := CSModel.isFeller_const μ

variable [IsProbabilityMeasure μ]

/-- **Exercise 6.5: the value functions** (Miao, p. 188). For §6.6.2, `v_n` is strictly
increasing and strictly concave on `[0, ∞)`, continuously differentiable on `(0, ∞)` with
`v_n′(x) = u′(g_n(x))`, and for `n ≥ 1` the optimal saving `s_n(x) ∈ [0, x]` exists and is the
unique maximizer. -/
theorem ex_6_5_value (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (bookModel u β R b ymin ymax μ).v n x z) ∧
      (∀ x, 0 < x → HasDerivAt (fun y => (bookModel u β R b ymin ymax μ).v n y z)
        (deriv u ((bookModel u β R b ymin ymax μ).cons n x z)) x) ∧
      ContinuousOn (deriv fun y => (bookModel u β R b ymin ymax μ).v n y z) (Set.Ioi 0) ∧
      ∀ x, 0 ≤ x → ∀ s ∈ Set.Icc 0 x,
        ((bookModel u β R b ymin ymax μ).obj n x z s =
          (bookModel u β R b ymin ymax μ).v (n + 1) x z ↔
          s = (bookModel u β R b ymin ymax μ).sav (n + 1) x z) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    fun x hx => CSModel.hasDerivAt_v h hs n z hx, CSModel.continuousOn_deriv_v h hs n z,
    fun x hx s hsx => ⟨CSModel.sav_unique h n hsx, fun he => ?_⟩⟩
  rw [he]
  exact (CSModel.sav_mem h n hx z).2

/-- **Exercise 6.5: `v_n′(x)` is increasing in `n`** (Miao, p. 188), weakly. -/
theorem ex_6_5_v_deriv_mono (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => (bookModel u β R b ymin ymax μ).v n y z) x ≤
      deriv (fun y => (bookModel u β R b ymin ymax μ).v (n + 1) y z) x := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  exact CSModel.deriv_v_le (bookModel_basic hu hβ hR hfloor) ⟨hu.diff, hu.inada⟩ n z hx

/-- **Exercise 6.5: `g_n` and `s_n` are continuous and increasing in `x`** (Miao, p. 188):
`g_n` strictly, `s_n` weakly (`ex_6_5_sav_not_strict`). -/
theorem ex_6_5_policy_x (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    ContinuousOn (fun x => (bookModel u β R b ymin ymax μ).cons n x z) (Set.Ici 0) ∧
      ContinuousOn (fun x => (bookModel u β R b ymin ymax μ).sav n x z) (Set.Ici 0) ∧
      StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (bookModel u β R b ymin ymax μ).sav n x z) (Set.Ici 0) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  have hz : Continuous fun x : ℝ => (x, z) := continuous_id.prodMk continuous_const
  refine ⟨(CSModel.continuousOn_cons h n).comp hz.continuousOn fun x hx => ⟨hx, Set.mem_univ _⟩,
    (CSModel.continuousOn_sav h n).comp hz.continuousOn fun x hx => ⟨hx, Set.mem_univ _⟩,
    CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z⟩

/-- **Correction to Exercise 6.5:** for `n ≥ 1`, `s_n` is not strictly increasing: the borrowing
constraint binds, `s_n(x) = 0`, for all small `x > 0`. -/
theorem ex_6_5_sav_not_strict (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    (∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, (bookModel u β R b ymin ymax μ).sav (n + 1) x z = 0) ∧
      ¬ StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).sav (n + 1) x z) (Set.Ici 0) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  exact ⟨CSModel.exists_sav_eq_zero h ⟨hu.diff, hu.inada⟩ n z,
    CSModel.not_strictMonoOn_sav h ⟨hu.diff, hu.inada⟩ n z⟩

/-- **Exercise 6.5: `g_n(x)` is decreasing in `n` and `s_n(x)` increasing in `n`** (Miao,
p. 188), weakly, for `x > 0`. -/
theorem ex_6_5_policy_n (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    (bookModel u β R b ymin ymax μ).cons (n + 1) x z ≤ (bookModel u β R b ymin ymax μ).cons n x z ∧
      (bookModel u β R b ymin ymax μ).sav n x z ≤
        (bookModel u β R b ymin ymax μ).sav (n + 1) x z := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  exact ⟨CSModel.cons_succ_le h ⟨hu.diff, hu.inada⟩ n z x hx,
    CSModel.sav_le_sav_succ h ⟨hu.diff, hu.inada⟩ n z hx⟩

/-- **Correction to Exercise 6.5:** the monotonicity in `n` is not strict: there are `x > 0`
with `g_{n+2}(x) = g_{n+1}(x)`, and with `g_1(x) = g_0(x)` (so also `v_1′(x) = v_0′(x)`). -/
theorem ex_6_5_n_not_strict (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    (∃ x > 0, (bookModel u β R b ymin ymax μ).cons (n + 2) x z =
      (bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      ∃ x > 0, (bookModel u β R b ymin ymax μ).cons 1 x z =
        (bookModel u β R b ymin ymax μ).cons 0 x z := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  exact CSModel.exists_cons_succ_eq (bookModel_basic hu hβ hR hfloor) ⟨hu.diff, hu.inada⟩ n z

/-- **Exercise 6.5: the first-order and envelope conditions** (Miao, p. 188): for `x > 0`,
`v_{n+1}′(x) = u′(g_{n+1}(x)) ≥ βR E v_n′(R s_{n+1}(x) + y − rb)`, with equality if
`s_{n+1}(x) > 0`. -/
theorem ex_6_5_foc (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => (bookModel u β R b ymin ymax μ).v (n + 1) y z) x =
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      β * R * ∫ y', deriv (fun x' => (bookModel u β R b ymin ymax μ).v n x' y')
          (R * (bookModel u β R b ymin ymax μ).sav (n + 1) x z + y'.1 - (R - 1) * b) ∂μ ≤
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      (0 < (bookModel u β R b ymin ymax μ).sav (n + 1) x z →
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) =
          β * R * ∫ y', deriv (fun x' => (bookModel u β R b ymin ymax μ).v n x' y')
            (R * (bookModel u β R b ymin ymax μ).sav (n + 1) x z + y'.1 - (R - 1) * b) ∂μ) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  set M := bookModel u β R b ymin ymax μ
  have hev : ∀ s, M.β * M.evd n z s =
      β * R * ∫ y', deriv (fun x' => M.v n x' y') (R * s + y'.1 - (R - 1) * b) ∂μ := by
    intro s
    change β * ∫ y', deriv (fun x' => M.v n x' y') (R * s + (y'.1 - (R - 1) * b)) * R ∂μ = _
    rw [integral_mul_const]
    simp only [add_sub_assoc]
    ring
  obtain ⟨f1, f2⟩ := CSModel.foc h hs n hx z
  rw [hev] at f1 f2
  exact ⟨CSModel.deriv_v h hs (n + 1) z hx, f1, f2⟩

/-- **The comparison of p. 189** (Exercise 6.5): `c_t(x; y_max) ≥ c_t(x) ≥ c_t(x; y_min)`, with
`c_t = g_{T−t}` and `c_t(x; y)` the consumption policy when income is `y` in every period
(`detModel`). -/
theorem ex_6_5_compare (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (hy : ymin ≤ ymax) (n : ℕ) (z z'' : Set.Icc ymin ymax)
    {x : ℝ} (hx : 0 < x) :
    ((bookModel u β R b ymin ymax μ).detModel ⟨ymin, le_rfl, hy⟩).cons n x z'' ≤
        (bookModel u β R b ymin ymax μ).cons n x z ∧
      (bookModel u β R b ymin ymax μ).cons n x z ≤
        ((bookModel u β R b ymin ymax μ).detModel ⟨ymax, hy, le_rfl⟩).cons n x z'' := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.cons_ge_low h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx,
    CSModel.cons_le_high h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx⟩
  · change ymin - (R - 1) * b ≤ z'.1 - (R - 1) * b
    linarith [z'.2.1]
  · change z'.1 - (R - 1) * b ≤ ymax - (R - 1) * b
    linarith [z'.2.2]

/-! ### Exercise 6.6: Markov income -/

/-- **Exercise 6.6** (Miao, p. 190): the problem of §6.6.2 with Markov income `y(z)`, `z ∈ Z`
following `Q`. The state is `(x, z)` with `x = Ra + y(z) + b`; next period
`x′ = R s + y(z′) − rb`. -/
def markovModel {Z : Type*} [MeasurableSpace Z] (u : ℝ → ℝ) (β R b : ℝ) (y : Z → ℝ)
    (Q : Kernel Z Z) : CSModel Z where
  u := u
  β := β
  Q := Q
  ρ := fun _ => R
  w := fun z => y z - (R - 1) * b

/-- **Exercise 6.6** (Miao, p. 190). For Markov income on a compact metric state space `Z`
(Feller `Q`, continuous income `y`, cash floor `y(z) − rb > 0`), for each current state `z`:
`v_n(·, z)` is strictly increasing, strictly concave and `C¹` on `(0, ∞)` with
`v_n′ = u′ ∘ g_n`; `g_n(·, z)` is strictly increasing and `s_n(·, z)` increasing; the first-order
condition holds with `E` the conditional expectation `∫ Q(z, dz′)`; `g_n` is decreasing and `s_n`
increasing in `n`; and consumption lies between the policies for the constant income paths at
the lowest and highest income states. -/
theorem ex_6_6 {Z : Type*} [MeasurableSpace Z] [MetricSpace Z] [CompactSpace Z] [BorelSpace Z]
    {y : Z → ℝ} {Q : Kernel Z Z} [IsMarkovKernel Q] (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hy : Continuous y) (hfloor : ∀ z, 0 < y z - (R - 1) * b) (hQ : IsFeller Q) {zlo zhi : Z}
    (hlo : ∀ z, y zlo ≤ y z) (hhi : ∀ z, y z ≤ y zhi) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => (markovModel u β R b y Q).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (markovModel u β R b y Q).v n x z) ∧
      ContinuousOn (deriv fun x => (markovModel u β R b y Q).v n x z) (Set.Ioi 0) ∧
      (∀ x, 0 < x → deriv (fun x' => (markovModel u β R b y Q).v n x' z) x =
        deriv u ((markovModel u β R b y Q).cons n x z)) ∧
      StrictMonoOn (fun x => (markovModel u β R b y Q).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (markovModel u β R b y Q).sav n x z) (Set.Ici 0) ∧
      (∀ x, 0 < x →
        β * (markovModel u β R b y Q).evd n z ((markovModel u β R b y Q).sav (n + 1) x z) ≤
          deriv u ((markovModel u β R b y Q).cons (n + 1) x z) ∧
        (0 < (markovModel u β R b y Q).sav (n + 1) x z →
          deriv u ((markovModel u β R b y Q).cons (n + 1) x z) =
            β * (markovModel u β R b y Q).evd n z ((markovModel u β R b y Q).sav (n + 1) x z))) ∧
      (∀ x, 0 < x → (markovModel u β R b y Q).cons (n + 1) x z ≤
        (markovModel u β R b y Q).cons n x z) ∧
      ∀ x, 0 < x → ∀ z'', ((markovModel u β R b y Q).detModel zlo).cons n x z'' ≤
        (markovModel u β R b y Q).cons n x z ∧
        (markovModel u β R b y Q).cons n x z ≤ ((markovModel u β R b y Q).detModel zhi).cons n x z''
      := by
  have : IsMarkovKernel (markovModel u β R b y Q).Q := ‹IsMarkovKernel Q›
  have h : (markovModel u β R b y Q).Basic :=
    ⟨hβ, hu.cont, hu.mono, hu.conc, continuous_const, fun _ => hR,
      hy.sub continuous_const, hfloor, hQ⟩
  have hs : (markovModel u β R b y Q).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    CSModel.continuousOn_deriv_v h hs n z, fun x hx => CSModel.deriv_v h hs n z hx,
    CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z,
    fun x hx => CSModel.foc h hs n hx z, fun x hx => CSModel.cons_succ_le h hs n z x hx,
    fun x hx z'' => ⟨CSModel.cons_ge_low h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx,
      CSModel.cons_le_high h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx⟩⟩
  · change y zlo - (R - 1) * b ≤ y z' - (R - 1) * b
    linarith [hlo z']
  · change y z' - (R - 1) * b ≤ y zhi - (R - 1) * b
    linarith [hhi z']

/-! ### Exercise 6.7: Phelps (1962), random returns -/

/-- **Exercise 6.7** (Phelps 1962; Miao, p. 190): no borrowing (`b = 0`), constant income `y`,
iid gross return `R′ ∈ [R_min, R_max]` with distribution `ν`; `x′ = R′ s + y`. -/
noncomputable def phelpsModel (u : ℝ → ℝ) (β y Rmin Rmax : ℝ) (ν : Measure (Set.Icc Rmin Rmax)) :
    CSModel (Set.Icc Rmin Rmax) where
  u := u
  β := β
  Q := Kernel.const _ ν
  ρ := fun R' => R'.1
  w := fun _ => y

/-- **Exercise 6.7** (Phelps 1962; Miao, p. 190). With `R_min > 0` and `y > 0`: `v_n` is strictly
increasing, strictly concave and `C¹` on `(0, ∞)` with `v_n′ = u′ ∘ g_n`; the first-order
condition is `u′(g_{n+1}(x)) ≥ β E[R′ v_n′(R′ s_{n+1}(x) + y)]`, with equality if
`s_{n+1}(x) > 0`; `g_n` is strictly and `s_n` weakly increasing in `x`; the saving constraint
binds for small `x`; `g_n` is decreasing and `s_n` increasing in `n`. -/
theorem ex_6_7 {y Rmin Rmax : ℝ} {ν : Measure (Set.Icc Rmin Rmax)} [IsProbabilityMeasure ν]
    (hu : CSUtility u) (hβ : 0 < β) (hRmin : 0 < Rmin) (hy : 0 < y) (n : ℕ)
    (z : Set.Icc Rmin Rmax) :
    StrictMonoOn (fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) ∧
      ContinuousOn (deriv fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) (Set.Ioi 0) ∧
      (∀ x, 0 < x → deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' z) x =
        deriv u ((phelpsModel u β y Rmin Rmax ν).cons n x z)) ∧
      (∀ x, 0 < x →
        β * ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R')
            (R'.1 * (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z + y) ∂ν ≤
          deriv u ((phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z) ∧
        (0 < (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z →
          deriv u ((phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z) =
            β * ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R')
              (R'.1 * (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z + y) ∂ν)) ∧
      StrictMonoOn (fun x => (phelpsModel u β y Rmin Rmax ν).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (phelpsModel u β y Rmin Rmax ν).sav n x z) (Set.Ici 0) ∧
      (∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z = 0) ∧
      ∀ x, 0 < x → (phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z ≤
          (phelpsModel u β y Rmin Rmax ν).cons n x z ∧
        (phelpsModel u β y Rmin Rmax ν).sav n x z ≤ (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z
      := by
  have : IsMarkovKernel (phelpsModel u β y Rmin Rmax ν).Q := by
    change IsMarkovKernel (Kernel.const _ ν)
    infer_instance
  have h : (phelpsModel u β y Rmin Rmax ν).Basic :=
    ⟨hβ, hu.cont, hu.mono, hu.conc, continuous_subtype_val, fun R' => hRmin.trans_le R'.2.1,
      continuous_const, fun _ => hy, CSModel.isFeller_const ν⟩
  have hs : (phelpsModel u β y Rmin Rmax ν).Smooth := ⟨hu.diff, hu.inada⟩
  have hev : ∀ s, (phelpsModel u β y Rmin Rmax ν).evd n z s =
      ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R') (R'.1 * s + y) ∂ν :=
    fun s => by
      change ∫ R', deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R') (R'.1 * s + y) *
        R'.1 ∂ν = _
      simp only [mul_comm]
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    CSModel.continuousOn_deriv_v h hs n z, fun x hx => CSModel.deriv_v h hs n z hx,
    fun x hx => ?_, CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z,
    CSModel.exists_sav_eq_zero h hs n z, fun x hx => ⟨CSModel.cons_succ_le h hs n z x hx,
      CSModel.sav_le_sav_succ h hs n z hx⟩⟩
  obtain ⟨f1, f2⟩ := CSModel.foc h hs n hx z
  rw [hev] at f1 f2
  exact ⟨f1, f2⟩

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.8: the deterministic CRRA consumption-saving problem

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSDeterministic`), namespace renamed.

Miao, Exercise 8, p. 190: maximize `Σ_{t=0}^T βᵗ c_t^{1−γ}/(1−γ)` subject to
`c_t + a_{t+1} = R a_t + y_t`, `a_0` given, `y_{t+1} = (1 + g) y_t`, with no borrowing constraint.
Without a terminal condition the problem is unbounded, so we impose the natural one,
`a_{T+1} ≥ 0` (at the optimum `a_{T+1} = 0`). `γ = 1` is log utility (`cs_crra`).

* `cs_budget`: the intertemporal budget constraint from any date `t`:
  `Σ_{k=0}^m c_{t+k}/R^k + a_{t+m+1}/R^m = R a_t + Σ_{k=0}^m y_{t+k}/R^k`.
* `cs_optimal_of_euler`: for any utility with tangent-line inequality (concavity), a feasible
  path satisfying the Euler equations `βᵗ u′(c_t) = λ/Rᵗ` (`λ ≥ 0`) and `a_{T+1} = 0` is optimal.
* `cs_crra_tangent`: the tangent-line inequality for CRRA utility, with `u′(c) = c^{−γ}`.
* **`ex_6_8`**: the explicit solution. With `θ = (βR)^{1/γ}` and total wealth
  `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ > 0`, consumption is `c_t = c_0 θᵗ` with
  `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ`; the path is feasible with `a_{T+1} = 0` and optimal; and the
  policy is consumption = (financial plus human wealth) / annuity factor:
  `c_t = (R a_t + y_t Σ_{k=0}^{T−t} ((1+g)/R)^k) / Σ_{k=0}^{T−t} (θ/R)^k`.
-/

namespace Miao.IncompleteMarkets

open Finset Real

/-- **The intertemporal budget constraint** (Miao, Exercise 8, p. 190): if
`c_{t+k} + a_{t+k+1} = R a_{t+k} + y_{t+k}` for `k ≤ m`, then
`Σ_{k=0}^m c_{t+k}/R^k + a_{t+m+1}/R^m = R a_t + Σ_{k=0}^m y_{t+k}/R^k`. -/
theorem cs_budget {R : ℝ} (hR : R ≠ 0) (c a y : ℕ → ℝ) (t : ℕ) :
    ∀ m, (∀ k ≤ m, c (t + k) + a (t + k + 1) = R * a (t + k) + y (t + k)) →
      ∑ k ∈ range (m + 1), c (t + k) / R ^ k + a (t + m + 1) / R ^ m =
        R * a t + ∑ k ∈ range (m + 1), y (t + k) / R ^ k := by
  intro m
  induction m with
  | zero =>
    intro h
    have := h 0 le_rfl
    simp only [zero_add, range_one, sum_singleton, pow_zero, div_one, add_zero] at this ⊢
    exact this
  | succ m ih =>
    intro h
    have ih' := ih fun k hk => h k (by omega)
    have hm := h (m + 1) le_rfl
    have e : t + (m + 1) = t + m + 1 := by omega
    rw [e] at hm
    rw [sum_range_succ (fun k => c (t + k) / R ^ k), sum_range_succ (fun k => y (t + k) / R ^ k), e]
    have hRm : R ^ (m + 1) = R ^ m * R := pow_succ R m
    have hRm0 : R ^ m ≠ 0 := pow_ne_zero m hR
    have key : R * a (t + m + 1) / R ^ (m + 1) = a (t + m + 1) / R ^ m := by
      rw [hRm]; field_simp
    have hm' : c (t + m + 1) / R ^ (m + 1) + a (t + m + 1 + 1) / R ^ (m + 1) =
        R * a (t + m + 1) / R ^ (m + 1) + y (t + m + 1) / R ^ (m + 1) := by
      rw [← add_div, ← add_div, hm]
    linarith

/-- **Sufficiency of the Euler equations** (Miao, Exercise 8): let `u(c′) ≤ u(c) + u′(c)(c′ − c)`
for `c, c′ > 0`. If `(c, a)` satisfies the budget constraints with `a_{T+1} = 0` and the Euler
equations `βᵗ u′(c_t) = λ / Rᵗ` with `λ ≥ 0`, then every feasible `(c′, a′)` (same `a_0`, positive
consumption, `a′_{T+1} ≥ 0`) has `Σ βᵗ u(c′_t) ≤ Σ βᵗ u(c_t)`. -/
theorem cs_optimal_of_euler {u du : ℝ → ℝ} {β R lam : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hlam : 0 ≤ lam) (htan : ∀ c c', 0 < c → 0 < c' → u c' ≤ u c + du c * (c' - c))
    {T : ℕ} {y c a c' a' : ℕ → ℝ} (ha : a 0 = a' 0)
    (hb : ∀ t ≤ T, c t + a (t + 1) = R * a t + y t)
    (hb' : ∀ t ≤ T, c' t + a' (t + 1) = R * a' t + y t) (hT : a (T + 1) = 0)
    (hT' : 0 ≤ a' (T + 1)) (hc : ∀ t ≤ T, 0 < c t) (hc' : ∀ t ≤ T, 0 < c' t)
    (heul : ∀ t ≤ T, β ^ t * du (c t) = lam / R ^ t) :
    ∑ t ∈ range (T + 1), β ^ t * u (c' t) ≤ ∑ t ∈ range (T + 1), β ^ t * u (c t) := by
  have B := cs_budget hR.ne' c a y 0 T fun k hk => by simpa using hb k hk
  have B' := cs_budget hR.ne' c' a' y 0 T fun k hk => by simpa using hb' k hk
  simp only [zero_add] at B B'
  rw [hT, zero_div, add_zero, ha] at B
  have hpv : ∑ t ∈ range (T + 1), (c' t - c t) / R ^ t ≤ 0 := by
    have : 0 ≤ a' (T + 1) / R ^ T := div_nonneg hT' (pow_pos hR T).le
    simp only [sub_div, sum_sub_distrib]
    linarith
  have hterm : ∀ t ∈ range (T + 1),
      β ^ t * u (c' t) ≤ β ^ t * u (c t) + lam * ((c' t - c t) / R ^ t) := by
    intro t ht
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := mul_le_mul_of_nonneg_left (htan (c t) (c' t) (hc t htT) (hc' t htT))
      (pow_pos hβ t).le
    have h2 : β ^ t * (du (c t) * (c' t - c t)) = lam * ((c' t - c t) / R ^ t) := by
      rw [← mul_assoc, heul t htT]
      ring
    linarith
  calc ∑ t ∈ range (T + 1), β ^ t * u (c' t)
      ≤ ∑ t ∈ range (T + 1), (β ^ t * u (c t) + lam * ((c' t - c t) / R ^ t)) :=
        sum_le_sum hterm
    _ = ∑ t ∈ range (T + 1), β ^ t * u (c t) +
          lam * ∑ t ∈ range (T + 1), (c' t - c t) / R ^ t := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ ∑ t ∈ range (T + 1), β ^ t * u (c t) := by
        have := mul_nonpos_of_nonneg_of_nonpos hlam hpv
        linarith

/-- **CRRA utility** `c^{1−γ}/(1−γ)`, with the logarithm at `γ = 1`. -/
noncomputable def cs_crra (γ c : ℝ) : ℝ := if γ = 1 then Real.log c else c ^ (1 - γ) / (1 - γ)

/-- The tangent-line inequality for CRRA utility: `u(c′) ≤ u(c) + c^{−γ}(c′ − c)` for
`c, c′ > 0`, `γ > 0` (Bernoulli's inequality; `log t ≤ t − 1` at `γ = 1`). -/
theorem cs_crra_tangent {γ : ℝ} (hγ : 0 < γ) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    cs_crra γ c' ≤ cs_crra γ c + c ^ (-γ) * (c' - c) := by
  set t := c' / c with htdef
  have ht : 0 < t := div_pos hc' hc
  have hc't : c' = c * t := by rw [htdef]; field_simp
  have hcinv : c ^ (-γ) = c ^ (1 - γ) / c := by
    rw [rpow_sub hc, rpow_one, rpow_neg hc.le]
    have : c ^ γ ≠ 0 := (rpow_pos_of_pos hc γ).ne'
    field_simp
  unfold cs_crra
  split_ifs with h1
  · subst h1
    rw [hc't, Real.log_mul hc.ne' ht.ne', rpow_neg_one]
    have := Real.log_le_sub_one_of_pos ht
    have e : c⁻¹ * (c * t - c) = t - 1 := by field_simp
    rw [e]
    linarith
  · have hp : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have hcp : 0 < c ^ (1 - γ) := rpow_pos_of_pos hc _
    rw [hc't, mul_rpow hc.le ht.le, hcinv]
    have e : c ^ (1 - γ) / c * (c * t - c) = c ^ (1 - γ) * (t - 1) := by field_simp
    rw [e]
    -- reduce to `t^p/p ≤ 1/p + (t − 1)`
    suffices hs : t ^ (1 - γ) / (1 - γ) ≤ 1 / (1 - γ) + (t - 1) by
      have := mul_le_mul_of_nonneg_left hs hcp.le
      have e2 : c ^ (1 - γ) * (t ^ (1 - γ) / (1 - γ)) = c ^ (1 - γ) * t ^ (1 - γ) / (1 - γ) := by
        ring
      have e3 : c ^ (1 - γ) * (1 / (1 - γ) + (t - 1)) =
          c ^ (1 - γ) / (1 - γ) + c ^ (1 - γ) * (t - 1) := by ring
      linarith
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · -- `γ > 1`: `t^p ≥ 1 + p(t − 1)`
      have h1 : 1 + (1 - γ) * Real.log t ≤ t ^ (1 - γ) := by
        rw [rpow_def_of_pos ht, mul_comm]
        linarith [Real.add_one_le_exp (Real.log t * (1 - γ))]
      have h2 : (1 - γ) * (t - 1) ≤ (1 - γ) * Real.log t :=
        mul_le_mul_of_nonpos_left (Real.log_le_sub_one_of_pos ht) hneg.le
      rw [div_le_iff_of_neg hneg]
      have : (1 / (1 - γ) + (t - 1)) * (1 - γ) = 1 + (1 - γ) * (t - 1) := by field_simp
      rw [this]
      linarith
    · -- `0 < γ < 1`: Bernoulli `t^p ≤ 1 + p(t − 1)`
      have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hpos.le
        (by linarith)
      rw [add_sub_cancel] at hb
      rw [div_le_iff₀ hpos]
      have : (1 / (1 - γ) + (t - 1)) * (1 - γ) = 1 + (1 - γ) * (t - 1) := by field_simp
      rw [this]
      linarith

/-- The growth factor of consumption, `θ = (βR)^{1/γ}`. -/
noncomputable def cs_theta (β R γ : ℝ) : ℝ := (β * R) ^ (1 / γ)

/-- Total wealth at date 0: `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ`. -/
noncomputable def cs_wealth (R g a₀ y₀ : ℝ) (T : ℕ) : ℝ :=
  R * a₀ + y₀ * ∑ t ∈ range (T + 1), ((1 + g) / R) ^ t

/-- The optimal consumption path `c_t = c_0 θᵗ`, `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ`. -/
noncomputable def cs_cstar (β R γ g a₀ y₀ : ℝ) (T t : ℕ) : ℝ :=
  cs_wealth R g a₀ y₀ T / (∑ k ∈ range (T + 1), (cs_theta β R γ / R) ^ k) *
    cs_theta β R γ ^ t

/-- The asset path generated by `cs_cstar` from `a_0` and income `y_t = (1+g)ᵗ y_0`. -/
noncomputable def cs_astar (β R γ g a₀ y₀ : ℝ) (T : ℕ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => R * cs_astar β R γ g a₀ y₀ T t + (1 + g) ^ t * y₀ - cs_cstar β R γ g a₀ y₀ T t

/-- **Exercise 6.8** (Miao, p. 190): the explicit solution of the deterministic CRRA problem
with growing income `y_t = (1+g)ᵗ y_0` and the terminal condition `a_{T+1} ≥ 0`. Let
`θ = (βR)^{1/γ}`, `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ > 0` and
`c_t = c_0 θᵗ`, `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ` (`γ = 1` is log utility, `θ = βR`). Then
* the path is feasible: `c_t > 0`, the budget constraints hold and `a_{T+1} = 0`;
* the Euler equation `c_{t+1} = θ c_t` holds;
* it is optimal among all feasible paths;
* the policy: `c_t Σ_{k=0}^{T−t} (θ/R)^k = R a_t + y_t Σ_{k=0}^{T−t} ((1+g)/R)^k`, i.e. consumption
  is financial plus human wealth divided by the annuity factor. -/
theorem ex_6_8 {β R γ g a₀ y₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) (hγ : 0 < γ) (T : ℕ)
    (hW : 0 < cs_wealth R g a₀ y₀ T) :
    (∀ t ≤ T, 0 < cs_cstar β R γ g a₀ y₀ T t) ∧
      (∀ t ≤ T, cs_cstar β R γ g a₀ y₀ T t + cs_astar β R γ g a₀ y₀ T (t + 1) =
        R * cs_astar β R γ g a₀ y₀ T t + (1 + g) ^ t * y₀) ∧
      cs_astar β R γ g a₀ y₀ T (T + 1) = 0 ∧
      (∀ t, cs_cstar β R γ g a₀ y₀ T (t + 1) = cs_theta β R γ * cs_cstar β R γ g a₀ y₀ T t) ∧
      (∀ c a : ℕ → ℝ, a 0 = a₀ → (∀ t ≤ T, c t + a (t + 1) = R * a t + (1 + g) ^ t * y₀) →
        0 ≤ a (T + 1) → (∀ t ≤ T, 0 < c t) →
        ∑ t ∈ range (T + 1), β ^ t * cs_crra γ (c t) ≤
          ∑ t ∈ range (T + 1), β ^ t * cs_crra γ (cs_cstar β R γ g a₀ y₀ T t)) ∧
      ∀ t ≤ T, cs_cstar β R γ g a₀ y₀ T t * ∑ k ∈ range (T - t + 1), (cs_theta β R γ / R) ^ k =
        R * cs_astar β R γ g a₀ y₀ T t +
          (1 + g) ^ t * y₀ * ∑ k ∈ range (T - t + 1), ((1 + g) / R) ^ k := by
  set θ := cs_theta β R γ with hθdef
  have hθ : 0 < θ := rpow_pos_of_pos (mul_pos hβ hR) _
  set A := ∑ k ∈ range (T + 1), (θ / R) ^ k with hAdef
  have hA : 0 < A := sum_pos (fun k _ => pow_pos (div_pos hθ hR) k) nonempty_range_add_one
  set W := cs_wealth R g a₀ y₀ T with hWdef
  set c₀ := W / A with hc₀def
  have hc₀ : 0 < c₀ := div_pos hW hA
  have hcs : ∀ t, cs_cstar β R γ g a₀ y₀ T t = c₀ * θ ^ t := fun t => rfl
  set y : ℕ → ℝ := fun t => (1 + g) ^ t * y₀ with hydef
  have hbud : ∀ t, cs_cstar β R γ g a₀ y₀ T t + cs_astar β R γ g a₀ y₀ T (t + 1) =
      R * cs_astar β R γ g a₀ y₀ T t + y t := fun t => by
    rw [cs_astar]; ring
  have hpos : ∀ t, 0 < cs_cstar β R γ g a₀ y₀ T t := fun t => by
    rw [hcs]; exact mul_pos hc₀ (pow_pos hθ t)
  have hshift : ∀ t k, cs_cstar β R γ g a₀ y₀ T (t + k) / R ^ k =
      cs_cstar β R γ g a₀ y₀ T t * (θ / R) ^ k := fun t k => by
    rw [hcs, hcs, div_pow, pow_add]; ring
  have hyshift : ∀ t k, y (t + k) / R ^ k = y t * ((1 + g) / R) ^ k := fun t k => by
    simp only [hydef, div_pow, pow_add]; ring
  -- the terminal condition from the budget constraint
  have hT : cs_astar β R γ g a₀ y₀ T (T + 1) = 0 := by
    have B := cs_budget hR.ne' (cs_cstar β R γ g a₀ y₀ T) (cs_astar β R γ g a₀ y₀ T) y 0 T
      fun k _ => hbud (0 + k)
    simp only [zero_add] at B
    have h1 : ∑ k ∈ range (T + 1), cs_cstar β R γ g a₀ y₀ T k / R ^ k = W := by
      have := fun k => hshift 0 k
      simp only [zero_add] at this
      simp only [this, ← mul_sum]
      rw [← hAdef, hcs, pow_zero, mul_one, hc₀def, div_mul_cancel₀ _ hA.ne']
    have h2 : ∑ k ∈ range (T + 1), y k / R ^ k = y₀ * ∑ k ∈ range (T + 1), ((1 + g) / R) ^ k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [hydef, div_pow]
      ring
    rw [h1, h2] at B
    have h3 : cs_astar β R γ g a₀ y₀ T 0 = a₀ := rfl
    rw [h3] at B
    have h4 : cs_astar β R γ g a₀ y₀ T (T + 1) / R ^ T = 0 := by
      simp only [hWdef, cs_wealth] at B; linarith
    rcases div_eq_zero_iff.1 h4 with h | h
    · exact h
    · exact absurd h (pow_ne_zero T hR.ne')
  refine ⟨fun t _ => hpos t, fun t _ => hbud t, hT, fun t => ?_, ?_, fun t ht => ?_⟩
  · rw [hcs, hcs, pow_succ]; ring
  · intro c a ha hb hb' hc
    refine cs_optimal_of_euler (u := cs_crra γ) (du := fun c => c ^ (-γ)) (lam := c₀ ^ (-γ))
      (y := y) hβ hR (rpow_nonneg hc₀.le _) (fun c c' hc hc' => cs_crra_tangent hγ hc hc')
      (a := cs_astar β R γ g a₀ y₀ T) (a' := a) ha.symm (fun t _ => hbud t) hb hT hb'
      (fun t _ => hpos t) hc fun t _ => ?_
    have hθγ : θ ^ (-γ) = (β * R)⁻¹ := by
      rw [hθdef, cs_theta, ← rpow_mul (mul_pos hβ hR).le]
      have : 1 / γ * -γ = -1 := by field_simp
      rw [this, rpow_neg_one]
    change β ^ t * (cs_cstar β R γ g a₀ y₀ T t) ^ (-γ) = c₀ ^ (-γ) / R ^ t
    rw [hcs, mul_rpow hc₀.le (pow_pos hθ t).le, ← rpow_natCast θ t, ← rpow_mul hθ.le,
      mul_comm (t : ℝ) (-γ), rpow_mul hθ.le, rpow_natCast, hθγ, inv_pow, mul_pow]
    have := pow_pos hβ t
    have := pow_pos hR t
    field_simp
  · have B := cs_budget hR.ne' (cs_cstar β R γ g a₀ y₀ T) (cs_astar β R γ g a₀ y₀ T) y t (T - t)
      fun k _ => hbud (t + k)
    have e : t + (T - t) + 1 = T + 1 := by omega
    rw [e, hT, zero_div, add_zero] at B
    simp only [hshift, hyshift, ← mul_sum] at B
    rw [B]

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §§7.4–7.5: tools (supergradients, the limit step, inequality (7.38))

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EUTools`), namespace renamed.

Miao, §§7.4–7.5, pp. 217–227. Tools for the Maximum Principle and the Euler-equation results.

* `eu_concave_le_fderiv` and `eu_le_of_le_add_tendsto_zero` are copied from
  `RecursiveMethods/DeterministicDP` (module `EulerEquations`: `concave_le_fderiv`,
  `le_of_le_add_tendsto_zero`), namespace renamed: a concave function lies below its tangent
  plane at a point of differentiability, on any convex set (not only on the whole space); and the
  limit step `s′_T ≤ s_T + w_T`, `w_T → 0` ⇒ `lim s′ ≤ lim s` in `[−∞, +∞]`.
* `eu_supergradient`: the supergradient inequality on a convex subset of `ℝ²`, with the partial
  derivatives written as `deriv` (as in `oc_supergradient`, which needs concavity on all of `ℝ²`).
* `eu_limsup_le`: the limit step of the sufficiency proofs in the form we use for optimality.
  If `S*_T → J*` and `S_T ≤ S*_T + w_T` with `w_T → 0`, then `S_T ≤ J* + ε` eventually: the
  partial sums of the competing plan are eventually at most `J* + ε`, whether or not they
  converge (they may tend to `−∞`).
* `eq_7_38` (**inequality (7.38)**, p. 224): for `f` concave on `[0, 1]`, `γ ∈ [0, 1)` and
  `λ ∈ [γ, 1)`, `(f(1) − f(λ))/(1 − λ) ≤ (f(1) − f(γ))/(1 − γ)`. The book allows
  `f : [0, 1] → ℝ ∪ {−∞}` with `f(1) > −∞`; when `f(γ) = −∞` the right side is `+∞` and there is
  nothing to prove, so we state the real-valued case.
* `eu_clm_pair`: a continuous linear form on `ℝⁿ × ℝⁿ` in coordinates,
  `L(v, w) = Σᵢ vᵢ L(eᵢ, 0) + Σᵢ wᵢ L(0, eᵢ)`, so that `L(v, w) = u_x · v + u_a · w` with the
  partial derivatives as vectors.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- A concave function lies below its tangent plane (copied from
`RecursiveMethods/DeterministicDP`, `concave_le_fderiv`): if `φ` is concave on a convex set `A`
containing `z₀` and `z`, and has derivative `φ'` at `z₀`, then `φ(z) ≤ φ(z₀) + φ'(z − z₀)`. -/
theorem eu_concave_le_fderiv {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {A : Set F'} {φ : F' → ℝ} (hφ : ConcaveOn ℝ A φ) {z₀ z : F'} (hz₀ : z₀ ∈ A) (hz : z ∈ A)
    {φ' : F' →L[ℝ] ℝ} (hd : HasFDerivAt φ φ' z₀) : φ z ≤ φ z₀ + φ' (z - z₀) := by
  set g : ℝ → ℝ := fun t => φ (z₀ + t • (z - z₀))
  have hg : HasDerivAt g (φ' (z - z₀)) 0 := by
    have hline : HasDerivAt (fun t : ℝ => z₀ + t • (z - z₀)) (z - z₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - z₀)).const_add z₀
    have hd' : HasFDerivAt φ φ' (z₀ + (0 : ℝ) • (z - z₀)) := by simpa using hd
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    simpa [g, Function.comp_def] using this
  have hslope : ∀ t : ℝ, 0 < t → t ≤ 1 → φ z - φ z₀ ≤ t⁻¹ • (g (0 + t) - g 0) := by
    intro t ht0 ht1
    have hc := hφ.2 hz₀ hz (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have e : (1 - t) • z₀ + t • z = z₀ + t • (z - z₀) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    simp only [g, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have hlim := hg.tendsto_slope_zero_right
  refine sub_le_iff_le_add'.1 (ge_of_tendsto hlim ?_)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
  exact hslope t ht.1 ht.2.le

/-- The limit step (copied from `RecursiveMethods/DeterministicDP`,
`le_of_le_add_tendsto_zero`): if `sₙ → L`, `wₙ → 0`, `s′ₙ ≤ sₙ + wₙ` and `s′ₙ → L′` in
`[−∞, +∞]`, then `L′ ≤ L`. -/
theorem eu_le_of_le_add_tendsto_zero {s s' w : ℕ → ℝ} {L L' : EReal}
    (hs : Tendsto (fun n => (s n : EReal)) atTop (𝓝 L))
    (hs' : Tendsto (fun n => (s' n : EReal)) atTop (𝓝 L'))
    (hw : Tendsto w atTop (𝓝 0)) (h : ∀ n, s' n ≤ s n + w n) : L' ≤ L := by
  have hw' : Tendsto (fun n => ((w n : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    have := EReal.tendsto_coe.2 hw
    rwa [EReal.coe_zero] at this
  have hsum : Tendsto (fun n => ((s n + w n : ℝ) : EReal)) atTop (𝓝 (L + 0)) := by
    simp only [EReal.coe_add]
    exact (EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp
      (hs.prodMk_nhds hw')
  rw [add_zero] at hsum
  exact le_of_tendsto_of_tendsto hs' hsum (Eventually.of_forall fun n =>
    EReal.coe_le_coe_iff.2 (h n))

/-- The limit step of the sufficiency proofs: if `S*_T → J*`, `w_T → 0` and
`S_T ≤ S*_T + w_T`, then for every `ε > 0`, eventually `S_T ≤ J* + ε`. -/
theorem eu_limsup_le {S Ss w : ℕ → ℝ} {J : ℝ} (hSs : Tendsto Ss atTop (𝓝 J))
    (hw : Tendsto w atTop (𝓝 0)) (h : ∀ T, S T ≤ Ss T + w T) :
    ∀ ε > 0, ∀ᶠ T in atTop, S T ≤ J + ε := by
  intro ε hε
  have hsum : Tendsto (fun T => Ss T + w T) atTop (𝓝 (J + 0)) := hSs.add hw
  rw [add_zero] at hsum
  filter_upwards [(tendsto_order.1 hsum).2 (J + ε) (by linarith)] with T hT
  exact (h T).trans hT.le

/-- **The supergradient inequality on a convex subset of `ℝ²`**: if `h` is concave on `S`,
`p, q ∈ S` and `h` is differentiable at `p`, then
`h(q) ≤ h(p) + (q₁ − p₁) ∂₁h(p) + (q₂ − p₂) ∂₂h(p)`. -/
theorem eu_supergradient {S : Set (ℝ × ℝ)} {h : ℝ × ℝ → ℝ} (hc : ConcaveOn ℝ S h)
    {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S) (hd : DifferentiableAt ℝ h p) :
    h q ≤ h p + (q.1 - p.1) * deriv (fun y => h (y, p.2)) p.1 +
      (q.2 - p.2) * deriv (fun b => h (p.1, b)) p.2 := by
  set L := fderiv ℝ h p
  have hL : HasFDerivAt h L p := hd.hasFDerivAt
  have h1 : deriv (fun y => h (y, p.2)) p.1 = L (1, 0) := by
    have : HasDerivAt (fun y : ℝ => (y, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hL.comp_hasDerivAt p.1 this).deriv
  have h2 : deriv (fun b => h (p.1, b)) p.2 = L (0, 1) := by
    have : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hL.comp_hasDerivAt p.2 this).deriv
  have ht := eu_concave_le_fderiv hc hp hq hL
  have hdec : q - p = (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) + (q.2 - p.2) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at ht
  rw [h1, h2]
  linarith

/-- **Inequality (7.38)** (Miao, p. 224): let `f` be concave on `[0, 1]`. Then for `γ ∈ [0, 1)`
and `λ ∈ [γ, 1)`, `(f(1) − f(λ))/(1 − λ) ≤ (f(1) − f(γ))/(1 − γ)`. The proof is the book's:
with `α = (1 − λ)/(1 − γ) ∈ (0, 1]`, `λ = αγ + (1 − α)·1`, so concavity gives
`f(λ) ≥ αf(γ) + (1 − α)f(1)`. -/
theorem eq_7_38 {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc 0 1) f) {γ lam : ℝ} (hγ0 : 0 ≤ γ)
    (hγl : γ ≤ lam) (hl1 : lam < 1) :
    (f 1 - f lam) / (1 - lam) ≤ (f 1 - f γ) / (1 - γ) := by
  have h1γ : 0 < 1 - γ := by linarith
  have h1l : 0 < 1 - lam := by linarith
  set α := (1 - lam) / (1 - γ) with hα
  have hα0 : 0 ≤ α := div_nonneg h1l.le h1γ.le
  have hα1 : α ≤ 1 := (div_le_one h1γ).2 (by linarith)
  have hcomb : α • γ + (1 - α) • (1 : ℝ) = lam := by
    simp only [smul_eq_mul, mul_one, hα]
    field_simp
    ring
  have hc : α • f γ + (1 - α) • f 1 ≤ f (α • γ + (1 - α) • (1 : ℝ)) :=
    hf.2 (⟨hγ0, by linarith⟩ : γ ∈ Set.Icc (0 : ℝ) 1)
      (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) hα0 (by linarith) (by ring)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hc
  rw [div_le_div_iff₀ h1l h1γ]
  have key : f 1 - f lam ≤ α * (f 1 - f γ) := by nlinarith
  have : α * (1 - γ) = 1 - lam := by rw [hα]; field_simp
  have h2 := mul_le_mul_of_nonneg_right key h1γ.le
  have h3 : α * (f 1 - f γ) * (1 - γ) = (f 1 - f γ) * (1 - lam) := by rw [← this]; ring
  linarith

/-- A continuous linear form on `ℝⁿ × ℝⁿ` in coordinates:
`L(v, w) = Σᵢ vᵢ L(eᵢ, 0) + Σᵢ wᵢ L(0, eᵢ)`. -/
theorem eu_clm_pair {n : ℕ} (L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (v w : Fin n → ℝ) :
    L (v, w) = ∑ i, v i * L (Pi.single i 1, 0) + ∑ i, w i * L (0, Pi.single i 1) := by
  have hv : (v, (0 : Fin n → ℝ)) = ∑ i, v i • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have hw : ((0 : Fin n → ℝ), w) = ∑ i, w i • ((0 : Fin n → ℝ), (Pi.single i 1 : Fin n → ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsplit : (v, w) = (v, (0 : Fin n → ℝ)) + ((0 : Fin n → ℝ), w) := by simp
  rw [hsplit, map_add, hv, hw, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §7.5: the Euler class, Euler equations and transversality conditions

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EUEuler`), namespace renamed.

Miao, §7.5, pp. 221–223. The **Euler class** (7.33): states `x ∈ X ⊆ ℝⁿ` (here `Fin n → ℝ`),
shocks `z ∈ Z` with transition function `Q`, the action is next period's state
`x_{t+1} ∈ Γ(x_t, z_t)`, the reward is `u(x_t, z_t, x_{t+1})` (Assumption 7.3.5, `φ = a`). The
stochastic setting is that of `OCMaxPrinciple`: a filtered probability space with adapted shocks;
a plan `(x_t)` has `x₀` given and `x_{t+1}` `ℱ_t`-measurable.

* `eu_EulerModel`, `uu`, `ux`, `ua`: the primitives and the partial derivatives
  `u_x = (∂u/∂xᵢ)ᵢ`, `u_a = (∂u/∂x′ᵢ)ᵢ` as vectors (components of the Fréchet derivative of
  `(x, x′) ↦ u(x, z, x′)`); `eu_dot` is the inner product `v · w = Σᵢ vᵢwᵢ`.
* `eu_Assumption732`, `eu_Assumption733`, `eu_Assumption734`, `eu_Assumption6411`:
  Assumptions 7.3.2–7.3.4
  and 6.4.11 for the Euler class (`A = X`).
* `IsPlan`, `eu_partialJ`, `IsOptimal`: feasible plans, the partial sums
  `S_T = Σ_{t ≤ T} βᵗ E u(x_t, z_t, x_{t+1})` of (7.33), and optimality: `S_T(x*) → J*` and every
  feasible plan with integrable rewards has `S_T ≤ J* + ε` eventually, for every `ε > 0` (a
  competing plan whose partial sums do not converge, or tend to `−∞`, is covered).
* `foc_7_21`: the first-order condition of the Bellman equation (7.21) at an interior maximiser,
  given the derivative of `y ↦ ∫ V(y, z′) Q(z, dz′)` (differentiation under the integral sign is
  a hypothesis). `euler_functional` (p. 221): with the envelope condition (7.22) it gives the
  **Euler equation in functional form**. `eq_7_34`: along the plan generated by `g`, with the
  Markov property, the **Euler equation in sequence form (7.34)** `IsEuler`.
* `variational_7_5` (p. 222): an optimal `x*_{t+1}` maximises
  `E[u(x*_t, z_t, y) + β u(y, z_{t+1}, x*_{t+2})]` over `ℱ_t`-measurable `y` with
  `y ∈ Γ(x*_t, z_t)`, `x*_{t+2} ∈ Γ(y, z_{t+1})`. `theorem_7_5_1_euler`: hence, for a
  deterministic plan and shocks, the necessity of the Euler equation (the part of Theorem 7.5.1
  that the book "outlined"), with `IsEuler` for the constant processes (`theorem_7_5_1_euler_seq`).
* `eq_7_36` (p. 223): the finite-horizon planner's last-period first-order condition gives
  `u′(c*_T) x*_{T+1} = 0` pathwise, hence `E[βᵀu′(c*_T) x*_{T+1}] = 0` (`eq_7_36_expect`).
* `eq_7_35_iff_7_37` (p. 223): given (7.34),
  `E βᵀ u_a(T) · x_{T+1} = −E β^{T+1} u_x(T + 1) · x_{T+1}`,
  so (7.35) ⇔ (7.37). `eq_7_37_is_7_32`: with `μ_T = V_x(x_T, z_T)` and the envelope condition,
  `E[μ_T · x_T] = E[u_x(x_T, z_T, x_{T+1}) · x_T]`, so (7.37) is (7.32).
* `eu_ux_nonneg`: Assumption 7.3.2 gives `u_x ≥ 0` at interior points, and only that;
  `eu_strictMono_deriv_zero`: a strictly increasing function can have zero derivative. With
  Assumption 7.3.3 (concavity), `u_x > 0` at interior points (`eu_ux_pos`).

**Departures.** The Euler equation in functional form needs the first-order condition at `x` and
the envelope condition at `g(x, z)`; the sequence form needs the Markov property, measurability
and integrability of `u_x` along the plan. The variational characterisation is in expectation
(conditionally on `ℱ_t` only through the choice of `y`); the pathwise first-order condition is
derived for deterministic plans, where it needs feasibility of `y` near `x*_{t+1}` (local
interiority of `(x*_t, x*_{t+1})` and `(x*_{t+1}, x*_{t+2})` in the graph of `Γ`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-- The inner product `v · w = Σᵢ vᵢ wᵢ` on `ℝⁿ`. -/
def eu_dot {n : ℕ} (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

/-- The **Euler class** of Miao §7.5 (7.33) (p. 221; Assumption 7.3.5, `φ(x, a, z, z′) = a`):
the state space `X ⊆ ℝⁿ`, the shock transition function `Q`, the feasibility correspondence `Γ`,
the reward `u(x, z, x′)` and the discount factor `β`. -/
structure eu_EulerModel (n : ℕ) (Z : Type*) [MeasurableSpace Z] where
  X : Set (Fin n → ℝ)
  Q : Kernel Z Z
  Γ : (Fin n → ℝ) → Z → Set (Fin n → ℝ)
  u : (Fin n → ℝ) → Z → (Fin n → ℝ) → ℝ
  β : ℝ

namespace eu_EulerModel

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] (M : eu_EulerModel n Z)

/-- The reward as a function of the pair `(x, x′)`: `uu z (x, x′) = u(x, z, x′)`. -/
def uu (z : Z) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := M.u p.1 z p.2

/-- The partial derivatives `u_x(x, z, x′) = (∂u/∂xᵢ)ᵢ`. -/
noncomputable def ux (x : Fin n → ℝ) (z : Z) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ (M.uu z) (x, y) (Pi.single i 1, 0)

/-- The partial derivatives `u_a(x, z, x′) = (∂u/∂x′ᵢ)ᵢ`. -/
noncomputable def ua (x : Fin n → ℝ) (z : Z) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ (M.uu z) (x, y) (0, Pi.single i 1)

/-- **Assumption 7.3.2** (Miao, p. 208) for the Euler class: `u(·, z, a)` is strictly increasing
on `X` (for the componentwise order). -/
def eu_Assumption732 : Prop := ∀ z a, StrictMonoOn (fun x => M.u x z a) M.X

/-- **Assumption 7.3.3** (Miao, p. 208) for the Euler class: `u(·, z, ·)` is concave on `X × X`,
strictly when the first components differ. -/
def eu_Assumption733 : Prop :=
  ∀ z, ∀ p ∈ M.X ×ˢ M.X, ∀ q ∈ M.X ×ˢ M.X, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    θ * M.uu z p + η * M.uu z q ≤ M.uu z (θ • p + η • q) ∧
    (p.1 ≠ q.1 → θ * M.uu z p + η * M.uu z q < M.uu z (θ • p + η • q))

/-- **Assumption 7.3.4** (Miao, p. 209) for the Euler class: `u(·, z, ·)` is continuously
differentiable on `int(X × X)`. -/
def eu_Assumption734 : Prop := ∀ z, ContDiffOn ℝ 1 (M.uu z) (interior (M.X ×ˢ M.X))

/-- **Assumption 6.4.11** (Miao, p. 176) for the Euler class: the graph of `Γ(·, z)` is convex. -/
def eu_Assumption6411 : Prop :=
  ∀ z, ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.Γ x z, ∀ a' ∈ M.Γ x' z, ∀ θ η : ℝ, 0 < θ → 0 < η →
    θ + η = 1 → θ • a + η • a' ∈ M.Γ (θ • x + η • x') z

/-- Assumption 7.3.3 makes `u(·, z, ·)` concave on `X × X`. -/
theorem concaveOn_of_733 {M : eu_EulerModel n Z} (h : M.eu_Assumption733) (hX : Convex ℝ M.X)
    (z : Z) : ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z) := by
  refine ⟨hX.prod hX, fun p hp q hq a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [add_zero] at hab; subst hab; simp
  simpa [smul_eq_mul] using (h z p hp q hq a b ha' hb' hab).1

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- A **feasible plan** for (7.33) from `x₀`: `x₀` given, `x_{t+1}` `ℱ_t`-measurable,
`x_t ∈ X` and `x_{t+1} ∈ Γ(x_t, z_t)`. -/
def IsPlan (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (x₀ : Fin n → ℝ)
    (x : ℕ → Ω → (Fin n → ℝ)) : Prop :=
  (∀ ω, x 0 ω = x₀) ∧ (∀ t, Measurable[ℱ t] (x (t + 1))) ∧
    ∀ t ω, x t ω ∈ M.X ∧ x (t + 1) ω ∈ M.Γ (x t ω) (z t ω)

/-- The partial sums `S_T = Σ_{t ≤ T} βᵗ E u(x_t, z_t, x_{t+1})` of the objective (7.33). -/
noncomputable def eu_partialJ (P : Measure Ω) (z : ℕ → Ω → Z) (x : ℕ → Ω → (Fin n → ℝ)) (T : ℕ) :
    ℝ :=
  ∑ t ∈ Finset.range (T + 1), M.β ^ t * ∫ ω, M.u (x t ω) (z t ω) (x (t + 1) ω) ∂P

/-- **Optimality** for (7.33) with value `J*`: `x*` is a feasible plan with integrable rewards,
`S_T(x*) → J*`, and for every feasible plan with integrable rewards and every `ε > 0`,
eventually `S_T ≤ J* + ε`. -/
def IsOptimal (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (x₀ : Fin n → ℝ)
    (xs : ℕ → Ω → (Fin n → ℝ)) (J : ℝ) : Prop :=
  M.IsPlan ℱ z x₀ xs ∧ (∀ t, Integrable (fun ω => M.u (xs t ω) (z t ω) (xs (t + 1) ω)) P) ∧
    Tendsto (M.eu_partialJ P z xs) atTop (𝓝 J) ∧
    ∀ x, M.IsPlan ℱ z x₀ x → (∀ t, Integrable (fun ω => M.u (x t ω) (z t ω) (x (t + 1) ω)) P) →
      ∀ ε > 0, ∀ᶠ T in atTop, M.eu_partialJ P z x T ≤ J + ε

/-- **The Euler equation in sequence form (7.34)** (Miao, p. 222), almost surely:
`u_a(x_t, z_t, x_{t+1}) + β E_t u_x(x_{t+1}, z_{t+1}, x_{t+2}) = 0`, componentwise. -/
def IsEuler (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z)
    (xs : ℕ → Ω → (Fin n → ℝ)) : Prop :=
  ∀ t i, (fun ω => M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i + M.β *
    (P[fun ω' => M.ux (xs (t + 1) ω') (z (t + 1) ω') (xs (t + 2) ω') i | ℱ t]) ω) =ᵐ[P] 0

/-- **The transversality condition (7.35)** (Miao, p. 222):
`lim_T E[βᵀ u_a(x_T, z_T, x_{T+1}) · x_{T+1}] = 0`. -/
def TVC735 (P : Measure Ω) (z : ℕ → Ω → Z) (xs : ℕ → Ω → (Fin n → ℝ)) : Prop :=
  Tendsto (fun T => M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P)
    atTop (𝓝 0)

/-- **The transversality condition (7.37)** (Miao, p. 223):
`lim_T E[βᵀ u_x(x_T, z_T, x_{T+1}) · x_T] = 0`. -/
def TVC737 (P : Measure Ω) (z : ℕ → Ω → Z) (xs : ℕ → Ω → (Fin n → ℝ)) : Prop :=
  Tendsto (fun T => M.β ^ T * ∫ ω, eu_dot (M.ux (xs T ω) (z T ω) (xs (T + 1) ω)) (xs T ω) ∂P)
    atTop (𝓝 0)

/-! ### The Euler equation from the Bellman equation (7.21) -/

/-- **The first-order condition of (7.21)** (Miao, p. 221): if `g ∈ int Γ(x, z)` maximises
`y ↦ u(x, z, y) + β ∫ V(y, z′) Q(z, dz′)` over `Γ(x, z)`, `u(x, z, ·)` is differentiable at
`(x, g)` and `y ↦ ∫ V(y, z′) Q(z, dz′)` has derivative `DV` at `g` with
`DV(eᵢ) = ∫ ∂V(g, z′)/∂yᵢ Q(z, dz′)` (differentiation under the integral sign), then
`u_a(x, z, g) + β ∫ V_x(g, z′) Q(z, dz′) = 0` componentwise. -/
theorem foc_7_21 (V : (Fin n → ℝ) → Z → ℝ) {x g : Fin n → ℝ} {z : Z} (hg : g ∈ interior (M.Γ x z))
    (hmax : ∀ y ∈ M.Γ x z, M.u x z y + M.β * ∫ z', V y z' ∂M.Q z ≤
      M.u x z g + M.β * ∫ z', V g z' ∂M.Q z)
    (hu : DifferentiableAt ℝ (M.uu z) (x, g)) {DV : (Fin n → ℝ) →L[ℝ] ℝ}
    (hV : HasFDerivAt (fun y => ∫ z', V y z' ∂M.Q z) DV g)
    (hDV : ∀ i, DV (Pi.single i 1) = ∫ z', fderiv ℝ (fun y => V y z') g (Pi.single i 1) ∂M.Q z)
    (i : Fin n) :
    M.ua x z g i + M.β * ∫ z', fderiv ℝ (fun y => V y z') g (Pi.single i 1) ∂M.Q z = 0 := by
  have hline : HasFDerivAt (fun y : Fin n → ℝ => (x, y))
      ((0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ _)) g :=
    (hasFDerivAt_const x g).prodMk (hasFDerivAt_id g)
  have hU := hu.hasFDerivAt.comp g hline
  have hW := hU.add (hV.const_mul M.β)
  have hmaxl : IsLocalMax (fun y => M.uu z (x, y) + M.β * ∫ z', V y z' ∂M.Q z) g := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hg] with y hy
    exact hmax y hy
  have h0 := hmaxl.hasFDerivAt_eq_zero hW
  have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h0
  rw [← hDV i]
  simpa [ua] using this

/-- **The Euler equation in functional form** (Miao, p. 221): the first-order condition at
`(x, z)` and the envelope condition (7.22) `V_x(g(x, z), z′) = u_x(g(x, z), z′, g(g(x, z), z′))`
give `u_a(x, z, g(x, z)) + β ∫ u_x(g(x, z), z′, g(g(x, z), z′)) Q(z, dz′) = 0`. -/
theorem euler_functional (Vx : (Fin n → ℝ) → Z → (Fin n → ℝ)) (g : (Fin n → ℝ) → Z → (Fin n → ℝ))
    {x : Fin n → ℝ} {z : Z}
    (hfoc : ∀ i, M.ua x z (g x z) i + M.β * ∫ z', Vx (g x z) z' i ∂M.Q z = 0)
    (henv : ∀ z', Vx (g x z) z' = M.ux (g x z) z' (g (g x z) z')) (i : Fin n) :
    M.ua x z (g x z) i + M.β * ∫ z', M.ux (g x z) z' (g (g x z) z') i ∂M.Q z = 0 := by
  have := hfoc i
  simp only [henv] at this
  exact this

/-- The Markov property in the form used to evaluate `E_t` of a function of
`(Y, z_t, z_{t+1})` with `Y` `ℱ_t`-measurable (as `OCModel.IsMarkovCond`, for vector states). -/
def EulerMarkov (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (Q : Kernel Z Z) : Prop :=
  ∀ t (G : (Fin n → ℝ) × Z × Z → ℝ), Measurable G → ∀ Y : Ω → (Fin n → ℝ), Measurable[ℱ t] Y →
    Integrable (fun ω => G (Y ω, z t ω, z (t + 1) ω)) P →
    P[fun ω => G (Y ω, z t ω, z (t + 1) ω) | ℱ t] =ᵐ[P] fun ω => ∫ z', G (Y ω, z t ω, z') ∂Q (z t ω)

/-- **The Euler equation in sequence form (7.34)** (Miao, p. 222): along the plan generated by
the policy function `g` (`x_{t+1} = g(x_t, z_t)`), the functional Euler equation and the Markov
property give (7.34), given measurability and integrability of `u_x` along the plan. -/
theorem eq_7_34 {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}
    (hM : EulerMarkov (n := n) P ℱ z M.Q) (g : (Fin n → ℝ) → Z → (Fin n → ℝ))
    {xs : ℕ → Ω → (Fin n → ℝ)}
    (hgen : ∀ t ω, xs (t + 1) ω = g (xs t ω) (z t ω)) (hxs : ∀ t, Measurable[ℱ t] (xs t))
    (hfun : ∀ t ω i, M.ua (xs t ω) (z t ω) (g (xs t ω) (z t ω)) i + M.β *
      ∫ z', M.ux (g (xs t ω) (z t ω)) z' (g (g (xs t ω) (z t ω)) z') i ∂M.Q (z t ω) = 0)
    (hG : ∀ i, Measurable fun p : (Fin n → ℝ) × Z × Z =>
      M.ux (g p.1 p.2.1) p.2.2 (g (g p.1 p.2.1) p.2.2) i)
    (hI : ∀ t i, Integrable (fun ω => M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i) P) :
    M.IsEuler P ℱ z xs := by
  intro t i
  have heq : (fun ω => M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i) = fun ω =>
      M.ux (g (xs t ω) (z t ω)) (z (t + 1) ω) (g (g (xs t ω) (z t ω)) (z (t + 1) ω)) i := by
    funext ω
    rw [hgen (t + 1) ω, hgen t ω]
  have hI' := hI t i
  rw [heq] at hI'
  have hc := hM t _ (hG i) (xs t) (hxs t) hI'
  filter_upwards [hc] with ω hω
  rw [heq, hω, hgen t ω]
  exact hfun t ω i

/-! ### The variational characterisation (p. 222) and the necessity of the Euler equation -/

variable {M}

/-- **The variational characterisation** (Miao, p. 222): if `x*` is optimal, then for every
`ℱ_t`-measurable `y` with `y ∈ X`, `y ∈ Γ(x*_t, z_t)` and `x*_{t+2} ∈ Γ(y, z_{t+1})` (and the
two rewards integrable), `E[u(x*_t, z_t, y) + β u(y, z_{t+1}, x*_{t+2})]` is at most its value at
`y = x*_{t+1}`: a variation of `x*_{t+1}` alone does not raise the expected reward. -/
theorem variational_7_5 {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}
    {z : ℕ → Ω → Z} (hβ : 0 < M.β) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (t : ℕ) (Y : Ω → (Fin n → ℝ)) (hY : Measurable[ℱ t] Y)
    (hYΓ : ∀ ω, Y ω ∈ M.Γ (xs t ω) (z t ω)) (hYX : ∀ ω, Y ω ∈ M.X)
    (hY2 : ∀ ω, xs (t + 2) ω ∈ M.Γ (Y ω) (z (t + 1) ω))
    (hi1 : Integrable (fun ω => M.u (xs t ω) (z t ω) (Y ω)) P)
    (hi2 : Integrable (fun ω => M.u (Y ω) (z (t + 1) ω) (xs (t + 2) ω)) P) :
    ∫ ω, (M.u (xs t ω) (z t ω) (Y ω) + M.β * M.u (Y ω) (z (t + 1) ω) (xs (t + 2) ω)) ∂P ≤
      ∫ ω, (M.u (xs t ω) (z t ω) (xs (t + 1) ω) +
        M.β * M.u (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω)) ∂P := by
  obtain ⟨hplan, hint, hJ, hcmp⟩ := hopt
  set x' : ℕ → Ω → (Fin n → ℝ) := fun s => if s = t + 1 then Y else xs s with hx'
  have hx't : x' t = xs t := by simp [x']
  have hx't1 : x' (t + 1) = Y := by simp [x']
  have hx't2 : x' (t + 2) = xs (t + 2) := by simp [x']
  have hx'o : ∀ s, s ≠ t + 1 → x' s = xs s := fun s hs => by simp [x', hs]
  -- the modified plan is feasible
  have hplan' : M.IsPlan ℱ z x₀ x' := by
    refine ⟨fun ω => by rw [hx'o 0 (by omega)]; exact hplan.1 ω, fun s => ?_, fun s ω => ?_⟩
    · by_cases hs : s + 1 = t + 1
      · have : s = t := by omega
        subst this; rw [hx't1]; exact hY
      · rw [hx'o _ hs]; exact hplan.2.1 s
    · by_cases hs : s = t
      · subst hs; rw [hx't, hx't1]; exact ⟨(hplan.2.2 s ω).1, hYΓ ω⟩
      by_cases hs1 : s = t + 1
      · subst hs1; rw [hx't1, hx't2]; exact ⟨hYX ω, hY2 ω⟩
      rw [hx'o s hs1, hx'o (s + 1) (by omega)]
      exact hplan.2.2 s ω
  -- the rewards of the modified plan
  set r : ℕ → ℝ := fun s => ∫ ω, M.u (xs s ω) (z s ω) (xs (s + 1) ω) ∂P with hr
  set A := (∫ ω, M.u (xs t ω) (z t ω) (Y ω) ∂P) - r t with hA
  set B := (∫ ω, M.u (Y ω) (z (t + 1) ω) (xs (t + 2) ω) ∂P) - r (t + 1) with hB
  have hterm : ∀ s, M.β ^ s * ∫ ω, M.u (x' s ω) (z s ω) (x' (s + 1) ω) ∂P =
      M.β ^ s * r s + ((if s = t then M.β ^ t * A else 0) +
        (if s = t + 1 then M.β ^ (t + 1) * B else 0)) := by
    intro s
    by_cases hs : s = t
    · subst hs; rw [hx't, hx't1]; simp [A]; ring
    by_cases hs1 : s = t + 1
    · subst hs1; rw [hx't1, hx't2]; simp [B]; ring
    rw [hx'o s hs1, hx'o (s + 1) (by omega)]
    simp [hs, hs1, r]
  have hint' : ∀ s, Integrable (fun ω => M.u (x' s ω) (z s ω) (x' (s + 1) ω)) P := by
    intro s
    by_cases hs : s = t
    · subst hs; rw [hx't, hx't1]; exact hi1
    by_cases hs1 : s = t + 1
    · subst hs1; rw [hx't1, hx't2]; exact hi2
    rw [hx'o s hs1, hx'o (s + 1) (by omega)]
    exact hint s
  have hsum : ∀ N, t + 1 ≤ N → M.eu_partialJ P z x' N =
      M.eu_partialJ P z xs N + (M.β ^ t * A + M.β ^ (t + 1) * B) := by
    intro N hN
    simp only [eu_partialJ]
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range (N + 1)) t, Finset.sum_ite_eq' (Finset.range (N + 1))]
    have h1 : t ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    have h2 : t + 1 ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    simp [h1, h2, r]
  -- `β^t A + β^{t+1} B ≤ 0`
  have hc : M.β ^ t * A + M.β ^ (t + 1) * B ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev := hcmp x' hplan' hint' ε hε
    have hlim : Tendsto (fun N => M.eu_partialJ P z xs N + (M.β ^ t * A + M.β ^ (t + 1) * B))
        atTop (𝓝 (J + (M.β ^ t * A + M.β ^ (t + 1) * B))) := hJ.add_const _
    have hle : J + (M.β ^ t * A + M.β ^ (t + 1) * B) ≤ J + ε := by
      refine le_of_tendsto hlim ?_
      filter_upwards [hev, eventually_ge_atTop (t + 1)] with N hN hN1
      rw [← hsum N hN1]; exact hN
    linarith
  have hβt : 0 < M.β ^ t := pow_pos hβ t
  have hAB : A + M.β * B ≤ 0 := by
    have e : M.β ^ t * A + M.β ^ (t + 1) * B = M.β ^ t * (A + M.β * B) := by ring
    rw [e] at hc
    by_contra hcon
    push Not at hcon
    linarith [mul_pos hβt hcon]
  rw [integral_add hi1 (hi2.const_mul _), integral_add (hint t) ((hint (t + 1)).const_mul _),
    integral_const_mul, integral_const_mul]
  have e2 : t + 1 + 1 = t + 2 := rfl
  simp only [hA, hB, hr, e2] at hAB
  linarith

/-- **Theorem 7.5.1, necessity of the Euler equation** (Miao, pp. 222, 224), for a deterministic
plan and shocks (`z_t = ζ_t`, `x*_t = ξ_t`). If `x*` is optimal, `β > 0`, every `y` near `ξ_{t+1}`
is a feasible variation (`y ∈ X`, `y ∈ Γ(ξ_t, ζ_t)`, `ξ_{t+2} ∈ Γ(y, ζ_{t+1})`) and `u` is
differentiable at `(ξ_t, ξ_{t+1})` and `(ξ_{t+1}, ξ_{t+2})`, then
`u_a(ξ_t, ζ_t, ξ_{t+1}) + β u_x(ξ_{t+1}, ζ_{t+1}, ξ_{t+2}) = 0`. -/
theorem theorem_7_5_1_euler {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}
    {z : ℕ → Ω → Z} (hβ : 0 < M.β) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (ζ : ℕ → Z) (ξ : ℕ → Fin n → ℝ)
    (hz : ∀ t ω, z t ω = ζ t) (hx : ∀ t ω, xs t ω = ξ t) (t : ℕ)
    (hloc : ∀ᶠ y in 𝓝 (ξ (t + 1)), y ∈ M.X ∧ y ∈ M.Γ (ξ t) (ζ t) ∧ ξ (t + 2) ∈ M.Γ y (ζ (t + 1)))
    (hd1 : DifferentiableAt ℝ (M.uu (ζ t)) (ξ t, ξ (t + 1)))
    (hd2 : DifferentiableAt ℝ (M.uu (ζ (t + 1))) (ξ (t + 1), ξ (t + 2))) (i : Fin n) :
    M.ua (ξ t) (ζ t) (ξ (t + 1)) i + M.β * M.ux (ξ (t + 1)) (ζ (t + 1)) (ξ (t + 2)) i = 0 := by
  set W : (Fin n → ℝ) → ℝ := fun y => M.uu (ζ t) (ξ t, y) + M.β * M.uu (ζ (t + 1)) (y, ξ (t + 2))
  have hmax : IsLocalMax W (ξ (t + 1)) := by
    filter_upwards [hloc] with y hy
    have h := variational_7_5 hβ hopt t (fun _ => y) measurable_const (fun ω => by
      rw [hx, hz]; exact hy.2.1) (fun _ => hy.1) (fun ω => by rw [hx, hz]; exact hy.2.2)
      (by simp only [hx, hz]; exact integrable_const _)
      (by simp only [hx, hz]; exact integrable_const _)
    simp only [hx, hz, integral_const, probReal_univ, one_smul] at h
    exact h
  have hl1 : HasFDerivAt (fun y : Fin n → ℝ => (ξ t, y))
      ((0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ _)) (ξ (t + 1)) :=
    (hasFDerivAt_const (ξ t) _).prodMk (hasFDerivAt_id _)
  have hl2 : HasFDerivAt (fun y : Fin n → ℝ => (y, ξ (t + 2)))
      ((ContinuousLinearMap.id ℝ _).prod (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (ξ (t + 1)) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const (ξ (t + 2)) _)
  have hW := (hd1.hasFDerivAt.comp (ξ (t + 1)) hl1).add
    ((hd2.hasFDerivAt.comp (ξ (t + 1)) hl2).const_mul M.β)
  have h0 := hmax.hasFDerivAt_eq_zero hW
  have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h0
  simpa [ua, ux] using this

/-- **Theorem 7.5.1, necessity of (7.34)** for a deterministic plan and shocks: under the
hypotheses of `theorem_7_5_1_euler` at every date, the constant processes satisfy the Euler
equation in sequence form (7.34). -/
theorem theorem_7_5_1_euler_seq {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0}
    {z : ℕ → Ω → Z} (hβ : 0 < M.β) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (ζ : ℕ → Z) (ξ : ℕ → Fin n → ℝ)
    (hz : ∀ t ω, z t ω = ζ t) (hx : ∀ t ω, xs t ω = ξ t)
    (hloc : ∀ t, ∀ᶠ y in 𝓝 (ξ (t + 1)),
      y ∈ M.X ∧ y ∈ M.Γ (ξ t) (ζ t) ∧ ξ (t + 2) ∈ M.Γ y (ζ (t + 1)))
    (hd : ∀ t, DifferentiableAt ℝ (M.uu (ζ t)) (ξ t, ξ (t + 1))) : M.IsEuler P ℱ z xs := by
  intro t i
  refine Eventually.of_forall fun ω => ?_
  simp only [hx, hz, Pi.zero_apply]
  rw [condExp_const (ℱ.le t)]
  exact theorem_7_5_1_euler hβ hopt ζ ξ hz hx t (hloc t) (hd t) (hd (t + 1)) i

/-! ### The finite-horizon planner (7.36) and the forms (7.35), (7.37) -/

/-- **(7.36), pathwise** (Miao, p. 223): in the last period the planner maximises
`u(w − y)` over `y ∈ [0, w]` (`w = z_T F(x_T)`, `c = w − y ≥ 0`); if the maximiser
`x*_{T+1} ∈ [0, w)` and `u` has derivative `u′` at `c*_T = w − x*_{T+1}`, then
`u′(c*_T) x*_{T+1} = 0`: `x*_{T+1} > 0` forces `u′(c*_T) = 0`. -/
theorem eq_7_36 {u : ℝ → ℝ} {w ys u' : ℝ} (hys : ys ∈ Set.Ico 0 w)
    (hmax : ∀ y ∈ Set.Icc 0 w, u (w - y) ≤ u (w - ys)) (hd : HasDerivAt u u' (w - ys)) :
    u' * ys = 0 := by
  rcases hys.1.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
  have hloc : IsLocalMax (fun y => u (w - y)) ys := by
    filter_upwards [Ioo_mem_nhds hpos hys.2] with y hy
    exact hmax y ⟨hy.1.le, hy.2.le⟩
  have h1 : HasDerivAt (fun y : ℝ => w - y) (-1) ys := by
    simpa using (hasDerivAt_id ys).const_sub w
  have hd' : HasDerivAt (fun y => u (w - y)) (-u') ys := (hd.comp ys h1).congr_deriv (by ring)
  have := hloc.hasDerivAt_eq_zero hd'
  have hu : u' = 0 := by linarith
  rw [hu, zero_mul]

/-- **(7.36)** (Miao, p. 223): if in every state the last-period choice `x*_{T+1}` solves the
planner's problem `max_{y ∈ [0, w]} u(w − y)`, then `E[βᵀ u′(c*_T) x*_{T+1}] = 0`; and if
`u′ ≥ 0`, `E[βᵀ u′(c*_T)] ≥ 0` (for `β ≥ 0`). -/
theorem eq_7_36_expect {P : Measure Ω} {u : ℝ → ℝ} {β : ℝ} (T : ℕ) {w xT u' : Ω → ℝ}
    (hys : ∀ ω, xT ω ∈ Set.Ico 0 (w ω))
    (hmax : ∀ ω, ∀ y ∈ Set.Icc 0 (w ω), u (w ω - y) ≤ u (w ω - xT ω))
    (hd : ∀ ω, HasDerivAt u (u' ω) (w ω - xT ω)) :
    ∫ ω, β ^ T * (u' ω * xT ω) ∂P = 0 ∧
      ((∀ ω, 0 ≤ u' ω) → 0 ≤ β → 0 ≤ ∫ ω, β ^ T * u' ω ∂P) := by
  refine ⟨?_, fun hu hβ => integral_nonneg fun ω => mul_nonneg (pow_nonneg hβ T) (hu ω)⟩
  have : ∀ ω, β ^ T * (u' ω * xT ω) = 0 := fun ω => by
    rw [eq_7_36 (hys ω) (hmax ω) (hd ω), mul_zero]
  simp [this]

/-- **(7.35) ⇔ (7.37)** (Miao, p. 223): given the Euler equation (7.34), with `x_{T+1}`
`ℱ_T`-measurable and `u_x(T + 1)` and `u_x(T + 1) · x_{T+1}` integrable,
`E[βᵀ u_a(x_T, z_T, x_{T+1}) · x_{T+1}] = −E[β^{T+1} u_x(x_{T+1}, z_{T+1}, x_{T+2}) · x_{T+1}]`
for every `T`, so the transversality conditions (7.35) and (7.37) are equivalent. -/
theorem eq_7_35_iff_7_37 {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℕ m0}
    {z : ℕ → Ω → Z} {xs : ℕ → Ω → (Fin n → ℝ)} (heuler : M.IsEuler P ℱ z xs)
    (hxs : ∀ t, Measurable[ℱ t] (xs (t + 1)))
    (hI1 : ∀ T i, Integrable (fun ω => M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i) P)
    (hI2 : ∀ T i, Integrable (fun ω => xs (T + 1) ω i *
      M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i) P) :
    (∀ T, M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P =
      -(M.β ^ (T + 1) * ∫ ω, eu_dot (M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 1 + 1) ω))
        (xs (T + 1) ω) ∂P)) ∧ (M.TVC735 P z xs ↔ M.TVC737 P z xs) := by
  have hid : ∀ T, M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P =
      -(M.β ^ (T + 1) * ∫ ω, eu_dot (M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 1 + 1) ω))
        (xs (T + 1) ω) ∂P) := by
    intro T
    -- coordinatewise: `E[u_a,i x_i] = −β E[x_i u_x,i]`
    have hco : ∀ i, Integrable (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i *
        xs (T + 1) ω i) P ∧ ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P =
        -(M.β * ∫ ω, xs (T + 1) ω i * M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i ∂P) := by
      intro i
      have hΔ : StronglyMeasurable[ℱ T] fun ω => xs (T + 1) ω i :=
        ((measurable_pi_apply i).comp (hxs T)).stronglyMeasurable
      obtain ⟨hint, heq⟩ := OCModel.oc_integral_mul_condExp hΔ (hI2 T i) (hI1 T i)
      have hae : (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i) =ᵐ[P]
          fun ω => -M.β * (xs (T + 1) ω i * (P[fun ω' => M.ux (xs (T + 1) ω') (z (T + 1) ω')
            (xs (T + 2) ω') i | ℱ T]) ω) := by
        filter_upwards [heuler T i] with ω hω
        simp only [Pi.zero_apply] at hω
        have : M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i = -(M.β * (P[fun ω' => M.ux (xs (T + 1) ω')
            (z (T + 1) ω') (xs (T + 2) ω') i | ℱ T]) ω) := by linarith
        rw [this]; ring
      refine ⟨(hint.const_mul (-M.β)).congr hae.symm, ?_⟩
      rw [integral_congr_ae hae, integral_const_mul, ← heq]
      ring
    have hsum : ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P =
        ∑ i, ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P := by
      simp only [eu_dot]
      exact integral_finsetSum _ fun i _ => (hco i).1
    have hsum2 : ∫ ω, eu_dot (M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 1 + 1) ω))
        (xs (T + 1) ω) ∂P =
        ∑ i, ∫ ω, xs (T + 1) ω i * M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i ∂P := by
      simp only [eu_dot]
      rw [integral_finsetSum _ fun i _ => ?_]
      · exact Finset.sum_congr rfl fun i _ => integral_congr_ae
          (Eventually.of_forall fun ω => mul_comm _ _)
      · exact (hI2 T i).congr (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsum, hsum2, Finset.sum_congr rfl fun i _ => (hco i).2, Finset.sum_neg_distrib,
      ← Finset.mul_sum, pow_succ]
    ring
  refine ⟨hid, ?_⟩
  set f := fun T => M.β ^ T * ∫ ω, eu_dot (M.ux (xs T ω) (z T ω) (xs (T + 1) ω)) (xs T ω) ∂P
  have hf : (fun T => M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω))
      (xs (T + 1) ω) ∂P) = fun T => -f (T + 1) := funext hid
  simp only [TVC735, TVC737]
  rw [hf]
  constructor
  · intro h
    have h' := h.neg
    simp only [neg_neg, neg_zero] at h'
    exact (tendsto_add_atTop_iff_nat 1).1 h'
  · intro h
    have := ((tendsto_add_atTop_iff_nat 1).2 h).neg
    simpa using this

/-- **(7.37) is (7.32)** (Miao, p. 223): if `μ_T = V_x(x_T, z_T)` and the envelope condition
(7.22) `V_x(x, z) = u_x(x, z, g(x, z))` holds, along the plan generated by `g`
`E[μ_T · x_T] = E[u_x(x_T, z_T, x_{T+1}) · x_T]`, so (7.37) is the transversality condition
(7.32) for the multiplier `μ_T = V_x`. -/
theorem eq_7_37_is_7_32 {P : Measure Ω} {z : ℕ → Ω → Z} {xs : ℕ → Ω → (Fin n → ℝ)}
    (g : (Fin n → ℝ) → Z → (Fin n → ℝ)) (Vx : (Fin n → ℝ) → Z → (Fin n → ℝ))
    {μ : ℕ → Ω → (Fin n → ℝ)} (hμ : ∀ T ω, μ T ω = Vx (xs T ω) (z T ω))
    (henv : ∀ x z', Vx x z' = M.ux x z' (g x z'))
    (hgen : ∀ t ω, xs (t + 1) ω = g (xs t ω) (z t ω)) :
    (∀ T, ∫ ω, eu_dot (μ T ω) (xs T ω) ∂P =
      ∫ ω, eu_dot (M.ux (xs T ω) (z T ω) (xs (T + 1) ω)) (xs T ω) ∂P) ∧
    (Tendsto (fun T => M.β ^ T * ∫ ω, eu_dot (μ T ω) (xs T ω) ∂P) atTop (𝓝 0) ↔
      M.TVC737 P z xs) := by
  have h : ∀ T, ∫ ω, eu_dot (μ T ω) (xs T ω) ∂P =
      ∫ ω, eu_dot (M.ux (xs T ω) (z T ω) (xs (T + 1) ω)) (xs T ω) ∂P := fun T => by
    congr 1
    funext ω
    rw [hμ, henv, hgen]
  refine ⟨h, ?_⟩
  simp only [TVC737, h]

/-! ### The sign of `u_x` -/

/-- **Assumption 7.3.2 gives `u_x ≥ 0`** at interior points (Miao, p. 226): if `u(·, z, y)` is
increasing on `X`, `x ∈ int X` and `u(·, z, ·)` is differentiable at `(x, y)`, then
`∂u(x, z, y)/∂xᵢ ≥ 0`. -/
theorem eu_ux_nonneg {z : Z} {x y : Fin n → ℝ} (hmono : MonotoneOn (fun x' => M.u x' z y) M.X)
    (hx : x ∈ interior M.X) (hd : DifferentiableAt ℝ (M.uu z) (x, y)) (i : Fin n) :
    0 ≤ M.ux x z y i := by
  set e : Fin n → ℝ := Pi.single i 1
  set h : ℝ → ℝ := fun s => M.uu z (x + s • e, y)
  have hline : HasDerivAt (fun s : ℝ => (x + s • e, y)) (e, (0 : Fin n → ℝ)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    exact h1.prodMk (hasDerivAt_const 0 y)
  have hd' : HasFDerivAt (M.uu z) (fderiv ℝ (M.uu z) (x, y)) (x + (0 : ℝ) • e, y) := by
    simpa using hd.hasFDerivAt
  have hh : HasDerivAt h (M.ux x z y i) 0 := by exact hd'.comp_hasDerivAt 0 hline
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • e ∈ M.X := by
    have hc : Continuous fun s : ℝ => x + s • e := by fun_prop
    have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (by
      simpa using mem_interior_iff_mem_nhds.1 hx)
    exact this
  refine ge_of_tendsto hh.tendsto_slope_zero_right ?_
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with s hs hpos
  have hpos' : (0 : ℝ) < s := hpos
  have hle : x ≤ x + s • e := fun j => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
    have : 0 ≤ (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simp [hj]
    nlinarith
  have hx0 : x ∈ M.X := interior_subset hx
  have hmon := hmono hx0 hs hle
  simp only [zero_add, smul_eq_mul]
  have : h s - h 0 ≥ 0 := by
    simp only [h, uu, zero_smul, add_zero]
    linarith
  positivity

/-- **A strictly increasing function can have zero derivative** (Miao, p. 226): `x ↦ x³` is
strictly increasing with derivative `0` at `0`, so Assumption 7.3.2 alone does not give a strict
sign for `u_x` (and hence for `u_a`). -/
theorem eu_strictMono_deriv_zero :
    StrictMono (fun x : ℝ => x ^ 3) ∧ deriv (fun x : ℝ => x ^ 3) 0 = 0 := by
  refine ⟨Odd.strictMono_pow (by decide), ?_⟩
  simp

/-- **With concavity, `u_x > 0`** at interior points (Miao, p. 226): if `u(·, z, ·)` is concave on
`X × X` and `u(·, z, y)` strictly increasing on `X`, `x ∈ int X`, `y ∈ X` and `u(·, z, ·)` is
differentiable at `(x, y)`, then `∂u(x, z, y)/∂xᵢ > 0`. (So in the deterministic case the
Euler equation gives `u_a < 0` when `β > 0`, as the book claims; only `u_a ≤ 0` is needed.) -/
theorem eu_ux_pos {z : Z} {x y : Fin n → ℝ} (hcon : ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z))
    (hsm : StrictMonoOn (fun x' => M.u x' z y) M.X) (hx : x ∈ interior M.X) (hy : y ∈ M.X)
    (hd : DifferentiableAt ℝ (M.uu z) (x, y)) (i : Fin n) : 0 < M.ux x z y i := by
  have hnn := eu_ux_nonneg hsm.monotoneOn hx hd i
  refine lt_of_le_of_ne hnn fun h0 => ?_
  set e : Fin n → ℝ := Pi.single i 1
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • e ∈ M.X := by
    have hc : Continuous fun s : ℝ => x + s • e := by fun_prop
    exact hc.continuousAt (x := 0) |>.preimage_mem_nhds (by
      simpa using mem_interior_iff_mem_nhds.1 hx)
  have hnear' : ∀ᶠ s in 𝓝[>] (0 : ℝ), x + s • e ∈ M.X := nhdsWithin_le_nhds hnear
  obtain ⟨s, hs, hpos⟩ := (hnear'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hpos' : (0 : ℝ) < s := hpos
  have hx0 : x ∈ M.X := interior_subset hx
  have htan := eu_concave_le_fderiv hcon (⟨hx0, hy⟩ : (x, y) ∈ M.X ×ˢ M.X)
    (⟨hs, hy⟩ : (x + s • e, y) ∈ M.X ×ˢ M.X) hd.hasFDerivAt
  have hdiff : (x + s • e, y) - (x, y) = s • (e, (0 : Fin n → ℝ)) := by
    ext j <;> simp
  rw [hdiff, map_smul, smul_eq_mul] at htan
  have hux : fderiv ℝ (M.uu z) (x, y) (e, 0) = 0 := h0.symm
  rw [hux, mul_zero, add_zero] at htan
  have hlt : x < x + s • e := by
    refine lt_of_le_of_ne (fun j => ?_) fun heq => ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
      have : 0 ≤ (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
        rcases eq_or_ne j i with rfl | hj
        · simp
        · simp [hj]
      nlinarith
    · have := congrFun heq i
      simp [e] at this
      linarith
  have := hsm hx0 hs hlt
  simp only [uu] at htan
  linarith

end eu_EulerModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §7.5: Theorem 7.5.2, sufficiency of the Euler and transversality conditions

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EUEulerSufficiency`), namespace renamed.

Miao, §7.5, pp. 226–227, in the Euler class `eu_EulerModel` with `X ⊆ ℝⁿ₊`.

* `eu_euler_sufficient`: the proof of Theorem 7.5.2 under minimal hypotheses. Let `x*` be a
  feasible plan satisfying the Euler equation (7.34) and the transversality condition (7.35), with
  `u(·, z_t, ·)` concave on a set containing `(x*_t, x*_{t+1})` and `(x_t, x_{t+1})` and
  differentiable at `(x*_t, x*_{t+1})`, `u_x ≥ 0` along `x*`, and `x ≥ 0`. Then
  `S_T(x) ≤ S_T(x*) + w_T` with `w_T = −E βᵀ u_a(x*_T, z_T, x*_{T+1}) · x*_{T+1} → 0`.
* **Theorem 7.5.2** (`theorem_7_5_2`): the book's hypotheses (Assumptions 7.3.2–7.3.4, interior
  plan, `X ⊆ ℝⁿ₊` convex) imply those of `eu_euler_sufficient`; `theorem_7_5_2_limit`: the limit
  step in `[−∞, +∞]`; `theorem_7_5_2_eventually`: optimality in the sense of `IsOptimal`.

**Corrections.** (1) "By Assumption 7.3.2 and the Euler equation, we deduce that `u_a < 0`":
strict monotonicity gives only `u_x ≥ 0` (`eu_ux_nonneg`; `eu_strictMono_deriv_zero`), hence
`u_a = −β E_t u_x ≤ 0` almost surely, which is all the proof needs (with `x_{T+1} ≥ 0`). With
concavity, `u_x > 0` at interior points (`eu_ux_pos`), so the strict sign holds in the
deterministic case. (2) The displayed identity has two misprints: the sum of the Euler terms runs
to `T − 1`, not `T` (the date-`T` term is the boundary term written separately), and `u_x` carries
the factor `β`: `Σ_{t<T} βᵗ (u_a(t) + β u_x(t + 1)) · (x*_{t+1} − x_{t+1})`. (3) The proof uses the
derivative of `u` at `(x*_0, x*_1)`, so `x₀ ∈ int X` is needed (the hypothesis
`x*_{t+1} ∈ int Γ(x*_t, z_t)` covers only `t ≥ 1`); and `Γ ⊆ X`. (4) Integrability of the rewards
and of the products in the telescoping is assumed (`EulerInt`). (5) Only concavity, not the strict
part of Assumption 7.3.3, and only `β ≥ 0` are used; Assumption 6.4.3 is not used.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace eu_EulerModel

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}

variable (P : Measure Ω) (z : ℕ → Ω → Z) (M : eu_EulerModel n Z) (xs x : ℕ → Ω → (Fin n → ℝ)) in
/-- The integrability used in the proof of Theorem 7.5.2, for the candidate `xs` and a competing
plan `x`, at every date and coordinate. -/
structure EulerInt : Prop where
  r_s : ∀ t, Integrable (fun ω => M.u (xs t ω) (z t ω) (xs (t + 1) ω)) P
  r_c : ∀ t, Integrable (fun ω => M.u (x t ω) (z t ω) (x (t + 1) ω)) P
  uxΔ : ∀ t i, Integrable (fun ω => (xs t ω i - x t ω i) *
    M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) P
  uaΔ : ∀ t i, Integrable (fun ω => (xs (t + 1) ω i - x (t + 1) ω i) *
    M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) P
  uxn : ∀ t i, Integrable (fun ω => M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i) P
  uax : ∀ t i, Integrable (fun ω => M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i * xs (t + 1) ω i) P

variable {M : eu_EulerModel n Z} {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **The proof of Theorem 7.5.2** (Miao, pp. 226–227), under minimal hypotheses: concavity of
`u(·, z_t, ·)` on a set `C(z_t)` containing `(x*_t, x*_{t+1})` and `(x_t, x_{t+1})`,
differentiability at `(x*_t, x*_{t+1})`, (7.34), `u_x ≥ 0` along `x*`, `x ≥ 0` and (7.35). Then
`S_T(x) ≤ S_T(x*) + w_T` with `w_T → 0`. -/
theorem eu_euler_sufficient [IsProbabilityMeasure P] (hβ : 0 ≤ M.β) {x₀ : Fin n → ℝ}
    {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs) (hx : M.IsPlan ℱ z x₀ x)
    (C : Z → Set ((Fin n → ℝ) × (Fin n → ℝ))) (hcon : ∀ z', ConcaveOn ℝ (C z') (M.uu z'))
    (hmem : ∀ t ω, (xs t ω, xs (t + 1) ω) ∈ C (z t ω) ∧ (x t ω, x (t + 1) ω) ∈ C (z t ω))
    (hd : ∀ t ω, DifferentiableAt ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω))
    (heuler : M.IsEuler P ℱ z xs)
    (hux : ∀ t ω i, 0 ≤ M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i)
    (hpos : ∀ t ω i, 0 ≤ x (t + 1) ω i) (hint : EulerInt P z M xs x) (htvc : M.TVC735 P z xs) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z x T ≤ M.eu_partialJ P z xs T + w T := by
  set A : ℕ → ℝ := fun t => ∑ i, ∫ ω, (xs t ω i - x t ω i) *
    M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i ∂P with hAdef
  set B : ℕ → ℝ := fun t => ∑ i, ∫ ω, (xs (t + 1) ω i - x (t + 1) ω i) *
    M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i ∂P with hBdef
  -- the period inequality (supergradient)
  have hper : ∀ t, A t + B t ≤ (∫ ω, M.u (xs t ω) (z t ω) (xs (t + 1) ω) ∂P) -
      ∫ ω, M.u (x t ω) (z t ω) (x (t + 1) ω) ∂P := by
    intro t
    have hpath : ∀ ω, (∑ i, (xs t ω i - x t ω i) * M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) +
        (∑ i, (xs (t + 1) ω i - x (t + 1) ω i) * M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) ≤
        M.u (xs t ω) (z t ω) (xs (t + 1) ω) - M.u (x t ω) (z t ω) (x (t + 1) ω) := by
      intro ω
      have h := eu_concave_le_fderiv (hcon (z t ω)) (hmem t ω).1 (hmem t ω).2 (hd t ω).hasFDerivAt
      have hdec := eu_clm_pair (fderiv ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω))
        (xs t ω - x t ω) (xs (t + 1) ω - x (t + 1) ω)
      have hneg : (x t ω, x (t + 1) ω) - (xs t ω, xs (t + 1) ω) =
          -(xs t ω - x t ω, xs (t + 1) ω - x (t + 1) ω) := by ext <;> simp
      rw [hneg, map_neg, hdec] at h
      simp only [uu, Pi.sub_apply] at h
      simp only [ux, ua]
      linarith
    have hi1 : Integrable (fun ω => ∑ i, (xs t ω i - x t ω i) *
        M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) P :=
      integrable_finsetSum _ fun i _ => hint.uxΔ t i
    have hi2 : Integrable (fun ω => ∑ i, (xs (t + 1) ω i - x (t + 1) ω i) *
        M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) P :=
      integrable_finsetSum _ fun i _ => hint.uaΔ t i
    have hm : ∫ ω, ((∑ i, (xs t ω i - x t ω i) * M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) +
        (∑ i, (xs (t + 1) ω i - x (t + 1) ω i) * M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i)) ∂P ≤
        ∫ ω, (M.u (xs t ω) (z t ω) (xs (t + 1) ω) - M.u (x t ω) (z t ω) (x (t + 1) ω)) ∂P :=
      integral_mono (hi1.add hi2) ((hint.r_s t).sub (hint.r_c t)) hpath
    rw [integral_add hi1 hi2, integral_sub (hint.r_s t) (hint.r_c t),
      integral_finsetSum _ fun i _ => hint.uxΔ t i,
      integral_finsetSum _ fun i _ => hint.uaΔ t i] at hm
    exact hm
  -- the Euler equation: `B_t = −β A_{t+1}`
  have heul : ∀ t, B t = -(M.β * A (t + 1)) := by
    intro t
    simp only [hAdef, hBdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΔ : StronglyMeasurable[ℱ t] fun ω => xs (t + 1) ω i - x (t + 1) ω i :=
      (((measurable_pi_apply i).comp (hxs.2.1 t)).sub
        ((measurable_pi_apply i).comp (hx.2.1 t))).stronglyMeasurable
    obtain ⟨_, heq⟩ := OCModel.oc_integral_mul_condExp hΔ (hint.uxΔ (t + 1) i) (hint.uxn t i)
    have hae : (fun ω => (xs (t + 1) ω i - x (t + 1) ω i) *
        M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) =ᵐ[P] fun ω => -M.β *
          ((xs (t + 1) ω i - x (t + 1) ω i) * (P[fun ω' => M.ux (xs (t + 1) ω') (z (t + 1) ω')
            (xs (t + 2) ω') i | ℱ t]) ω) := by
      filter_upwards [heuler t i] with ω hω
      simp only [Pi.zero_apply] at hω
      have : M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i = -(M.β * (P[fun ω' => M.ux (xs (t + 1) ω')
          (z (t + 1) ω') (xs (t + 2) ω') i | ℱ t]) ω) := by linarith
      rw [this]; ring
    rw [integral_congr_ae hae, integral_const_mul, ← heq]
    ring
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hxs.1, hx.1]
  -- telescoping
  have htel : ∀ T, ∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t) = M.β ^ T * B T := by
    intro T
    have h1 : ∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t) =
        ∑ t ∈ Finset.range (T + 1), (M.β ^ t * A t - M.β ^ (t + 1) * A (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by rw [heul t]; ring
    rw [h1, Finset.sum_range_sub' (fun t => M.β ^ t * A t) (T + 1), hA0, heul T]
    ring
  -- the sign: `B_T ≥ E u_a(T) · x*_{T+1}`
  have hsign : ∀ T, ∑ i, ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P ≤ B T := by
    intro T
    simp only [hBdef]
    refine Finset.sum_le_sum fun i _ => ?_
    have hneg : ∀ᵐ ω ∂P, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i ≤ 0 := by
      have hce := condExp_nonneg (m := ℱ T) (μ := P)
        (f := fun ω' => M.ux (xs (T + 1) ω') (z (T + 1) ω') (xs (T + 2) ω') i)
        (Eventually.of_forall fun ω => hux T ω i)
      filter_upwards [heuler T i, hce] with ω hω hc
      simp only [Pi.zero_apply] at hω hc
      nlinarith [mul_nonneg hβ hc]
    refine integral_mono_ae ((hint.uax T i)) (hint.uaΔ T i) ?_
    filter_upwards [hneg] with ω hω
    have := mul_nonpos_of_nonneg_of_nonpos (hpos T ω i) hω
    nlinarith
  refine ⟨fun T => -(M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω))
    (xs (T + 1) ω) ∂P), by simpa using htvc.neg, fun T => ?_⟩
  have hsum : (∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t)) ≤
      ∑ t ∈ Finset.range (T + 1), M.β ^ t * ((∫ ω, M.u (xs t ω) (z t ω) (xs (t + 1) ω) ∂P) -
        ∫ ω, M.u (x t ω) (z t ω) (x (t + 1) ω) ∂P) :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hper t) (pow_nonneg hβ t)
  rw [htel] at hsum
  have hdot : ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P =
      ∑ i, ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P := by
    simp only [eu_dot]
    exact integral_finsetSum _ fun i _ => hint.uax T i
  have hB := mul_le_mul_of_nonneg_left (hsign T) (pow_nonneg hβ T)
  rw [← hdot] at hB
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  simp only [eu_partialJ]
  linarith

/-- **Theorem 7.5.2 (sufficiency of the Euler and transversality conditions)** (Miao, p. 226).
Let `X ⊆ ℝⁿ₊` be convex, `Γ ⊆ X`, and Assumptions 5.1.2 (`β ≥ 0` is used), 7.3.2, 7.3.3 and 7.3.4
hold. Let the feasible plan `x*` with `x*_{t+1} ∈ int Γ(x*_t, z_t)` and `x₀ ∈ int X` satisfy the
Euler equation (7.34) and the transversality condition (7.35). Then every feasible plan `x` with
the integrability `EulerInt` satisfies `S_T(x) ≤ S_T(x*) + w_T` with `w_T → 0`. -/
theorem theorem_7_5_2 [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y) (hXc : Convex ℝ M.X)
    (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1) (h732 : M.eu_Assumption732)
    (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) {x₀ : Fin n → ℝ}
    {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs) (hx0 : x₀ ∈ interior M.X)
    (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) (hx : M.IsPlan ℱ z x₀ x)
    (hint : EulerInt P z M xs x) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z x T ≤ M.eu_partialJ P z xs T + w T := by
  have hin : ∀ t ω, xs t ω ∈ interior M.X := by
    intro t ω
    cases t with
    | zero => rw [hxs.1 ω]; exact hx0
    | succ t => exact interior_mono (hΓX _ _) (hinter t ω)
  have hmemI : ∀ t ω, (xs t ω, xs (t + 1) ω) ∈ interior (M.X ×ˢ M.X) := fun t ω => by
    rw [interior_prod_eq]; exact ⟨hin t ω, hin (t + 1) ω⟩
  have hd : ∀ t ω, DifferentiableAt ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω) := fun t ω =>
    ((h734 (z t ω)).differentiableOn one_ne_zero).differentiableAt
      (isOpen_interior.mem_nhds (hmemI t ω))
  refine eu_euler_sufficient h512.1.le hxs hx (fun _ => M.X ×ˢ M.X)
    (fun z' => concaveOn_of_733 h733 hXc z')
    (fun t ω => ⟨interior_subset (hmemI t ω), (hx.2.2 t ω).1, hΓX _ _ (hx.2.2 t ω).2⟩)
    hd heuler (fun t ω i => ?_) (fun t ω i => hXpos _ (hx.2.2 (t + 1) ω).1 i) hint htvc
  exact eu_ux_nonneg (h732 _ _).monotoneOn (hin (t + 1) ω) (hd (t + 1) ω) i

/-- **Theorem 7.5.2, the limit step** (Miao, p. 227): under the hypotheses of `theorem_7_5_2`,
if the partial sums of `x*` and of `x` converge in `[−∞, +∞]`, then `J(x) ≤ J(x*)`. -/
theorem theorem_7_5_2_limit [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y)
    (hXc : Convex ℝ M.X) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1)
    (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734)
    {x₀ : Fin n → ℝ} {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs)
    (hx0 : x₀ ∈ interior M.X) (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) (hx : M.IsPlan ℱ z x₀ x)
    (hint : EulerInt P z M xs x) {J J' : EReal}
    (hJ : Tendsto (fun T => (M.eu_partialJ P z xs T : EReal)) atTop (𝓝 J))
    (hJ' : Tendsto (fun T => (M.eu_partialJ P z x T : EReal)) atTop (𝓝 J')) : J' ≤ J := by
  obtain ⟨w, hw, hle⟩ := theorem_7_5_2 hXpos hXc hΓX h512 h732 h733 h734 hxs hx0 hinter heuler
    htvc hx hint
  exact eu_le_of_le_add_tendsto_zero hJ hJ' hw hle

/-- **Theorem 7.5.2, optimality** (Miao, p. 227): under the hypotheses of `theorem_7_5_2` for
every competing plan, if the rewards of `x*` are integrable and `S_T(x*) → J*`, then `x*` is
optimal in the sense of `IsOptimal` among the plans with the integrability `EulerInt`. -/
theorem theorem_7_5_2_eventually [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y)
    (hXc : Convex ℝ M.X) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1)
    (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734)
    {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs)
    (hx0 : x₀ ∈ interior M.X) (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) {J : ℝ}
    (hJ : Tendsto (M.eu_partialJ P z xs) atTop (𝓝 J)) {x : ℕ → Ω → (Fin n → ℝ)}
    (hx : M.IsPlan ℱ z x₀ x) (hint : EulerInt P z M xs x) :
    ∀ ε > 0, ∀ᶠ T in atTop, M.eu_partialJ P z x T ≤ J + ε := by
  obtain ⟨w, hw, hle⟩ := theorem_7_5_2 hXpos hXc hΓX h512 h732 h733 h734 hxs hx0 hinter heuler
    htvc hx hint
  exact eu_limsup_le hJ hw hle

end eu_EulerModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 7.5.1 (Phelps 1962; Levhari–Srinivasan 1969)

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EUPhelps`), namespace renamed.

Miao, §7.5, pp. 227–228: `max E Σ βᵗ u(c_t)` with CRRA `u(c) = c^{1−γ}/(1−γ)` (`log c` at
`γ = 1`, `cs_crra` from §6.6.2), `x_{t+1} = R_{t+1}(x_t − c_t)`, `x₀ > 0`, returns `R_t > 0`.

* `eq_7_39`: the policy `c = Ax` with `A = 1 − (βm)^{1/γ}`, `m = E[R^{1−γ}]`, solves the Euler
  equation after `E_t` is taken, `A^{−γ}x^{−γ} = β A^{−γ}(x − Ax)^{−γ} m`; `eq_7_39_unique`: it is
  the only `A ∈ (0, 1)` that does. `example_7_5_1_log`: `γ = 1` gives `A = 1 − β`.
  `example_7_5_1_A_mem`: `A ∈ (0, 1)` iff `0 < βm < 1` (for `βm ≥ 0`, as here).
* `example_7_5_1_tvc_det`: `βᵗA^{−γ}(1 − A)^{t(1−γ)}x₀^{1−γ}mᵗ = A^{−γ}x₀^{1−γ}(1 − A)ᵗ → 0`.
* The stochastic model in the Euler class (**the book's change of variables**, p. 221): the
  state is the saving `y_t = x_{t−1} − c_{t−1}` (with `R_0 = 1`, `y_0 = x₀`), so
  `x_t = R_t y_t`, `c_t = R_t y_t − y_{t+1}` and `u(y, R, y′) = u(Ry − y′)` with
  `Γ(y, R) = {y′ : 0 ≤ y′ < Ry}` (`eu_phelpsModel`); then `X = ℝ₊`,
  `u_x = R u′(c) > 0`, `u_a = −u′(c) < 0`. `eu_phelpsCash`, `eu_phelpsState`: the cash on hand and
  the state under `c_t = Ax_t`.
* `example_7_5_1_cash_rpow` and `example_7_5_1_tvc_formula`: the printed computation,
  `E[βᵗc_t^{−γ}x_t] = βᵗA^{−γ}(1 − A)^{t(1−γ)}x₀^{1−γ}E[Π_{s=1}^t R_s^{1−γ}]` (correct);
  `example_7_5_1_prod_moment`: `E[Π_{s=1}^t R_s^{1−γ}] = mᵗ` when `E_t[R_{t+1}^{1−γ}] = m`
  (`example_7_5_1_condmoment`: this holds when `R_{t+1}` is independent of `ℱ_t`);
  `example_7_5_1_tvc`: the transversality condition of the book holds.
* `example_7_5_1_euler`: the policy satisfies the Euler equation (7.34); `example_7_5_1`:
  it is optimal, by the sufficiency argument of Theorem 7.5.2 (`eu_euler_sufficient`).

**Departures.** (1) The book's "iid" is used only through `E_t[R_{t+1}^{1−γ}] = m`; the
integrability of `R_{t+1}^{1−γ}`, of `Π_{s ≤ t} R_s^{1−γ}` and of `(x_t)^{−γ}R_{t+1}^{1−γ}` is
assumed (it does not follow from iid without moment conditions such as `E[R^{−γ}] < ∞`).
(2) Theorem 7.5.2 does not apply verbatim: off the graph of `Γ` (`c ≤ 0`) the reward is not
defined (it is `−∞` for `γ ≥ 1`), so Assumptions 7.3.2–7.3.4 fail on `X × X`, and the strict part
of Assumption 7.3.3 fails on the graph (`u` is constant along `(y, y′) + s(1, R)`). The proof of
Theorem 7.5.2 needs only concavity on the graph (`eu_euler_sufficient`), which holds.
(3) Consumption is kept positive (`y′ < Ry`); for `γ < 1` the book allows `c = 0`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### The algebra of (7.39) -/

/-- **(7.39)** (Miao, p. 227): with `m = E[R^{1−γ}]`, `βm > 0` and `A = 1 − (βm)^{1/γ}`, the
Euler equation `A^{−γ}x^{−γ} = β E[R A^{−γ}R^{−γ}(x − Ax)^{−γ}] = β A^{−γ}(x − Ax)^{−γ} m`
holds for every `x > 0`. -/
theorem eq_7_39 {β m γ x : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m) (hx : 0 < x) :
    (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x ^ (-γ) =
      β * ((1 - (β * m) ^ (1 / γ)) ^ (-γ) * (x - (1 - (β * m) ^ (1 / γ)) * x) ^ (-γ) * m) := by
  set A := 1 - (β * m) ^ (1 / γ)
  have h1A : 1 - A = (β * m) ^ (1 / γ) := by simp [A]
  have hpos : 0 < (β * m) ^ (1 / γ) := Real.rpow_pos_of_pos hbm _
  have hxA : x - A * x = (1 - A) * x := by ring
  rw [hxA, Real.mul_rpow (by rw [h1A]; exact hpos.le) hx.le, h1A, ← Real.rpow_mul hbm.le]
  have e : 1 / γ * -γ = -1 := by field_simp
  rw [e, Real.rpow_neg_one]
  have hb0 : β ≠ 0 := left_ne_zero_of_mul hbm.ne'
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hbm.ne'
  field_simp

/-- **(7.39) is the only solution** in `(0, 1)` (Miao, p. 227): if `A ∈ (0, 1)` satisfies
`A^{−γ}x^{−γ} = β A^{−γ}(x − Ax)^{−γ} m` for some `x > 0`, then `A = 1 − (βm)^{1/γ}`. -/
theorem eq_7_39_unique {β m γ x A : ℝ} (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A < 1) (hx : 0 < x)
    (h : A ^ (-γ) * x ^ (-γ) = β * (A ^ (-γ) * (x - A * x) ^ (-γ) * m)) :
    A = 1 - (β * m) ^ (1 / γ) := by
  have h1A : 0 < 1 - A := by linarith
  have hxA : x - A * x = (1 - A) * x := by ring
  rw [hxA, Real.mul_rpow h1A.le hx.le] at h
  have hAp : 0 < A ^ (-γ) := Real.rpow_pos_of_pos hA0 _
  have hxp : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx _
  have h1 : 1 = β * m * (1 - A) ^ (-γ) := by
    have := h
    field_simp at this
    nlinarith [this]
  have h2 : (1 - A) ^ γ = β * m := by
    rw [Real.rpow_neg h1A.le] at h1
    have hne : (1 - A) ^ γ ≠ 0 := (Real.rpow_pos_of_pos h1A _).ne'
    field_simp at h1
    linarith
  have h3 : (β * m) ^ (1 / γ) = 1 - A := by
    rw [← h2, one_div, Real.rpow_rpow_inv h1A.le hγ.ne']
  linarith

/-- **Example 7.5.1, log utility** (Miao, p. 228): for `γ = 1`, `E[R^{1−γ}] = 1`, so
`A = 1 − β`. -/
theorem example_7_5_1_log {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (R : Ω → ℝ) (β : ℝ) :
    1 - (β * ∫ ω, R ω ^ ((1 : ℝ) - 1) ∂P) ^ (1 / (1 : ℝ)) = 1 - β := by
  simp

/-- **Example 7.5.1, `A ∈ (0, 1)`** (Miao, p. 228): for `γ > 0` and `βm ≥ 0`,
`A = 1 − (βm)^{1/γ} ∈ (0, 1)` iff `0 < βm < 1` (equivalently `0 < (βm)^{1/γ} < 1`). -/
theorem example_7_5_1_A_mem {β m γ : ℝ} (hγ : 0 < γ) (hbm : 0 ≤ β * m) :
    (0 < 1 - (β * m) ^ (1 / γ) ∧ 1 - (β * m) ^ (1 / γ) < 1) ↔ (0 < β * m ∧ β * m < 1) := by
  have hg : 0 < 1 / γ := by positivity
  constructor
  · rintro ⟨h0, h1⟩
    have hp : 0 < (β * m) ^ (1 / γ) := by linarith
    have hbm' : 0 < β * m := by
      rcases hbm.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow hg.ne'] at hp; exact absurd hp (lt_irrefl 0)
      · exact h
    refine ⟨hbm', ?_⟩
    have hlt : (β * m) ^ (1 / γ) < 1 := by linarith
    rcases (Real.rpow_lt_one_iff_of_pos hbm').1 hlt with h | h
    · linarith [h.2]
    · exact h.1
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith [Real.rpow_lt_one hbm h1 hg], by linarith [Real.rpow_pos_of_pos h0 (1 / γ)]⟩

/-- **The transversality computation, deterministic part** (Miao, p. 228): with
`A = 1 − (βm)^{1/γ} ∈ (0, 1)`,
`βᵗ A^{−γ}(1 − A)^{t(1−γ)} x₀^{1−γ} mᵗ = A^{−γ} x₀^{1−γ} (1 − A)ᵗ`, which tends to `0`. -/
theorem example_7_5_1_tvc_det {β m γ x₀ : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m)
    (hbm1 : β * m < 1) :
    (∀ t : ℕ, β ^ t * (1 - (β * m) ^ (1 / γ)) ^ (-γ) *
      ((β * m) ^ (1 / γ)) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) * m ^ t =
      (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x₀ ^ (1 - γ) * ((β * m) ^ (1 / γ)) ^ t) ∧
    Tendsto (fun t : ℕ => (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x₀ ^ (1 - γ) *
      ((β * m) ^ (1 / γ)) ^ t) atTop (𝓝 0) := by
  set q := (β * m) ^ (1 / γ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hbm _
  have hq1 : q < 1 := Real.rpow_lt_one hbm.le hbm1 (by positivity)
  have hqγ : q ^ γ = β * m := by rw [hq, one_div, Real.rpow_inv_rpow hbm.le hγ.ne']
  refine ⟨fun t => ?_, ?_⟩
  · have e1 : q ^ ((t : ℝ) * (1 - γ)) = (q ^ (1 - γ)) ^ t := by
      rw [mul_comm, Real.rpow_mul_natCast hq0.le]
    have e2 : β * m * q ^ (1 - γ) = q := by
      rw [← hqγ, ← Real.rpow_add hq0]; simp
    rw [e1]
    calc β ^ t * (1 - q) ^ (-γ) * (q ^ (1 - γ)) ^ t * x₀ ^ (1 - γ) * m ^ t
        = (1 - q) ^ (-γ) * x₀ ^ (1 - γ) * (β * m * q ^ (1 - γ)) ^ t := by ring
      _ = _ := by rw [e2]
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul
      ((1 - q) ^ (-γ) * x₀ ^ (1 - γ))
    simpa using this

/-! ### CRRA utility -/

/-- The derivative of CRRA utility: `u′(c) = c^{−γ}` for `c > 0`. -/
theorem eu_crra_hasDerivAt {γ c : ℝ} (hc : 0 < c) : HasDerivAt (cs_crra γ) (c ^ (-γ)) c := by
  by_cases h1 : γ = 1
  · subst h1
    have : cs_crra 1 = Real.log := funext fun x => by simp [cs_crra]
    rw [this, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have hp : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have : cs_crra γ = fun x => x ^ (1 - γ) / (1 - γ) := funext fun x => by simp [cs_crra, h1]
    rw [this]
    have h := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
    refine h.congr_deriv ?_
    have e : 1 - γ - 1 = -γ := by ring
    rw [e]
    field_simp

/-- CRRA utility is concave on `(0, ∞)` (from the tangent-line inequality `cs_crra_tangent`). -/
theorem eu_crra_concave {γ : ℝ} (hγ : 0 < γ) : ConcaveOn ℝ (Set.Ioi 0) (cs_crra γ) := by
  refine ⟨convex_Ioi 0, fun a ha b hb θ η hθ hη hs => ?_⟩
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  set c := θ • a + η • b
  have hc : 0 < c := by
    simp only [c, smul_eq_mul]
    rcases hθ.eq_or_lt with h | h
    · subst h; simp only [zero_add] at hs; subst hs; simpa using hb'
    · nlinarith [mul_pos h ha']
  have h1 := cs_crra_tangent hγ hc ha'
  have h2 := cs_crra_tangent hγ hc hb'
  have e : θ * (a - c) + η * (b - c) = 0 := by
    simp only [c, smul_eq_mul]
    have : η = 1 - θ := by linarith
    subst this; ring
  simp only [smul_eq_mul]
  have h1' := mul_le_mul_of_nonneg_left h1 hθ
  have h2' := mul_le_mul_of_nonneg_left h2 hη
  have e2 : θ * (c ^ (-γ) * (a - c)) + η * (c ^ (-γ) * (b - c)) = 0 := by
    linear_combination c ^ (-γ) * e
  have e3 : θ * cs_crra γ c + η * cs_crra γ c = cs_crra γ c := by rw [← add_mul, hs, one_mul]
  linarith

/-! ### The model in the Euler class -/

/-- **Example 7.5.1 in the Euler class** (Miao, pp. 221, 227): the state is the saving
`y = x − c ≥ 0` carried into the period, the shock is the return `R`, the choice is next
period's saving `y′ ∈ [0, Ry)` and the reward is `u(Ry − y′)`. -/
noncomputable def eu_phelpsModel (γ β : ℝ) : eu_EulerModel 1 ℝ where
  X := {y | 0 ≤ y 0}
  Q := 0
  Γ := fun y R => {y' | 0 ≤ y' 0 ∧ y' 0 < R * y 0}
  u := fun y R y' => cs_crra γ (R * y 0 - y' 0)
  β := β

/-- The partial derivatives of the reward of `eu_phelpsModel` at a point with consumption
`c = R y₀ − y′₀ > 0`: the reward is differentiable and its derivative applied to `v` is
`c^{−γ}(R v₁ − v₂)`. -/
theorem eu_phelps_fderiv {γ β R : ℝ} {p : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hc : 0 < R * p.1 0 - p.2 0) :
    DifferentiableAt ℝ ((eu_phelpsModel γ β).uu R) p ∧
      ∀ v, fderiv ℝ ((eu_phelpsModel γ β).uu R) p v =
        (R * p.1 0 - p.2 0) ^ (-γ) * (R * v.1 0 - v.2 0) := by
  have hg : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => R * q.1 0 - q.2 0) p := by
    fun_prop
  have hd : DifferentiableAt ℝ ((eu_phelpsModel γ β).uu R) p := by
    have := (eu_crra_hasDerivAt (γ := γ) hc).differentiableAt.comp p hg
    exact this
  refine ⟨hd, fun v => ?_⟩
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hd' : HasFDerivAt ((eu_phelpsModel γ β).uu R) (fderiv ℝ ((eu_phelpsModel γ β).uu R) p)
      (p + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hin : HasDerivAt (fun s : ℝ => R * (p + s • v).1 0 - (p + s • v).2 0)
      (R * v.1 0 - v.2 0) 0 := by
    have : (fun s : ℝ => R * (p + s • v).1 0 - (p + s • v).2 0) =
        fun s => (R * p.1 0 - p.2 0) + s * (R * v.1 0 - v.2 0) := by
      funext s; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (R * v.1 0 - v.2 0)).const_add
      (R * p.1 0 - p.2 0)
  have hc' : 0 < R * (p + (0 : ℝ) • v).1 0 - (p + (0 : ℝ) • v).2 0 := by simpa using hc
  have h2 := (eu_crra_hasDerivAt (γ := γ) hc').comp (0 : ℝ) hin
  have huniq := h1.unique h2
  simp only [zero_smul, add_zero] at huniq
  rw [huniq]

/-- The cash on hand under the policy `c_t = A x_t`: `x₀` given,
`x_{t+1} = R_{t+1}(1 − A)x_t`. -/
noncomputable def eu_phelpsCash {Ω : Type*} (R : ℕ → Ω → ℝ) (A x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => R (t + 1) ω * ((1 - A) * eu_phelpsCash R A x₀ t ω)

/-- The state (saving carried into the period) under the policy `c_t = A x_t`: `y₀ = x₀`,
`y_{t+1} = (1 − A)x_t`. -/
noncomputable def eu_phelpsState {Ω : Type*} (R : ℕ → Ω → ℝ) (A x₀ : ℝ) : ℕ → Ω → (Fin 1 → ℝ)
  | 0 => fun _ _ => x₀
  | t + 1 => fun ω _ => (1 - A) * eu_phelpsCash R A x₀ t ω

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ m0}

/-- The cash on hand is positive. -/
theorem eu_phelpsCash_pos {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hR : ∀ t ω, 0 < R t ω) (hA : A < 1)
    (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) : 0 < eu_phelpsCash R A x₀ t ω := by
  induction t with
  | zero => exact hx₀
  | succ t ih =>
    have : 0 < 1 - A := by linarith
    exact mul_pos (hR _ ω) (mul_pos this ih)

/-- With `R₀ = 1`, the cash on hand is `x_t = R_t y_t`. -/
theorem eu_phelps_cash_eq {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hR0 : ∀ ω, R 0 ω = 1) (t : ℕ) (ω : Ω) :
    R t ω * eu_phelpsState R A x₀ t ω 0 = eu_phelpsCash R A x₀ t ω := by
  cases t with
  | zero => simp [eu_phelpsState, eu_phelpsCash, hR0]
  | succ t => rfl

/-- The cash on hand is adapted. -/
theorem eu_phelpsCash_measurable {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hRm : ∀ t, Measurable[ℱ t] (R t))
    (t : ℕ) : Measurable[ℱ t] (eu_phelpsCash R A x₀ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (hRm (t + 1)).mul ((ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl).const_mul _)

/-- **The printed computation, pathwise** (Miao, p. 228): `x_t = (1 − A)ᵗ x₀ Π_{s=1}^t R_s`, so
`x_t^{1−γ} = (1 − A)^{t(1−γ)} x₀^{1−γ} Π_{s=1}^t R_s^{1−γ}`. -/
theorem example_7_5_1_cash_rpow {R : ℕ → Ω → ℝ} {A x₀ γ : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hA : A < 1) (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) :
    eu_phelpsCash R A x₀ t ω ^ (1 - γ) = (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
      ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
  have h1A : 0 < 1 - A := by linarith
  induction t with
  | zero => simp [eu_phelpsCash]
  | succ t ih =>
    have hc := eu_phelpsCash_pos hR hA hx₀ t ω
    simp only [eu_phelpsCash]
    rw [Real.mul_rpow (hR _ ω).le (mul_pos h1A hc).le, Real.mul_rpow h1A.le hc.le, ih,
      Finset.prod_range_succ]
    have e : (1 - A) ^ (((t + 1 : ℕ) : ℝ) * (1 - γ)) =
        (1 - A) ^ ((t : ℝ) * (1 - γ)) * (1 - A) ^ (1 - γ) := by
      rw [← Real.rpow_add h1A]; congr 1; push_cast; ring
    rw [e]
    ring

/-- **`E_t[R_{t+1}^{1−γ}] = m` from independence** (Miao, p. 228: "`R_t` is iid"): if
`R_{t+1}` is independent of `ℱ_t` and `E[R_{t+1}^{1−γ}] = m`, then `E_t[R_{t+1}^{1−γ}] = m`
almost surely. -/
theorem example_7_5_1_condmoment [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ m : ℝ} (t : ℕ)
    (hRm : Measurable (R (t + 1)))
    (hind : Indep (MeasurableSpace.comap (R (t + 1)) inferInstance) (ℱ t) P)
    (hm : ∫ ω, R (t + 1) ω ^ (1 - γ) ∂P = m) :
    P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m := by
  have hle : MeasurableSpace.comap (R (t + 1)) inferInstance ≤ m0 := hRm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap (R (t + 1)) inferInstance]
      fun ω => R (t + 1) ω ^ (1 - γ) :=
    ((Measurable.pow_const measurable_id (1 - γ)).comp (comap_measurable (R (t + 1)))
      ).stronglyMeasurable
  have := condExp_indep_eq hle (ℱ.le t) hsm hind
  rw [hm] at this
  exact this

/-- **`E[Π_{s=1}^t R_s^{1−γ}] = mᵗ`** (Miao, p. 228): if `E_t[R_{t+1}^{1−γ}] = m` almost surely,
`R` is adapted and the partial products are integrable. -/
theorem example_7_5_1_prod_moment [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ m : ℝ}
    (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P)
    (t : ℕ) : ∫ ω, ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) ∂P = m ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmeas : StronglyMeasurable[ℱ t] fun ω => ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
      refine (Finset.measurable_prod _ fun s hs => ?_).stronglyMeasurable
      have hst : s + 1 ≤ t := by have := Finset.mem_range.1 hs; omega
      exact (((hRm (s + 1)).mono (ℱ.mono hst) le_rfl).pow_const _)
    have hprod : (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) =
        fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) * R (t + 1) ω ^ (1 - γ) := by
      funext ω; rw [Finset.prod_range_succ]
    obtain ⟨_, heq⟩ := OCModel.oc_integral_mul_condExp hmeas (by rw [← hprod]; exact hI2 t)
      (hI1 t)
    have hae : (fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) *
        (P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t]) ω) =ᵐ[P]
        fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) * m := by
      filter_upwards [hcm t] with ω hω
      rw [hω]
    rw [hprod, heq, integral_congr_ae hae, integral_mul_const, ih, pow_succ]

/-- **The transversality computation as printed** (Miao, p. 228): with `c_t = A x_t`,
`E[βᵗ c_t^{−γ} x_t] = βᵗ A^{−γ}(1 − A)^{t(1−γ)} x₀^{1−γ} E[Π_{s=1}^t R_s^{1−γ}]`. -/
theorem example_7_5_1_tvc_formula {R : ℕ → Ω → ℝ} {A x₀ γ β : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hA0 : 0 < A) (hA : A < 1) (hx₀ : 0 < x₀) (t : ℕ) :
    ∫ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * eu_phelpsCash R A x₀ t ω) ∂P =
      β ^ t * A ^ (-γ) * (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
        ∫ ω, ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) ∂P := by
  have hpt : ∀ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * eu_phelpsCash R A x₀ t ω) =
      β ^ t * A ^ (-γ) * (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
        ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
    intro ω
    have hc := eu_phelpsCash_pos hR hA hx₀ t ω
    have e : eu_phelpsCash R A x₀ t ω ^ (-γ) * eu_phelpsCash R A x₀ t ω =
        eu_phelpsCash R A x₀ t ω ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hc.ne']
    rw [Real.mul_rpow hA0.le hc.le, mul_assoc (A ^ (-γ)), e,
      example_7_5_1_cash_rpow hR hA hx₀ t ω]
    ring
  simp only [hpt]
  rw [integral_const_mul]

/-- **The transversality condition of Example 7.5.1** (Miao, p. 228):
`lim_t E[βᵗ c_t^{−γ} x_t] = 0` when `0 < βm < 1`, `A = 1 − (βm)^{1/γ}`, given
`E_t[R_{t+1}^{1−γ}] = m` and the integrability of the partial products. -/
theorem example_7_5_1_tvc [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) (hA : A = 1 - (β * m) ^ (1 / γ))
    (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω) (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P) :
    Tendsto (fun t : ℕ => ∫ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      eu_phelpsCash R A x₀ t ω) ∂P) atTop (𝓝 0) := by
  subst hA
  have hA := (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  obtain ⟨hdet, hlim⟩ := example_7_5_1_tvc_det (x₀ := x₀) hγ hbm hbm1
  refine hlim.congr fun t => ?_
  rw [example_7_5_1_tvc_formula hR hA.1 hA.2 hx₀ t,
    example_7_5_1_prod_moment hRm hcm hI1 hI2 t]
  have e : 1 - (1 - (β * m) ^ (1 / γ)) = (β * m) ^ (1 / γ) := by ring
  rw [e]
  exact (hdet t).symm

/-- The derivatives of the reward along the policy `c_t = Ax_t` (Miao, p. 227): consumption is
`c_t = R_t y_t − y_{t+1} = A x_t > 0`, `u_a = −c_t^{−γ}` and `u_x = c_t^{−γ} R_t`. -/
theorem eu_phelps_derivs {R : ℕ → Ω → ℝ} {γ β A x₀ : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hR0 : ∀ ω, R 0 ω = 1) (hA0 : 0 < A) (hA1 : A < 1) (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) :
    R t ω * eu_phelpsState R A x₀ t ω 0 - eu_phelpsState R A x₀ (t + 1) ω 0 =
      A * eu_phelpsCash R A x₀ t ω ∧
    DifferentiableAt ℝ ((eu_phelpsModel γ β).uu (R t ω))
      (eu_phelpsState R A x₀ t ω, eu_phelpsState R A x₀ (t + 1) ω) ∧
    (eu_phelpsModel γ β).ua (eu_phelpsState R A x₀ t ω) (R t ω)
      (eu_phelpsState R A x₀ (t + 1) ω) 0 = -(A * eu_phelpsCash R A x₀ t ω) ^ (-γ) ∧
    (eu_phelpsModel γ β).ux (eu_phelpsState R A x₀ t ω) (R t ω)
      (eu_phelpsState R A x₀ (t + 1) ω) 0 = (A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * R t ω := by
  have hcons : R t ω * eu_phelpsState R A x₀ t ω 0 - eu_phelpsState R A x₀ (t + 1) ω 0 =
      A * eu_phelpsCash R A x₀ t ω := by
    rw [eu_phelps_cash_eq hR0]
    simp only [eu_phelpsState]
    ring
  have hc := eu_phelpsCash_pos hR hA1 hx₀ t ω
  have hf := eu_phelps_fderiv (γ := γ) (β := β) (R := R t ω)
    (p := (eu_phelpsState R A x₀ t ω, eu_phelpsState R A x₀ (t + 1) ω))
    (by rw [hcons]; positivity)
  refine ⟨hcons, hf.1, ?_, ?_⟩
  · simp only [eu_EulerModel.ua]
    rw [hf.2, hcons]
    simp
  · simp only [eu_EulerModel.ux]
    rw [hf.2, hcons]
    simp

/-- **Example 7.5.1, the Euler equation** (Miao, p. 227): the policy `c_t = A x_t` with
`A = 1 − (βm)^{1/γ}` satisfies (7.34) in the Euler-class form,
`−c_t^{−γ} + β E_t[R_{t+1} c_{t+1}^{−γ}] = 0`, given `E_t[R_{t+1}^{1−γ}] = m` and the
integrability of `R_{t+1}^{1−γ}` and of `((1 − A)x_t)^{−γ} R_{t+1}^{1−γ}`. -/
theorem example_7_5_1_euler [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) (hA : A = 1 - (β * m) ^ (1 / γ))
    (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω) (hR0 : ∀ ω, R 0 ω = 1)
    (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI3 : ∀ t, Integrable (fun ω => ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      R (t + 1) ω ^ (1 - γ)) P) :
    (eu_phelpsModel γ β).IsEuler P ℱ R (eu_phelpsState R A x₀) := by
  have hA01 : 0 < A ∧ A < 1 := by rw [hA]; exact (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  have h1A : 0 < 1 - A := by linarith [hA01.2]
  intro t i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  set f : Ω → ℝ := fun ω => A ^ (-γ) * ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) with hf
  have hux : (fun ω' => (eu_phelpsModel γ β).ux (eu_phelpsState R A x₀ (t + 1) ω') (R (t + 1) ω')
      (eu_phelpsState R A x₀ (t + 2) ω') 0) = fun ω' => f ω' * R (t + 1) ω' ^ (1 - γ) := by
    funext ω'
    rw [(eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ (t + 1) ω').2.2.2]
    have hct := eu_phelpsCash_pos hR hA01.2 hx₀ t ω'
    have hR1 := hR (t + 1) ω'
    have e : eu_phelpsCash R A x₀ (t + 1) ω' =
        R (t + 1) ω' * ((1 - A) * eu_phelpsCash R A x₀ t ω') := rfl
    rw [e, show A * (R (t + 1) ω' * ((1 - A) * eu_phelpsCash R A x₀ t ω')) =
        A * ((1 - A) * eu_phelpsCash R A x₀ t ω') * R (t + 1) ω' by ring,
      Real.mul_rpow (mul_pos hA01.1 (mul_pos h1A hct)).le hR1.le,
      Real.mul_rpow hA01.1.le (mul_pos h1A hct).le]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hR1.ne']
    simp only [hf]
    ring
  have hfm : StronglyMeasurable[ℱ t] f :=
    (((eu_phelpsCash_measurable hRm t).const_mul (1 - A)).pow_const (-γ) |>.const_mul
      (A ^ (-γ))).stronglyMeasurable
  have hfg : Integrable (fun ω => f ω * R (t + 1) ω ^ (1 - γ)) P := by
    refine ((hI3 t).const_mul (A ^ (-γ))).congr (Eventually.of_forall fun ω => ?_)
    simp only [hf]; ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hfm hfg (hI1 t)
  rw [hux]
  filter_upwards [hpull, hcm t] with ω h1 h2
  have h1' : (P[fun ω => f ω * R (t + 1) ω ^ (1 - γ) | ℱ t]) ω = f ω * m := by
    rw [show (fun ω => f ω * R (t + 1) ω ^ (1 - γ)) = f * fun ω => R (t + 1) ω ^ (1 - γ) from rfl,
      h1, Pi.mul_apply, h2]
  rw [h1', (eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ t ω).2.2.1]
  simp only [Pi.zero_apply, hf]
  have hct := eu_phelpsCash_pos hR hA01.2 hx₀ t ω
  have key := eq_7_39 hγ hbm hct
  rw [← hA] at key
  rw [Real.mul_rpow hA01.1.le hct.le, key, show eu_phelpsCash R A x₀ t ω -
    A * eu_phelpsCash R A x₀ t ω = (1 - A) * eu_phelpsCash R A x₀ t ω by ring]
  simp only [eu_phelpsModel]
  ring

/-- **Example 7.5.1, optimality** (Miao, p. 228): the policy `c_t = A x_t`,
`A = 1 − (βm)^{1/γ}`, `0 < βm < 1`, is optimal: by the sufficiency argument of Theorem 7.5.2
(`eu_euler_sufficient`, with concavity on the graph of `Γ`), the Euler equation and the
transversality condition, every feasible plan `x` (with the integrability `EulerInt`) has
`S_T(x) ≤ S_T(x*) + w_T`, `w_T → 0`. The shock is the return process `R` (adapted, positive,
`R_0 = 1`) with `E_t[R_{t+1}^{1−γ}] = m`. -/
theorem example_7_5_1 [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hβ : 0 < β ∧ β < 1) (hbm : 0 < β * m) (hbm1 : β * m < 1)
    (hA : A = 1 - (β * m) ^ (1 / γ)) (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω)
    (hR0 : ∀ ω, R 0 ω = 1) (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P)
    (hI3 : ∀ t, Integrable (fun ω => ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      R (t + 1) ω ^ (1 - γ)) P)
    {x : ℕ → Ω → (Fin 1 → ℝ)} (hx : (eu_phelpsModel γ β).IsPlan ℱ R (fun _ => x₀) x)
    (hint : eu_EulerModel.EulerInt P R (eu_phelpsModel γ β) (eu_phelpsState R A x₀) x) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, (eu_phelpsModel γ β).eu_partialJ P R x T ≤
        (eu_phelpsModel γ β).eu_partialJ P R (eu_phelpsState R A x₀) T + w T := by
  have hA01 : 0 < A ∧ A < 1 := by rw [hA]; exact (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  have h1A : 0 < 1 - A := by linarith [hA01.2]
  have hD := fun t ω => eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ t ω
  have hcpos := fun t ω => eu_phelpsCash_pos hR hA01.2 hx₀ t ω
  have hst : ∀ t ω, 0 < eu_phelpsState R A x₀ t ω 0 := fun t ω => by
    cases t with
    | zero => exact hx₀
    | succ t => exact mul_pos h1A (hcpos t ω)
  -- the candidate is a feasible plan
  have hplan : (eu_phelpsModel γ β).IsPlan ℱ R (fun _ => x₀) (eu_phelpsState R A x₀) := by
    refine ⟨fun ω => rfl, fun t => ?_, fun t ω => ⟨(hst t ω).le, (hst (t + 1) ω).le, ?_⟩⟩
    · change Measurable[ℱ t] fun ω (_ : Fin 1) => (1 - A) * eu_phelpsCash R A x₀ t ω
      exact (continuous_pi fun _ => continuous_id).measurable.comp
        ((eu_phelpsCash_measurable hRm t).const_mul _)
    · have := (hD t ω).1
      have := mul_pos hA01.1 (hcpos t ω)
      linarith
  -- the graph of `Γ` and concavity on it
  set C : ℝ → Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
    fun r => {p | 0 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 < r * p.1 0} with hC
  have hcon : ∀ r, ConcaveOn ℝ (C r) ((eu_phelpsModel γ β).uu r) := by
    intro r
    have hconv : Convex ℝ (C r) := by
      intro p hp q hq a b ha hb hab
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
      · nlinarith [mul_nonneg ha hp1, mul_nonneg hb hq1]
      · nlinarith [mul_nonneg ha hp2, mul_nonneg hb hq2]
      rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; simpa using hq3
      · nlinarith [mul_pos h (sub_pos.2 hp3), mul_nonneg hb (sub_pos.2 hq3).le]
    refine ⟨hconv, fun p hp q hq a b ha hb hab => ?_⟩
    have hcp : (0 : ℝ) < r * p.1 0 - p.2 0 := by linarith [hp.2.2]
    have hcq : (0 : ℝ) < r * q.1 0 - q.2 0 := by linarith [hq.2.2]
    have h := (eu_crra_concave hγ).2 (show r * p.1 0 - p.2 0 ∈ Set.Ioi (0 : ℝ) from hcp)
      (show r * q.1 0 - q.2 0 ∈ Set.Ioi (0 : ℝ) from hcq) ha hb hab
    simp only [smul_eq_mul] at h
    simp only [eu_EulerModel.uu, eu_phelpsModel, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert h using 2
    ring
  -- the transversality condition (7.35)
  have htvc : (eu_phelpsModel γ β).TVC735 P R (eu_phelpsState R A x₀) := by
    have hlim := example_7_5_1_tvc (P := P) hγ hbm hbm1 hA hx₀ hR hRm hcm hI1 hI2
    have := hlim.const_mul (-(1 - A))
    rw [mul_zero] at this
    unfold eu_EulerModel.TVC735
    refine this.congr fun T => ?_
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [eu_dot, Fin.sum_univ_one, (hD T ω).2.2.1]
    simp only [eu_phelpsState, eu_phelpsModel]
    ring
  refine eu_EulerModel.eu_euler_sufficient hβ.1.le hplan hx C hcon (fun t ω => ⟨?_, ?_⟩)
    (fun t ω => (hD t ω).2.1)
    (example_7_5_1_euler hγ hbm hbm1 hA hx₀ hR hR0 hRm hcm hI1 hI3) (fun t ω i => ?_)
    (fun t ω i => ?_) hint htvc
  · refine ⟨(hst t ω).le, (hst (t + 1) ω).le, ?_⟩
    have := (hD t ω).1
    have := mul_pos hA01.1 (hcpos t ω)
    linarith
  · exact ⟨(hx.2.2 t ω).1, (hx.2.2 t ω).2⟩
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [(hD (t + 1) ω).2.2.2]
    exact mul_nonneg (Real.rpow_pos_of_pos (mul_pos hA01.1 (hcpos _ ω)) _).le (hR _ ω).le
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    exact (hx.2.2 (t + 1) ω).1

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The utility function of the consumption–saving problem

Copied from `EconomicDynamics/Applications` (module `CDUtility`), namespace renamed.

Miao, §8.3, p. 237: "the utility function `u` satisfies the usual conditions: `u′ > 0`,
`u′′ < 0`, `lim_{c→0} u′(c) = ∞`, and `lim_{c→∞} u′(c) = 0`."

`cd_Utility` records these conditions on `(0, ∞)`: `u` has derivative `du` there, `du > 0`,
`du` is strictly decreasing (the content of `u′′ < 0` that is used) and continuous, and the two
Inada limits hold. Consumption is strictly positive throughout this part (`u` may be `−∞` at
`0`, e.g. `log`); see the corrections file.

* `cd_tangent`, `cd_tangent_strict`: `u(c′) ≤ u(c) + u′(c)(c′ − c)`, strictly if `c′ ≠ c`.
* `cd_u_strictMono`, `cd_u_strictConcave`: `u` is strictly increasing and strictly concave.
* `cd_du_surj`, `cd_duInv`: `u′` maps `(0, ∞)` onto `(0, ∞)`; its inverse `(u′)⁻¹` is strictly
  decreasing and continuous (`cd_duInv_cont`), by monotonicity and surjectivity.
* `cd_crraUtility`: CRRA utility `c^{1−γ}/(1−γ)` (`log` at `γ = 1`), `γ > 0`, is a `cd_Utility`
  with `u′(c) = c^{−γ}`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, §8.3, p. 237: the "usual conditions" on the utility function, on `(0, ∞)`:
`u′ = du > 0`, `u′` strictly decreasing (`u′′ < 0`) and continuous, `u′(0+) = ∞`,
`u′(∞) = 0`. -/
structure cd_Utility where
  /-- The period utility function. -/
  u : ℝ → ℝ
  /-- Its derivative on `(0, ∞)`. -/
  du : ℝ → ℝ
  hasDerivAt : ∀ c, 0 < c → HasDerivAt u (du c) c
  du_pos : ∀ c, 0 < c → 0 < du c
  du_anti : StrictAntiOn du (Set.Ioi 0)
  du_cont : ContinuousOn du (Set.Ioi 0)
  inada_zero : Tendsto du (𝓝[>] 0) atTop
  inada_top : Tendsto du atTop (𝓝 0)

namespace cd_Utility

variable (U : cd_Utility)

/-- Miao, p. 237 (`u′′ < 0`): the tangent-line inequality `u(c′) ≤ u(c) + u′(c)(c′ − c)` for
`c, c′ > 0`, strict when `c′ ≠ c` (mean value theorem and `u′` strictly decreasing). -/
theorem cd_tangent_strict {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hne : c' ≠ c) :
    U.u c' < U.u c + U.du c * (c' - c) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hcont : ContinuousOn U.u (Set.Icc c' c) := fun z hz =>
      (U.hasDerivAt z (lt_of_lt_of_le hc' hz.1)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope U.u U.du h hcont
      (fun z hz => U.hasDerivAt z (lt_trans hc' hz.1))
    have hξ0 : 0 < ξ := lt_trans hc' hξ.1
    have hlt : U.du c < U.du ξ := U.du_anti (Set.mem_Ioi.2 hξ0) (Set.mem_Ioi.2 hc) hξ.2
    have hpos : 0 < c - c' := sub_pos.2 h
    have e : U.u c - U.u c' = U.du ξ * (c - c') := by
      rw [hξeq]; field_simp
    nlinarith
  · have hcont : ContinuousOn U.u (Set.Icc c c') := fun z hz =>
      (U.hasDerivAt z (lt_of_lt_of_le hc hz.1)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope U.u U.du h hcont
      (fun z hz => U.hasDerivAt z (lt_trans hc hz.1))
    have hξ0 : 0 < ξ := lt_trans hc hξ.1
    have hlt : U.du ξ < U.du c := U.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hξ0) hξ.1
    have hpos : 0 < c' - c := sub_pos.2 h
    have e : U.u c' - U.u c = U.du ξ * (c' - c) := by
      rw [hξeq]; field_simp
    nlinarith

/-- Miao, p. 237: the tangent-line inequality `u(c′) ≤ u(c) + u′(c)(c′ − c)` for `c, c′ > 0`. -/
theorem cd_tangent {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    U.u c' ≤ U.u c + U.du c * (c' - c) := by
  by_cases h : c' = c
  · subst h; simp
  · exact (U.cd_tangent_strict hc hc' h).le

/-- Miao, p. 237 (`u′ > 0`): `u` is strictly increasing on `(0, ∞)`. -/
theorem cd_u_strictMono : StrictMonoOn U.u (Set.Ioi 0) := by
  intro c hc c' hc' h
  have hc0 : (0 : ℝ) < c := hc
  have hc0' : (0 : ℝ) < c' := hc'
  have h1 := U.cd_tangent hc0' hc0
  have h2 := U.du_pos c' hc0'
  have : U.du c' * (c - c') < 0 := mul_neg_of_pos_of_neg h2 (sub_neg.2 h)
  linarith

/-- Miao, p. 237 (`u′′ < 0`): `u` is strictly concave on `(0, ∞)`. -/
theorem cd_u_strictConcave : StrictConcaveOn ℝ (Set.Ioi 0) U.u := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) ?_ ?_
  · exact fun z hz => (U.hasDerivAt z hz).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [(U.hasDerivAt a ha).deriv, (U.hasDerivAt b hb).deriv]
    exact U.du_anti ha hb hab

/-- Miao, p. 237 (Inada conditions): `u′` maps `(0, ∞)` onto `(0, ∞)`. -/
theorem cd_du_surj {v : ℝ} (hv : 0 < v) : ∃ c, 0 < c ∧ U.du c = v := by
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), v < U.du c := U.inada_zero.eventually_gt_atTop v
  have h1' : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c := self_mem_nhdsWithin
  obtain ⟨c₁, hc₁, hc₁0⟩ := (h1.and h1').exists
  have h2 : ∀ᶠ c in atTop, U.du c < v := U.inada_top.eventually (gt_mem_nhds hv)
  obtain ⟨c₂, hc₂, hc₂le⟩ := (h2.and (eventually_ge_atTop c₁)).exists
  have hcont : ContinuousOn U.du (Set.Icc c₁ c₂) := U.du_cont.mono fun z hz =>
    Set.mem_Ioi.2 (lt_of_lt_of_le hc₁0 hz.1)
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hc₂le hcont ⟨hc₂.le, hc₁.le⟩
  exact ⟨c, lt_of_lt_of_le hc₁0 hc.1, hcv⟩

/-- Miao, p. 241: the inverse `(u′)⁻¹` of marginal utility on `(0, ∞)` (junk value `1`
elsewhere). -/
noncomputable def cd_duInv (v : ℝ) : ℝ :=
  if h : 0 < v then Classical.choose (U.cd_du_surj h) else 1

/-- `(u′)⁻¹(v) > 0`. -/
theorem cd_duInv_pos (v : ℝ) : 0 < U.cd_duInv v := by
  unfold cd_duInv
  split_ifs with h
  · exact (Classical.choose_spec (U.cd_du_surj h)).1
  · exact one_pos

/-- `u′((u′)⁻¹(v)) = v` for `v > 0`. -/
theorem cd_du_duInv {v : ℝ} (hv : 0 < v) : U.du (U.cd_duInv v) = v := by
  simp only [cd_duInv, hv, ↓reduceDIte]
  exact (Classical.choose_spec (U.cd_du_surj hv)).2

/-- `u′` is injective on `(0, ∞)`. -/
theorem cd_du_inj {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (h : U.du c = U.du c') : c = c' :=
  U.du_anti.injOn hc hc' h

/-- `(u′)⁻¹(u′(c)) = c` for `c > 0`. -/
theorem cd_duInv_du {c : ℝ} (hc : 0 < c) : U.cd_duInv (U.du c) = c :=
  U.cd_du_inj (U.cd_duInv_pos _) hc (U.cd_du_duInv (U.du_pos c hc))

/-- `(u′)⁻¹` is strictly decreasing on `(0, ∞)`. -/
theorem cd_duInv_anti : StrictAntiOn U.cd_duInv (Set.Ioi 0) := by
  intro v hv v' hv' h
  have hv0 : (0 : ℝ) < v := hv
  have hv0' : (0 : ℝ) < v' := hv'
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := U.du_anti (Set.mem_Ioi.2 (U.cd_duInv_pos v)) (Set.mem_Ioi.2 (U.cd_duInv_pos v')) hlt
    rw [U.cd_du_duInv hv0, U.cd_du_duInv hv0'] at this
    linarith
  · have := congrArg U.du heq
    rw [U.cd_du_duInv hv0, U.cd_du_duInv hv0'] at this
    linarith

/-- `(u′)⁻¹` is continuous on `(0, ∞)`: it is monotone and maps `(0, ∞)` onto `(0, ∞)`. -/
theorem cd_duInv_cont : ContinuousOn U.cd_duInv (Set.Ioi 0) := by
  intro v hv
  have hv0 : (0 : ℝ) < v := hv
  have hmono : MonotoneOn (fun w => -U.cd_duInv w) (Set.Ioi 0) := fun a ha b hb hab => by
    rcases hab.lt_or_eq with h | h
    · exact neg_le_neg (U.cd_duInv_anti ha hb h).le
    · rw [h]
  have himage : (fun w => -U.cd_duInv w) '' Set.Ioi 0 = Set.Iio 0 := by
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩
      exact Set.mem_Iio.2 (neg_lt_zero.2 (U.cd_duInv_pos w))
    · intro hz
      have hz' : 0 < -z := neg_pos.2 hz
      refine ⟨U.du (-z), Set.mem_Ioi.2 (U.du_pos _ hz'), ?_⟩
      simp only [U.cd_duInv_du hz', neg_neg]
  have hc : ContinuousAt (fun w => -U.cd_duInv w) v := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ioi_mem_nhds hv0) ?_
    rw [himage]
    exact Iio_mem_nhds (neg_lt_zero.2 (U.cd_duInv_pos v))
  have : ContinuousAt U.cd_duInv v := by
    have h2 := hc.neg
    have e : (-fun w => -U.cd_duInv w) = U.cd_duInv := funext fun w => neg_neg _
    rw [e] at h2
    exact h2
  exact this.continuousWithinAt

end cd_Utility

/-- CRRA marginal utility `c^{−γ}` is strictly decreasing on `(0, ∞)` for `γ > 0`. -/
theorem cd_rpow_neg_strictAnti {γ : ℝ} (hγ : 0 < γ) :
    StrictAntiOn (fun c : ℝ => c ^ (-γ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact Real.rpow_lt_rpow_of_neg ha hab (neg_neg_of_pos hγ)

/-- Miao, p. 237 and Exercise 8.8: CRRA utility `c^{1−γ}/(1−γ)` (`log c` at `γ = 1`), `γ > 0`,
satisfies the usual conditions, with `u′(c) = c^{−γ}`. -/
noncomputable def cd_crraUtility {γ : ℝ} (hγ : 0 < γ) : cd_Utility where
  u := cs_crra γ
  du := fun c => c ^ (-γ)
  hasDerivAt := fun _ hc => eu_crra_hasDerivAt hc
  du_pos := fun _ hc => Real.rpow_pos_of_pos hc _
  du_anti := cd_rpow_neg_strictAnti hγ
  du_cont := fun _ hc =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hc))).continuousWithinAt
  inada_zero := tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hγ)
  inada_top := tendsto_rpow_neg_atTop hγ

/-- The CRRA instance has `u = cs_crra γ`. -/
theorem cd_crraUtility_u {γ : ℝ} (hγ : 0 < γ) : (cd_crraUtility hγ).u = cs_crra γ := rfl

/-- The CRRA instance has `u′(c) = c^{−γ}`. -/
theorem cd_crraUtility_du {γ : ℝ} (hγ : 0 < γ) (c : ℝ) : (cd_crraUtility hγ).du c = c ^ (-γ) :=
  rfl

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The consumption–saving problem: budget, no-Ponzi condition, natural debt limit

Copied from `EconomicDynamics/Applications` (module `CDBudget`), namespace renamed.

Miao, §8.3, pp. 237–239.

* `cd_Budget` is the budget constraint (8.3) `c_t + a_{t+1} = Ra_t + y_t`; `cd_NoPonzi` is the
  no-Ponzi-game condition (8.5), read as `liminf_T a_{T+1}/R^T ≥ 0` (the limit need not exist).
* `eq_8_6`: the present-value budget identity (8.6). `cd_rollover`: rolling over the debt
  `a_{T+1} = R^T a_1 < 0` violates (8.5).
* `theorem_8_3_1`: with `R > 1`, labour income in `[0, y_max]`, `c ≥ 0` and `a_{t+1} ≥ −b`, the
  limit in (8.5) exists and is `≥ 0`; `theorem_8_3_1_pv`: the present value of consumption is at
  most `Ra_0` plus that of income. These are pathwise, so they hold almost surely for a
  stochastic income process.
* The converse (a.s. `a_t ≥ −y_min/r`). As printed, with only "support `[y_min, y_max]`", it is
  false: `theorem_8_3_1_converse_counterexample` (constant income `y_max`, `a_t ≡ −y_max/r`). The
  book's proof also has a gap: from "for each `n`, with positive probability `a_{t+n}/R^n <
  −ε/2`" it concludes "with positive probability `lim a_{t+n}/R^n < 0`", which needs one event for
  all `n` (for i.i.d. income the event that income stays low forever is null). We prove the
  converse, `theorem_8_3_1_converse`, under the hypothesis that from any event of positive
  probability `{a_t < −y_min/r − ε}` income stays below `y_min + δ` for `N` periods with positive
  probability (true for i.i.d. income with `y_min` in the support), by truncating at `N` and
  bounding the tail by `y_max/(rR^N)` (`cd_converse_path`).
* `cd_natural_debt_nonbinding`: if `b > y_min/r` the borrowing constraint never binds.
* `cd_IsPath`, `cd_change_of_variables` (p. 239): `â_t = a_t + b`, `x_t = Ra_t + y_t + b` give
  `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`, `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0 ↔ a_{t+1} ≥ −b`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology MeasureTheory

/-- Miao, (8.3), p. 237: the budget constraint `c_t + a_{t+1} = Ra_t + y_t`. -/
def cd_Budget (R : ℝ) (y c a : ℕ → ℝ) : Prop := ∀ t, c t + a (t + 1) = R * a t + y t

/-- Miao, (8.5), p. 237: the no-Ponzi-game condition `lim_{T→∞} a_{T+1}/R^T ≥ 0`, read as
`liminf ≥ 0`: for every `ε > 0`, eventually `a_{T+1}/R^T ≥ −ε`. -/
def cd_NoPonzi (R : ℝ) (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ a (T + 1) / R ^ T

/-- Miao, (8.6), p. 238: `∑_{t≤T} c_t/R^t + a_{T+1}/R^T = Ra_0 + ∑_{t≤T} y_t/R^t`. -/
theorem eq_8_6 {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → ℝ} (h : cd_Budget R y c a) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / R ^ t + a (T + 1) / R ^ T =
      R * a 0 + ∑ t ∈ Finset.range (T + 1), y t / R ^ t := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, div_one]
    linarith [h 0]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun t => c t / R ^ t) (n + 1),
      Finset.sum_range_succ (fun t => y t / R ^ t) (n + 1)]
    have hn := h (n + 1)
    have hp : R ^ (n + 1) ≠ 0 := pow_ne_zero _ hR
    have e : c (n + 1) / R ^ (n + 1) + a (n + 1 + 1) / R ^ (n + 1) - a (n + 1) / R ^ n =
        y (n + 1) / R ^ (n + 1) := by
      rw [pow_succ]
      field_simp
      linarith
    linarith

/-- Miao, p. 238: rolling over the initial debt, `a_{T+1} = R^T a_1` with `a_1 < 0`, gives
`a_{T+1}/R^T = a_1 → a_1 < 0`, so (8.5) fails. -/
theorem cd_rollover {R : ℝ} (hR : 0 < R) {a : ℕ → ℝ} (h : ∀ T, a (T + 1) = R ^ T * a 1)
    (ha : a 1 < 0) :
    (∀ T, a (T + 1) / R ^ T = a 1) ∧ Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 (a 1)) ∧
      ¬ cd_NoPonzi R a := by
  have e : ∀ T, a (T + 1) / R ^ T = a 1 := fun T => by
    rw [h T]; field_simp
  refine ⟨e, ?_, ?_⟩
  · simp only [e]; exact tendsto_const_nhds
  · intro hNP
    obtain ⟨T, hT⟩ := (hNP (-a 1 / 2) (by linarith)).exists
    rw [e T] at hT
    linarith

/-- `y_t/R^t ≤ y_max ρ^t` with `ρ = R⁻¹`: the present value of bounded income is summable. -/
theorem cd_summable_pv {R ymax : ℝ} (hR : 1 < R) {y : ℕ → ℝ} (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) :
    Summable fun t => y t / R ^ t := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  refine Summable.of_nonneg_of_le (fun t => div_nonneg (hy t).1 (pow_nonneg (by linarith) _))
    (fun t => ?_) ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ymax)
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_right (hy t).2 (pow_nonneg hρ0 _)

/-- `b/R^T → 0` for `R > 1`. -/
theorem cd_tendsto_div_pow {R : ℝ} (hR : 1 < R) (b : ℝ) :
    Tendsto (fun T : ℕ => b / R ^ T) atTop (𝓝 0) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul b
  rw [mul_zero] at this
  refine this.congr fun T => ?_
  rw [div_eq_mul_inv, inv_pow]

/-- Miao, **Theorem 8.3.1** (first part), p. 238: if `R > 1`, income lies in `[0, y_max]`,
`c_t ≥ 0` and `a_{t+1} ≥ −b` for all `t`, then `lim a_{T+1}/R^T` exists and is `≥ 0`, so the
no-Ponzi-game condition (8.5) holds. The statement is pathwise, hence holds almost surely for a
stochastic income process with support in `[0, y_max]`. -/
theorem theorem_8_3_1 {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) :
    ∃ L, 0 ≤ L ∧ Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 L) ∧
      HasSum (fun t => c t / R ^ t) (R * a 0 + ∑' t, y t / R ^ t - L) := by
  have hR0 : (0 : ℝ) < R := by linarith
  set Hy := ∑' t, y t / R ^ t
  have hsy := cd_summable_pv hR hy
  have hy0 : ∀ t, 0 ≤ y t / R ^ t := fun t => div_nonneg (hy t).1 (pow_nonneg hR0.le _)
  have hc0 : ∀ t, 0 ≤ c t / R ^ t := fun t => div_nonneg (hc t) (pow_nonneg hR0.le _)
  set Sc : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), c t / R ^ t
  set Sy : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), y t / R ^ t
  have hSy : Tendsto Sy atTop (𝓝 Hy) :=
    hsy.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSyle : ∀ T, Sy T ≤ Hy := fun T => hsy.sum_le_tsum _ (fun t _ => hy0 t)
  have hid : ∀ T, a (T + 1) / R ^ T = R * a 0 + Sy T - Sc T := fun T => by
    have := eq_8_6 hR0.ne' hbud T
    simp only [Sy, Sc]; linarith
  have hlow : ∀ T, -b / R ^ T ≤ a (T + 1) / R ^ T := fun T =>
    div_le_div_of_nonneg_right (hbor T) (pow_nonneg hR0.le _)
  have hScmono : Monotone Sc := monotone_nat_of_le_succ fun T => by
    simp only [Sc, Finset.sum_range_succ (n := T + 1)]
    linarith [hc0 (T + 1)]
  have hRT : ∀ T, b / R ^ T ≤ b := fun T =>
    div_le_self hb (one_le_pow₀ hR.le)
  have hScle : ∀ T, Sc T ≤ R * a 0 + Hy + b := fun T => by
    have h1 := hid T
    have h2 := hlow T
    have h3 := hSyle T
    have h4 := hRT T
    rw [neg_div] at h2
    linarith
  have hbdd : BddAbove (Set.range Sc) := ⟨_, Set.forall_mem_range.2 hScle⟩
  set Lc := ⨆ T, Sc T
  have hSc : Tendsto Sc atTop (𝓝 Lc) := tendsto_atTop_ciSup hScmono hbdd
  refine ⟨R * a 0 + Hy - Lc, ?_, ?_, ?_⟩
  · have hlim : Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 (R * a 0 + Hy - Lc)) := by
      simp only [hid]
      exact (hSy.const_add _).sub hSc |>.congr fun T => by ring
    exact le_of_tendsto_of_tendsto' (cd_tendsto_div_pow hR (-b)) hlim hlow
  · simp only [hid]
    exact (hSy.const_add _).sub hSc |>.congr fun T => by ring
  · have e : R * a 0 + Hy - (R * a 0 + Hy - Lc) = Lc := by ring
    rw [e]
    refine (hasSum_iff_tendsto_nat_of_nonneg hc0 Lc).2 ?_
    have := hSc.comp (tendsto_sub_atTop_nat 1)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    simp only [Function.comp_apply, Sc, Nat.sub_add_cancel hT]

/-- Miao, **Theorem 8.3.1**, p. 238: the inequality `Ra_0 + ∑ y_t/R^t ≥ ∑ c_t/R^t` derived in
the proof (present value of consumption at most initial wealth plus that of income). -/
theorem theorem_8_3_1_pv {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) :
    Summable (fun t => c t / R ^ t) ∧ ∑' t, c t / R ^ t ≤ R * a 0 + ∑' t, y t / R ^ t := by
  obtain ⟨L, hL, -, hs⟩ := theorem_8_3_1 hR hb hy hc hbud hbor
  exact ⟨hs.summable, by rw [hs.tsum_eq]; linarith⟩

/-- Miao, **Theorem 8.3.1**: the first part gives the no-Ponzi-game condition (8.5). -/
theorem theorem_8_3_1_noPonzi {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) : cd_NoPonzi R a := by
  obtain ⟨L, hL, hlim, -⟩ := theorem_8_3_1 hR hb hy hc hbud hbor
  intro ε hε
  exact (hlim.eventually (Ioi_mem_nhds (show -ε < L by linarith))).mono fun T hT => le_of_lt hT

/-- The telescoping bound used in the proof of Theorem 8.3.1: if
`B_{k+1} ≤ B_k + Yρ^{k+1}` for `n₀ ≤ k < n₀ + m`, `ρ = R⁻¹`, `r = R − 1`, then
`B_{n₀+m} + Yρ^{n₀+m}/r ≤ B_{n₀} + Yρ^{n₀}/r`. -/
theorem cd_telescope {R Y : ℝ} (hR : 1 < R) {B : ℕ → ℝ} (n₀ m : ℕ)
    (h : ∀ k < m, B (n₀ + k + 1) ≤ B (n₀ + k) + Y * R⁻¹ ^ (n₀ + k + 1)) :
    B (n₀ + m) + Y * R⁻¹ ^ (n₀ + m) / (R - 1) ≤ B n₀ + Y * R⁻¹ ^ n₀ / (R - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := h m (Nat.lt_succ_self m)
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hr : (0 : ℝ) < R - 1 := by linarith
    have hR0 : R ≠ 0 := by linarith
    have e : Y * R⁻¹ ^ (n₀ + m + 1) + Y * R⁻¹ ^ (n₀ + m + 1) / (R - 1) =
        Y * R⁻¹ ^ (n₀ + m) / (R - 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [← add_assoc]
    linarith

/-- The pathwise step of the proof of Theorem 8.3.1 (converse), corrected. If `c ≥ 0`, income
lies in `[y_min, y_max]` with `y_min ≥ 0`, `a_t < −y_min/r − ε`, income stays below
`y_min + rε/4` for `N` periods from `t`, and `y_max/(rR^N) ≤ ε/4`, then (8.5) fails along the
path: `a_{t+n}/R^n < −ε/2` for every `n ≥ N`. -/
theorem cd_converse_path {R ymin ymax ε : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) (hε : 0 < ε)
    {y c a : ℕ → ℝ} (hy : ∀ t, ymin ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t)
    (hbud : cd_Budget R y c a) {t N : ℕ} (hat : a t < -ymin / (R - 1) - ε)
    (hlow : ∀ k < N, y (t + k) ≤ ymin + (R - 1) * ε / 4)
    (hN : ymax * R⁻¹ ^ N / (R - 1) ≤ ε / 4) :
    (∀ n, N ≤ n → a (t + n) / R ^ n < -ε / 2) ∧ ¬ cd_NoPonzi R a := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hr : (0 : ℝ) < R - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.2 hR0.le
  set B : ℕ → ℝ := fun n => a (t + n) / R ^ n
  have hymax : 0 ≤ ymax := le_trans hymin ((hy 0).1.trans (hy 0).2)
  have hstep : ∀ n, B (n + 1) ≤ B n + y (t + n) * R⁻¹ ^ (n + 1) := fun n => by
    simp only [B]
    have h1 := hbud (t + n)
    have h2 := hc (t + n)
    have e : t + (n + 1) = t + n + 1 := by omega
    rw [e]
    have hp : (0 : ℝ) < R ^ n := pow_pos hR0 n
    have key : a (t + n + 1) / R ^ (n + 1) =
        a (t + n) / R ^ n + y (t + n) / R ^ (n + 1) - c (t + n) / R ^ (n + 1) := by
      rw [show a (t + n + 1) = R * a (t + n) + y (t + n) - c (t + n) by linarith, pow_succ]
      field_simp
    rw [key, inv_pow, ← div_eq_mul_inv]
    have := div_nonneg h2 (pow_pos hR0 (n + 1)).le
    linarith
  -- first `N` periods: low income
  have h1 : B (0 + N) + (ymin + (R - 1) * ε / 4) * R⁻¹ ^ (0 + N) / (R - 1) ≤
      B 0 + (ymin + (R - 1) * ε / 4) * R⁻¹ ^ 0 / (R - 1) := by
    refine cd_telescope hR 0 N fun k hk => ?_
    have h3 := hstep k
    have hy' := hlow k hk
    have : y (t + k) * R⁻¹ ^ (k + 1) ≤ (ymin + (R - 1) * ε / 4) * R⁻¹ ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hy' (pow_nonneg hρ0 _)
    simp only [zero_add]
    linarith
  -- afterwards: income at most `y_max`
  have h2 : ∀ m, B (N + m) + ymax * R⁻¹ ^ (N + m) / (R - 1) ≤
      B N + ymax * R⁻¹ ^ N / (R - 1) := fun m => by
    refine cd_telescope hR N m fun k _ => ?_
    have h3 := hstep (N + k)
    have : y (t + (N + k)) * R⁻¹ ^ (N + k + 1) ≤ ymax * R⁻¹ ^ (N + k + 1) :=
      mul_le_mul_of_nonneg_right (hy _).2 (pow_nonneg hρ0 _)
    linarith
  have hB0 : B 0 = a t := by simp [B]
  simp only [zero_add, pow_zero, mul_one] at h1
  have hlowpos : 0 ≤ (ymin + (R - 1) * ε / 4) * R⁻¹ ^ N / (R - 1) :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg hρ0 _)) hr.le
  have hmid : (ymin + (R - 1) * ε / 4) / (R - 1) = ymin / (R - 1) + ε / 4 := by
    field_simp
  have hbound : ∀ n, N ≤ n → B n < -ε / 2 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h3 := h2 m
    have h4 : 0 ≤ ymax * R⁻¹ ^ (N + m) / (R - 1) :=
      div_nonneg (mul_nonneg hymax (pow_nonneg hρ0 _)) hr.le
    rw [hB0, hmid] at h1
    have : -ymin / (R - 1) = -(ymin / (R - 1)) := neg_div _ _
    linarith
  refine ⟨hbound, fun hNP => ?_⟩
  -- `a_{T+1}/R^T = B_n · R/R^t` with `T + 1 = t + n`
  set η : ℝ := ε / 2 * (R / R ^ t)
  have hη : 0 < η := by positivity
  obtain ⟨T, hT, hTN⟩ := ((hNP (η / 2) (by linarith)).and (eventually_ge_atTop (t + N))).exists
  obtain ⟨n, hn⟩ : ∃ n, T + 1 = t + n := ⟨T + 1 - t, by omega⟩
  have hnN : N ≤ n := by omega
  have hrel : a (T + 1) / R ^ T = B n * (R / R ^ t) := by
    simp only [B]
    rw [hn]
    have hpow : R ^ T * R = R ^ t * R ^ n := by rw [← pow_succ, ← pow_add, hn]
    have h5 : R ^ T ≠ 0 := pow_ne_zero _ hR0.ne'
    have h6 : R ^ t ≠ 0 := pow_ne_zero _ hR0.ne'
    have h7 : R ^ n ≠ 0 := pow_ne_zero _ hR0.ne'
    field_simp
    linear_combination (-a (t + n)) * hpow
  rw [hrel] at hT
  have h8 := hbound n hnN
  have h9 : 0 < R / R ^ t := by positivity
  have : B n * (R / R ^ t) < -ε / 2 * (R / R ^ t) := mul_lt_mul_of_pos_right h8 h9
  simp only [η] at hT
  nlinarith

/-- Miao, **Theorem 8.3.1** (converse), p. 238, corrected. Let income `y_t(ω) ∈ [y_min, y_max]`,
`y_min ≥ 0`, `c ≥ 0`, the budget (8.3) hold pathwise and (8.5) hold almost surely. Suppose the
income process can stay low after any event of positive probability: whenever
`{a_t < −y_min/r − ε}` has positive probability, so does its intersection with
`{y_{t+k} ≤ y_min + δ for k < N}` (`δ > 0`, any `N`). Then `a_t ≥ −y_min/r` almost surely. -/
theorem theorem_8_3_1_converse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {R ymin ymax : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) {y c a : ℕ → Ω → ℝ}
    (hy : ∀ t ω, ymin ≤ y t ω ∧ y t ω ≤ ymax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, cd_Budget R (fun t => y t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi R (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -ymin / (R - 1) - ε} →
      0 < μ ({ω | a t ω < -ymin / (R - 1) - ε} ∩ {ω | ∀ k < N, y (t + k) ω ≤ ymin + δ})) :
    ∀ t, ∀ᵐ ω ∂μ, -ymin / (R - 1) ≤ a t ω := by
  intro t
  have hr : (0 : ℝ) < R - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hnull : μ {ω | ¬ cd_NoPonzi R (fun t => a t ω)} = 0 := ae_iff.1 hNP
  have hE : ∀ ε : ℝ, 0 < ε → μ {ω | a t ω < -ymin / (R - 1) - ε} = 0 := by
    intro ε hε
    by_contra hne
    have hpos : 0 < μ {ω | a t ω < -ymin / (R - 1) - ε} := pos_iff_ne_zero.2 hne
    -- choose `N` with `y_max ρ^N / r ≤ ε/4`
    have hlim : Tendsto (fun N : ℕ => |ymax| * R⁻¹ ^ N / (R - 1)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul |ymax|).div_const
        (R - 1)
      simpa using this
    obtain ⟨N, hN⟩ := (hlim.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))).exists
    have hN' : ymax * R⁻¹ ^ N / (R - 1) ≤ ε / 4 := by
      refine le_trans ?_ hN
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hρ0 _)) hr.le
    have hpos' := hsupp t ε ((R - 1) * ε / 4) N hε (by positivity) hpos
    have hsub : {ω | a t ω < -ymin / (R - 1) - ε} ∩
        {ω | ∀ k < N, y (t + k) ω ≤ ymin + (R - 1) * ε / 4} ⊆
        {ω | ¬ cd_NoPonzi R (fun t => a t ω)} := by
      rintro ω ⟨h1, h2⟩
      exact (cd_converse_path hR hymin hε (fun t => hy t ω) (fun t => hc t ω) (hbud ω) h1 h2
        hN').2
    exact (measure_mono_null hsub hnull ▸ hpos').false
  rw [ae_iff]
  have hcover : {ω | ¬ -ymin / (R - 1) ≤ a t ω} ⊆
      ⋃ n : ℕ, {ω | a t ω < -ymin / (R - 1) - 1 / ((n : ℝ) + 1)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_le] at hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hω)
    exact Set.mem_iUnion.2 ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n => hE _ Nat.one_div_pos_of_nat)

/-- Miao, **Theorem 8.3.1** (converse), p. 238: counterexample to the statement as printed.
With income in `[y_min, y_max]`, `y_min < y_max`, but constant at `y_max` (so the stated
support condition alone does not exclude it), the plan `c_t = 0`, `a_t = −y_max/r` satisfies the
budget (8.3) and (8.5), yet `a_t < −y_min/r`. (A Dirac measure turns it into a stochastic
counterexample.) -/
theorem theorem_8_3_1_converse_counterexample {R ymin ymax : ℝ} (hR : 1 < R)
    (hlt : ymin < ymax) :
    ∃ y c a : ℕ → ℝ, (∀ t, ymin ≤ y t ∧ y t ≤ ymax) ∧ (∀ t, 0 ≤ c t) ∧ cd_Budget R y c a ∧
      cd_NoPonzi R a ∧ ∀ t, a t < -ymin / (R - 1) := by
  have hr : (0 : ℝ) < R - 1 := by linarith
  refine ⟨fun _ => ymax, fun _ => 0, fun _ => -ymax / (R - 1), fun _ => ⟨hlt.le, le_rfl⟩,
    fun _ => le_rfl, fun t => ?_, fun ε hε => ?_, fun t => ?_⟩
  · field_simp; ring
  · have := cd_tendsto_div_pow hR (-ymax / (R - 1))
    exact (this.eventually (Ioi_mem_nhds (show -ε < 0 by linarith))).mono fun T hT => le_of_lt hT
  · exact div_lt_div_of_pos_right (neg_lt_neg hlt) hr

/-- Miao, p. 239: if `b > y_min/r` the borrowing constraint `a_{t+1} ≥ −b` never binds: under the
hypotheses of `theorem_8_3_1_converse`, `a_{t+1} > −b` almost surely. -/
theorem cd_natural_debt_nonbinding {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {R ymin ymax b : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) {y c a : ℕ → Ω → ℝ}
    (hy : ∀ t ω, ymin ≤ y t ω ∧ y t ω ≤ ymax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, cd_Budget R (fun t => y t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi R (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -ymin / (R - 1) - ε} →
      0 < μ ({ω | a t ω < -ymin / (R - 1) - ε} ∩ {ω | ∀ k < N, y (t + k) ω ≤ ymin + δ}))
    (hb : ymin / (R - 1) < b) : ∀ t, ∀ᵐ ω ∂μ, -b < a (t + 1) ω := by
  intro t
  filter_upwards [theorem_8_3_1_converse μ hR hymin hy hc hbud hNP hsupp (t + 1)] with ω hω
  rw [neg_div] at hω
  linarith

/-- Miao, p. 239: a consumption plan `c` and a cash-on-hand path `x` from `x₀` in the
redefined variables: `x_0 = x₀`, `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb` with `r = R − 1`. The
saving `â_{t+1}` is `x_t − c_t`. -/
def cd_IsPath (R b : ℝ) (y : ℕ → ℝ) (x₀ : ℝ) (c x : ℕ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t, x (t + 1) = R * (x t - c t) + y (t + 1) - (R - 1) * b

/-- Miao, p. 239: the change of variables `â_t = a_t + b`, `x_t = Ra_t + y_t + b` turns the
budget (8.3) and the borrowing constraint `a_{t+1} ≥ −b` into `x_{t+1} = R(x_t − c_t) + y_{t+1}
− rb`, `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0`; and `x_t ≥ y_t − rb` whenever `a_t ≥ −b`. -/
theorem cd_change_of_variables {R b : ℝ} (hR : 0 ≤ R) {y c a : ℕ → ℝ}
    (h : cd_Budget R y c a) :
    cd_IsPath R b y (R * a 0 + y 0 + b) c (fun t => R * a t + y t + b) ∧
      (∀ t, c t + (a (t + 1) + b) = R * a t + y t + b) ∧
      (∀ t, 0 ≤ a (t + 1) + b ↔ -b ≤ a (t + 1)) ∧
      ∀ t, -b ≤ a t → y t - (R - 1) * b ≤ R * a t + y t + b := by
  refine ⟨⟨rfl, fun t => ?_⟩, fun t => by linarith [h t], fun t => ?_, fun t ht => ?_⟩
  · have := h t
    linear_combination R * this
  · constructor <;> intro h' <;> linarith
  · nlinarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §8.3.2: the income-fluctuation problem with iid income, in cash on hand

Copied from `EconomicDynamics/Applications` (module `SIModel`), namespace renamed.

Miao, §8.3, pp. 237–240, and §8.3.2, pp. 249–250. The consumer maximises `E Σ βᵗ u(c_t)`
subject to `c_t + a_{t+1} = R a_t + y_t`, `a_{t+1} ≥ −b`; labour income `y_t` is iid with law
`μ` supported in `[y_min, y_max]`. With `r = R − 1`, `â_{t+1} = a_{t+1} + b` and cash on hand
`x_t = R a_t + y_t + b` (p. 239) the constraints become `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0` and
`x_{t+1} = R â_{t+1} + y_{t+1} − rb` (`SIModel.next`, `si_cash_on_hand`). Cash on hand never
falls below `x_min = y_min − rb` (`SIModel.next_ge`).

* `SIModel`: the primitives `(β, R, b, y_min, y_max, μ, u, u′)` with the book's standing
  hypotheses: `β ∈ (0, 1)`, `u′ > 0`, `u′` strictly decreasing (`u′′ < 0`) and continuous,
  `u′(0+) = ∞`, `u′(∞) = 0`, and `b < y_min/r`, i.e. `x_min > 0` (p. 239).
* `SIModel.Solution`: what the book assumes on p. 240: a solution `V` of the Bellman equation
  `V(x) = max_{â ∈ [0, x]} u(x − â) + β E V(Râ + y − rb)` (attained at the saving policy `â(x)`)
  which is strictly increasing, strictly concave and continuously differentiable, with the
  envelope condition `V′(x) = u′(c(x))`, `c(x) = x − â(x)`.
* The tools used throughout: `dV_strictAnti` (`V′` is strictly decreasing), the mean value
  bounds `tangent_V`, `SIModel.tangent_u`, integrability of `V` and `V′` along next period's cash on
  hand, the continuation value `W(s) = E V(Rs + y − rb)` and its marginal value
  `D(s) = E V′(Rs + y − rb)` with `R(s′ − s)D(s′) ≤ W(s′) − W(s) ≤ R(s′ − s)D(s)`
  (`W_sub_bounds`), `D` strictly decreasing (`D_strictAnti`) and continuous (`D_continuousOn`).

**Departures.** (1) `u` is real-valued and continuous at `0` (consumption `c = 0` is feasible),
which excludes the logarithm, as in §6.6.2. (2) "`V` is continuously differentiable" is taken
on `[x_min, ∞)` with `V` differentiable (two-sided) at every `x ≥ x_min`; the marginal value
`E V′(y − rb)` at a binding constraint involves `V′(x_min)`. (3) The book's `R > 1` is replaced
by `R > 0` (Lemma 8.3.1 is stated for `R > 0`); none of the results below needs `R > 1`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

/-- The **income-fluctuation problem** of Miao §8.3.2 (pp. 237–240, 249): discount factor `β`,
gross interest rate `R`, borrowing limit `b`, iid income with law `μ` supported in
`[y_min, y_max]`, utility `u` with derivative `du = u′` on `(0, ∞)`. -/
structure SIModel where
  β : ℝ
  R : ℝ
  b : ℝ
  ymin : ℝ
  ymax : ℝ
  μ : ProbabilityMeasure ℝ
  u : ℝ → ℝ
  du : ℝ → ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  R_pos : 0 < R
  b_nonneg : 0 ≤ b
  ymin_le_ymax : ymin ≤ ymax
  supp : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Set.Icc ymin ymax
  xmin_pos : 0 < ymin - (R - 1) * b
  u_cont : ContinuousOn u (Set.Ici 0)
  hasDerivAt_u : ∀ c, 0 < c → HasDerivAt u (du c) c
  du_pos : ∀ c, 0 < c → 0 < du c
  du_anti : StrictAntiOn du (Set.Ioi 0)
  du_cont : ContinuousOn du (Set.Ioi 0)
  inada_zero : Tendsto du (𝓝[>] 0) atTop
  inada_top : Tendsto du atTop (𝓝 0)

/-- Miao, p. 239: with `x_t = R a_t + y_t + b`, `â_{t+1} = a_{t+1} + b` and `r = R − 1`, the
budget `c_t + a_{t+1} = R a_t + y_t` becomes `c_t + â_{t+1} = x_t` and
`x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`; the borrowing limit `a_{t+1} ≥ −b` is `â_{t+1} ≥ 0`. -/
theorem si_cash_on_hand (R b a a' y y' c : ℝ) (hbud : c + a' = R * a + y) :
    c + (a' + b) = R * a + y + b ∧
      R * a' + y' + b = R * ((R * a + y + b) - c) + y' - (R - 1) * b ∧
      (-b ≤ a' ↔ 0 ≤ a' + b) := by
  refine ⟨by linarith, ?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have : a' = R * a + y - c := by linarith
  subst this
  ring

/-- The mean value bounds for `u` (`u′` decreasing): for `0 ≤ c < c′`,
`u′(c′)(c′ − c) ≤ u(c′) − u(c)`, and if `c > 0` also `u(c′) − u(c) ≤ u′(c)(c′ − c)`. -/
theorem SIModel.tangent_u (M : SIModel) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    M.du c' * (c' - c) ≤ M.u c' - M.u c ∧ (0 < c → M.u c' - M.u c ≤ M.du c * (c' - c)) := by
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope M.u M.du hcc
    (M.u_cont.mono fun z hz => Set.mem_Ici.2 (hc.trans hz.1))
    (fun z hz => M.hasDerivAt_u z (hc.trans_lt hz.1))
  have hpos : 0 < c' - c := sub_pos.2 hcc
  have heq : M.u c' - M.u c = M.du ξ * (c' - c) := by
    rw [hslope]; field_simp
  have hξ0 : 0 < ξ := hc.trans_lt hξ.1
  refine ⟨?_, fun hc0 => ?_⟩
  · rw [heq]
    exact mul_le_mul_of_nonneg_right
      (M.du_anti.antitoneOn (Set.mem_Ioi.2 hξ0) (Set.mem_Ioi.2 (hξ0.trans hξ.2)) hξ.2.le) hpos.le
  · rw [heq]
    exact mul_le_mul_of_nonneg_right
      (M.du_anti.antitoneOn (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 hξ0) hξ.1.le) hpos.le

/-- A strictly positive integrand has a strictly positive integral under a probability
measure. -/
theorem si_integral_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ y ∂μ, 0 < f y) : 0 < ∫ y, f y ∂μ := by
  have hnn : 0 ≤ᵐ[μ] f := hpos.mono fun y hy => hy.le
  rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
  · exact h
  · have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hf).1 h.symm
    obtain ⟨y, hy1, hy2⟩ := (hpos.and h0).exists
    simp only [Pi.zero_apply] at hy2
    linarith

namespace SIModel

variable (M : SIModel)

/-- The law of income as a measure. -/
abbrev law : Measure ℝ := (M.μ : Measure ℝ)

/-- The net interest rate `r = R − 1`. -/
def r : ℝ := M.R - 1

/-- The lowest cash on hand `x_min = y_min − rb` (Miao, p. 249). -/
def xmin : ℝ := M.ymin - M.r * M.b

/-- Next period's cash on hand `x′ = Rs + y − rb` after saving `s = â` and income `y`. -/
def next (s y : ℝ) : ℝ := M.R * s + y - M.r * M.b

theorem xmin_pos' : 0 < M.xmin := M.xmin_pos

theorem next_ge {s y : ℝ} (hs : 0 ≤ s) (hy : M.ymin ≤ y) : M.xmin ≤ M.next s y := by
  have := mul_nonneg M.R_pos.le hs
  simp only [next, xmin]
  linarith

theorem next_sub (s s' y : ℝ) : M.next s' y - M.next s y = M.R * (s' - s) := by
  simp only [next]; ring

theorem continuous_next (y : ℝ) : Continuous fun s => M.next s y := by
  simp only [next]; fun_prop

theorem continuous_next_y (s : ℝ) : Continuous fun y => M.next s y := by
  simp only [next]; fun_prop

/-- Almost surely, `x_min ≤ Rs + y − rb ≤ Rs + y_max − rb`. -/
theorem ae_next {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ y ∂M.law, M.xmin ≤ M.next s y ∧ M.next s y ≤ M.next s M.ymax := by
  filter_upwards [M.supp] with y hy
  exact ⟨M.next_ge hs hy.1, by simp only [next]; linarith [hy.2]⟩

/-- A function continuous on `[x_min, ∞)` is integrable along next period's cash on hand. -/
theorem integrable_comp {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici M.xmin)) {s : ℝ}
    (hs : 0 ≤ s) : Integrable (fun y => f (M.next s y)) M.law := by
  set g : ℝ → ℝ := f ∘ fun z => max z M.xmin
  have hg : Continuous g :=
    hf.comp_continuous (continuous_id.max continuous_const)
      fun z => Set.mem_Ici.2 (le_max_right _ _)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := M.xmin) (b := M.next s M.ymax)).exists_bound_of_continuousOn
      (hf.mono Set.Icc_subset_Ici_self)
  have heq : (fun y => g (M.next s y)) =ᵐ[M.law] fun y => f (M.next s y) := by
    filter_upwards [M.ae_next hs] with y hy
    simp only [g, Function.comp_apply, max_eq_left hy.1]
  refine Integrable.of_bound ((hg.comp (M.continuous_next_y s)).aestronglyMeasurable.congr heq) C ?_
  filter_upwards [M.ae_next hs] with y hy
  exact hC _ hy

/-- A **solution** of the problem as assumed in Miao, p. 240: a value function `V` with
derivative `dV = V′` and saving policy `sav = â` that solves the Bellman equation (the maximum is
attained at `â(x)`), strictly increasing, strictly concave and continuously differentiable on
`[x_min, ∞)`, with the envelope condition `V′(x) = u′(x − â(x))`. -/
structure Solution where
  V : ℝ → ℝ
  dV : ℝ → ℝ
  sav : ℝ → ℝ
  hasDerivAt_V : ∀ x, M.xmin ≤ x → HasDerivAt V (dV x) x
  dV_cont : ContinuousOn dV (Set.Ici M.xmin)
  V_mono : StrictMonoOn V (Set.Ici M.xmin)
  V_concave : StrictConcaveOn ℝ (Set.Ici M.xmin) V
  sav_mem : ∀ x, M.xmin ≤ x → sav x ∈ Set.Icc 0 x
  bellman : ∀ x, M.xmin ≤ x → V x = M.u (x - sav x) + M.β * ∫ y, V (M.next (sav x) y) ∂M.law
  bellman_le : ∀ x, M.xmin ≤ x → ∀ s ∈ Set.Icc 0 x,
    M.u (x - s) + M.β * ∫ y, V (M.next s y) ∂M.law ≤ V x
  envelope : ∀ x, M.xmin ≤ x → dV x = M.du (x - sav x)

namespace Solution

variable {M} (S : M.Solution)

/-- The consumption policy `c(x) = x − â(x)`. -/
def cons (x : ℝ) : ℝ := x - S.sav x

/-- The continuation value `W(s) = E V(Rs + y − rb)`. -/
noncomputable def W (s : ℝ) : ℝ := ∫ y, S.V (M.next s y) ∂M.law

/-- The expected marginal value `D(s) = E V′(Rs + y − rb)`. -/
noncomputable def D (s : ℝ) : ℝ := ∫ y, S.dV (M.next s y) ∂M.law

theorem V_contOn : ContinuousOn S.V (Set.Ici M.xmin) :=
  fun x hx => (S.hasDerivAt_V x hx).continuousAt.continuousWithinAt

/-- `V′` is strictly decreasing on `[x_min, ∞)` (strict concavity). -/
theorem dV_strictAnti : StrictAntiOn S.dV (Set.Ici M.xmin) := by
  intro a ha c hc hac
  have h := S.V_concave.strictAntiOn_deriv (fun x hx => (S.hasDerivAt_V x hx).differentiableAt)
    ha hc hac
  rwa [(S.hasDerivAt_V a ha).deriv, (S.hasDerivAt_V c hc).deriv] at h

/-- `V′ ≥ 0` on `[x_min, ∞)` (`V` is increasing). -/
theorem dV_nonneg {x : ℝ} (hx : M.xmin ≤ x) : 0 ≤ S.dV x := by
  have h := (hasDerivAt_iff_tendsto_slope.1 (S.hasDerivAt_V x hx)).mono_left
    (nhdsGT_le_nhdsNE x)
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.2 (S.V_mono.monotoneOn (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (hx.trans (Set.mem_Ioi.1 hz).le)) (Set.mem_Ioi.1 hz).le))
    (sub_pos.2 (Set.mem_Ioi.1 hz)).le

/-- The mean value bounds for `V`: for `x_min ≤ z ≤ z′`,
`V′(z′)(z′ − z) ≤ V(z′) − V(z) ≤ V′(z)(z′ − z)`. -/
theorem tangent_V {z z' : ℝ} (hz : M.xmin ≤ z) (hzz : z ≤ z') :
    S.dV z' * (z' - z) ≤ S.V z' - S.V z ∧ S.V z' - S.V z ≤ S.dV z * (z' - z) := by
  rcases hzz.lt_or_eq with hlt | heq
  · obtain ⟨ξ, hξm, hslope⟩ := exists_hasDerivAt_eq_slope S.V S.dV hlt
      (S.V_contOn.mono fun w hw => Set.mem_Ici.2 (hz.trans hw.1))
      (fun w hw => S.hasDerivAt_V w (hz.trans hw.1.le))
    have hpos : 0 < z' - z := sub_pos.2 hlt
    have heq : S.V z' - S.V z = S.dV ξ * (z' - z) := by
      rw [hslope]; field_simp
    have hξ : M.xmin ≤ ξ := hz.trans hξm.1.le
    rw [heq]
    refine ⟨mul_le_mul_of_nonneg_right (S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hξ)
      (Set.mem_Ici.2 (hz.trans hlt.le)) hξm.2.le) hpos.le,
      mul_le_mul_of_nonneg_right (S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hz)
      (Set.mem_Ici.2 hξ) hξm.1.le) hpos.le⟩
  · subst heq; simp

theorem integrable_V {s : ℝ} (hs : 0 ≤ s) : Integrable (fun y => S.V (M.next s y)) M.law :=
  M.integrable_comp S.V_contOn hs

theorem integrable_dV {s : ℝ} (hs : 0 ≤ s) : Integrable (fun y => S.dV (M.next s y)) M.law :=
  M.integrable_comp S.dV_cont hs

/-- `R(s′ − s)D(s′) ≤ W(s′) − W(s) ≤ R(s′ − s)D(s)` for `0 ≤ s ≤ s′`. -/
theorem W_sub_bounds {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    M.R * (s' - s) * S.D s' ≤ S.W s' - S.W s ∧ S.W s' - S.W s ≤ M.R * (s' - s) * S.D s := by
  have hs' : 0 ≤ s' := hs.trans hss
  have hR := M.R_pos
  have hsub : S.W s' - S.W s = ∫ y, (S.V (M.next s' y) - S.V (M.next s y)) ∂M.law :=
    (integral_sub (S.integrable_V hs') (S.integrable_V hs)).symm
  have hD : ∀ t, M.R * (s' - s) * S.D t = ∫ y, S.dV (M.next t y) * (M.R * (s' - s)) ∂M.law :=
    fun t => by rw [integral_mul_const, D, mul_comm]
  have hle : ∀ᵐ y ∂M.law, M.xmin ≤ M.next s y ∧ M.next s y ≤ M.next s' y := by
    filter_upwards [M.ae_next hs] with y hy
    refine ⟨hy.1, ?_⟩
    have := M.next_sub s s' y
    nlinarith
  rw [hsub, hD, hD]
  constructor
  · refine integral_mono_ae ((S.integrable_dV hs').mul_const _)
      ((S.integrable_V hs').sub (S.integrable_V hs)) ?_
    filter_upwards [hle] with y hy
    have := (S.tangent_V hy.1 hy.2).1
    rwa [M.next_sub] at this
  · refine integral_mono_ae ((S.integrable_V hs').sub (S.integrable_V hs))
      ((S.integrable_dV hs).mul_const _) ?_
    filter_upwards [hle] with y hy
    have := (S.tangent_V hy.1 hy.2).2
    rwa [M.next_sub] at this

/-- `D(s) ≤ V′(x_min)`. -/
theorem D_le {s : ℝ} (hs : 0 ≤ s) : S.D s ≤ S.dV M.xmin := by
  have : S.D s ≤ ∫ _y, S.dV M.xmin ∂M.law := by
    refine integral_mono_ae (S.integrable_dV hs) (integrable_const _) ?_
    filter_upwards [M.ae_next hs] with y hy
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1) hy.1
  simpa using this

/-- `D(s) ≥ 0`. -/
theorem D_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ S.D s := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.dV_nonneg hy.1

/-- `D` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem D_strictAnti : StrictAntiOn S.D (Set.Ici 0) := by
  intro s hs s' hs' hss
  have hs0 : (0 : ℝ) ≤ s := hs
  have hs'0 : (0 : ℝ) ≤ s' := hs'
  have hpos : 0 < ∫ y, (S.dV (M.next s y) - S.dV (M.next s' y)) ∂M.law := by
    refine si_integral_pos ((S.integrable_dV hs0).sub (S.integrable_dV hs'0)) ?_
    filter_upwards [M.ae_next hs0] with y hy
    have hlt : M.next s y < M.next s' y := by
      have := M.next_sub s s' y
      have := mul_pos M.R_pos (sub_pos.2 hss)
      linarith
    exact sub_pos.2 (S.dV_strictAnti (Set.mem_Ici.2 hy.1) (Set.mem_Ici.2 (hy.1.trans hlt.le)) hlt)
  rw [integral_sub (S.integrable_dV hs0) (S.integrable_dV hs'0)] at hpos
  change S.D s' < S.D s
  simp only [D]
  linarith

/-- `D` is continuous on `[0, ∞)` (dominated convergence, `0 ≤ V′ ≤ V′(x_min)`). -/
theorem D_continuousOn : ContinuousOn S.D (Set.Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => S.dV M.xmin)
    (fun s hs => (S.integrable_dV hs).aestronglyMeasurable) (fun s hs => ?_)
    (integrable_const _) ?_
  · filter_upwards [M.ae_next hs] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (S.dV_nonneg hy.1)]
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1) hy.1
  · filter_upwards [M.supp] with y hy
    exact S.dV_cont.comp (M.continuous_next y).continuousOn
      fun s hs => Set.mem_Ici.2 (M.next_ge hs hy.1)

end Solution

end SIModel

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §8.3.2: interior consumption and the Euler inequality from the Bellman equation

Copied from `EconomicDynamics/Applications` (module `SIEuler`), namespace renamed.

Miao, §8.3, p. 239, (8.7), in the stationary form used in §8.3.2 (pp. 249–259). For a solution
`(V, â)` of the Bellman equation (`SIModel.Solution`), and every `x ≥ x_min`:

* `cons_pos`: **consumption is interior**, `c(x) = x − â(x) > 0` (the Inada condition
  `u′(0+) = ∞` against the bounded marginal continuation value `βR V′(x_min)`);
* `euler`: **the Euler inequality** `u′(c(x)) ≥ βR E V′(Râ(x) + y − rb)`, with equality if
  `â(x) > 0`; it is derived from the maximisation in the Bellman equation by one-sided
  difference quotients (mean value bounds for `u` and `V`, continuity of `D`), not assumed;
* `eq_8_7`: the same with `E V′(x′) = E u′(c(x′))` (envelope condition): this is (8.7),
  `u′(c_t) ≥ βR E_t u′(c_{t+1})`, with equality if `â_{t+1} > 0`;
* `dV_pos`, `D_pos`: `V′ > 0` and `D > 0`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

theorem cons_eq (x : ℝ) : S.cons x = x - S.sav x := rfl

/-- The Bellman objective at the optimum: `V(x) = u(c(x)) + βW(â(x))`. -/
theorem bellman' {x : ℝ} (hx : M.xmin ≤ x) : S.V x = M.u (x - S.sav x) + M.β * S.W (S.sav x) :=
  S.bellman x hx

/-- The Bellman inequality: `u(x − s) + βW(s) ≤ V(x)` for `s ∈ [0, x]`. -/
theorem bellman_le' {x : ℝ} (hx : M.xmin ≤ x) {s : ℝ} (hs : s ∈ Set.Icc 0 x) :
    M.u (x - s) + M.β * S.W s ≤ S.V x :=
  S.bellman_le x hx s hs

/-- **Consumption is interior** (Miao, p. 240): `c(x) = x − â(x) > 0` for `x ≥ x_min`. -/
theorem cons_pos {x : ℝ} (hx : M.xmin ≤ x) : 0 < S.cons x := by
  have hx0 : 0 < x := M.xmin_pos.trans_le hx
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  rw [cons_eq]
  rcases hsx.lt_or_eq with hlt | heq
  · exact sub_pos.2 hlt
  exfalso
  set K := M.β * M.R * S.dV M.xmin
  obtain ⟨c, hcK, hc⟩ : ∃ c, K < M.du c ∧ c ∈ Set.Ioo 0 x :=
    ((M.inada_zero.eventually (eventually_gt_atTop K)).and (Ioo_mem_nhdsGT hx0)).exists
  have hsmem : x - c ∈ Set.Icc 0 x := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hle := S.bellman_le' hx hsmem
  rw [S.bellman' hx, heq, sub_self, show x - (x - c) = c by ring] at hle
  have hW := (S.W_sub_bounds hsmem.1 hsmem.2).2
  rw [show x - (x - c) = c by ring] at hW
  have hD := S.D_le hsmem.1
  have hu := (M.tangent_u le_rfl hc.1).1
  rw [sub_zero] at hu
  have hβ := M.β_pos
  have hR := M.R_pos
  have e1 : M.β * (S.W x - S.W (x - c)) ≤ M.β * (M.R * c * S.dV M.xmin) := by
    refine mul_le_mul_of_nonneg_left (hW.trans ?_) hβ.le
    exact mul_le_mul_of_nonneg_left hD (mul_nonneg hR.le hc.1.le)
  have e2 : c * K < c * M.du c := mul_lt_mul_of_pos_left hcK hc.1
  have e3 : c * K = M.β * (M.R * c * S.dV M.xmin) := by simp only [K]; ring
  nlinarith

/-- The Euler inequality from right difference quotients: `βR D(â(x)) ≤ u′(c(x))`. -/
theorem euler_le {x : ℝ} (hx : M.xmin ≤ x) : M.β * M.R * S.D (S.sav x) ≤ M.du (S.cons x) := by
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  have hc := S.cons_pos hx
  rw [cons_eq] at hc ⊢
  set s₀ := S.sav x
  have hsx' : s₀ < x := by linarith
  have hβ := M.β_pos
  have hV := S.bellman' hx
  have hduc : ContinuousAt (fun s => M.du (x - s)) s₀ :=
    ((M.du_cont _ (Set.mem_Ioi.2 hc)).continuousAt (Ioi_mem_nhds hc)).comp
      (continuous_const.sub continuous_id).continuousAt
  have hDw : ContinuousWithinAt S.D (Set.Ici 0) s₀ := S.D_continuousOn s₀ (Set.mem_Ici.2 hs0)
  have hf : Tendsto (fun s => M.du (x - s) - M.β * M.R * S.D s) (𝓝[>] s₀)
      (𝓝 (M.du (x - s₀) - M.β * M.R * S.D s₀)) :=
    (hduc.tendsto.mono_left nhdsWithin_le_nhds).sub
      (((hDw.mono fun t ht => Set.mem_Ici.2 (hs0.trans (Set.mem_Ioi.1 ht).le)).tendsto
        ).const_mul _)
  have hev : ∀ᶠ s in 𝓝[>] s₀, 0 ≤ M.du (x - s) - M.β * M.R * S.D s := by
    filter_upwards [Ioo_mem_nhdsGT hsx'] with s hs
    have hsm : s ∈ Set.Icc 0 x := ⟨hs0.trans hs.1.le, hs.2.le⟩
    have hle := S.bellman_le' hx hsm
    rw [hV] at hle
    have hW := (S.W_sub_bounds hs0 hs.1.le).1
    have hu := (M.tangent_u (c := x - s) (c' := x - s₀) (by linarith [hs.2])
      (by linarith [hs.1])).2 (by linarith [hs.2])
    have hpos : 0 < s - s₀ := sub_pos.2 hs.1
    have key : (s - s₀) * (M.β * M.R * S.D s) ≤ (s - s₀) * M.du (x - s) := by
      have e1 : M.β * (M.R * (s - s₀) * S.D s) ≤ M.β * (S.W s - S.W s₀) :=
        mul_le_mul_of_nonneg_left hW hβ.le
      have e2 : x - s₀ - (x - s) = s - s₀ := by ring
      rw [e2] at hu
      nlinarith
    have := le_of_mul_le_mul_left key hpos
    linarith
  have := ge_of_tendsto hf hev
  linarith

/-- The Euler equation from left difference quotients: if `â(x) > 0` then
`u′(c(x)) ≤ βR D(â(x))`. -/
theorem euler_ge {x : ℝ} (hx : M.xmin ≤ x) (hpos : 0 < S.sav x) :
    M.du (S.cons x) ≤ M.β * M.R * S.D (S.sav x) := by
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  have hc := S.cons_pos hx
  rw [cons_eq] at hc ⊢
  set s₀ := S.sav x
  have hβ := M.β_pos
  have hV := S.bellman' hx
  have hduc : ContinuousAt (fun s => M.du (x - s)) s₀ :=
    ((M.du_cont _ (Set.mem_Ioi.2 hc)).continuousAt (Ioi_mem_nhds hc)).comp
      (continuous_const.sub continuous_id).continuousAt
  have hDc : ContinuousAt S.D s₀ :=
    (S.D_continuousOn s₀ (Set.mem_Ici.2 hs0)).continuousAt (Ici_mem_nhds hpos)
  have hf : Tendsto (fun s => M.du (x - s) - M.β * M.R * S.D s) (𝓝[<] s₀)
      (𝓝 (M.du (x - s₀) - M.β * M.R * S.D s₀)) :=
    ((hduc.tendsto.sub (hDc.tendsto.const_mul _))).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] s₀, M.du (x - s) - M.β * M.R * S.D s ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT hpos] with s hs
    have hsm : s ∈ Set.Icc 0 x := ⟨hs.1.le, (hs.2.trans_le hsx).le⟩
    have hle := S.bellman_le' hx hsm
    rw [hV] at hle
    have hW := (S.W_sub_bounds hs.1.le hs.2.le).2
    have hu := (M.tangent_u (c := x - s₀) (c' := x - s) hc.le (by linarith [hs.2])).1
    have hpos' : 0 < s₀ - s := sub_pos.2 hs.2
    have key : (s₀ - s) * M.du (x - s) ≤ (s₀ - s) * (M.β * M.R * S.D s) := by
      have e1 : M.β * (S.W s₀ - S.W s) ≤ M.β * (M.R * (s₀ - s) * S.D s) :=
        mul_le_mul_of_nonneg_left hW hβ.le
      have e2 : x - s - (x - s₀) = s₀ - s := by ring
      rw [e2] at hu
      nlinarith
    have := le_of_mul_le_mul_left key hpos'
    linarith
  have := le_of_tendsto hf hev
  linarith

/-- **The Euler inequality** (Miao, (8.7), p. 239, stationary form): for `x ≥ x_min`,
`βR E V′(Râ(x) + y − rb) ≤ u′(c(x))`, with equality if `â(x) > 0`. Derived from the Bellman
equation. -/
theorem euler {x : ℝ} (hx : M.xmin ≤ x) :
    M.β * M.R * S.D (S.sav x) ≤ M.du (S.cons x) ∧
      (0 < S.sav x → M.du (S.cons x) = M.β * M.R * S.D (S.sav x)) :=
  ⟨S.euler_le hx, fun h => le_antisymm (S.euler_ge hx h) (S.euler_le hx)⟩

/-- `V′(x) = u′(c(x)) > 0` for `x ≥ x_min`. -/
theorem dV_pos {x : ℝ} (hx : M.xmin ≤ x) : 0 < S.dV x := by
  rw [S.envelope x hx]
  exact M.du_pos _ (S.cons_pos hx)

/-- `D(s) > 0` for `s ≥ 0`. -/
theorem D_pos {s : ℝ} (hs : 0 ≤ s) : 0 < S.D s := by
  refine si_integral_pos (S.integrable_dV hs) ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.dV_pos hy.1

/-- The envelope condition along next period's cash on hand:
`D(s) = E u′(c(Rs + y − rb))`. -/
theorem D_eq {s : ℝ} (hs : 0 ≤ s) : S.D s = ∫ y, M.du (S.cons (M.next s y)) ∂M.law := by
  refine integral_congr_ae ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.envelope _ hy.1

/-- **(8.7)** (Miao, p. 239), for iid income: `u′(c_t) ≥ βR E_t u′(c_{t+1})`, with equality if
`â_{t+1} > 0`, where `c_{t+1} = c(Râ(x_t) + y_{t+1} − rb)`. -/
theorem eq_8_7 {x : ℝ} (hx : M.xmin ≤ x) :
    M.β * M.R * ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law ≤ M.du (S.cons x) ∧
      (0 < S.sav x →
        M.du (S.cons x) = M.β * M.R * ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law) := by
  rw [← S.D_eq (S.sav_mem x hx).1]
  exact S.euler hx

end SIModel.Solution

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §8.3.2: Lemmas 8.3.1 and 8.3.2 (the consumption and saving policies)

Copied from `EconomicDynamics/Applications` (module `SIPolicies`), namespace renamed.

Miao, §8.3.2, pp. 249–251.

* **Lemma 8.3.1** (`lemma_8_3_1`): `c` is strictly increasing on `[x_min, ∞)` and for
  `x_min ≤ x < x′`, `0 ≤ â(x′) − â(x) < x′ − x`, with equality (in the first inequality) iff
  `â(x′) = â(x) = 0`. As the book remarks (p. 250), the proof uses neither `βR < 1` nor
  anything about uncertainty. Consequences: `â` is nondecreasing and `1`-Lipschitz, so `â` and
  `c` are continuous (`sav_lipschitz`, `continuousOn_sav`, `continuousOn_cons`); where the
  constraint does not bind, `â` is strictly increasing with slope `< 1`
  (`sav_strictMono_of_pos`, p. 250).
* `sav_eq_zero_iff`: the constraint binds at `x` iff `u′(x) ≥ βR E V′(y − rb)`.
* **Lemma 8.3.2** (Schechtman–Escudero; `lemma_8_3_2`): if `βR < 1` there is `x̂ > x_min`,
  the unique solution of `u′(x̂) = βR E V′(y − rb)`, with `â(x) = 0` for `x ≤ x̂` and `â(x) > 0`
  for `x > x̂`. The book argues by contradiction with a constraint that "never binds"; the proof
  here shows directly that the constraint binds at `x_min` (`sav_xmin`), from
  `βR E V′(y − rb) ≤ βR V′(x_min) < V′(x_min)`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- If `â(x) > 0` and `x < x′` then `â(x) < â(x′)` and `â(x′) − â(x) < x′ − x`. -/
theorem sav_lt_of_pos {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x') (hpos : 0 < S.sav x) :
    S.sav x < S.sav x' ∧ S.sav x' - S.sav x < x' - x := by
  have hx' : M.xmin ≤ x' := hx.trans hxx.le
  have hc := S.cons_pos hx
  have hc' := S.cons_pos hx'
  rw [cons_eq] at hc hc'
  have he := (S.euler hx).2 hpos
  rw [cons_eq] at he
  have hs0' := (S.sav_mem x' hx').1
  have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hlt : S.sav x < S.sav x' := by
    by_contra hcon
    push Not at hcon
    have h1 := S.euler_le hx'
    rw [cons_eq] at h1
    have h2 := S.D_strictAnti.antitoneOn (Set.mem_Ici.2 hs0') (Set.mem_Ici.2 hpos.le) hcon
    have h3 := M.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') (by linarith : x - S.sav x <
      x' - S.sav x')
    nlinarith
  refine ⟨hlt, ?_⟩
  have he' := (S.euler hx').2 (hpos.trans hlt)
  rw [cons_eq] at he'
  have h2 := S.D_strictAnti (Set.mem_Ici.2 hpos.le) (Set.mem_Ici.2 hs0') hlt
  by_contra hcon
  push Not at hcon
  have h3 := M.du_anti.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc)
    (by linarith : x' - S.sav x' ≤ x - S.sav x)
  nlinarith

/-- If `â(x) = 0` and `x < x′` then `â(x′) < x′ − x`. -/
theorem sav_lt_of_zero {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x') (hzero : S.sav x = 0) :
    S.sav x' < x' - x := by
  have hx' : M.xmin ≤ x' := hx.trans hxx.le
  rcases (S.sav_mem x' hx').1.lt_or_eq with hpos | hz
  · by_contra hcon
    push Not at hcon
    have hc' := S.cons_pos hx'
    rw [cons_eq] at hc'
    have he' := (S.euler hx').2 hpos
    rw [cons_eq] at he'
    have h0 := S.euler_le hx
    rw [cons_eq, hzero, sub_zero] at h0
    have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have h1 := S.D_strictAnti.antitoneOn (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x' - x))
      (Set.mem_Ici.2 hpos.le) hcon
    have h2 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤
      x' - x)) (by linarith : (0 : ℝ) < x' - x)
    have hx0 : 0 < x := M.xmin_pos.trans_le hx
    have h3 := M.du_anti.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hx0)
      (by linarith : x' - S.sav x' ≤ x)
    nlinarith
  · rw [← hz]; linarith

/-- **Lemma 8.3.1** (Miao, p. 249). Let `β ∈ (0, 1)` and `R > 0`. The consumption policy `c` is
strictly increasing on `[x_min, ∞)`, and for `x_min ≤ x < x′`,
`0 ≤ â(x′) − â(x) < x′ − x`, with `â(x′) − â(x) = 0` iff `â(x′) = â(x) = 0`. -/
theorem lemma_8_3_1 : StrictMonoOn S.cons (Set.Ici M.xmin) ∧
    ∀ x x', M.xmin ≤ x → x < x' →
      0 ≤ S.sav x' - S.sav x ∧ S.sav x' - S.sav x < x' - x ∧
        (S.sav x' - S.sav x = 0 ↔ S.sav x' = 0 ∧ S.sav x = 0) := by
  refine ⟨fun x hx x' hx' hxx => ?_, fun x x' hx hxx => ?_⟩
  · have hx0 : M.xmin ≤ x := hx
    have hx0' : M.xmin ≤ x' := hx'
    have h1 := S.dV_strictAnti hx hx' hxx
    rw [S.envelope x hx0, S.envelope x' hx0'] at h1
    by_contra hcon
    push Not at hcon
    have := M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos hx0')) (Set.mem_Ioi.2
      (S.cons_pos hx0)) hcon
    rw [cons_eq, cons_eq] at this
    linarith
  · rcases (S.sav_mem x hx).1.lt_or_eq with hpos | hz
    · obtain ⟨h1, h2⟩ := S.sav_lt_of_pos hx hxx hpos
      refine ⟨by linarith, h2, ⟨fun h => by linarith, fun h => by linarith [h.1, h.2]⟩⟩
    · have h1 := S.sav_lt_of_zero hx hxx hz.symm
      have h0 := (S.sav_mem x' (hx.trans hxx.le)).1
      rw [← hz]
      refine ⟨by linarith, by linarith, ⟨fun h => ⟨by linarith, rfl⟩, fun h => by linarith [h.1]⟩⟩

/-- `â` is nondecreasing on `[x_min, ∞)`. -/
theorem sav_mono : MonotoneOn S.sav (Set.Ici M.xmin) := by
  intro x hx x' _ hxx
  rcases hxx.lt_or_eq with hlt | heq
  · linarith [((S.lemma_8_3_1).2 x x' hx hlt).1]
  · rw [heq]

/-- `c` is nondecreasing on `[x_min, ∞)`. -/
theorem cons_mono : MonotoneOn S.cons (Set.Ici M.xmin) := S.lemma_8_3_1.1.monotoneOn

/-- `0 ≤ â(x′) − â(x) ≤ x′ − x` for `x_min ≤ x ≤ x′`. -/
theorem sav_sub_bounds {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x ≤ x') :
    0 ≤ S.sav x' - S.sav x ∧ S.sav x' - S.sav x ≤ x' - x := by
  rcases hxx.lt_or_eq with hlt | heq
  · obtain ⟨h1, h2, -⟩ := (S.lemma_8_3_1).2 x x' hx hlt
    exact ⟨h1, h2.le⟩
  · subst heq; simp

/-- `0 ≤ c(x′) − c(x) ≤ x′ − x` for `x_min ≤ x ≤ x′`. -/
theorem cons_sub_bounds {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x ≤ x') :
    0 ≤ S.cons x' - S.cons x ∧ S.cons x' - S.cons x ≤ x' - x := by
  obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx hxx
  rw [cons_eq, cons_eq]
  constructor <;> linarith

/-- `â` is `1`-Lipschitz on `[x_min, ∞)`. -/
theorem sav_lipschitz : LipschitzOnWith 1 S.sav (Set.Ici M.xmin) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x x' with h | h
  · obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx h
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h2
  · obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx' h
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
    exact h2

/-- `â` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_sav : ContinuousOn S.sav (Set.Ici M.xmin) :=
  S.sav_lipschitz.continuousOn

/-- `c` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_cons : ContinuousOn S.cons (Set.Ici M.xmin) :=
  continuousOn_id.sub S.continuousOn_sav

/-- Miao, p. 250: where the borrowing constraint does not bind, the saving function is strictly
increasing with slope less than `1`: if `â(x) > 0` and `x < x′`, then
`â(x) < â(x′)` and `â(x′) − â(x) < x′ − x` (so also `c(x) < c(x′)`). -/
theorem sav_strictMono_of_pos {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x')
    (hpos : 0 < S.sav x) :
    S.sav x < S.sav x' ∧ S.sav x' - S.sav x < x' - x ∧ S.cons x < S.cons x' :=
  ⟨(S.sav_lt_of_pos hx hxx hpos).1, (S.sav_lt_of_pos hx hxx hpos).2,
    S.lemma_8_3_1.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hxx.le)) hxx⟩

/-- The borrowing constraint binds at `x` iff `u′(x) ≥ βR E V′(y − rb)`. -/
theorem sav_eq_zero_iff {x : ℝ} (hx : M.xmin ≤ x) :
    S.sav x = 0 ↔ M.β * M.R * S.D 0 ≤ M.du x := by
  constructor
  · intro h
    have := S.euler_le hx
    rwa [cons_eq, h, sub_zero] at this
  · intro h
    by_contra hne
    have hpos : 0 < S.sav x := lt_of_le_of_ne (S.sav_mem x hx).1 (Ne.symm hne)
    have he := (S.euler hx).2 hpos
    have hc := S.cons_pos hx
    rw [cons_eq] at he hc
    have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have h1 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
    have h2 := M.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 (M.xmin_pos.trans_le hx))
      (by linarith : x - S.sav x < x)
    nlinarith

/-- With `βR < 1` the constraint binds at `x_min`, and `u′(x_min) > βR E V′(y − rb)`. -/
theorem sav_xmin (hβR : M.β * M.R < 1) :
    S.sav M.xmin = 0 ∧ M.β * M.R * S.D 0 < M.du M.xmin := by
  have hD := S.D_le le_rfl
  have hdV := S.dV_pos le_rfl
  have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hK : M.β * M.R * S.D 0 < S.dV M.xmin := by nlinarith
  rw [S.envelope _ le_rfl] at hK
  have hz : S.sav M.xmin = 0 := by
    by_contra hne
    have hpos : 0 < S.sav M.xmin := lt_of_le_of_ne (S.sav_mem _ le_rfl).1 (Ne.symm hne)
    have he := (S.euler le_rfl).2 hpos
    rw [cons_eq] at he
    have h1 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
    nlinarith
  rw [hz, sub_zero] at hK
  exact ⟨hz, hK⟩

/-- **Lemma 8.3.2** (Schechtman and Escudero (1977); Miao, p. 251). Let `βR < 1` (and
`x_min = y_min − rb > 0`). There is `x̂ > x_min` such that `â(x) = 0` if `x_min ≤ x ≤ x̂` and
`â(x) > 0` if `x > x̂`; `x̂` is the unique solution of `u′(x̂) = βR E V′(y − rb)`. -/
theorem lemma_8_3_2 (hβR : M.β * M.R < 1) :
    ∃ xhat, M.xmin < xhat ∧ M.du xhat = M.β * M.R * S.D 0 ∧
      (∀ z, 0 < z → M.du z = M.β * M.R * S.D 0 → z = xhat) ∧
      ∀ x, M.xmin ≤ x → (x ≤ xhat → S.sav x = 0) ∧ (xhat < x → 0 < S.sav x) := by
  obtain ⟨-, hK⟩ := S.sav_xmin hβR
  set K := M.β * M.R * S.D 0
  have hK0 : 0 < K := mul_pos (mul_pos M.β_pos M.R_pos) (S.D_pos le_rfl)
  obtain ⟨X, hX⟩ := (eventually_atTop.1 ((M.inada_top.eventually (gt_mem_nhds hK0)).and
    (eventually_gt_atTop M.xmin)))
  have hXX := hX (max X (M.xmin + 1)) (le_max_left _ _)
  set X' := max X (M.xmin + 1)
  have hcont : ContinuousOn M.du (Set.Icc M.xmin X') :=
    M.du_cont.mono fun z hz => Set.mem_Ioi.2 (M.xmin_pos.trans_le hz.1)
  obtain ⟨xhat, hxm, hxe⟩ := intermediate_value_Ioo' hXX.2.le hcont ⟨hXX.1, hK⟩
  have hpos : ∀ z, M.xmin ≤ z → 0 < z := fun z hz => M.xmin_pos.trans_le hz
  refine ⟨xhat, hxm.1, hxe, fun z hz hze => ?_, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases lt_trichotomy z xhat with hlt | heq | hgt
    · have := M.du_anti (Set.mem_Ioi.2 hz) (Set.mem_Ioi.2 (hpos _ hxm.1.le)) hlt; linarith
    · exact heq
    · have := M.du_anti (Set.mem_Ioi.2 (hpos _ hxm.1.le)) (Set.mem_Ioi.2 hz) hgt; linarith
  · refine (S.sav_eq_zero_iff hx).2 ?_
    change K ≤ M.du x
    rw [← hxe]
    exact M.du_anti.antitoneOn (Set.mem_Ioi.2 (hpos _ hx)) (Set.mem_Ioi.2 (hpos _ hxm.1.le)) h
  · have hlt := M.du_anti (Set.mem_Ioi.2 (hpos _ hxm.1.le)) (Set.mem_Ioi.2 (hpos _ hx)) h
    rw [hxe] at hlt
    have hne : S.sav x ≠ 0 := fun h0 => by
      have := (S.sav_eq_zero_iff hx).1 h0
      linarith
    exact lt_of_le_of_ne (S.sav_mem x hx).1 (Ne.symm hne)

end SIModel.Solution

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §8.3.2, Case 1 (`βR < 1`): Lemma 8.3.3, `x_max` and Exercise 8.9

Copied from `EconomicDynamics/Applications` (module `SIBounded`), namespace renamed.

Miao, §8.3.2, pp. 252–254, and Exercise 9, p. 289.

* **Footnote 2** (p. 253, `footnote_2`): if `−cu′′(c)/u′(c) ≤ γ` for `c > c₀ > 0`, then
  `u′(c)/u′(c₀) ≥ (c₀/c)^γ` for `c > c₀`; it follows from `c ↦ u′(c)c^γ` being nondecreasing on
  `[c₀, ∞)` (`footnote_2_mono`).
* `cons_unbounded` (p. 253): if `βR < 1` and `â` is unbounded, then `c(x) → ∞`.
* **(8.16)** (`eq_8_16`): with `m = Râ(x) + y_min − rb` and `M = Râ(x) + y_max − rb`,
  `V′(M) ≤ E V′(x′) ≤ V′(M)(1 + (y_max − y_min)/c(m))^γ` once `c(m) ≥ c₀`.
* **Lemma 8.3.3** (Schechtman–Escudero; `lemma_8_3_3`): if `βR < 1` and the relative risk
  aversion is below `γ` for large `c`, there is `x*` with `x_{t+1} < x_t` whenever `x_t > x*`
  (for every income `y ≤ y_max`, `lemma_8_3_3_all`).
* **Exercise 8.9** (`ex_8_9`): if moreover `y_min < y_max`, the smallest critical value
  `x_max` (`Solution.xmax`) exists; `x_max > x_min`, and `x_max` is the largest solution of
  `Râ(x) + y_max − rb = x`. The interval `[x_min, x_max]` is invariant (`mapsTo_Icc`, p. 254).

**Correction** (`eq_8_16_identity_false`). The proof of Lemma 8.3.3 says "by definition,
`c(y_max − rb + Râ) = c(y_min − rb + Râ) + y_max − y_min`". This is false: by Lemma 8.3.1 only
`≤` holds (`cons_high_le`), and the inequality is strict whenever `y_min < y_max` and the
borrowing constraint does not bind at `m`, which is the situation of the proof (`â → ∞`).
The `≤` suffices for (8.16). Also, the contradiction in the proof that `c(x) → ∞` is
`u′(c̄) = βRu′(c̄)` (printed `c̄ = βRc̄`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

namespace SIModel

variable (M : SIModel)

theorem next_ymin (s : ℝ) : M.next s M.ymin = M.R * s + M.xmin := by
  simp only [next, xmin]; ring

theorem next_ymax_sub (s : ℝ) : M.next s M.ymax - M.next s M.ymin = M.ymax - M.ymin := by
  simp only [next]; ring

/-- Footnote 2, the monotone form: if `−cu′′(c)/u′(c) ≤ γ` for `c > c₀ > 0`, then `u′(c)c^γ`
is nondecreasing on `[c₀, ∞)`. -/
theorem footnote_2_mono {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) :
    MonotoneOn (fun c => M.du c * c ^ γ) (Set.Ici c₀) := by
  have hd : ∀ c, 0 < c → HasDerivAt (fun c => M.du c * c ^ γ)
      (ddu c * c ^ γ + M.du c * (γ * c ^ (γ - 1))) c := fun c hc =>
    (hddu c hc).mul (Real.hasDerivAt_rpow_const (Or.inl hc.ne'))
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici c₀)
    (f' := fun c => ddu c * c ^ γ + M.du c * (γ * c ^ (γ - 1))) (fun c hc => ?_)
    (fun c hc => ?_) (fun c hc => ?_)
  · exact (hd c (hc₀.trans_le hc)).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hc
    exact (hd c (hc₀.trans hc)).hasDerivWithinAt
  · rw [interior_Ici] at hc
    have hc0 : 0 < c := hc₀.trans hc
    have hdu := M.du_pos c hc0
    have h1 := hγ c hc
    rw [div_le_iff₀ hdu] at h1
    have hP : 0 < c ^ γ := Real.rpow_pos_of_pos hc0 γ
    rw [Real.rpow_sub_one hc0.ne']
    have e : ddu c * c ^ γ + M.du c * (γ * (c ^ γ / c)) =
        (c ^ γ / c) * (c * ddu c + γ * M.du c) := by
      field_simp
    rw [e]
    exact mul_nonneg (div_nonneg hP.le hc0.le) (by linarith)

/-- **Footnote 2** (Miao, p. 253): if `−cu′′(c)/u′(c) ≤ γ` for all `c > c₀ > 0`, then
`u′(c)/u′(c₀) ≥ (c₀/c)^γ` for all `c > c₀`. -/
theorem footnote_2 {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) {c : ℝ}
    (hc : c₀ < c) : (c₀ / c) ^ γ ≤ M.du c / M.du c₀ := by
  have hm := M.footnote_2_mono hddu hc₀ hγ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc.le) hc.le
  simp only at hm
  have hc0 : 0 < c := hc₀.trans hc
  rw [Real.div_rpow hc₀.le hc0.le, div_le_div_iff₀ (Real.rpow_pos_of_pos hc0 γ)
    (M.du_pos c₀ hc₀)]
  linarith

/-- From footnote 2: `u′(c) ≤ u′(c′)(c′/c)^γ` for `c₀ ≤ c ≤ c′`. -/
theorem du_le_rpow {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) {c c' : ℝ}
    (hc : c₀ ≤ c) (hcc : c ≤ c') : M.du c ≤ M.du c' * (c' / c) ^ γ := by
  have hm := M.footnote_2_mono hddu hc₀ hγ (Set.mem_Ici.2 hc) (Set.mem_Ici.2 (hc.trans hcc)) hcc
  simp only at hm
  have hc0 : 0 < c := hc₀.trans_le hc
  have hP : 0 < c ^ γ := Real.rpow_pos_of_pos hc0 γ
  rw [Real.div_rpow (hc0.le.trans hcc) hc0.le, ← mul_div_assoc, le_div_iff₀ hP]
  exact hm

/-- `(1 + t)^γ ≤ e^{γt}` for `t ≥ 0`, `γ ≥ 0`. -/
theorem si_one_add_rpow_le {t γ : ℝ} (ht : 0 ≤ t) (hγ : 0 ≤ γ) :
    (1 + t) ^ γ ≤ Real.exp (γ * t) := by
  calc (1 + t) ^ γ ≤ (Real.exp t) ^ γ :=
        Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp t]) hγ
    _ = Real.exp (γ * t) := by rw [← Real.exp_mul, mul_comm]

end SIModel

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- `E V′(x′) ≤ V′(Rs + y_min − rb)`. -/
theorem D_le_low {s : ℝ} (hs : 0 ≤ s) : S.D s ≤ S.dV (M.next s M.ymin) := by
  have : S.D s ≤ ∫ _y, S.dV (M.next s M.ymin) ∂M.law := by
    refine integral_mono_ae (S.integrable_dV hs) (integrable_const _) ?_
    filter_upwards [M.supp] with y hy
    refine S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 (M.next_ge hs le_rfl))
      (Set.mem_Ici.2 (M.next_ge hs hy.1)) ?_
    simp only [SIModel.next]; linarith [hy.1]
  simpa using this

/-- `V′(Rs + y_max − rb) ≤ E V′(x′)`. -/
theorem high_le_D {s : ℝ} (hs : 0 ≤ s) : S.dV (M.next s M.ymax) ≤ S.D s := by
  have : ∫ _y, S.dV (M.next s M.ymax) ∂M.law ≤ S.D s := by
    refine integral_mono_ae (integrable_const _) (S.integrable_dV hs) ?_
    filter_upwards [M.ae_next hs] with y hy
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hy.1)
      (Set.mem_Ici.2 (hy.1.trans hy.2)) hy.2
  simpa using this

/-- `â` unbounded gives `â(x) > K` for all large `x`. -/
theorem sav_eventually_gt (hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x) (K : ℝ) :
    ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → K < S.sav x := by
  obtain ⟨X, hX, hK⟩ := hunb K
  exact ⟨X, hX, fun x hx => hK.trans_le (S.sav_mono (Set.mem_Ici.2 hX)
    (Set.mem_Ici.2 (hX.trans hx)) hx)⟩

/-- Miao, p. 253: if `βR < 1` and `â` is unbounded, then `c(x) → ∞`: for every `C`, `c(x) > C`
for all large `x`. -/
theorem cons_unbounded (hβR : M.β * M.R < 1) (hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x)
    (C : ℝ) : ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → C < S.cons x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, M.xmin ≤ x → S.cons x ≤ C := ⟨C, fun x hx => by
    obtain ⟨x', hx', hc'⟩ := hcon x hx
    exact (S.cons_mono (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hx')) hx').trans hc'⟩
  have hne : (S.cons '' Set.Ici M.xmin).Nonempty := ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.2
    le_rfl)⟩
  have hbdd : BddAbove (S.cons '' Set.Ici M.xmin) := ⟨C, by
    rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  set cbar := sSup (S.cons '' Set.Ici M.xmin)
  have hle : ∀ x, M.xmin ≤ x → S.cons x ≤ cbar := fun x hx =>
    le_csSup hbdd (Set.mem_image_of_mem _ (Set.mem_Ici.2 hx))
  have hcbar : 0 < cbar := (S.cons_pos le_rfl).trans_le (hle _ le_rfl)
  have hβR0 : 0 ≤ M.β * M.R := (mul_pos M.β_pos M.R_pos).le
  have hlt : M.β * M.R * M.du cbar < M.du cbar := by
    have := M.du_pos cbar hcbar; nlinarith
  have hcont : Tendsto (fun w => M.β * M.R * M.du w) (𝓝 cbar) (𝓝 (M.β * M.R * M.du cbar)) :=
    (((M.du_cont _ (Set.mem_Ioi.2 hcbar)).continuousAt (Ioi_mem_nhds hcbar)).tendsto).const_mul _
  obtain ⟨z, hz, hz0⟩ := ((hcont.eventually_lt_const hlt).filter_mono nhdsWithin_le_nhds |>.and
    (Ioo_mem_nhdsLT hcbar) : ∀ᶠ w in 𝓝[<] cbar, _ ∧ w ∈ Set.Ioo 0 cbar).exists
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hzx⟩ := exists_lt_of_lt_csSup hne hz0.2
  obtain ⟨X, hX, hXK⟩ := S.sav_eventually_gt hunb (max 0 ((x₁ - M.xmin) / M.R))
  have hs := hXK X le_rfl
  have hs0 : 0 < S.sav X := lt_of_le_of_lt (le_max_left _ _) hs
  have hsx : (x₁ - M.xmin) / M.R < S.sav X := lt_of_le_of_lt (le_max_right _ _) hs
  set m := M.next (S.sav X) M.ymin
  have hm : x₁ ≤ m := by
    rw [show m = M.R * S.sav X + M.xmin from M.next_ymin _, ← sub_le_iff_le_add]
    rw [div_lt_iff₀ M.R_pos] at hsx
    linarith
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  have he := (S.euler hX).2 hs0
  have hD := S.D_le_low hs0.le
  rw [S.envelope m hmx] at hD
  have hcm : z < S.cons m := hzx.trans_le (S.cons_mono (Set.mem_Ici.2 hx₁) (Set.mem_Ici.2 hmx) hm)
  have h1 := M.du_anti (Set.mem_Ioi.2 hz0.1) (Set.mem_Ioi.2 (hz0.1.trans hcm)) hcm
  have h2 := M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos hX)) (Set.mem_Ioi.2 hcbar)
    (hle X hX)
  have h3 : M.β * M.R * S.D (S.sav X) ≤ M.β * M.R * M.du z :=
    mul_le_mul_of_nonneg_left (hD.trans h1.le) hβR0
  linarith

/-- Lemma 8.3.1 at `m ≤ M`: `c(Rs + y_max − rb) ≤ c(Rs + y_min − rb) + y_max − y_min`. -/
theorem cons_high_le {s : ℝ} (hs : 0 ≤ s) :
    S.cons (M.next s M.ymax) ≤ S.cons (M.next s M.ymin) + (M.ymax - M.ymin) := by
  have h := (S.cons_sub_bounds (M.next_ge hs le_rfl) (by
    have := M.next_ymax_sub s; linarith [M.ymin_le_ymax] : M.next s M.ymin ≤ M.next s M.ymax)).2
  rw [M.next_ymax_sub] at h
  linarith

/-- **The identity on p. 253 is false**: if `y_min < y_max` and the borrowing constraint does not
bind at `m = Rs + y_min − rb`, then `c(Rs + y_max − rb) < c(m) + y_max − y_min` strictly. -/
theorem eq_8_16_identity_false {s : ℝ} (hs : 0 ≤ s) (hy : M.ymin < M.ymax)
    (hpos : 0 < S.sav (M.next s M.ymin)) :
    S.cons (M.next s M.ymax) < S.cons (M.next s M.ymin) + (M.ymax - M.ymin) := by
  have hlt : M.next s M.ymin < M.next s M.ymax := by
    have := M.next_ymax_sub s; linarith
  have h := (S.sav_lt_of_pos (M.next_ge hs le_rfl) hlt hpos).1
  have e := M.next_ymax_sub s
  simp only [cons_eq]
  linarith

/-- **(8.16)** (Miao, p. 253), corrected: with `m = Rs + y_min − rb`, `M = Rs + y_max − rb`, and
`c(m) ≥ c₀` (where the relative risk aversion is `≤ γ` above `c₀`),
`V′(M) ≤ E V′(Rs + y − rb) ≤ V′(M)(1 + (y_max − y_min)/c(m))^γ`. -/
theorem eq_8_16 {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ)
    {s : ℝ} (hs : 0 ≤ s) (hcm : c₀ ≤ S.cons (M.next s M.ymin)) :
    S.dV (M.next s M.ymax) ≤ S.D s ∧
      S.D s ≤ S.dV (M.next s M.ymax) *
        (1 + (M.ymax - M.ymin) / S.cons (M.next s M.ymin)) ^ γ := by
  refine ⟨S.high_le_D hs, ?_⟩
  set m := M.next s M.ymin
  set Mx := M.next s M.ymax
  have hmx : M.xmin ≤ m := M.next_ge hs le_rfl
  have hmM : m ≤ Mx := by have := M.next_ymax_sub s; linarith [M.ymin_le_ymax]
  have hMx : M.xmin ≤ Mx := hmx.trans hmM
  have hcm0 : 0 < S.cons m := hc₀.trans_le hcm
  have hcmM : S.cons m ≤ S.cons Mx := S.cons_mono (Set.mem_Ici.2 hmx) (Set.mem_Ici.2 hMx) hmM
  have h1 := M.du_le_rpow hddu hc₀ hγ hcm hcmM
  have h2 : S.cons Mx / S.cons m ≤ 1 + (M.ymax - M.ymin) / S.cons m := by
    rw [div_le_iff₀ hcm0, add_mul, div_mul_cancel₀ _ hcm0.ne', one_mul]
    exact S.cons_high_le hs
  have h3 := Real.rpow_le_rpow (div_nonneg (hcm0.le.trans hcmM) hcm0.le) h2 hγ0
  have hD := S.D_le_low hs
  rw [S.envelope m hmx] at hD
  rw [S.envelope Mx hMx]
  calc S.D s ≤ M.du (S.cons m) := hD
    _ ≤ M.du (S.cons Mx) * (S.cons Mx / S.cons m) ^ γ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (M.du_pos _ (hcm0.trans_le hcmM)).le

/-- **Lemma 8.3.3** (Schechtman and Escudero (1977); Miao, p. 252). Let `βR < 1`, and let
`−cu′′(c)/u′(c) < γ` for all `c` sufficiently large, for some `γ > 0`. Then there is `x*`
such that `x_t > x*` implies `x_{t+1} < x_t`: `Râ(x) + y_max − rb < x` for every `x > x*`. -/
theorem lemma_8_3_3 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → M.next (S.sav x) M.ymax < x := by
  by_cases hbdd : ∃ K, ∀ x, M.xmin ≤ x → S.sav x ≤ K
  · obtain ⟨K, hK⟩ := hbdd
    refine ⟨max M.xmin (M.next K M.ymax), le_max_left _ _, fun x hx => ?_⟩
    have hx0 : M.xmin ≤ x := (le_max_left _ _).trans hx.le
    have h1 := hK x hx0
    have h2 : M.next (S.sav x) M.ymax ≤ M.next K M.ymax := by
      simp only [SIModel.next]
      nlinarith [M.R_pos]
    exact h2.trans_lt ((le_max_right _ _).trans_lt hx)
  push Not at hbdd
  have hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x := fun K => by
    obtain ⟨x, hx, h⟩ := hbdd K; exact ⟨x, hx, h⟩
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 hγ
  set c₀ := max c₁ 1
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hγ' : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ := fun c hc =>
    (hc₁ c ((le_max_left _ _).trans hc.le)).le
  have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  set ε := (1 - M.β * M.R) / (2 * (M.β * M.R))
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hεβ : M.β * M.R * (1 + ε) < 1 := by
    have key : ∀ p : ℝ, 0 < p → p * (1 + (1 - p) / (2 * p)) = (1 + p) / 2 := fun p hp => by
      field_simp; ring
    have : M.β * M.R * (1 + ε) = (1 + M.β * M.R) / 2 := key _ hβR0
    rw [this]; linarith
  set L := Real.log (1 + ε)
  have hL : 0 < L := Real.log_pos (by linarith)
  set Δ := M.ymax - M.ymin
  have hΔ : 0 ≤ Δ := sub_nonneg.2 M.ymin_le_ymax
  set C₁ := max (c₀ + 1) (γ * Δ / L + 1)
  obtain ⟨X₂, hX₂, hcX₂⟩ := S.cons_unbounded hβR hunb C₁
  obtain ⟨X₃, hX₃, hsX₃⟩ := S.sav_eventually_gt hunb (max 0 ((X₂ - M.xmin) / M.R))
  refine ⟨X₃, hX₃, fun x hx => ?_⟩
  have hx0 : M.xmin ≤ x := hX₃.trans hx.le
  have hsK := hsX₃ x hx.le
  have hs0 : 0 < S.sav x := lt_of_le_of_lt (le_max_left _ _) hsK
  have hsX : (X₂ - M.xmin) / M.R < S.sav x := lt_of_le_of_lt (le_max_right _ _) hsK
  set s := S.sav x
  set m := M.next s M.ymin
  set Mx := M.next s M.ymax
  have hm : X₂ ≤ m := by
    rw [show m = M.R * s + M.xmin from M.next_ymin _, ← sub_le_iff_le_add]
    rw [div_lt_iff₀ M.R_pos] at hsX
    linarith
  have hcm : C₁ < S.cons m := hcX₂ m hm
  have hcm0 : c₀ ≤ S.cons m := by
    have : c₀ + 1 ≤ C₁ := le_max_left _ _
    linarith
  have hcmpos : 0 < S.cons m := hc₀.trans_le hcm0
  obtain ⟨-, hD⟩ := S.eq_8_16 hddu hc₀ hγ0.le hγ' hs0.le hcm0
  have hpow : (1 + Δ / S.cons m) ^ γ ≤ 1 + ε := by
    refine (SIModel.si_one_add_rpow_le (div_nonneg hΔ hcmpos.le) hγ0.le).trans ?_
    rw [← Real.exp_log (show 0 < 1 + ε by linarith)]
    refine Real.exp_le_exp.2 ?_
    have hC : γ * Δ / L < S.cons m := by
      have : γ * Δ / L + 1 ≤ C₁ := le_max_right _ _
      linarith
    rw [div_lt_iff₀ hL] at hC
    rw [mul_div_assoc', div_le_iff₀ hcmpos]
    linarith
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  have hMx : M.xmin ≤ Mx := hmx.trans (by
    have := M.next_ymax_sub s; linarith [M.ymin_le_ymax] : m ≤ Mx)
  have hdVM := S.dV_pos hMx
  have he' := (S.euler hx0).2 hs0
  have he : S.dV x = M.β * M.R * S.D s := by rw [S.envelope x hx0]; exact he'
  have key : S.dV x < S.dV Mx := by
    rw [he]
    calc M.β * M.R * S.D s ≤ M.β * M.R * (S.dV Mx * (1 + ε)) :=
          mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_left hpow hdVM.le))
            hβR0.le
      _ = (M.β * M.R * (1 + ε)) * S.dV Mx := by ring
      _ < 1 * S.dV Mx := mul_lt_mul_of_pos_right hεβ hdVM
      _ = S.dV Mx := one_mul _
  by_contra hcon
  push Not at hcon
  have := S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hMx) hcon
  linarith

/-- Lemma 8.3.3 for every income realisation: `x_{t+1} = Râ(x_t) + y − rb < x_t` for all
`y ≤ y_max`. -/
theorem lemma_8_3_3_all (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x := by
  obtain ⟨xs, hxs, h⟩ := S.lemma_8_3_3 hβR hddu hγ0 hγ
  refine ⟨xs, hxs, fun x hx y hy => lt_of_le_of_lt ?_ (h x hx)⟩
  simp only [SIModel.next]; linarith

/-- The fixed points of the highest-income map `x ↦ Râ(x) + y_max − rb` in `[x_min, ∞)`. -/
def fixHigh : Set ℝ := {x | M.xmin ≤ x ∧ M.next (S.sav x) M.ymax = x}

/-- `x_max` (Miao, p. 254): the largest fixed point of `x ↦ Râ(x) + y_max − rb`. -/
noncomputable def xmax : ℝ := sSup S.fixHigh

/-- `x ↦ Râ(x) + y_max − rb − x` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_gap : ContinuousOn (fun x => M.next (S.sav x) M.ymax - x)
    (Set.Ici M.xmin) :=
  ((M.continuous_next M.ymax).comp_continuousOn S.continuousOn_sav).sub continuousOn_id

/-- **Exercise 8.9** (Miao, p. 289). Let `βR < 1`, the relative risk aversion be below `γ > 0`
for large `c`, and `y_min < y_max`. Then `x_max` is the largest solution of
`Râ(x) + y_max − rb = x` in `[x_min, ∞)`, `x_max > x_min`, every `x > x_max` has
`Râ(x) + y_max − rb < x`, and `x_max` is the smallest critical value `x*` of Lemma 8.3.3. -/
theorem ex_8_9 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) :
    M.xmin < S.xmax ∧ IsGreatest S.fixHigh S.xmax ∧
      (∀ x, S.xmax < x → M.next (S.sav x) M.ymax < x) ∧
      IsLeast {xs | M.xmin ≤ xs ∧ ∀ x, xs < x → M.next (S.sav x) M.ymax < x} S.xmax := by
  obtain ⟨xs, hxs, hcrit⟩ := S.lemma_8_3_3 hβR hddu hγ0 hγ
  set h : ℝ → ℝ := fun x => M.next (S.sav x) M.ymax - x
  have hcont := S.continuousOn_gap
  have hh0 : 0 < h M.xmin := by
    have := mul_nonneg M.R_pos.le (S.sav_mem M.xmin le_rfl).1
    have e : h M.xmin = M.R * S.sav M.xmin + (M.ymax - M.ymin) := by
      simp only [h, SIModel.next, SIModel.xmin]; ring
    rw [e]
    linarith
  have hneg : ∀ x, xs < x → h x < 0 := fun x hx => by
    have := hcrit x hx; simp only [h]; linarith
  have hbdd : BddAbove S.fixHigh := ⟨xs, fun x hx => by
    by_contra hcon
    push Not at hcon
    have := hcrit x hcon
    rw [hx.2] at this
    exact lt_irrefl _ this⟩
  have hzero : ∀ a b, M.xmin ≤ a → a ≤ b → 0 ≤ h a → h b < 0 → ∃ z ∈ S.fixHigh, a ≤ z := by
    intro a b ha hab hha hhb
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab
      (hcont.mono fun w hw => Set.mem_Ici.2 (ha.trans hw.1)) ⟨hhb.le, hha⟩
    refine ⟨z, ⟨ha.trans hz.1, ?_⟩, hz.1⟩
    linarith
  obtain ⟨z₀, hz₀, -⟩ := hzero M.xmin (xs + 1) le_rfl (by linarith) hh0.le (hneg _ (by linarith))
  have hne : S.fixHigh.Nonempty := ⟨z₀, hz₀⟩
  have hclosed : IsClosed S.fixHigh := by
    have : S.fixHigh = Set.Ici M.xmin ∩ h ⁻¹' {0} := by
      ext x
      simp only [fixHigh, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage,
        Set.mem_singleton_iff, h, sub_eq_zero]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hmem : S.xmax ∈ S.fixHigh := hclosed.csSup_mem hne hbdd
  have hgt : M.xmin < S.xmax := by
    rcases hmem.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h2 := hmem.2
      rw [← heq] at h2
      have : h M.xmin = 0 := by simp only [h]; linarith
      linarith
  have habove : ∀ x, S.xmax < x → M.next (S.sav x) M.ymax < x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hx0 : M.xmin ≤ x := hgt.le.trans hx.le
    obtain ⟨z, hz, hxz⟩ := hzero x (max x xs + 1) hx0 (by linarith [le_max_left x xs])
      (by simp only [h]; linarith) (hneg _ (by linarith [le_max_right x xs]))
    have := le_csSup hbdd hz
    change z ≤ S.xmax at this
    linarith
  refine ⟨hgt, ⟨hmem, fun x hx => le_csSup hbdd hx⟩, habove, ⟨⟨hgt.le, habove⟩, ?_⟩⟩
  rintro xs' ⟨-, hxs'⟩
  by_contra hcon
  push Not at hcon
  have := hxs' _ hcon
  rw [hmem.2] at this
  exact lt_irrefl _ this

/-- Miao, p. 254: if `x_f ≥ x_min` is a fixed point of `x ↦ Râ(x) + y_max − rb`, the interval
`[x_min, x_f]` is invariant: `x ∈ [x_min, x_f]` and `y ∈ [y_min, y_max]` give
`Râ(x) + y − rb ∈ [x_min, x_f]`. With `x_f = x_max` this is the long-run interval. -/
theorem mapsTo_Icc {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) {x y : ℝ}
    (hx : x ∈ Set.Icc M.xmin xf) (hy : y ∈ Set.Icc M.ymin M.ymax) :
    M.next (S.sav x) y ∈ Set.Icc M.xmin xf := by
  refine ⟨M.next_ge (S.sav_mem x hx.1).1 hy.1, ?_⟩
  have h1 := S.sav_mono (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hxf) hx.2
  have h2 : M.next (S.sav x) y ≤ M.next (S.sav xf) M.ymax := by
    simp only [SIModel.next]
    nlinarith [M.R_pos, hy.2]
  rwa [hfix] at h2

end SIModel.Solution

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

Copied from `RecursiveMethods/ConvergenceApplications` (module `TransitionFunctions`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`theorem_8_1`, `theorem_8_1_cor`), Exercise 8.1 (`ex_8_1`),
Theorem 8.2 (`theorem_8_2`), Exercise 8.2 (`ex_8_2`), Theorem 8.3 and its corollary
(`theorem_8_3`, `theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`ex_8_3`), the
`n`-step transition functions and Exercise 8.4 (`kpow`, `ex_8_4a`, `ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
    IsTransitionFunction Q ↔
      ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ ∀ z A, MeasurableSet A → κ z A = Q z A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμQ using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun z => μ z A) = fun z => Q z A := funext fun z => hμQ z A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun z => hμ z⟩, fun z A hA => hμQ z A hA⟩
  · rintro ⟨κ, hκ, hQ⟩
    refine ⟨fun z => ⟨κ z, inferInstance, fun A hA => hQ z A hA⟩, fun A hA => ?_⟩
    have : (fun z => Q z A) = fun z => κ z A := funext fun z => (hQ z A hA).symm
    rw [this]
    exact κ.measurable_coe hA

variable (κ : Kernel Z Z)

/-- The **Markov operator** on nonnegative functions (SLP (1), p. 213):
`(Tf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def markovOp (f : Z → ℝ≥0∞) (z : Z) : ℝ≥0∞ := ∫⁻ z', f z' ∂κ z

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- The **adjoint** `T*` (SLP (2), p. 213): `(T*λ)(A) = ∫ Q(z, A) λ(dz)`. -/
noncomputable def adjointOp (lam : Measure Z) : Measure Z := lam.bind κ

theorem markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (markovOp_indicator κ hs c)
    rw [this]
    exact measurable_const.mul (κ.measurable_coe hs)
  · intro f g hfg hf hg ihf ihg
    have : markovOp κ (f + g) = fun z => markovOp κ f z + markovOp κ g z := funext fun z =>
      lintegral_add_left hf _
    rw [this]
    exact ihf.add ihg
  · intro f hf hmono ih
    have : markovOp κ (fun x => ⨆ n, f n x) = fun z => ⨆ n, markovOp κ (f n) z :=
      funext fun z => lintegral_iSup hf hmono
    rw [this]
    exact Measurable.iSup ih

variable [IsMarkovKernel κ]

theorem integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM)
    rw [heq]
    exact (theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((integrable_of_bounded hf hfM).const_mul α)
    ((integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
  have hTf := theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => integrable_of_bounded (theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    theorem_8_3 κ lam hf.ennreal_ofReal,
    theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    pairing (fun z => a * f z + b * g z) lam = a * pairing f lam + b * pairing g lam ∧
      pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * pairing f lam + (1 - α) * pairing f μ := by
  constructor
  · simp only [pairing]
    rw [integral_add ((integrable_of_bounded hf hfM).const_mul a)
      ((integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [pairing]
    rw [integral_add_measure ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [kpow_add, markovOp_comp _ _ hf]
  · rw [add_comm, kpow_add, adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence: basic tools

Copied from `RecursiveMethods/ConvergenceApplications` (module `WeakBasics`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §12.1, pp. 353–358. `(S, ρ)` is a metric space with its Borel sets.

* **Exercise 12.1** (`ex_12_1`): for a Borel `S ⊆ ℝˡ`, the Borel sets of `S` are the Borel sets of
  `ℝˡ` contained in `S`; relatively open sets are traces of open sets; relative interiors are
  relatively open; and an open set is its own interior.
* **Exercise 12.2** (`ex_12_2`): the distance `ρ(s, A)` is `1`-Lipschitz, hence uniformly
  continuous, and `Ā = {s : ρ(s, A) = 0}` for nonempty `A`.
* `ConvWeak` (p. 354): `λₙ ⇒ λ` if `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f`.
* **Lemma 12.1** (`lemma_12_1`): for a closed `F` the continuous functions
  `fₙ(s) = max(0, 1 − n ρ(s, F))` decrease, equal `1` on `F`, lie in `[0, 1]`, and
  `∫ fₙ dλ → λ(F)` for every probability measure `λ`. The book proves the limit with the sets
  `Fₙ = {ρ(·, F) ≤ 1/n}`; here dominated convergence is used.
* **Lemma 12.2** (`lemma_12_2`): for measurable `a ≤ f < b`, the sets `Fᵢ = {f ≥ a + ic/k}` give
  `a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. The `Fᵢ` are
  closed if `f` is continuous. The book sums by parts; here the pointwise inequality
  `m/k ≤ g < (m + 1)/k`, with `m = #{i ≤ k : i/k ≤ g}`, is integrated.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-- **Exercise 12.1.** For a Borel set `S ⊆ ℝˡ`: (a) the Borel sets of `S` are the Borel subsets
of `ℝˡ` contained in `S`; (b) the relatively open sets are the traces `A′ ∩ S` of open sets;
(c) relative interiors are relatively open; (d) a relatively open set is its own interior. -/
theorem ex_12_1 {l : ℕ} {S : Set (Fin l → ℝ)} (hS : MeasurableSet S) :
    (∀ A : Set S, MeasurableSet A ↔ MeasurableSet (Subtype.val '' A)) ∧
      (∀ A : Set S, IsOpen A ↔ ∃ A' : Set (Fin l → ℝ), IsOpen A' ∧ Subtype.val ⁻¹' A' = A) ∧
      (∀ A : Set S, IsOpen (interior A)) ∧ ∀ A : Set S, IsOpen A → interior A = A := by
  refine ⟨fun A => ⟨fun hA => hS.subtype_image hA, fun hA => ?_⟩, fun A => isOpen_induced_iff,
    fun A => isOpen_interior, fun A hA => hA.interior_eq⟩
  have := (measurable_subtype_coe (p := fun x => x ∈ S)) hA
  rwa [Subtype.val_injective.preimage_image] at this

variable {S : Type*} [MetricSpace S]

/-- **Exercise 12.2.** (a) `|ρ(x, A) − ρ(y, A)| ≤ ρ(x, y)`; (b) `ρ(·, A)` is uniformly
continuous; (c) for nonempty `A`, `Ā = {s : ρ(s, A) = 0}`. -/
theorem ex_12_2 (A : Set S) :
    (∀ x y, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y) ∧
      UniformContinuous (fun s => Metric.infDist s A) ∧
      (A.Nonempty → closure A = {s | Metric.infDist s A = 0}) := by
  refine ⟨fun x y => ?_, (Metric.lipschitz_infDist_pt A).uniformContinuous, fun hA => ?_⟩
  · have := (Metric.lipschitz_infDist_pt A).dist_le_mul x y
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
  · ext s; exact Metric.mem_closure_iff_infDist_zero hA

/-- The functions of Lemma 12.1: `fₙ(s) = max(0, 1 − (n + 1) ρ(s, F))`. -/
noncomputable def bump (F : Set S) (n : ℕ) (s : S) : ℝ :=
  max 0 (1 - (n + 1) * Metric.infDist s F)

theorem continuous_bump (F : Set S) (n : ℕ) : Continuous (bump F n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (Metric.continuous_infDist_pt F)))

theorem bump_mem (F : Set S) (n : ℕ) (s : S) : 0 ≤ bump F n s ∧ bump F n s ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by
    have := Metric.infDist_nonneg (x := s) (s := F)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩

theorem bump_eq_one {F : Set S} {s : S} (hs : s ∈ F) (n : ℕ) : bump F n s = 1 := by
  simp [bump, Metric.infDist_zero_of_mem hs]

theorem bump_antitone (F : Set S) (s : S) : Antitone fun n => bump F n s := fun m n hmn => by
  refine max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_right ?_
    Metric.infDist_nonneg) 1)
  exact_mod_cast Nat.succ_le_succ hmn

/-- `fₙ → 1_F` pointwise for closed nonempty `F`. -/
theorem tendsto_bump {F : Set S} (hF : IsClosed F) (hne : F.Nonempty) (s : S) :
    Tendsto (fun n => bump F n s) atTop (𝓝 (F.indicator 1 s)) := by
  by_cases hs : s ∈ F
  · simp [bump_eq_one hs, indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hpos : 0 < Metric.infDist s F :=
      (hF.notMem_iff_infDist_pos hne).1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist s F)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have : 1 ≤ (n + 1) * Metric.infDist s F := by
      rw [div_lt_iff₀ hpos] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp only [bump]
    exact (max_eq_left (by linarith)).symm

variable [MeasurableSpace S] [BorelSpace S]

/-- `λₙ` **converges weakly** to `λ` (p. 354): `∫ f dλₙ → ∫ f dλ` for every bounded continuous
`f`. -/
def ConvWeak (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- **Lemma 12.1.** For a closed set `F` there are continuous `fₙ`, decreasing in `n`, with
`fₙ = 1` on `F`, `0 ≤ fₙ ≤ 1`, and `∫ fₙ dλ → λ(F)` for every probability measure `λ`. -/
theorem lemma_12_1 {F : Set S} (hF : IsClosed F) :
    ∃ f : ℕ → S → ℝ, (∀ n, Continuous (f n)) ∧ (∀ s, Antitone fun n => f n s) ∧
      (∀ n, ∀ s ∈ F, f n s = 1) ∧ (∀ n s, 0 ≤ f n s ∧ f n s ≤ 1) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        Tendsto (fun n => ∫ s, f n s ∂μ) atTop (𝓝 (μ.real F)) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ _ _ _ => le_rfl, fun _ s hs => hs.elim,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, fun μ _ => by simp⟩
  refine ⟨bump F, continuous_bump F, bump_antitone F, fun n s hs => bump_eq_one hs n,
    bump_mem F, fun μ _ => ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := bump F)
    (f := F.indicator 1) (fun _ => 1)
    (fun n => (continuous_bump F n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (bump_mem F n s).1]; exact (bump_mem F n s).2)
    (Eventually.of_forall fun s => tendsto_bump hF hne s)
  rwa [integral_indicator_one hF.measurableSet] at hlim

/-- For `0 ≤ g < 1` and `m = #{1 ≤ i ≤ k : i/k ≤ g}`: `m/k ≤ g < (m + 1)/k`. -/
theorem count_bounds {k : ℕ} (hk : 1 ≤ k) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card : ℝ) / k ≤ g ∧
      g < (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card + 1 : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkg : 0 ≤ k * g := mul_nonneg hk'.le hg0
  have hfloor : ⌊(k : ℝ) * g⌋₊ ≤ k := by
    have : (k : ℝ) * g < k := by nlinarith
    exact_mod_cast (Nat.floor_le hkg).trans this.le
  have hset : ((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g) =
      Finset.Icc 1 ⌊(k : ℝ) * g⌋₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [div_le_iff₀ hk', mul_comm g, ← Nat.le_floor_iff hkg]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hfloor⟩, h3⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  constructor
  · rw [div_le_iff₀ hk']; have := Nat.floor_le hkg; linarith [mul_comm (k : ℝ) g]
  · rw [lt_div_iff₀ hk', mul_comm]; exact Nat.lt_floor_add_one _

omit [BorelSpace S] in
/-- **Lemma 12.2.** For measurable `f` with `a ≤ f < b`, `c = b − a`, and `ε > 0`, there are `k ≥ 1`
and sets `Fᵢ = {f ≥ a + ic/k}`, `1 ≤ i ≤ k`, independent of `μ`, with
`a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. If `f` is
continuous the `Fᵢ` are closed. -/
theorem lemma_12_2 {f : S → ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ s, a ≤ f s ∧ f s < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ F : ℕ → Set S, (∀ i, MeasurableSet (F i)) ∧
      (Continuous f → ∀ i, IsClosed (F i)) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) ≤ ∫ s, f s ∂μ ∧
          ∫ s, f s ∂μ ≤ a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) + ε := by
  set k := ⌈(b - a) / ε⌉₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set F : ℕ → Set S := fun i => {s | a + (b - a) * i / k ≤ f s}
  refine ⟨k, hk, F, fun i => measurableSet_le measurable_const hf,
    fun hc i => isClosed_le continuous_const hc, fun μ _ => ?_⟩
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hba : 0 < b - a := by have := hab s₀; linarith
  have hck : (b - a) / k ≤ ε := by
    rw [div_le_iff₀ hk']
    have := Nat.le_ceil ((b - a) / ε)
    rw [div_le_iff₀ hε] at this
    have : (⌈(b - a) / ε⌉₊ : ℝ) ≤ k := by simp [k]
    nlinarith
  -- the pointwise inequality, with `g = (f − a)/(b − a)`
  set cnt : S → ℝ := fun s => ∑ i ∈ Finset.Icc 1 k, (F i).indicator 1 s
  have hcnt : ∀ s, cnt s = (((Finset.Icc 1 k).filter fun i : ℕ =>
      (i : ℝ) / k ≤ (f s - a) / (b - a)).card : ℝ) := fun s => by
    simp only [cnt, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : a + (b - a) * i / k ≤ f s ↔ (i : ℝ) / k ≤ (f s - a) / (b - a) := by
      have e : (b - a) * (i : ℝ) / k = (i : ℝ) / k * (b - a) := by ring
      rw [le_div_iff₀ hba, ← e]; constructor <;> intro h <;> linarith
    by_cases h : a + (b - a) * i / k ≤ f s
    · have hm : s ∈ F i := h
      simp [Set.indicator_of_mem hm, this.1 h]
    · have hm : s ∉ F i := h
      have h2 : ¬ ((i : ℝ) / k ≤ (f s - a) / (b - a)) := fun h' => h (this.2 h')
      simp [Set.indicator_of_notMem hm, h2]
  have hpt : ∀ s, (b - a) / k * cnt s ≤ f s - a ∧ f s - a ≤ (b - a) / k * cnt s + (b - a) / k := by
    intro s
    obtain ⟨h1, h2⟩ := hab s
    obtain ⟨c1, c2⟩ := count_bounds hk (g := (f s - a) / (b - a)) (div_nonneg (by linarith) hba.le)
      ((div_lt_one hba).2 (by linarith))
    rw [hcnt]
    constructor
    · calc (b - a) / k * _ = (b - a) * (_ / k) := by ring
        _ ≤ (b - a) * ((f s - a) / (b - a)) := mul_le_mul_of_nonneg_left c1 hba.le
        _ = f s - a := by field_simp
    · calc f s - a = (b - a) * ((f s - a) / (b - a)) := by field_simp
        _ ≤ (b - a) * ((_ + 1) / k) := mul_le_mul_of_nonneg_left c2.le hba.le
        _ = _ := by ring
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable (|a| + |b|)
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; obtain ⟨h1, h2⟩ := hab s
      constructor <;> linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b])
  have hci : Integrable cnt μ := integrable_finsetSum _ fun i _ =>
    (integrable_const 1).indicator (measurableSet_le measurable_const hf)
  have hint_cnt : ∫ s, cnt s ∂μ = ∑ i ∈ Finset.Icc 1 k, μ.real (F i) := by
    rw [integral_finsetSum _ fun i _ => (integrable_const 1).indicator
      (measurableSet_le measurable_const hf)]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one
      (measurableSet_le measurable_const hf)
  have hfa : Integrable (fun s => f s - a) μ := hfi.sub (integrable_const a)
  have hca : Integrable (fun s => (b - a) / k * cnt s + (b - a) / k) μ :=
    (hci.const_mul _).add (integrable_const _)
  have hlo := integral_mono (hci.const_mul ((b - a) / k)) hfa fun s => (hpt s).1
  have hhi := integral_mono hfa hca fun s => (hpt s).2
  rw [integral_const_mul, hint_cnt, integral_sub hfi (integrable_const a)] at hlo
  rw [integral_add (hci.const_mul _) (integrable_const _), integral_const_mul, hint_cnt,
    integral_sub hfi (integrable_const a)] at hhi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlo hhi
  constructor <;> linarith

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Characterizations of weak convergence

Copied from `RecursiveMethods/ConvergenceApplications` (module `Portmanteau`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §12.1, Theorem 12.3, pp. 358–360. For probability measures `λₙ`, `λ` on a metric space the
following are equivalent (`theorem_12_3`):

* (a) `λₙ ⇒ λ`;
* (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`;
* (c) `liminf λₙ(G) ≥ λ(G)` for open `G`;
* (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`.

`limsup ≤` and `liminf ≥` are written as: for every `ε > 0`, eventually `λₙ(F) < λ(F) + ε`
(`LimsupLe`), respectively `λₙ(G) > λ(G) − ε`. The proofs follow the book: (a) ⇒ (b) by
Lemma 12.1, (b) ⇒ (a) by Lemma 12.2, (b) ⇔ (c) by complements, (b) ⇒ (d) through the interior and
the closure, and (d) ⇒ (b) through thickenings with null boundaries.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- `limsup uₙ ≤ c`, written without `limsup`. -/
def LimsupLe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, u n < c + ε

/-- `liminf uₙ ≥ c`, written without `liminf`. -/
def LiminfGe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, c - ε < u n

theorem tendsto_of_limsup_liminf {u : ℕ → ℝ} {c : ℝ} (h1 : LimsupLe u c) (h2 : LiminfGe u c) :
    Tendsto u atTop (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [h2 (c - a) (by linarith)] with n hn; linarith
  · filter_upwards [h1 (a - c) (by linarith)] with n hn; linarith

/-- A continuous function with values in `[0, 1]` as a bounded continuous function. -/
noncomputable def toBCF {f : S → ℝ} (hc : Continuous f) (h : ∀ s, 0 ≤ f s ∧ f s ≤ 1) : S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hc⟩ 1 fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith [h x, h y]

/-- (a) ⇒ (b). -/
theorem limsup_closed_of_weak {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] (h : ConvWeak ls l) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨f, hc, -, h1, h01, hlim⟩ := lemma_12_1 hF
  obtain ⟨m, hm⟩ := ((hlim l).eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  set g := toBCF (hc m) (h01 m)
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], μ.real F ≤ ∫ s, g s ∂μ := by
    intro μ _
    rw [← integral_indicator_one hF.measurableSet]
    refine integral_mono (integrable_const (1 : ℝ) |>.indicator hF.measurableSet)
      (g.integrable μ) fun s => ?_
    by_cases hs : s ∈ F
    · simp [indicator_of_mem hs, g, toBCF, h1 m s hs]
    · simp [indicator_of_notMem hs, g, toBCF, (h01 m s).1]
  filter_upwards [(h g).eventually (gt_mem_nhds (show ∫ s, g s ∂l < l.real F + ε by
    change ∫ s, f m s ∂l < _; linarith))] with n hn
  exact (hint (ls n)).trans_lt hn

/-- The upper half of (b) ⇒ (a), through Lemma 12.2. -/
theorem limsup_integral_of_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) (g : S →ᵇ ℝ) :
    LimsupLe (fun n => ∫ s, g s ∂ls n) (∫ s, g s ∂l) := by
  intro ε hε
  set a := -‖g‖ - 1
  set b := ‖g‖ + 1
  have hab : ∀ s, a ≤ g s ∧ g s < b := fun s => by
    have := abs_le.1 ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm s)
    constructor <;> linarith
  have hc : 0 < b - a := by simp only [a, b]; linarith [norm_nonneg g]
  obtain ⟨k, hk, F, -, hFc, hF⟩ :=
    lemma_12_2 g.continuous.measurable hab (ε := ε / 3) (by positivity)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set δ := ε / (3 * (b - a))
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc 1 k, (ls n).real (F i) < l.real (F i) + δ :=
    (Filter.eventually_all_finset _).2 fun i _ => hb (F i) (hFc g.continuous i) δ hδ
  filter_upwards [hev] with n hn
  obtain ⟨-, hup⟩ := hF (ls n)
  obtain ⟨hlo, -⟩ := hF l
  have hsum : ∑ i ∈ Finset.Icc 1 k, (ls n).real (F i) ≤
      ∑ i ∈ Finset.Icc 1 k, l.real (F i) + k * δ := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 k, (l.real (F i) + δ) :=
          Finset.sum_le_sum fun i hi => (hn i hi).le
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hkδ : (b - a) / k * (k * δ) = ε / 3 := by
    simp only [δ]; field_simp
  have := mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hk'.le)
  rw [mul_add, hkδ] at this
  linarith

/-- (b) ⇒ (a). -/
theorem weak_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) : ConvWeak ls l := by
  intro g
  refine tendsto_of_limsup_liminf (limsup_integral_of_closed hb g) fun ε hε => ?_
  filter_upwards [limsup_integral_of_closed hb (-g) ε hε] with n hn
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, integral_neg] at hn
  linarith

/-- (b) ⇒ (c), by complements. -/
theorem liminf_open_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {G : Set S}
    (hG : IsOpen G) : LiminfGe (fun n => (ls n).real G) (l.real G) := by
  intro ε hε
  filter_upwards [hb Gᶜ hG.isClosed_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hG.measurableSet,
    probReal_compl_eq_one_sub hG.measurableSet] at hn
  linarith

/-- (c) ⇒ (b), by complements. -/
theorem limsup_closed_of_liminf_open {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hc : ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  filter_upwards [hc Fᶜ hF.isOpen_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hF.measurableSet,
    probReal_compl_eq_one_sub hF.measurableSet] at hn
  linarith

/-- (b) ⇒ (d): `λ(Å) = λ(A) = λ(Ā)` when `λ(∂A) = 0`. -/
theorem tendsto_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {A : Set S}
    (h0 : l (frontier A) = 0) :
    Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A)) := by
  have hcl : l.real (closure A) ≤ l.real (interior A) := by
    rw [closure_eq_interior_union_frontier]
    refine (measureReal_union_le _ _).trans ?_
    rw [measureReal_def (s := frontier A), h0, ENNReal.toReal_zero, add_zero]
  have h1 : l.real (interior A) ≤ l.real A := measureReal_mono interior_subset
  have h2 : l.real A ≤ l.real (closure A) := measureReal_mono subset_closure
  refine tendsto_of_limsup_liminf (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [hb _ isClosed_closure ε hε] with n hn
    have := measureReal_mono (μ := ls n) (subset_closure (s := A))
    linarith
  · filter_upwards [liminf_open_of_limsup_closed hb isOpen_interior ε hε] with n hn
    have := measureReal_mono (μ := ls n) (interior_subset (s := A))
    linarith

/-- (d) ⇒ (b), through thickenings `{ρ(·, F) < r}` with null boundaries. -/
theorem limsup_closed_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hd : ∀ A, MeasurableSet A → l (frontier A) = 0 →
      Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) {F : Set S} (hF : IsClosed F) :
    LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l F
  have hlim :=
    tendsto_measure_thickening_of_isClosed (μ := l) ⟨1, one_pos, measure_ne_top _ _⟩ hF
  have hrs' : Tendsto rs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hrs, Eventually.of_forall fun n => (hpos n).1⟩
  have hlim' : Tendsto (fun n => l.real (Metric.thickening (rs n) F)) atTop (𝓝 (l.real F)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hlim.comp hrs')
  obtain ⟨m, hm⟩ := (hlim'.eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  have hA := hd _ Metric.isOpen_thickening.measurableSet (hpos m).2
  filter_upwards [hA.eventually (gt_mem_nhds (show l.real (Metric.thickening (rs m) F) <
    l.real (Metric.thickening (rs m) F) + ε / 2 by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (Metric.self_subset_thickening (hpos m).1 F)
  linarith

/-- **Theorem 12.3.** For probability measures on a metric space, the following are equivalent:
(a) `λₙ ⇒ λ`; (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`; (c) `liminf λₙ(G) ≥ λ(G)` for open
`G`; (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`. -/
theorem theorem_12_3 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    (ConvWeak ls l ↔ ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) ∧
      (ConvWeak ls l ↔ ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) ∧
      (ConvWeak ls l ↔ ∀ A, MeasurableSet A → l (frontier A) = 0 →
        Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) := by
  refine ⟨⟨fun h F hF => limsup_closed_of_weak h hF, weak_of_limsup_closed⟩, ⟨fun h G hG =>
    liminf_open_of_limsup_closed (fun F hF => limsup_closed_of_weak h hF) hG,
    fun hc => weak_of_limsup_closed fun F hF => limsup_closed_of_liminf_open hc hF⟩,
    ⟨fun h A _ h0 => tendsto_of_null_frontier (fun F hF => limsup_closed_of_weak h hF) h0,
    fun hd => weak_of_limsup_closed fun F hF => limsup_closed_of_null_frontier hd hF⟩⟩

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence-determining families and uniqueness

Copied from `RecursiveMethods/ConvergenceApplications` (module `Determining`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §12.1, Theorems 12.4–12.6 and their corollaries, pp. 360–364.

* **Theorem 12.4** (`theorem_12_4`): if `𝒜` is closed under finite intersections and every open
  set is a countable union of members of `𝒜`, then `λₙ(A) → λ(A)` on `𝒜` gives `λₙ ⇒ λ`.
  Finite unions converge by inclusion–exclusion (`tendsto_finite_union`), and then condition (c)
  of Theorem 12.3 holds.
* **Theorem 12.5** (`theorem_12_5`): in a second countable metric space, it suffices that every
  ball `b(x, ε)` contain some `A ∈ 𝒜` with `x ∈ Å`. The book takes `S` a Borel subset of `ℝˡ`;
  every subset of `ℝˡ` is second countable, so the theorem applies to it.
* **Corollary** (`theorem_12_5_cor`): finite intersections of open balls with `λ`-null
  boundaries form a convergence-determining class (`IsConvDetermining`).
* **Theorem 12.6** (`theorem_12_6`): every Borel set lies between a closed and an open set whose
  measures differ by less than `ε`. Proved from Mathlib's regularity of finite measures on
  metric spaces.
* **Corollaries 1–2** (`theorem_12_6_cor1`, `theorem_12_6_cor2`): two probability measures that
  agree on closed sets, or on integrals of bounded continuous functions, are equal; so weak
  limits are unique (`convWeak_unique`), and a convergence-determining class determines measures
  (`IsConvDetermining.eq`, the book's "(Why?)" on p. 362).
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [BorelSpace S] in
/-- Finite unions `⋃_{j<m} Aⱼ` of members of `𝒜` converge, by inclusion–exclusion. -/
theorem tendsto_finite_union {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) :
    ∀ m (A : ℕ → Set S), (∀ i, A i ∈ 𝒜) →
      Tendsto (fun n => (ls n).real (⋃ j ∈ Finset.range m, A j)) atTop
        (𝓝 (l.real (⋃ j ∈ Finset.range m, A j))) := by
  intro m
  induction m with
  | zero => intro A _; simp
  | succ m ih =>
    intro A hA
    have hU : (⋃ j ∈ Finset.range (m + 1), A j) = (⋃ j ∈ Finset.range m, A j) ∪ A m := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hI : (⋃ j ∈ Finset.range m, A j) ∩ A m = ⋃ j ∈ Finset.range m, (A j ∩ A m) := by
      rw [iUnion₂_inter]
    have hmU : MeasurableSet (⋃ j ∈ Finset.range m, A j) :=
      Finset.measurableSet_biUnion _ fun j _ => hmeas _ (hA j)
    have key : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        μ.real (⋃ j ∈ Finset.range (m + 1), A j) = μ.real (⋃ j ∈ Finset.range m, A j) +
          μ.real (A m) - μ.real (⋃ j ∈ Finset.range m, (A j ∩ A m)) := by
      intro μ _
      rw [hU, ← hI]
      have := measureReal_union_add_inter (μ := μ) (s := ⋃ j ∈ Finset.range m, A j)
        (hmeas _ (hA m)) (measure_ne_top μ _) (measure_ne_top μ _)
      linarith
    simp_rw [key]
    exact ((ih A hA).add (h _ (hA m))).sub
      (ih (fun j => A j ∩ A m) fun j => hinter _ (hA j) _ (hA m))

/-- **Theorem 12.4.** If `𝒜` is closed under finite intersections and every open set is a
countable union of members of `𝒜`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_4 {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hopen : ∀ G, IsOpen G → ∃ T : Set (Set S), T.Countable ∧ T ⊆ 𝒜 ∧ ⋃₀ T = G)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine (theorem_12_3 ls l).2.1.2 fun G hG ε hε => ?_
  obtain ⟨T, hTc, hT𝒜, hTG⟩ := hopen G hG
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · rw [sUnion_empty] at hTG
    subst hTG
    exact Eventually.of_forall fun n => by simp; linarith
  obtain ⟨A, hAeq⟩ := hTc.exists_eq_range hTne
  have hA : ∀ i, A i ∈ 𝒜 := fun i => hT𝒜 (hAeq ▸ mem_range_self i)
  have hGA : G = ⋃ i, A i := by rw [← hTG, hAeq, sUnion_range]
  -- continuity from below
  set U : ℕ → Set S := fun m => ⋃ j ∈ Finset.range m, A j
  have hmono : Monotone U := fun m m' hmm' => biUnion_subset_biUnion_left
    (Finset.coe_subset.2 (Finset.range_subset_range.2 hmm'))
  have hUG : (⋃ m, U m) = G := by
    rw [hGA]
    ext x
    simp only [U, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨_, j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j + 1, j, by omega, hj⟩⟩
  have hlim : Tendsto (fun m => l.real (U m)) atTop (𝓝 (l.real G)) := by
    have := tendsto_measure_iUnion_atTop (μ := l) hmono
    rw [hUG] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds (show l.real G - ε / 2 < l.real G by
    linarith))).exists
  filter_upwards [(tendsto_finite_union hmeas hinter h m A hA).eventually
    (lt_mem_nhds (show l.real (U m) - ε / 2 < l.real (U m) by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (show U m ⊆ G from hUG ▸ subset_iUnion U m)
  simp only [U] at hn hm this
  linarith

/-- **Theorem 12.5.** In a second countable metric space (for instance any Borel `S ⊆ ℝˡ`), if
`𝒜` is closed under finite intersections and every ball `b(x, ε)` contains some `A ∈ 𝒜` with
`x ∈ Å`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_5 [SecondCountableTopology S] {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hball : ∀ x, ∀ ε > 0, ∃ A ∈ 𝒜, x ∈ interior A ∧ A ⊆ Metric.ball x ε)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine theorem_12_4 hmeas hinter (fun G hG => ?_) h
  -- for `x ∈ G` choose `Aₓ ∈ 𝒜` with `x ∈ Åₓ ⊆ Aₓ ⊆ G`
  have hx : ∀ x : G, ∃ A ∈ 𝒜, (x : S) ∈ interior A ∧ A ⊆ G := fun x => by
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hG x x.2
    obtain ⟨A, hA, hxA, hAb⟩ := hball x ε hε
    exact ⟨A, hA, hxA, hAb.trans hεG⟩
  choose A hA hxA hAG using hx
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : G => interior (A x))
    fun _ => isOpen_interior
  have hcover : (⋃ x : G, interior (A x)) = G := by
    refine subset_antisymm (iUnion_subset fun x => interior_subset.trans (hAG x)) fun y hy => ?_
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hxA ⟨y, hy⟩⟩
  refine ⟨A '' T, hTc.image A, image_subset_iff.2 fun x _ => hA x, subset_antisymm ?_ ?_⟩
  · exact sUnion_subset fun _ ⟨x, _, hx⟩ => hx ▸ hAG x
  · intro y hy
    rw [← hcover, ← hTeq] at hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 hy
    exact ⟨A x, ⟨x, hxT, rfl⟩, interior_subset hyx⟩

/-- `𝒜` is a **convergence-determining class** (p. 362): `λₙ(A) → λ(A)` for all `A ∈ 𝒜` with
`λ(∂A) = 0` implies `λₙ ⇒ λ`. -/
def IsConvDetermining (𝒜 : Set (Set S)) : Prop :=
  ∀ (ls : ℕ → Measure S) (l : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
    IsProbabilityMeasure l →
      (∀ A ∈ 𝒜, l (frontier A) = 0 → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) →
        ConvWeak ls l

omit [MeasurableSpace S] [BorelSpace S] in
/-- The boundary of a finite intersection lies in the union of the boundaries. -/
theorem frontier_iInter_fin_subset {m : ℕ} (s : Fin m → Set S) :
    frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  rw [frontier, interior_iInter_of_finite] at hx
  obtain ⟨hcl, hint⟩ := hx
  simp only [mem_iInter, not_forall] at hint
  obtain ⟨i, hi⟩ := hint
  exact mem_iUnion.2 ⟨i, closure_mono (iInter_subset s i) hcl, hi⟩

/-- Finite intersections of open balls. -/
def ballInters (S : Type*) [MetricSpace S] : Set (Set S) :=
  {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ, A = ⋂ i, Metric.ball (c i) (r i)}

/-- **Corollary to Theorem 12.5.** In a second countable metric space, finite intersections of
open balls form a convergence-determining class. -/
theorem theorem_12_5_cor [SecondCountableTopology S] : IsConvDetermining (ballInters S) := by
  intro ls l _ _ h
  -- the finite intersections of balls whose boundaries are `λ`-null
  set 𝒜 : Set (Set S) := {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ,
    (∀ i, l (frontier (Metric.ball (c i) (r i))) = 0) ∧ A = ⋂ i, Metric.ball (c i) (r i)}
  have hfr : ∀ A ∈ 𝒜, l (frontier A) = 0 := by
    rintro A ⟨m, c, r, hnull, rfl⟩
    refine measure_mono_null (frontier_iInter_fin_subset _) ?_
    exact measure_iUnion_null hnull
  refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨m, c, r, _, hA⟩ => hA ▸
    MeasurableSet.iInter fun i => Metric.isOpen_ball.measurableSet) ?_ ?_
    (fun A hA => h A (by obtain ⟨m, c, r, -, hA⟩ := hA; exact ⟨m, c, r, hA⟩) (hfr A hA))
  · rintro A ⟨m, c, r, hn, rfl⟩ B ⟨m', c', r', hn', rfl⟩
    refine ⟨m + m', Fin.append c c', Fin.append r r', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hn i
      · simpa using hn' i
    · ext x
      simp only [mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩ i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa using h1 i
        · simpa using h2 i
      · intro h
        exact ⟨fun i => by simpa using h (Fin.castAdd m' i),
          fun i => by simpa using h (Fin.natAdd m i)⟩
  · intro x ε hε
    obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l {x}
    obtain ⟨n, hn⟩ := (hrs.eventually (gt_mem_nhds hε)).exists
    refine ⟨Metric.ball x (rs n), ⟨1, fun _ => x, fun _ => rs n, fun _ => ?_, ?_⟩, ?_,
      Metric.ball_subset_ball hn.le⟩
    · simpa [Metric.thickening_singleton] using (hpos n).2
    · ext y; simp
    · rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (hpos n).1

/-- **Theorem 12.6.** For a probability measure on a metric space, every Borel set `B` lies
between a closed `A` and an open `C` with `λ(C) − λ(A) < ε`. -/
theorem theorem_12_6 (l : Measure S) [IsProbabilityMeasure l] {B : Set S} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A C, IsClosed A ∧ IsOpen C ∧ A ⊆ B ∧ B ⊆ C ∧ l.real C - l.real A < ε := by
  have hε2 : (ENNReal.ofReal (ε / 2)) ≠ 0 := by simp [hε]
  obtain ⟨A, hAB, hA, hlt⟩ := hB.exists_isClosed_lt_add (measure_ne_top l B) hε2
  obtain ⟨C, hBC, hC, hCl⟩ := B.exists_isOpen_lt_of_lt (l B + ENNReal.ofReal (ε / 2))
    (ENNReal.lt_add_right (measure_ne_top l B) hε2)
  refine ⟨A, C, hA, hC, hAB, hBC, ?_⟩
  have h1 : l.real B < l.real A + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hlt
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have h2 : l.real C < l.real B + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hCl
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Corollary 1 to Theorem 12.6.** Probability measures that agree on closed sets are equal. -/
theorem theorem_12_6_cor1 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ A, IsClosed A → l A = μ A) : l = μ := by
  have hr : ∀ A, IsClosed A → l.real A = μ.real A := fun A hA => by simp [Measure.real, h A hA]
  have hopen : ∀ C, IsOpen C → l.real C = μ.real C := fun C hC => by
    have := hr Cᶜ hC.isClosed_compl
    rwa [probReal_compl_eq_one_sub hC.measurableSet, probReal_compl_eq_one_sub hC.measurableSet,
      sub_right_inj] at this
  ext B hB
  have hle : ∀ (ν₁ ν₂ : Measure S) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      (∀ A, IsClosed A → ν₁.real A = ν₂.real A) → (∀ C, IsOpen C → ν₁.real C = ν₂.real C) →
        ν₁.real B ≤ ν₂.real B := by
    intro ν₁ ν₂ _ _ hc ho
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hlt⟩ := theorem_12_6 ν₂ hB hε
    calc ν₁.real B ≤ ν₁.real C := measureReal_mono hBC
      _ = ν₂.real C := ho C hC
      _ < ν₂.real A + ε := by linarith
      _ ≤ ν₂.real B + ε := by linarith [measureReal_mono (μ := ν₂) hAB]
  have h1 := hle l μ hr hopen
  have h2 := hle μ l (fun A hA => (hr A hA).symm) (fun C hC => (hopen C hC).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (le_antisymm h1 h2)

/-- **Corollary 2 to Theorem 12.6.** Probability measures with the same integrals of all
bounded continuous functions are equal (Lemma 12.1 and Corollary 1). -/
theorem theorem_12_6_cor2 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂l = ∫ s, f s ∂μ) : l = μ := by
  refine theorem_12_6_cor1 fun A hA => ?_
  obtain ⟨f, hc, -, -, h01, hlim⟩ := lemma_12_1 hA
  have heq : ∀ n, ∫ s, f n s ∂l = ∫ s, f n s ∂μ := fun n => h (toBCF (hc n) (h01 n))
  have := tendsto_nhds_unique (hlim l) ((hlim μ).congr fun n => (heq n).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- Weak limits are unique (p. 364). -/
theorem convWeak_unique {ls : ℕ → Measure S} {l μ : Measure S} [IsProbabilityMeasure l]
    [IsProbabilityMeasure μ] (h1 : ConvWeak ls l) (h2 : ConvWeak ls μ) : l = μ :=
  theorem_12_6_cor2 fun f => tendsto_nhds_unique (h1 f) (h2 f)

/-- A convergence-determining class determines probability measures (p. 362, "(Why?)"): apply
the definition to the constant sequence `μ`. -/
theorem IsConvDetermining.eq {𝒜 : Set (Set S)} (h𝒜 : IsConvDetermining 𝒜) {l μ : Measure S}
    [IsProbabilityMeasure l] [IsProbabilityMeasure μ] (h : ∀ A ∈ 𝒜, l A = μ A) : l = μ := by
  have hw : ConvWeak (fun _ => μ) l := h𝒜 (fun _ => μ) l (fun _ => inferInstance) inferInstance
    fun A hA _ => by simp [Measure.real, h A hA]
  exact convWeak_unique hw (fun f => tendsto_const_nhds)

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Distribution functions on `ℝˡ`

Copied from `RecursiveMethods/ConvergenceApplications` (module `DistributionFunctions`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §12.2, pp. 364–369. Points of `ℝˡ` are functions `Fin l → ℝ`, ordered coordinatewise. The
distribution function of `λ` is `F(x) = λ((−∞, x])` (`distFun`). The half-open box `(a, b]` is
`∏ᵢ (aᵢ, bᵢ]` (`box`), and for `t ⊆ {1, …, l}` its vertex `a + θₜd` takes `bᵢ` for `i ∈ t` and
`aᵢ` otherwise (`vertex`).

* **Exercise 12.3** (`ex_12_3`): a nondecreasing `F` continuous from above and from below at `x`
  is continuous at `x`.
* **Theorem 12.7a** (`theorem_12_7a`): (D1) `F` is nondecreasing, tends to `0` as any coordinate
  tends to `−∞`, and to `1` as all coordinates tend to `+∞`; (D2) `F` is continuous from above;
  (D3) `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b]) ≥ 0`. (D3) comes from the identity
  `1_{(a,b]} = ∏ᵢ (1[xᵢ ≤ bᵢ] − 1[xᵢ ≤ aᵢ])`, expanded as a sum over `t`.
* **Theorem 12.7b**, uniqueness (`distFun_injective`): the sets `(−∞, x]` form a π-system
  generating the Borel sets of `ℝˡ`, so `F` determines `λ`. Existence is in
  `MultivariateStieltjes`.
* **Theorem 12.7c** (`theorem_12_7c`): `F` is continuous from below at `x` iff `λ(∂(−∞, x]) = 0`.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set

variable {l : ℕ}

/-- The distribution function `F(x) = λ((−∞, x])`. -/
noncomputable def distFun (μ : Measure (Fin l → ℝ)) (x : Fin l → ℝ) : ℝ := μ.real (Iic x)

/-- The half-open box `(a, b] = ∏ᵢ (aᵢ, bᵢ]`. -/
def box (a b : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Ioc (a i) (b i)

/-- The vertex of `(a, b]` taking `bᵢ` for `i ∈ t` and `aᵢ` otherwise. -/
def vertex (a b : Fin l → ℝ) (t : Finset (Fin l)) : Fin l → ℝ := fun i => if i ∈ t then b i else a i

/-- The alternating vertex sum `Σₜ (−1)^{l − |t|} F(a + θₜd)` of (D3). -/
def vertexSum (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) : ℝ :=
  ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * F (vertex a b t)

/-- The vector `ε1 = (ε, …, ε)`. -/
def diag (ε : ℝ) : Fin l → ℝ := fun _ => ε

/-- `F` is **continuous from above** at `x`: `F(x + ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromAbove (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x + diag ε)) (𝓝[>] 0) (𝓝 (F x))

/-- `F` is **continuous from below** at `x`: `F(x − ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromBelow (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x - diag ε)) (𝓝[>] 0) (𝓝 (F x))

theorem Iic_eq_pi (x : Fin l → ℝ) : Iic x = Set.pi univ fun i => Iic (x i) := by
  ext y; simp [Pi.le_def]

/-- The product expansion: `1_{(a,b]}(y) = Σₜ (−1)^{l − |t|} 1[y ≤ a + θₜd]` for `a ≤ b`. -/
theorem box_indicator_eq {a b : Fin l → ℝ} (hab : a ≤ b) (y : Fin l → ℝ) :
    (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * (Iic (vertex a b t)).indicator 1 y := by
  classical
  -- `1_{(a,b]}(y) = ∏ᵢ (1[yᵢ ≤ bᵢ] − 1[yᵢ ≤ aᵢ])`
  have hprod : (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∏ i, ((Iic (b i)).indicator (1 : ℝ → ℝ) (y i) + -(Iic (a i)).indicator 1 (y i)) := by
    by_cases hy : y ∈ box a b
    · rw [indicator_of_mem hy, Pi.one_apply]
      symm
      refine Finset.prod_eq_one fun i _ => ?_
      have hi := hy i (mem_univ i)
      rw [indicator_of_mem (show y i ∈ Iic (b i) from hi.2),
        indicator_of_notMem (show y i ∉ Iic (a i) from fun h => (not_le.2 hi.1) h)]
      simp
    · rw [indicator_of_notMem hy]
      simp only [box, Set.mem_pi, mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : y i ≤ a i
      · rw [indicator_of_mem (show y i ∈ Iic (b i) from h1.trans (hab i)),
          indicator_of_mem (show y i ∈ Iic (a i) from h1)]; simp
      · have h2 : ¬ y i ≤ b i := fun h => hi ⟨not_le.1 h1, h⟩
        rw [indicator_of_notMem (show y i ∉ Iic (b i) from h2),
          indicator_of_notMem (show y i ∉ Iic (a i) from h1)]; simp
  rw [hprod, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin]
  -- the product of indicators is the indicator of `(−∞, vertex]`
  have hv : (∏ i ∈ t, (Iic (b i)).indicator (1 : ℝ → ℝ) (y i)) *
      ∏ i ∈ Finset.univ \ t, (Iic (a i)).indicator (1 : ℝ → ℝ) (y i) =
        (Iic (vertex a b t)).indicator 1 y := by
    by_cases hy : y ≤ vertex a b t
    · rw [indicator_of_mem (show y ∈ Iic (vertex a b t) from hy), Pi.one_apply]
      rw [Finset.prod_eq_one fun i hi => ?_, Finset.prod_eq_one fun i hi => ?_, one_mul]
      · have := hy i; simp only [vertex, Finset.mem_sdiff] at this hi
        simp only [hi.2, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (a i) from this)]; rfl
      · have := hy i; simp only [vertex] at this
        simp only [hi, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (b i) from this)]; rfl
    · rw [indicator_of_notMem (show y ∉ Iic (vertex a b t) from hy)]
      rw [Pi.le_def] at hy
      push Not at hy
      obtain ⟨i, hi⟩ := hy
      by_cases hit : i ∈ t
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero hit (indicator_of_notMem (show y i ∉ Iic (b i) from
          not_le.2 hi) _), zero_mul]
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hit⟩)
          (indicator_of_notMem (show y i ∉ Iic (a i) from not_le.2 hi) _), mul_zero]
  rw [← hv]
  ring

theorem measurableSet_box (a b : Fin l → ℝ) : MeasurableSet (box a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- (D3): `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b])`. -/
theorem vertexSum_eq (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] {a b : Fin l → ℝ}
    (hab : a ≤ b) : vertexSum (distFun μ) a b = μ.real (box a b) := by
  rw [← integral_indicator_one (measurableSet_box a b)]
  simp_rw [box_indicator_eq hab]
  rw [integral_finsetSum _ fun t _ =>
    ((integrable_const 1).indicator measurableSet_Iic).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic]
  rfl

theorem distFun_mono (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] : Monotone (distFun μ) :=
  fun _ _ hxy => measureReal_mono (Iic_subset_Iic.2 hxy)

/-- Continuity from above of `F`, as a squeeze along `ε ↓ 0`, given decreasing sets whose
measures converge. -/
theorem contFromAbove_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) : ContFromAbove (distFun μ) x := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x + diag (1 / (n + 1)))
  have hanti : Antitone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.add_apply, diag]
    gcongr
  have hinter : (⋂ n, A n) = Iic x := by
    ext y
    simp only [A, mem_iInter, mem_Iic, Pi.le_def, Pi.add_apply, diag]
    constructor
    · intro h i
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      linarith [h n i]
    · intro h n i
      linarith [h i, show (0 : ℝ) < 1 / (n + 1) by positivity]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (Iic x))) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [ContFromAbove, tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_of_lt_of_le hc (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [show (0 : ℝ) < ε from hε])
  · obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [hε.2]) hn

/-- **Theorem 12.7a.** The distribution function of a probability measure on `ℝˡ` satisfies
(D1): it is nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all
coordinates tend to `+∞`; (D2): it is continuous from above; and (D3): the alternating vertex
sum over any box is `λ((a, b]) ≥ 0`. -/
theorem theorem_12_7a (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    (Monotone (distFun μ) ∧
      (∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → distFun μ x < ε) ∧
      (∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < distFun μ x)) ∧
      (∀ x, ContFromAbove (distFun μ) x) ∧
      ∀ a b, a ≤ b → vertexSum (distFun μ) a b = μ.real (box a b) ∧
        0 ≤ vertexSum (distFun μ) a b := by
  refine ⟨⟨distFun_mono μ, fun i ε hε => ?_, fun ε hε => ?_⟩, contFromAbove_distFun μ,
    fun a b hab => ⟨vertexSum_eq μ hab, vertexSum_eq μ hab ▸ measureReal_nonneg⟩⟩
  · -- the `i`-th marginal of `(−∞, −n]` tends to `0`
    set A : ℕ → Set (Fin l → ℝ) := fun n => {y | y i ≤ -n}
    have hanti : Antitone A := fun m n hmn y hy => by
      simp only [A, mem_ofPred_eq] at hy ⊢
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hempty : (⋂ n, A n) = ∅ := by
      ext y
      simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y i)
      exact ⟨n, by linarith⟩
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hε)).exists
    refine ⟨-n, fun x hx => lt_of_le_of_lt (measureReal_mono fun y hy => ?_) hn⟩
    exact (hy i).trans hx
  · -- the sets `(−∞, n1]` increase to `ℝˡ`
    set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (diag n)
    have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
      simp only [diag]; exact_mod_cast hmn
    have hunion : (⋃ n, A n) = univ := by
      refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌈∑ j, |y j|⌉₊, fun i => ?_⟩
      simp only [diag]
      calc y i ≤ |y i| := le_abs_self _
        _ ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        _ ≤ ⌈∑ j, |y j|⌉₊ := Nat.le_ceil _
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, measure_univ] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 1) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))).exists
    exact ⟨n, fun x hx => lt_of_lt_of_le hn (distFun_mono μ fun i => hx i)⟩

/-- The sets `(−∞, x]` generate the Borel sets of `ℝˡ`. -/
theorem generateFrom_Iic_pi :
    MeasurableSpace.generateFrom (range fun x : Fin l → ℝ => Iic x) =
      (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) := by
  rw [← generateFrom_eq_pi (C := fun _ => range (Iic : ℝ → Set ℝ))
    (fun _ => (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm)
    fun _ => ⟨fun n => Iic (n : ℝ), fun n => mem_range_self _,
      eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩]
  congr 1
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => Iic (x i), fun i _ => ⟨x i, rfl⟩, (Iic_eq_pi x).symm⟩
  · rintro ⟨T, hT, rfl⟩
    choose x hx using fun i => hT i (mem_univ i)
    exact ⟨x, by change Iic x = _; rw [Iic_eq_pi]; congr 1; funext i; exact hx i⟩

/-- **Theorem 12.7b** (uniqueness). A probability measure on `ℝˡ` is determined by its
distribution function. -/
theorem distFun_injective {μ ν : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : distFun μ = distFun ν) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_Iic_pi.symm ?_ ?_ (by simp)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact ⟨x ⊓ y, Iic_inter_Iic.symm⟩
  · rintro _ ⟨x, rfl⟩
    have := congrFun h x
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- The open lower orthant `{y : y < x}` (all coordinates strictly smaller). -/
def lowerOpen (x : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Iio (x i)

theorem frontier_Iic_eq (x : Fin l → ℝ) : frontier (Iic x) = Iic x \ lowerOpen x := by
  rw [frontier, isClosed_Iic.closure_eq, Iic_eq_pi, interior_pi_set finite_univ]
  simp_rw [interior_Iic]
  rfl

theorem lowerOpen_subset (x : Fin l → ℝ) : lowerOpen x ⊆ Iic x := fun _ hy i => (hy i trivial).le

/-- `F(x − ε1) → λ({y < x})` as `ε ↓ 0`. -/
theorem tendsto_distFun_below (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) :
    Tendsto (fun ε => distFun μ (x - diag ε)) (𝓝[>] 0) (𝓝 (μ.real (lowerOpen x))) := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x - diag (1 / (n + 1)))
  have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.sub_apply, diag]
    gcongr
  have hunion : (⋃ n, A n) = lowerOpen x := by
    ext y
    simp only [A, mem_iUnion, mem_Iic, Pi.le_def, Pi.sub_apply, diag, lowerOpen, Set.mem_pi,
      mem_univ, true_implies, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩ i; linarith [hn i, show (0 : ℝ) < 1 / (n + 1) by positivity]
    · intro h
      choose N hN using fun i => exists_nat_one_div_lt (sub_pos.2 (h i))
      refine ⟨Finset.univ.sup N, fun i => ?_⟩
      have hle : (N i : ℝ) ≤ Finset.univ.sup N := by
        exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ i)
      have : 1 / ((Finset.univ.sup N : ℕ) + 1 : ℝ) ≤ 1 / (N i + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hN i]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (lowerOpen x))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_lt_of_le hn (distFun_mono μ fun i => by
      simp only [Pi.sub_apply, diag]; linarith [hε.2])
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine lt_of_le_of_lt (measureReal_mono (s₂ := lowerOpen x) fun y hy i _ => ?_) hc
    have := hy i
    simp only [Pi.sub_apply, diag] at this
    exact lt_of_le_of_lt this (by linarith [show (0 : ℝ) < ε from hε])

/-- **Theorem 12.7c.** `F` is continuous from below at `x` iff the boundary of `(−∞, x]` is
`λ`-null. -/
theorem theorem_12_7c (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] (x : Fin l → ℝ) :
    ContFromBelow (distFun μ) x ↔ μ (frontier (Iic x)) = 0 := by
  have hdiff : μ.real (frontier (Iic x)) = distFun μ x - μ.real (lowerOpen x) := by
    rw [frontier_Iic_eq, measureReal_sdiff (lowerOpen_subset x)
      (MeasurableSet.univ_pi fun _ => measurableSet_Iio)]
    rfl
  have h0 : μ (frontier (Iic x)) = 0 ↔ μ.real (frontier (Iic x)) = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]; simp [measure_ne_top]
  rw [h0, hdiff, sub_eq_zero]
  constructor
  · intro h
    exact tendsto_nhds_unique h (tendsto_distFun_below μ x)
  · intro h
    rw [ContFromBelow, h]
    exact tendsto_distFun_below μ x

/-- **Exercise 12.3.** A nondecreasing `F` that is continuous from above and from below at `x` is
continuous at `x`. -/
theorem ex_12_3 {F : (Fin l → ℝ) → ℝ} (hF : Monotone F) {x : Fin l → ℝ}
    (ha : ContFromAbove F x) (hb : ContFromBelow F x) : ContinuousAt F x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₁, hε₁, h1⟩ := (Metric.tendsto_nhdsWithin_nhds.1 ha) δ hδ
  obtain ⟨ε₂, hε₂, h2⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hb) δ hδ
  set ε := min ε₁ ε₂ / 2
  have hε : 0 < ε := by positivity
  have hu := h1 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_left ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  have hl := h2 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_right ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  rw [Real.dist_eq] at hu hl
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hε] at hy
  have hlo : x - diag ε ≤ y := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.sub_apply, diag]; linarith
  have hhi : y ≤ x + diag ε := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.add_apply, diag]; linarith
  have := hF hlo
  have := hF hhi
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hu hl
  constructor <;> linarith

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence of distribution functions

Copied from `RecursiveMethods/ConvergenceApplications` (module `DistributionConvergence`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

SLP §12.3, Theorem 12.8 and Exercises 12.4–12.5, pp. 369–372.

* `nullCoord μ i`: the levels `c` with `λ{y : yᵢ = c} = 0`. Its complement is countable
  (`countable_nullCoord_compl`), so it is dense.
* `continuousAt_distFun`: a point whose coordinates are all null levels is a continuity point
  of `F`.
* **Theorem 12.8** (`theorem_12_8`): `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every continuity point `x` of
  `F`. For (⇐), boxes with null-level coordinates satisfy the hypotheses of Theorem 12.5, and
  their measures are alternating sums of `F` at continuity points.
* **Exercise 12.4** (`ex_12_4`): for `S ⊆ ℝˡ` Borel, `λₙ ⇒ λ` on `S` iff the extensions
  `λ̂(A) = λ(A ∩ S)` converge weakly on `ℝˡ`.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {l : ℕ}

/-- The levels `c` with `λ{y : yᵢ = c} = 0`. -/
def nullCoord (μ : Measure (Fin l → ℝ)) (i : Fin l) : Set ℝ := {c | μ {y | y i = c} = 0}

theorem countable_nullCoord_compl (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    (nullCoord μ i)ᶜ.Countable := by
  refine (Measure.countable_meas_level_set_pos (μ := μ) (measurable_pi_apply i)).mono ?_
  intro c hc
  exact pos_iff_ne_zero.2 hc

theorem dense_nullCoord (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    Dense (nullCoord μ i) := by
  simpa using (countable_nullCoord_compl μ i).dense_compl ℝ

/-- A point whose coordinates are null levels is a continuity point of `F`. -/
theorem continuousAt_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {v : Fin l → ℝ} (hv : ∀ i, v i ∈ nullCoord μ i) : ContinuousAt (distFun μ) v := by
  refine ex_12_3 (distFun_mono μ) (contFromAbove_distFun μ v) ((theorem_12_7c μ v).2 ?_)
  refine measure_mono_null (t := ⋃ i, {y : Fin l → ℝ | y i = v i}) (fun y hy => ?_)
    (measure_iUnion_null fun i => hv i)
  rw [frontier_Iic_eq] at hy
  obtain ⟨hle, hlt⟩ := hy
  simp only [lowerOpen, Set.mem_pi, mem_univ, true_implies, mem_Iio, not_forall, not_lt] at hlt
  obtain ⟨i, hi⟩ := hlt
  exact mem_iUnion.2 ⟨i, le_antisymm (hle i) hi⟩

/-- A continuity point of `F` has a `λ`-null boundary of `(−∞, x]`. -/
theorem frontier_null_of_continuousAt (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {x : Fin l → ℝ} (h : ContinuousAt (distFun μ) x) : μ (frontier (Iic x)) = 0 := by
  refine (theorem_12_7c μ x).1 ?_
  have hc : Tendsto (fun ε : ℝ => x - diag ε) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun ε : ℝ => x - diag ε) (𝓝 0) (𝓝 (x - diag 0)) :=
      (continuous_const.sub (continuous_pi fun _ => continuous_id)).tendsto 0
    have h0 : x - diag 0 = x := by ext; simp [diag]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h.tendsto.comp hc

theorem box_inter (a b a' b' : Fin l → ℝ) : box a b ∩ box a' b' = box (a ⊔ a') (b ⊓ b') := by
  ext y
  simp only [box, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_Ioc, Pi.sup_apply,
    Pi.inf_apply, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2⟩ i; exact ⟨⟨(h1 i).1, (h2 i).1⟩, (h1 i).2, (h2 i).2⟩
  · intro h; exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩

theorem box_eq_empty {a b : Fin l → ℝ} (h : ¬ a ≤ b) : box a b = ∅ := by
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  ext y
  simp only [box, Set.mem_pi, mem_univ, true_implies, mem_Ioc, mem_empty_iff_false, iff_false,
    not_forall]
  exact ⟨i, fun h => by linarith [h.1, h.2]⟩

/-- **Theorem 12.8.** For probability measures on `ℝˡ`, `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every
continuity point `x` of `F`. -/
theorem theorem_12_8 (ls : ℕ → Measure (Fin l → ℝ)) (μ : Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ∀ x, ContinuousAt (distFun μ) x →
      Tendsto (fun n => distFun (ls n) x) atTop (𝓝 (distFun μ x)) := by
  constructor
  · intro h x hx
    exact (theorem_12_3 ls μ).2.2.1 h (Iic x) measurableSet_Iic
      (frontier_null_of_continuousAt μ hx)
  · intro h
    set 𝒜 : Set (Set (Fin l → ℝ)) := {A | ∃ a b, (∀ i, a i ∈ nullCoord μ i ∧
      b i ∈ nullCoord μ i) ∧ A = box a b}
    refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨a, b, _, hA⟩ => hA ▸ measurableSet_box a b) ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨a', b', hab', rfl⟩
      refine ⟨a ⊔ a', b ⊓ b', fun i => ⟨?_, ?_⟩, box_inter a b a' b'⟩
      · simp only [Pi.sup_apply]; rcases le_total (a i) (a' i) with h1 | h1
        · rw [max_eq_right h1]; exact (hab' i).1
        · rw [max_eq_left h1]; exact (hab i).1
      · simp only [Pi.inf_apply]; rcases le_total (b i) (b' i) with h1 | h1
        · rw [min_eq_left h1]; exact (hab i).2
        · rw [min_eq_right h1]; exact (hab' i).2
    · intro x ε hε
      have hε2 : 0 < ε / 2 := by positivity
      choose a ha hai using fun i => (dense_nullCoord μ i).exists_between
        (show x i - ε / 2 < x i by linarith)
      choose b hb hbi using fun i => (dense_nullCoord μ i).exists_between
        (show x i < x i + ε / 2 by linarith)
      refine ⟨box a b, ⟨a, b, fun i => ⟨ha i, hb i⟩, rfl⟩, ?_, fun y hy => ?_⟩
      · refine mem_interior.2 ⟨Set.pi univ fun i => Ioo (a i) (b i), fun y hy i _ =>
          ⟨(hy i trivial).1, (hy i trivial).2.le⟩,
          isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo, fun i _ => ⟨(hai i).2, (hbi i).1⟩⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro i
        have := hy i trivial
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [(hai i).1, (hbi i).2, this.1, this.2]
    · rintro _ ⟨a, b, hab, rfl⟩
      by_cases hle : a ≤ b
      · simp_rw [← vertexSum_eq _ hle]
        refine tendsto_finsetSum _ fun t _ => (h _ ?_).const_mul _
        refine continuousAt_distFun μ fun i => ?_
        simp only [vertex]
        split_ifs
        · exact (hab i).2
        · exact (hab i).1
      · simp [box_eq_empty hle]

/-- **Exercise 12.4.** For `S ⊆ ℝˡ`, `λₙ ⇒ λ` on `S` iff the extensions `λ̂(A) = λ(A ∩ S)` converge
weakly on `ℝˡ`. (Measurability of `S` is not needed.) -/
theorem ex_12_4 {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ConvWeak (fun n => (ls n).map Subtype.val) (μ.map Subtype.val) := by
  have hmap : ∀ (ν : Measure S) {F : Set (Fin l → ℝ)}, MeasurableSet F →
      (ν.map Subtype.val).real F = ν.real (Subtype.val ⁻¹' F) := fun ν F hF => by
    rw [measureReal_def, Measure.map_apply measurable_subtype_coe hF]; rfl
  rw [(theorem_12_3 ls μ).1, (theorem_12_3 _ _).1]
  constructor
  · intro h F hF
    simp_rw [hmap _ hF.measurableSet]
    exact h _ (hF.preimage continuous_subtype_val)
  · intro h A hA
    obtain ⟨F, hF, rfl⟩ := isClosed_induced_iff.1 hA
    have := h F hF
    simp_rw [hmap _ hF.measurableSet] at this
    exact this

/-- **Exercise 12.5a.** On `S = [a, b] ⊆ ℝˡ`, if `λₙ([a, x]) → λ([a, x])` for every `x ∈ S`, then
`λₙ ⇒ λ` (through Exercise 12.4 and Theorem 12.8). -/
theorem ex_12_5a {a b : Fin l → ℝ} (ls : ℕ → Measure (Icc a b)) (μ : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h : ∀ x ∈ Icc a b, Tendsto (fun n => (ls n).real (Subtype.val ⁻¹' Icc a x)) atTop
      (𝓝 (μ.real (Subtype.val ⁻¹' Icc a x)))) : ConvWeak ls μ := by
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := s₀.2.1.trans s₀.2.2
  refine (ex_12_4 ls μ).2 ((theorem_12_8 _ _).2 fun y _ => ?_)
  have hmap : ∀ (ν : Measure (Icc a b)), distFun (ν.map Subtype.val) y =
      ν.real (Subtype.val ⁻¹' Iic y) := fun ν => by
    rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl
  simp_rw [hmap]
  by_cases hay : a ≤ y
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = Subtype.val ⁻¹' Icc a (y ⊓ b) := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_Icc, le_inf_iff]
      exact ⟨fun hs => ⟨s.2.1, hs, s.2.2⟩, fun hs => hs.2.1⟩
    rw [hpre]
    exact h _ ⟨le_inf hay hab, inf_le_right⟩
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = ∅ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hs => hay (s.2.1.trans hs)
    simp [hpre]

/-- The continuous nondecreasing ramp `gₙ(s) = min 1 (n Σᵢ max 0 (sᵢ - xᵢ))`, which increases to the
indicator of `{s : ¬ s ≤ x}` (used for Exercise 12.5b in place of the book's Lemma 12.1
functions). -/
noncomputable def ramp (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : ℝ :=
  min 1 ((n : ℝ) * ∑ i, max 0 (s i - x i))

theorem continuous_ramp (x : Fin l → ℝ) (n : ℕ) : Continuous (ramp x n) := by
  unfold ramp; fun_prop

theorem ramp_mem (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : 0 ≤ ramp x n s ∧ ramp x n s ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg n.cast_nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)), min_le_left _ _⟩

theorem monotone_ramp (x : Fin l → ℝ) (n : ℕ) : Monotone (ramp x n) := fun s t hst =>
  min_le_min_left _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    max_le_max le_rfl (by linarith [hst i])) n.cast_nonneg)

theorem tendsto_ramp (x s : Fin l → ℝ) :
    Tendsto (fun n => ramp x n s) atTop (𝓝 ((Iic x)ᶜ.indicator 1 s)) := by
  by_cases hs : s ≤ x
  · have : ∀ n, ramp x n s = 0 := fun n => by
      have : ∀ i, max 0 (s i - x i) = 0 := fun i => max_eq_left (by linarith [hs i])
      simp [ramp, this]
    simp only [this, indicator_of_notMem (show s ∉ (Iic x)ᶜ by simpa using hs)]
    exact tendsto_const_nhds
  · obtain ⟨i, hi⟩ : ∃ i, x i < s i := by
      by_contra h; push Not at h; exact hs h
    have hc : s i - x i ≤ ∑ j, max 0 (s j - x j) :=
      (le_max_right _ _).trans (Finset.single_le_sum (f := fun j => max 0 (s j - x j))
        (fun j _ => le_max_left _ _) (Finset.mem_univ i))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (s i - x i))
    rw [indicator_of_mem (show s ∈ (Iic x)ᶜ by simpa using hs)]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hpos : 0 < s i - x i := by linarith
    have : 1 ≤ (n : ℝ) * ∑ j, max 0 (s j - x j) := by
      have h1 : 1 < N * (s i - x i) := by rwa [div_lt_iff₀ hpos] at hN
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp [ramp, min_eq_left this]

/-- **Exercise 12.5b** (corrected). On `S = [a, b]`, probability measures agreeing on the integrals
of all continuous nondecreasing functions are equal. (The book's hint cites "Theorem 12.1", i.e.
Lemma 12.1, whose functions are nonincreasing; nondecreasing functions suffice, which is what
Theorem 12.12 needs.) -/
theorem ex_12_5b {a b : Fin l → ℝ} (lam μ : Measure (Icc a b)) [IsProbabilityMeasure lam]
    [IsProbabilityMeasure μ] (h : ∀ f : Icc a b →ᵇ ℝ, Monotone f → ∫ s, f s ∂lam = ∫ s, f s ∂μ) :
    lam = μ := by
  have hE : ∀ x : Fin l → ℝ, MeasurableSet (Subtype.val ⁻¹' (Iic x)ᶜ : Set (Icc a b)) :=
    fun x => measurableSet_Iic.compl.preimage measurable_subtype_coe
  have hlim : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] (x : Fin l → ℝ),
      Tendsto (fun n => ∫ s, ramp x n (s : Fin l → ℝ) ∂ν) atTop
        (𝓝 (ν.real (Subtype.val ⁻¹' (Iic x)ᶜ))) := fun ν _ x => by
    rw [← integral_indicator_one (hE x)]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => ((continuous_ramp x n).comp continuous_subtype_val).aestronglyMeasurable)
      (integrable_const 1) (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (ramp_mem x n s).1]; exact (ramp_mem x n s).2
    · exact tendsto_ramp x s
  have heq : ∀ x : Fin l → ℝ, lam.real (Subtype.val ⁻¹' (Iic x)ᶜ) =
      μ.real (Subtype.val ⁻¹' (Iic x)ᶜ) := fun x => by
    refine tendsto_nhds_unique (hlim lam x) ?_
    have := hlim μ x
    refine this.congr fun n => (h ⟨⟨fun s => ramp x n s,
      (continuous_ramp x n).comp continuous_subtype_val⟩, ⟨1, fun s t => ?_⟩⟩
      (fun s t hst => monotone_ramp x n hst)).symm
    have := ramp_mem x n s; have := ramp_mem x n t
    simp only [Real.dist_eq, abs_le]; constructor <;> linarith
  have hconv : ConvWeak (fun _ => μ) lam := by
    refine ex_12_5a _ _ fun x _ => ?_
    have hpre : (Subtype.val ⁻¹' Icc a x : Set (Icc a b)) = (Subtype.val ⁻¹' (Iic x)ᶜ)ᶜ := by
      ext s
      simp only [mem_preimage, mem_Icc, mem_compl_iff, mem_Iic, not_not]
      exact ⟨fun hs => hs.2, fun hs => ⟨s.2.1, hs⟩⟩
    rw [hpre, probReal_compl_eq_one_sub (hE x), probReal_compl_eq_one_sub (hE x), heq]
    exact tendsto_const_nhds
  exact convWeak_unique hconv fun _ => tendsto_const_nhds

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375)

Copied from `RecursiveMethods/ConvergenceApplications` (module `Helly`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

* the **support** of a probability measure (p. 371): the intersection of two closed sets of measure
  one is closed of measure one ("(Why?)"), and on a second-countable space the smallest closed set
  of measure one exists (`exists_support`, by Lindelöf — the book's "extends to any family" needs
  separability);
* the general lemma behind every compactness argument of the chapter: a **tight** sequence of
  probability measures on a separable metric space has a weakly convergent subsequence
  (`exists_convWeak_subseq_of_tight`, through Prokhorov's theorem);
* **Theorem 12.9 (Helly)** and its **Corollary 1**, corrected: hypothesis (3), `Fₙ(a̲) = 0` and
  `Fₙ(b̄) = 1`, does not confine the measures to `[a̲, b̄]` when `l ≥ 2`
  (`theorem_12_9_false_hyp`: `δ_{(-n, 0)}` has no weakly convergent subsequence), and the
  conclusion `F(a̲) = 0` fails even for `l = 1` (`theorem_12_9_false_concl`: `δ_{1/(n+1)}`). The
  true statement takes the measures concentrated on `[a̲, b̄]` and concludes the same of the limit
  (`theorem_12_9_cor1`, `theorem_12_9`);
* **Exercise 12.6**: (a) holds for `l = 1` (`ex_12_6a`) and fails for `l = 2`
  (`ex_12_6a_false`); (b), (c) are tightness (`ex_12_6b`, `ex_12_6c`; closedness is not needed);
* **Corollary 2** (corrected): a monotone sequence of distribution functions of measures
  concentrated on `[a̲, b̄]` converges weakly (`theorem_12_9_cor2`).
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-! ### The support of a measure -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- `A` is the **support** of `μ` (SLP p. 371): the smallest closed set of measure one. -/
def IsSupport (μ : Measure X) (A : Set X) : Prop :=
  IsClosed A ∧ μ A = 1 ∧ ∀ B, IsClosed B → μ B = 1 → A ⊆ B

variable [OpensMeasurableSpace X]

/-- The "(Why?)" of p. 371: two closed sets of measure one meet in a closed set of measure one. -/
theorem support_inter (μ : Measure X) [IsProbabilityMeasure μ] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hμA : μ A = 1) (hμB : μ B = 1) : IsClosed (A ∩ B) ∧ μ (A ∩ B) = 1 := by
  refine ⟨hA.inter hB, (prob_compl_eq_zero_iff (hA.inter hB).measurableSet).1 ?_⟩
  rw [compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA.measurableSet).2 hμA)
    ((prob_compl_eq_zero_iff hB.measurableSet).2 hμB)

/-- The support exists and is unique on a second-countable space (SLP p. 371–372; the extension
from two sets to an arbitrary family needs Lindelöf). -/
theorem exists_support [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃! A, IsSupport μ A := by
  set C := {B : Set X | IsClosed B ∧ μ B = 1}
  have hcl : IsClosed (⋂₀ C) := isClosed_sInter fun B hB => hB.1
  have hnull : μ (⋂₀ C)ᶜ = 0 := by
    rw [compl_sInter]
    obtain ⟨T, hTc, hTsub, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable (compl '' C)
      (by rintro _ ⟨B, hB, rfl⟩; exact hB.1.isOpen_compl)
    rw [← hTeq]
    refine (measure_sUnion_null_iff hTc).2 fun U hU => ?_
    obtain ⟨B, hB, rfl⟩ := hTsub hU
    exact (prob_compl_eq_zero_iff hB.1.measurableSet).2 hB.2
  refine ⟨⋂₀ C, ⟨hcl, (prob_compl_eq_zero_iff hcl.measurableSet).1 hnull,
    fun B hB hμB => sInter_subset_of_mem ⟨hB, hμB⟩⟩, fun A hA => ?_⟩
  exact (hA.2.2 _ hcl ((prob_compl_eq_zero_iff hcl.measurableSet).1 hnull)).antisymm
    (sInter_subset_of_mem ⟨hA.1, hA.2.1⟩)

/-! ### Tightness and weakly convergent subsequences -/

/-- A **tight** sequence of probability measures on a separable metric space (for every `ε > 0` a
compact `K` with `λₙ(K) > 1 - ε` for all `n`) has a weakly convergent subsequence. This is the
form in which Helly's theorem is used throughout the chapter (Prokhorov's theorem). -/
theorem exists_convWeak_subseq_of_tight {S : Type*} [MetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S] (ls : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  let P : ℕ → ProbabilityMeasure S := fun n => ⟨ls n, inferInstance⟩
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure S) : Measure S) | μ ∈ range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => hεtop ▸ le_top⟩
    obtain ⟨K, hK, hKn⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    have h1 : (ls n).real Kᶜ ≤ ε.toReal := by
      rw [probReal_compl_eq_one_sub hK.measurableSet]; linarith [hKn n]
    change (ls n) Kᶜ ≤ ε
    rw [← ofReal_measureReal (μ := ls n) (s := Kᶜ), ← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨ν, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨ν, inferInstance, φ, hφ, fun f =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f⟩

/-! ### Helly's theorem -/

variable {l : ℕ}

/-- A weak limit of measures concentrated on a closed set is concentrated on it (Theorem 12.3b). -/
theorem measure_eq_one_of_convWeak {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ls : ℕ → Measure S} {μ : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure μ] (h : ConvWeak ls μ) {F : Set S} (hF : IsClosed F)
    (hls : ∀ n, ls n F = 1) : μ F = 1 := by
  have hlim := (theorem_12_3 ls μ).1.1 h F hF
  have h1 : 1 ≤ μ.real F := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨n, hn⟩ := (hlim ε hε).exists
    have h1n : (ls n).real F = 1 := by rw [measureReal_def, hls n, ENNReal.toReal_one]
    change (ls n).real F < _ at hn
    linarith
  have : μ.real F = 1 := le_antisymm measureReal_le_one h1
  rw [← ofReal_measureReal, this, ENNReal.ofReal_one]

/-- **Corollary 1 to Theorem 12.9** (Helly, measure form), corrected: probability measures on
`ℝˡ` concentrated on `[a̲, b̄]` have a subsequence converging weakly to a probability measure
concentrated on `[a̲, b̄]`. -/
theorem theorem_12_9_cor1 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight ls fun ε hε =>
    ⟨Icc a b, isCompact_Icc, fun n => by
      rw [measureReal_def, h n, ENNReal.toReal_one]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  exact ⟨μ, hμ, measure_eq_one_of_convWeak hconv isClosed_Icc fun n => h (φ n), φ, hφ, hconv⟩

/-- Concentration on `[a̲, b̄]` in terms of the distribution function: `F(x) = 0` whenever some
`xᵢ < a̲ᵢ`, and `F(b̄) = 1`. -/
theorem concentrated_iff {a b : Fin l → ℝ} (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    μ (Icc a b) = 1 ↔ (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 := by
  constructor
  · intro h
    have hc : μ (Icc a b)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 h
    refine ⟨fun x ⟨i, hi⟩ => ?_, ?_⟩
    · have : μ (Iic x) = 0 := measure_mono_null (t := (Icc a b)ᶜ) (fun y hy hyab => by
        exact absurd ((hyab.1 i).trans (hy i)) (not_le.2 hi)) hc
      rw [distFun, measureReal_def, this, ENNReal.toReal_zero]
    · have : μ (Iic b) = 1 :=
        le_antisymm prob_le_one (h ▸ measure_mono fun y hy => hy.2)
      rw [distFun, measureReal_def, this, ENNReal.toReal_one]
  · rintro ⟨h0, h1⟩
    have hb : μ (Iic b)ᶜ = 0 := by
      have : μ.real (Iic b)ᶜ = 0 := by
        rw [probReal_compl_eq_one_sub measurableSet_Iic]; rw [distFun] at h1; linarith
      exact (measureReal_eq_zero_iff).1 this
    have hk : ∀ i (k : ℕ), μ (Iic (Function.update b i (a i - 1 / (k + 1)))) = 0 := fun i k => by
      have := h0 (Function.update b i (a i - 1 / (k + 1))) ⟨i, by
        simp only [Function.update_self]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := k)]⟩
      exact (measureReal_eq_zero_iff).1 this
    refine (prob_compl_eq_zero_iff measurableSet_Icc).1 (measure_mono_null (t := (Iic b)ᶜ ∪
      ⋃ i, ⋃ k : ℕ, Iic (Function.update b i (a i - 1 / (k + 1)))) ?_
      (measure_union_null hb (measure_iUnion_null fun i => measure_iUnion_null (hk i))))
    intro y hy
    by_cases hyb : y ≤ b
    · right
      obtain ⟨i, hi⟩ : ∃ i, y i < a i := by
        by_contra hne; push Not at hne; exact hy ⟨hne, hyb⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hi)
      simp only [mem_iUnion]
      refine ⟨i, k, fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hji
      · simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne hji]; exact hyb j
    · exact Or.inl hyb

/-- **Theorem 12.9 (Helly)**, corrected: distribution functions vanishing whenever some
`xᵢ < a̲ᵢ` and equal to one at `b̄` have a subsequence converging weakly to a distribution
function with the same properties. -/
theorem theorem_12_9 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)]
    (h0 : ∀ n x, (∃ i, x i < a i) → distFun (ls n) x = 0) (h1 : ∀ n, distFun (ls n) b = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ :=
    theorem_12_9_cor1 ls fun n => (concentrated_iff (ls n)).2 ⟨h0 n, h1 n⟩
  exact ⟨μ, hμ, ((concentrated_iff μ).1 hab).1, ((concentrated_iff μ).1 hab).2, φ, hφ, hconv⟩

/-- The distribution function of a unit mass. -/
theorem distFun_dirac (p x : Fin l → ℝ) :
    distFun (Measure.dirac p) x = if p ≤ x then 1 else 0 := by
  rw [distFun, measureReal_def, Measure.dirac_apply' p measurableSet_Iic]
  split_ifs with h
  · rw [indicator_of_mem (show p ∈ Iic x from h)]; simp
  · rw [indicator_of_notMem (show p ∉ Iic x from h)]; simp

/-- The sequence `δ_{(-n, 0)}` on `ℝ²` has no weakly convergent subsequence: its mass escapes
to `-∞` in the first coordinate. -/
theorem not_convWeak_escape (φ : ℕ → ℕ) (hφ : StrictMono φ) (μ : Measure (Fin 2 → ℝ))
    [IsProbabilityMeasure μ] :
    ¬ ConvWeak ((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) μ := by
  intro hconv
  have : ∀ n, IsProbabilityMeasure
      (((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  set G : ℕ → Set (Fin 2 → ℝ) := fun M => {y | -(M : ℝ) < y 0}
  have hG : ∀ M, IsOpen (G M) := fun M => isOpen_lt continuous_const (continuous_apply 0)
  have hnull : ∀ M, μ (G M) = 0 := fun M => by
    have hlim := (theorem_12_3 _ μ).2.1.1 hconv (G M) (hG M)
    have : μ.real (G M) ≤ 0 := le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨n, hn, hnM⟩ := ((hlim ε hε).and (eventually_ge_atTop M)).exists
      have hφn : M ≤ φ n := hnM.trans (hφ.id_le n)
      have : ((Measure.dirac (![-(φ n : ℝ), 0] : Fin 2 → ℝ))).real (G M) = 0 := by
        rw [measureReal_def, Measure.dirac_apply' _ (hG M).measurableSet,
          indicator_of_notMem (by simpa [G] using hφn)]; simp
      simp only [Function.comp_apply] at hn
      linarith
    exact (measureReal_eq_zero_iff).1 (le_antisymm this measureReal_nonneg)
  have hU : (⋃ M, G M) = univ := eq_univ_of_forall fun y => by
    obtain ⟨M, hM⟩ := exists_nat_gt (-(y 0))
    exact mem_iUnion.2 ⟨M, by simp only [G, mem_ofPred]; linarith⟩
  have := measure_iUnion_null hnull
  rw [hU, measure_univ] at this
  exact one_ne_zero this

/-- **Theorem 12.9 / Corollary 1 are false as printed (hypothesis).** On `ℝ²`, `δ_{(-n, 0)}`
satisfies (3) with `a̲ = (0, -1)`, `b̄ = (1, 1)` (`Fₙ(a̲) = 0`, `Fₙ(b̄) = 1`), but no
subsequence converges weakly. -/
theorem theorem_12_9_false_hyp :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ n, distFun (ls n) ![0, -1] = 0 ∧ distFun (ls n) ![1, 1] = 1) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun n => ⟨?_, ?_⟩, fun φ hφ μ _ => not_convWeak_escape φ hφ μ⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 1; norm_num at this
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; fin_cases i <;> simp; linarith [n.cast_nonneg (α := ℝ)]

/-- **Theorem 12.9 / Corollary 1 are false as printed (conclusion).** On `ℝ`, `δ_{1/(n+1)}`
satisfies (3) with `a̲ = 0`, `b̄ = 1`, and does converge weakly, but every weak limit of every
subsequence has `F(a̲) = 1`, not `0`. -/
theorem theorem_12_9_false_concl :
    let ls := fun n : ℕ => Measure.dirac (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)
    (∀ n, distFun (ls n) 0 = 0 ∧ distFun (ls n) 1 = 1) ∧ ConvWeak ls (Measure.dirac 0) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ →
        ConvWeak (ls ∘ φ) μ → distFun μ 0 = 1 := by
  intro ls
  have hconv : ConvWeak ls (Measure.dirac 0) := fun f => by
    simp only [ls, integral_dirac]
    exact (f.continuous.tendsto 0).comp (tendsto_pi_nhds.2 fun _ =>
      tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨fun n => ⟨?_, ?_⟩, hconv, fun φ hφ μ _ h => ?_⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 0; simp only [Pi.zero_apply] at this
    linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; simp only [Pi.one_apply]
    exact (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  · have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
      inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
    have : μ = Measure.dirac 0 :=
      convWeak_unique h fun f => (hconv f).comp hφ.tendsto_atTop
    rw [this, distFun_dirac, ite_eq_left_iff]
    exact fun h => absurd le_rfl h

/-! ### Exercise 12.6 -/

/-- **Exercise 12.6a** (`l = 1`). If for every `ε > 0` there are `a̲, b̄` with
`Fₙ(b̄) - Fₙ(a̲) > 1 - ε` for all `n`, some subsequence converges weakly. -/
theorem ex_12_6a (ls : ℕ → Measure (Fin 1 → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (h : ∀ ε > 0, ∃ a b : Fin 1 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) :
    ∃ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  refine exists_convWeak_subseq_of_tight ls fun ε hε => ?_
  obtain ⟨a, b, hab⟩ := h ε hε
  refine ⟨Icc a b, isCompact_Icc, fun n => (hab n).trans_le ?_⟩
  have hsub : Iic b \ Iic a ⊆ Icc a b := fun y ⟨hyb, hya⟩ => by
    refine ⟨fun i => ?_, hyb⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_contra hlt
    exact hya fun j => (Subsingleton.elim j 0 ▸ (not_le.1 hlt).le)
  exact (le_measureReal_sdiff).trans (measureReal_mono hsub)

/-- **Exercise 12.6a is false for `l ≥ 2`**: `δ_{(-n, 0)}` on `ℝ²` has `Fₙ(b̄) - Fₙ(a̲) = 1` for
`a̲ = (0, -1)`, `b̄ = (1, 1)`, yet no subsequence converges weakly. -/
theorem ex_12_6a_false :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ ε > 0, ∃ a b : Fin 2 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun ε hε => ⟨![0, -1], ![1, 1], fun n => ?_⟩, theorem_12_9_false_hyp.2⟩
  rw [(theorem_12_9_false_hyp.1 n).1, (theorem_12_9_false_hyp.1 n).2]
  linarith

/-- **Exercise 12.6b.** A tight sequence of probability measures on `ℝˡ` has a weakly convergent
subsequence. -/
theorem ex_12_6b (ls : ℕ → Measure (Fin l → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-- **Exercise 12.6c.** The same on `S ⊆ ℝˡ` (the book assumes `S` closed; this is not needed). -/
theorem ex_12_6c {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-! ### Corollary 2: monotone sequences -/

/-- **Corollary 2 to Theorem 12.9**, corrected: a monotone sequence of distribution functions
(`Fₙ₊₁ ≤ Fₙ` for all `n`, or `Fₙ₊₁ ≥ Fₙ` for all `n`) of measures concentrated on `[a̲, b̄]`
converges weakly to a probability measure concentrated on `[a̲, b̄]`. Proof: Helly gives a
subsequential limit `μ`; the whole sequence `Fₙ(x)` converges (bounded and monotone), so at
continuity points of `F_μ` its limit is `F_μ(x)`, and Theorem 12.8 applies. -/
theorem theorem_12_9_cor2 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1)
    (hmono : (∀ n, distFun (ls (n + 1)) ≤ distFun (ls n)) ∨
      (∀ n, distFun (ls n) ≤ distFun (ls (n + 1)))) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧ ConvWeak ls μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ := theorem_12_9_cor1 ls h
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  have hconvx : ∀ x, ∃ c, Tendsto (fun n => distFun (ls n) x) atTop (𝓝 c) := fun x => by
    have hbdd : ∀ n, 0 ≤ distFun (ls n) x ∧ distFun (ls n) x ≤ 1 := fun n =>
      ⟨measureReal_nonneg, measureReal_le_one⟩
    rcases hmono with hm | hm
    · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => hm n x)
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (hbdd n).1⟩⟩
    · exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hm n x)
        ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbdd n).2⟩⟩
  refine ⟨μ, hμ, hab, (theorem_12_8 ls μ).2 fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hconvx x
  have hsub := (theorem_12_8 (ls ∘ φ) μ).1 hconv x hx
  rwa [tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hsub] at hc

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378)

Copied from `RecursiveMethods/ConvergenceApplications` (module `FellerInvariant`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

* **Exercise 12.7**: on any metric space, the Feller property `T[C(S)] ⊆ C(S)` is equivalent to
  `sₙ → s ⇒ P(sₙ, ·) ⇒ P(s, ·)` and to `λₙ ⇒ λ ⇒ T*λₙ ⇒ T*λ` (`ex_12_7`);
* **Exercise 12.8**: the cycle `s ↦ 1 - s` on `[0, 1]` is Feller; from `δ_s`, `s ≠ 1/2`, the even
  and odd iterates converge to the distinct non-invariant `δ_s`, `δ_{1-s}`; the invariant
  measures are exactly the measures symmetric about `1/2` (`ex_12_8a`–`ex_12_8c`);
* the limit step shared by Theorems 12.10 and 12.12 and Exercise 12.12 (`invariant_of_convWeak`):
  if `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
  invariant;
* **Theorem 12.10**: on a compact metric space a Feller transition function has an invariant
  probability measure, through the Cesàro averages of `T*ⁿδ_s` and Prokhorov's theorem. (The book
  works on compact `S ⊆ ℝˡ` and invokes Helly on `ℝˡ`; any compact metric space works. `S` must be
  nonempty.)
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
/-- Bounded continuous functions are bounded by their sup norm. -/
theorem bcf_abs_le_norm (f : S →ᵇ ℝ) (s : S) : |f s| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s

/-- Point masses at a convergent sequence converge weakly. -/
theorem convWeak_dirac {s : ℕ → S} {s₀ : S} (hs : Tendsto s atTop (𝓝 s₀)) :
    ConvWeak (fun n => Measure.dirac (s n)) (Measure.dirac s₀) := fun f => by
  simp only [integral_dirac]
  exact (f.continuous.tendsto s₀).comp hs

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [MetricSpace S] [BorelSpace S] [IsMarkovKernel κ] in
theorem adjointOp_dirac (s : S) : adjointOp κ (Measure.dirac s) = κ s :=
  Measure.dirac_bind κ.measurable s

/-- `∫ Tf dλ = ∫ f d(T*λ)` for bounded continuous `f` (Theorem 8.3). -/
theorem integral_markovOpR (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovOpR κ f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  theorem_8_3_cor κ lam f.continuous.measurable (bcf_abs_le_norm f)

/-- Under the Feller property, `Tf` as a bounded continuous function. -/
noncomputable def fellerBCF {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) :
    S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨markovOpR κ f, hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩⟩ (2 * ‖f‖) fun x y => by
      have hx := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 x
      have hy := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      linarith [abs_sub (markovOpR κ f x) (markovOpR κ f y)]

theorem fellerBCF_apply {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : fellerBCF hF f s = markovOpR κ f s := rfl

/-- **Exercise 12.7.** On a metric space the following are equivalent: (a) the Feller property;
(b) `sₙ → s` implies `P(sₙ, ·) ⇒ P(s, ·)`; (c) `λₙ ⇒ λ` implies `T*λₙ ⇒ T*λ`. -/
theorem ex_12_7 :
    (IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀)) ∧
    (IsFeller κ ↔ ∀ (ls : ℕ → Measure S) (lam : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
      IsProbabilityMeasure lam → ConvWeak ls lam →
        ConvWeak (fun n => adjointOp κ (ls n)) (adjointOp κ lam)) := by
  have hab : IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀) := by
    constructor
    · intro hF s s₀ hs f
      exact ((hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩).tendsto s₀).comp hs
    · intro h f hf ⟨M, hM⟩
      rw [continuous_iff_seqContinuous]
      intro s s₀ hs
      exact h s s₀ hs (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        linarith [abs_sub (f x) (f y), hM x, hM y])
  refine ⟨hab, ⟨fun hF ls lam hls hlam h f => ?_, fun h => hab.2 fun s s₀ hs => ?_⟩⟩
  · rw [← integral_markovOpR κ lam f]
    exact (h (fellerBCF hF f)).congr fun n => integral_markovOpR κ (ls n) f
  · have := h _ _ (fun n => inferInstance) inferInstance (convWeak_dirac hs)
    simpa only [adjointOp_dirac] using this

/-! ### Exercise 12.8: the cycle `s ↦ 1 - s` -/

/-- The transition function of `sₜ₊₁ = 1 - sₜ` on `[0, 1]`: `P(s, ·) = δ_{1-s}`. -/
noncomputable def flipKernel : Kernel unitInterval unitInterval :=
  Kernel.deterministic unitInterval.symm unitInterval.continuous_symm.measurable

theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel := by
  unfold flipKernel; infer_instance

theorem adjointOp_flip (μ : Measure unitInterval) :
    adjointOp flipKernel μ = μ.map unitInterval.symm :=
  Measure.deterministic_comp_eq_map _

theorem adjointOp_flip_dirac (s : unitInterval) :
    adjointOp flipKernel (Measure.dirac s) = Measure.dirac (unitInterval.symm s) := by
  rw [adjointOp_flip, Measure.map_dirac' unitInterval.continuous_symm.measurable]

/-- **Exercise 12.8a.** `P(s, ·) = δ_{1-s}`, and `P` has the Feller property. -/
theorem ex_12_8a : (∀ s, flipKernel s = Measure.dirac (unitInterval.symm s)) ∧
    IsFeller flipKernel := by
  have hP : ∀ s, flipKernel s = Measure.dirac (unitInterval.symm s) := fun s =>
    Kernel.deterministic_apply _ s
  refine ⟨hP, fun f hf _ => ?_⟩
  have : markovOpR flipKernel f = f ∘ unitInterval.symm := funext fun s => by
    simp only [markovOpR, hP, integral_dirac, Function.comp_apply]
  rw [this]
  exact hf.comp unitInterval.continuous_symm

theorem iterate_flip_dirac (s : unitInterval) (n : ℕ) :
    (adjointOp flipKernel)^[2 * n] (Measure.dirac s) = Measure.dirac s ∧
      (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s) =
        Measure.dirac (unitInterval.symm s) := by
  induction n with
  | zero => exact ⟨rfl, adjointOp_flip_dirac s⟩
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h2, Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac, unitInterval.symm_symm,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac,
      unitInterval.symm_symm, adjointOp_flip_dirac]
    exact ⟨rfl, rfl⟩

theorem symm_ne_self {s : unitInterval} (hs : (s : ℝ) ≠ 1 / 2) : unitInterval.symm s ≠ s := by
  intro h
  have := congrArg Subtype.val h
  rw [unitInterval.coe_symm_eq] at this
  exact hs (by linarith)

/-- **Exercise 12.8b.** From `δ_s` with `s ≠ 1/2`, the even iterates converge to `δ_s` and the odd
ones to `δ_{1-s}`; the two limits differ and neither is invariant. -/
theorem ex_12_8b (s : unitInterval) (hs : (s : ℝ) ≠ 1 / 2) :
    ConvWeak (fun n => (adjointOp flipKernel)^[2 * n] (Measure.dirac s)) (Measure.dirac s) ∧
      ConvWeak (fun n => (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s))
        (Measure.dirac (unitInterval.symm s)) ∧
      Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) ∧
      adjointOp flipKernel (Measure.dirac s) ≠ Measure.dirac s ∧
      adjointOp flipKernel (Measure.dirac (unitInterval.symm s)) ≠
        Measure.dirac (unitInterval.symm s) := by
  have hne : Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) := fun h =>
    symm_ne_self hs (dirac_eq_dirac_iff.1 h).symm
  refine ⟨fun f => ?_, fun f => ?_, hne, ?_, ?_⟩
  · simp only [fun n => (iterate_flip_dirac s n).1]; exact tendsto_const_nhds
  · simp only [fun n => (iterate_flip_dirac s n).2]; exact tendsto_const_nhds
  · rw [adjointOp_flip_dirac]; exact hne.symm
  · rw [adjointOp_flip_dirac, unitInterval.symm_symm]; exact hne

/-- **Exercise 12.8c.** The invariant measures are exactly the measures symmetric about `1/2`;
among them are `δ_{1/2}` and `½(δ_s + δ_{1-s})` for every `s`, so there are infinitely many. -/
theorem ex_12_8c :
    (∀ μ : Measure unitInterval, adjointOp flipKernel μ = μ ↔ μ.map unitInterval.symm = μ) ∧
      ∀ s : unitInterval, adjointOp flipKernel
        ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s))) =
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s)) := by
  refine ⟨fun μ => by rw [adjointOp_flip], fun s => ?_⟩
  have hm := unitInterval.continuous_symm.measurable
  rw [adjointOp_flip, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm, unitInterval.symm_symm, add_comm]
  exact hm.aemeasurable

/-! ### Invariant limits and Theorem 12.10 -/

variable {κ}

omit [MetricSpace S] [BorelSpace S] in
theorem isProbabilityMeasure_iterate (lam : Measure S) [IsProbabilityMeasure lam] (n : ℕ) :
    IsProbabilityMeasure ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (theorem_8_2 κ _).1

/-- If `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
invariant under a Feller `P` (the limit step of Theorem 12.10). -/
theorem invariant_of_convWeak (hF : IsFeller κ) {ν : ℕ → Measure S}
    [∀ n, IsProbabilityMeasure (ν n)] {μ : Measure S} [IsProbabilityMeasure μ]
    (hconv : ConvWeak ν μ)
    (hdiff : ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ν n - ∫ s, f s ∂adjointOp κ (ν n))
      atTop (𝓝 0)) : adjointOp κ μ = μ := by
  have : IsProbabilityMeasure (adjointOp κ μ) := (theorem_8_2 κ μ).1
  refine theorem_12_6_cor2 fun f => ?_
  rw [← integral_markovOpR κ μ f]
  have h1 : Tendsto (fun n => ∫ s, f s ∂adjointOp κ (ν n)) atTop (𝓝 (∫ s, f s ∂μ)) := by
    have := (hconv f).sub (hdiff f)
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  exact tendsto_nhds_unique ((hconv (fellerBCF hF f)).congr fun n =>
    integral_markovOpR κ (ν n) f) h1

/-- **Theorem 12.10.** On a nonempty compact metric space, a transition function with the Feller
property has an invariant probability measure. -/
theorem theorem_12_10 [CompactSpace S] [Nonempty S] (hF : IsFeller κ) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  have : TopologicalSpace.SeparableSpace S := inferInstance
  set lam₀ := Measure.dirac (Classical.arbitrary S)
  set L : ℕ → Measure S := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  set avg : ℕ → Measure S := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul, c]
    push_cast
    exact ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)⟩
  have hint : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← integral_markovOpR κ (avg N) g]
    change ∫ s, fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← integral_markovOpR κ (L n) g]
    rfl
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight avg fun ε hε =>
    ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, invariant_of_convWeak hF hconv fun f => ?_⟩
  have hdiff : ∀ N, ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * (∫ s, f s ∂L 0 - ∫ s, f s ∂L (N + 1)) := fun N => by
    rw [hint, hintT, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hbd : ∀ n, |∫ s, f s ∂L n| ≤ ‖f‖ := fun n => by
    rw [← Real.norm_eq_abs]
    exact f.norm_integral_le_norm (L n)
  have hlim : Tendsto (fun N : ℕ => ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N)) atTop
      (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖)) (fun N => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
      linarith [abs_sub (∫ s, f s ∂L 0) (∫ s, f s ∂L (N + 1)), hbd 0, hbd (N + 1)]
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).mul_const (2 * ‖f‖)
  exact hlim.comp hφ.tendsto_atTop

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monotone Markov processes (SLP §12.4, pp. 378–383)

Copied from `RecursiveMethods/ConvergenceApplications` (module `MonotoneProcesses`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

* **dominance** `μ ≥ λ` (p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for all bounded measurable nondecreasing `f`;
* **Exercise 12.9**: dominance orders distribution functions the other way (`ex_12_9a`); on `ℝ`
  the converse holds (`ex_12_9b`, via the layer-cake formula and the classification of lower
  sets of `ℝ`); on `ℝ²` it fails (`ex_12_9c`, `μ = ½(δ_{(1,0)} + δ_{(0,1)})`,
  `λ = ½(δ_{(0,0)} + δ_{(1,1)})`);
* **Exercise 12.10**: squeezing between dominance-ordered weakly convergent sequences (for any
  `S ⊆ ℝˡ`, not only rectangles);
* **Exercise 12.11**: `P` monotone ⇔ `T*` preserves dominance ⇔ `s ≥ s′ ⇒ P(s, ·) ≥ P(s′, ·)`;
* monotone sequences of measures on `[a, b]` converge weakly (`convWeak_of_dominance_mono`, from
  Corollary 2 to Helly);
* **Exercise 12.12**: `T*ⁿδ_a` increases and `T*ⁿδ_b` decreases, and both converge to invariant
  measures;
* **Assumption 12.1**, **Exercise 12.14**, **Lemma 12.11** and **Theorem 12.12** (a monotone Feller
  process satisfying the mixing condition has a unique invariant measure, which is globally
  stable). The proof of Theorem 12.12 supplies the two steps the book leaves implicit: the lower
  bound `(Tⁿf)(b) - (Tⁿf)(a) ≥ 0`, and uniqueness from global convergence.
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

/-! ### Dominance -/

variable {S : Type*} [MeasurableSpace S] [Preorder S]

/-- `μ` **dominates** `λ` (SLP p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for every bounded measurable
nondecreasing `f`. -/
def Dominates (μ lam : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ M, ∀ s, |f s| ≤ M) → Monotone f → ∫ s, f s ∂lam ≤ ∫ s, f s ∂μ

theorem Dominates.trans {μ ν lam : Measure S} (h1 : Dominates μ ν) (h2 : Dominates ν lam) :
    Dominates μ lam := fun f hf hb hm => (h2 f hf hb hm).trans (h1 f hf hb hm)

/-- Dominance compares the masses of measurable upper sets. -/
theorem Dominates.real_le {μ lam : Measure S} (h : Dominates μ lam) {U : Set S}
    (hU : MeasurableSet U) (hup : IsUpperSet U) : lam.real U ≤ μ.real U := by
  have hm : Monotone (U.indicator (1 : S → ℝ)) := fun s t hst => by
    by_cases hs : s ∈ U
    · simp [hs, hup hst hs]
    · rw [indicator_of_notMem hs]; exact indicator_nonneg (fun _ _ => zero_le_one) t
  have := h (U.indicator 1) (measurable_const.indicator hU) ⟨1, fun s => by
    by_cases hs : s ∈ U
    · rw [indicator_of_mem hs, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem hs, abs_zero]; exact zero_le_one⟩ hm
  rwa [integral_indicator_one hU, integral_indicator_one hU] at this

variable {l : ℕ}

/-- **Exercise 12.9a.** If `μ ≥ λ` on `ℝˡ` then `F_μ ≤ F_λ`. -/
theorem ex_12_9a {μ lam : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    distFun μ x ≤ distFun lam x := by
  have := h.real_le measurableSet_Iic.compl (isLowerSet_Iic x).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  simp only [distFun]; linarith

/-- **Exercise 12.9a** on `S ⊆ ℝˡ`: if `μ ≥ λ` then `μ(S ∩ (-∞, x]) ≤ λ(S ∩ (-∞, x])` for every
`x ∈ ℝˡ`. -/
theorem ex_12_9a_subtype {S : Set (Fin l → ℝ)} {μ lam : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    μ.real (Subtype.val ⁻¹' Iic x) ≤ lam.real (Subtype.val ⁻¹' Iic x) := by
  have hm : MeasurableSet (Subtype.val ⁻¹' Iic x : Set S) :=
    measurableSet_Iic.preimage measurable_subtype_coe
  have := h.real_le hm.compl (fun s t (hst : (s : Fin l → ℝ) ≤ t) hs ht => hs (hst.trans ht))
  rw [probReal_compl_eq_one_sub hm, probReal_compl_eq_one_sub hm] at this
  linarith

/-- On `ℝ`, `F_μ ≤ F_λ` gives `μ(L) ≤ λ(L)` for every lower set `L`: `L` is `∅`, `ℝ`,
`(-∞, c]` or `(-∞, c)`. -/
theorem measure_lower_le {μ lam : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) {L : Set ℝ} (hL : IsLowerSet L) :
    μ L ≤ lam L := by
  have hE : ∀ x, μ (Iic x) ≤ lam (Iic x) := fun x =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (h x)
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  by_cases hbdd : BddAbove L
  · by_cases hc : sSup L ∈ L
    · have : L = Iic (sSup L) :=
        Subset.antisymm (fun y hy => le_csSup hbdd hy) (fun y hy => hL hy hc)
      rw [this]; exact hE _
    · have hLc : L = ⋃ n : ℕ, Iic (sSup L - 1 / ((n : ℝ) + 1)) := by
        ext y
        simp only [mem_iUnion, mem_Iic]
        constructor
        · intro hy
          have hlt : y < sSup L := lt_of_le_of_ne (le_csSup hbdd hy) fun h => hc (h ▸ hy)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩
          have := Nat.one_div_pos_of_nat (α := ℝ) (n := n)
          obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y < sSup L by linarith)
          exact hL hyz.le hz
      have hmono : Monotone fun n : ℕ => Iic (sSup L - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
        Iic_subset_Iic.2 (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
              linarith)) _)
      rw [hLc]
      exact le_of_tendsto_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
        (tendsto_measure_iUnion_atTop hmono) fun n => hE _
  · have : L = univ := eq_univ_of_forall fun y => by
      obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.1 hbdd y
      exact hL hyz.le hz
    rw [this, measure_univ, measure_univ]

/-- **Exercise 12.9b.** On `ℝ`, `F_μ ≤ F_λ` implies `μ ≥ λ`. -/
theorem ex_12_9b (μ lam : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) : Dominates μ lam := by
  intro f hf ⟨M, hM⟩ hmono
  set g := fun s => f s + M
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    have := hM s; rw [abs_le] at this; simp only [g]; linarith
  have hgM : ∀ s, |g s| ≤ 2 * M := fun s => by
    have := hM s; rw [abs_le] at this
    rw [abs_of_nonneg (hg0 s)]; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const M
  have hshift : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ s, f s ∂ν = ∫ s, g s ∂ν - M :=
    fun ν _ => by
      simp only [g]
      rw [integral_add (integrable_of_bounded hf hM) (integrable_const M), integral_const,
        probReal_univ, one_smul]
      ring
  have hlc : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫ s, g s ∂ν = (∫⁻ t in Ioi 0, ν {s | t < g s}).toReal := fun ν _ => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hgm.aemeasurable]
  have hup : ∀ t, IsUpperSet {s | t < g s} := fun t s s' hss' (hs : t < g s) =>
    show t < g s' from lt_of_lt_of_le hs (add_le_add_left (hmono hss') M)
  have hle : ∀ t, lam {s | t < g s} ≤ μ {s | t < g s} := fun t => by
    have hmeas : MeasurableSet {s | t < g s} := measurableSet_lt measurable_const hgm
    have := measure_lower_le h (hup t).compl
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 this
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hmeas,
      probReal_compl_eq_one_sub hmeas] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (by
      rw [← measureReal_def, ← measureReal_def]; linarith)
  have hfin : ∫⁻ t in Ioi 0, μ {s | t < g s} ≠ ⊤ := by
    rw [← lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hgm.aemeasurable]
    exact (integrable_of_bounded hgm hgM (μ := μ)).lintegral_lt_top.ne
  rw [hshift lam, hshift μ, hlc lam, hlc μ]
  linarith [ENNReal.toReal_mono hfin (lintegral_mono hle)]

/-- The mass of a measurable set under `½(δ_p + δ_q)`. -/
theorem real_half_dirac {α : Type*} [MeasurableSpace α] (p q : α) {A : Set α}
    (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac p + Measure.dirac q)).real A =
      (A.indicator (1 : α → ℝ) p + A.indicator (1 : α → ℝ) q) / 2 := by
  rw [measureReal_def, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' p hA,
    Measure.dirac_apply' q hA, smul_eq_mul]
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;>
    simp [hp, hq, ENNReal.toReal_inv, ENNReal.toReal_add]
  all_goals norm_num

/-- **Exercise 12.9c.** On `ℝ²` the converse of Exercise 12.9a fails:
`μ = ½(δ_{(1,0)} + δ_{(0,1)})` and `λ = ½(δ_{(0,0)} + δ_{(1,1)})` have `F_μ ≤ F_λ`, but the
nondecreasing indicator of `{x ≥ (1, 1)}` integrates to `0` under `μ` and to `½` under `λ`. -/
theorem ex_12_9c :
    let μ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![1, 0] : Fin 2 → ℝ) + Measure.dirac ![0, 1])
    let lam := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![0, 0] : Fin 2 → ℝ) + Measure.dirac ![1, 1])
    (∀ x, distFun μ x ≤ distFun lam x) ∧ ¬ Dominates μ lam := by
  intro μ lam
  have hle : ∀ (a b : ℝ) (x : Fin 2 → ℝ), (![a, b] : Fin 2 → ℝ) ≤ x ↔ a ≤ x 0 ∧ b ≤ x 1 :=
    fun a b x => by simp [Pi.le_def, Fin.forall_fin_two]
  have hle2 : ∀ a b c d : ℝ, (![a, b] : Fin 2 → ℝ) ≤ ![c, d] ↔ a ≤ c ∧ b ≤ d :=
    fun a b c d => by simp [Pi.le_def, Fin.forall_fin_two]
  refine ⟨fun x => ?_, fun h => ?_⟩
  · have i1 : ∀ p : Fin 2 → ℝ, 0 ≤ (Iic x).indicator (1 : (Fin 2 → ℝ) → ℝ) p := fun p =>
      indicator_nonneg (fun _ _ => zero_le_one) p
    have hA : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨by linarith [h.1], h.2⟩
    have hB : (![0, 1] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨h.1, by linarith [h.2]⟩
    have hC : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 1] : Fin 2 → ℝ) ∈ Iic x →
        (![1, 1] : Fin 2 → ℝ) ∈ Iic x := fun h h' => by
      rw [mem_Iic, hle] at h h' ⊢; exact ⟨h.1, h'.2⟩
    simp only [distFun, μ, lam, real_half_dirac _ _ measurableSet_Iic]
    by_cases h1 : (![1, 0] : Fin 2 → ℝ) ∈ Iic x <;> by_cases h2 : (![0, 1] : Fin 2 → ℝ) ∈ Iic x
    · simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (hA h1),
        indicator_of_mem (hC h1 h2), Pi.one_apply, le_refl]
    · simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_mem (hA h1),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem (hB h2),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2]
      linarith [i1 ![0, 0], i1 ![1, 1]]
  · have hU : MeasurableSet (Ici (![1, 1] : Fin 2 → ℝ)) := measurableSet_Ici
    have := h.real_le hU (isUpperSet_Ici _)
    have n00 : (![0, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have n10 : (![1, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.2]
    have n01 : (![0, 1] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have m11 : (![1, 1] : Fin 2 → ℝ) ∈ Ici ![1, 1] := mem_Ici.2 le_rfl
    simp only [μ, lam, real_half_dirac _ _ hU, indicator_of_notMem n00, indicator_of_notMem n10,
      indicator_of_notMem n01, indicator_of_mem m11, Pi.one_apply] at this
    linarith

/-! ### Exercise 12.10 -/

theorem distFun_map_val {S : Set (Fin l → ℝ)} (ν : Measure S) (x : Fin l → ℝ) :
    distFun (ν.map Subtype.val) x = ν.real (Subtype.val ⁻¹' Iic x) := by
  rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl

/-- **Exercise 12.10.** If `μ₁ₙ ≤ λₙ ≤ μ₂ₙ` and `μ₁ₙ ⇒ μ`, `μ₂ₙ ⇒ μ`, then `λₙ ⇒ μ`. (The book
states it for `S = [a, b]`; the argument through Exercise 12.4 and Theorem 12.8 works for any
`S ⊆ ℝˡ`.) -/
theorem ex_12_10 {S : Set (Fin l → ℝ)} (μ₁ μ₂ ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (μ₁ n)] [∀ n, IsProbabilityMeasure (μ₂ n)]
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h₁ : ∀ n, Dominates (ls n) (μ₁ n)) (h₂ : ∀ n, Dominates (μ₂ n) (ls n))
    (hc₁ : ConvWeak μ₁ μ) (hc₂ : ConvWeak μ₂ μ) : ConvWeak ls μ := by
  rw [ex_12_4, theorem_12_8] at hc₁ hc₂ ⊢
  intro x hx
  have e1 := hc₁ x hx
  have e2 := hc₂ x hx
  simp only [distFun_map_val] at e1 e2 ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le e2 e1
    (fun n => ex_12_9a_subtype (h₂ n) x) (fun n => ex_12_9a_subtype (h₁ n) x)

/-! ### Exercise 12.11 and iterates -/

variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Exercise 12.11.** The following are equivalent: (a) `P` is monotone; (b) `μ ≥ λ` implies
`T*μ ≥ T*λ`; (c) `s ≥ s′` implies `P(s, ·) ≥ P(s′, ·)`. -/
theorem ex_12_11 :
    (IsMonotoneTF κ ↔ ∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) ∧
    (IsMonotoneTF κ ↔ ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) := by
  have hab : IsMonotoneTF κ → ∀ (μ lam : Measure S), IsProbabilityMeasure μ →
      IsProbabilityMeasure lam → Dominates μ lam →
        Dominates (adjointOp κ μ) (adjointOp κ lam) := fun hM μ lam _ _ h f hf hb hm => by
    obtain ⟨M, hMb⟩ := hb
    rw [← theorem_8_3_cor κ lam hf hMb, ← theorem_8_3_cor κ μ hf hMb]
    have := theorem_8_1_cor κ hf hMb
    exact h _ this.1 ⟨M, this.2⟩ (hM f hf ⟨M, hMb⟩ hm)
  have hbc : (∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) →
        ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s') := fun h s s' hss' => by
    have := h (Measure.dirac s) (Measure.dirac s') inferInstance inferInstance
      (fun f hf _ hm => by
        rw [integral_dirac' f s' hf.stronglyMeasurable, integral_dirac' f s hf.stronglyMeasurable]
        exact hm hss')
    rwa [adjointOp_dirac, adjointOp_dirac] at this
  have hca : (∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) → IsMonotoneTF κ :=
    fun h f hf hb hm s' s hss' => h s s' hss' f hf hb hm
  exact ⟨⟨hab, fun h => hca (hbc h)⟩, ⟨fun h => hbc (hab h), hca⟩⟩

omit [Preorder S] [IsMarkovKernel κ] in
theorem markovOpR_kpow_zero {f : S → ℝ} (hf : Measurable f) : markovOpR (kpow κ 0) f = f := by
  funext s
  simp only [markovOpR, kpow, Kernel.id_apply]
  exact integral_dirac' f s hf.stronglyMeasurable

omit [Preorder S] in
/-- `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem markovOpR_kpow_add (n m : ℕ) {f : S → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ s, |f s| ≤ M) :
    markovOpR (kpow κ (n + m)) f = markovOpR (kpow κ n) (markovOpR (kpow κ m) f) := by
  have := ex_8_4a κ m
  have := ex_8_4a κ n
  funext s
  rw [kpow_add]
  exact Kernel.integral_comp (integrable_of_bounded hf hM)

/-- The iterates of a monotone transition function are monotone. -/
theorem isMonotoneTF_kpow {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (n : ℕ) :
    IsMonotoneTF (kpow κ n) := by
  induction n with
  | zero => intro f hf _ hm; rw [markovOpR_kpow_zero κ hf]; exact hm
  | succ n ih =>
    intro f hf ⟨M, hb⟩ hm
    have := ex_8_4a κ n
    rw [add_comm, markovOpR_kpow_add κ 1 n hf hb, kpow_one]
    have := theorem_8_1_cor (kpow κ n) hf hb
    exact hM _ this.1 ⟨M, this.2⟩ (ih f hf ⟨M, hb⟩ hm)

omit [Preorder S] [IsMarkovKernel κ] in
theorem iterate_dirac (n : ℕ) (s : S) :
    (adjointOp κ)^[n] (Measure.dirac s) = kpow κ n s := by
  rw [adjointOp_iterate, adjointOp_dirac]

/-- `T*ⁿ` preserves dominance for monotone `P`. -/
theorem dominates_iterate {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    {μ lam : Measure S} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : Dominates μ lam) (n : ℕ) :
    Dominates ((adjointOp κ)^[n] μ) ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (ex_12_11 κ).1.1 hM _ _ (isProbabilityMeasure_iterate μ n)
      (isProbabilityMeasure_iterate lam n) ih

/-! ### Monotone processes on `[a, b]` -/

variable {a b : Fin l → ℝ}

/-- The bottom `a` of `[a, b]`. -/
def IccBot (hab : a ≤ b) : Icc a b := ⟨a, left_mem_Icc.2 hab⟩

/-- The top `b` of `[a, b]`. -/
def IccTop (hab : a ≤ b) : Icc a b := ⟨b, right_mem_Icc.2 hab⟩

theorem IccBot_le (hab : a ≤ b) (s : Icc a b) : IccBot hab ≤ s := s.2.1

theorem le_IccTop (hab : a ≤ b) (s : Icc a b) : s ≤ IccTop hab := s.2.2

/-- Every probability measure dominates `δ_a` and is dominated by `δ_b`. -/
theorem dominates_dirac_bot_top (hab : a ≤ b) (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    Dominates ν (Measure.dirac (IccBot hab)) ∧ Dominates (Measure.dirac (IccTop hab)) ν := by
  refine ⟨fun f hf ⟨M, hM⟩ hm => ?_, fun f hf ⟨M, hM⟩ hm => ?_⟩
  · rw [integral_dirac]
    have := integral_mono (integrable_const (f (IccBot hab))) (integrable_of_bounded hf hM (μ := ν))
      fun s => hm (IccBot_le hab s)
    rwa [integral_const, probReal_univ, one_smul] at this
  · rw [integral_dirac]
    have := integral_mono (integrable_of_bounded hf hM (μ := ν))
      (integrable_const (f (IccTop hab))) fun s => hm (le_IccTop hab s)
    rwa [integral_const, probReal_univ, one_smul] at this

/-- A probability measure on `ℝˡ` concentrated on `[a, b]` is the extension of a probability
measure on `[a, b]`. -/
theorem exists_subtype_measure (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (h : μ (Icc a b) = 1) :
    ∃ ν : Measure (Icc a b), IsProbabilityMeasure ν ∧ ν.map Subtype.val = μ := by
  have hmap : (μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc]
    exact Measure.restrict_eq_self_of_ae_mem
      (mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 h))
  refine ⟨μ.comap Subtype.val, ?_, hmap⟩
  have : IsProbabilityMeasure ((μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ)) := by
    rw [hmap]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).1 this

theorem map_val_Icc (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    ν.map Subtype.val (Icc a b) = 1 := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc]
  have : (Subtype.val ⁻¹' Icc a b : Set (Icc a b)) = univ := eq_univ_of_forall fun s => s.2
  rw [this, measure_univ]

/-- A **monotone sequence of measures** on `[a, b]` (SLP p. 379) converges weakly (Corollary 2 to
Helly, through Exercise 12.9a and Exercise 12.4). -/
theorem convWeak_of_dominance_mono (ν : ℕ → Measure (Icc a b)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmono : (∀ n, Dominates (ν (n + 1)) (ν n)) ∨ (∀ n, Dominates (ν n) (ν (n + 1)))) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ ConvWeak ν μ := by
  obtain ⟨μ', hμ', hab', hconv⟩ := theorem_12_9_cor2 (a := a) (b := b)
    (fun n => (ν n).map Subtype.val) (fun n => map_val_Icc (ν n)) (by
      rcases hmono with h | h
      · exact Or.inl fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x
      · exact Or.inr fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x)
  obtain ⟨μ, hμ, hmap⟩ := exists_subtype_measure μ' hab'
  refine ⟨μ, hμ, (ex_12_4 ν μ).2 ?_⟩
  rw [hmap]; exact hconv

/-- **Exercise 12.12.** For monotone Feller `P` on `[a, b]`, `T*ⁿδ_a` is increasing and `T*ⁿδ_b`
decreasing, and each converges weakly to an invariant measure. -/
theorem ex_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) :
    (∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab)))) ∧
    (∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab)))) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccBot hab))) μ ∧
      adjointOp κ μ = μ) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccTop hab))) μ ∧
      adjointOp κ μ = μ) := by
  have hP : ∀ (lam : Measure (Icc a b)) [IsProbabilityMeasure lam],
      IsProbabilityMeasure (adjointOp κ lam) := fun lam _ => (theorem_8_2 κ lam).1
  have hbot : ∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).1 n
  have htop : ∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).2 n
  have hlim : ∀ s : Icc a b, ((∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac s))
      ((adjointOp κ)^[n] (Measure.dirac s))) ∨ (∀ n, Dominates ((adjointOp κ)^[n]
        (Measure.dirac s)) ((adjointOp κ)^[n + 1] (Measure.dirac s)))) →
      ∃ μ, IsProbabilityMeasure μ ∧
        ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac s)) μ ∧ adjointOp κ μ = μ :=
    fun s hs => by
      have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] (Measure.dirac s)) := fun n =>
        isProbabilityMeasure_iterate _ n
      obtain ⟨μ, hμ, hconv⟩ := convWeak_of_dominance_mono _ hs
      refine ⟨μ, hμ, hconv, invariant_of_convWeak hF hconv fun f => ?_⟩
      have := (hconv f).sub ((hconv f).comp (tendsto_add_atTop_nat 1))
      rw [sub_self] at this
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  exact ⟨hbot, htop, hlim _ (Or.inl hbot), hlim _ (Or.inr htop)⟩

/-! ### Assumption 12.1, Exercise 12.14, Lemma 12.11 and Theorem 12.12 -/

/-- **Assumption 12.1.** There are `c ∈ [a, b]`, `ε > 0` and `N ≥ 1` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε`. -/
def Assumption12_1 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) (c : Icc a b) (ε : ℝ)
    (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (IccBot hab)).real (Ici c) ∧
    ε ≤ (kpow κ N (IccTop hab)).real (Iic c)

/-- **Exercise 12.14.** Under monotonicity, Assumption 12.1 holds from every starting point:
`Pᴺ(s, [a, c]) ≥ ε` and `Pᴺ(s, [c, b]) ≥ ε`. -/
theorem ex_12_14 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    (s : Icc a b) : ε ≤ (kpow κ N s).real (Iic c) ∧ ε ≤ (kpow κ N s).real (Ici c) := by
  have := ex_8_4a κ N
  have hdom := (ex_12_11 (kpow κ N)).2.1 (isMonotoneTF_kpow hM N)
  refine ⟨?_, hA.2.2.1.trans ((hdom s _ (IccBot_le hab s)).real_le measurableSet_Ici
    (isUpperSet_Ici c))⟩
  have := (hdom _ s (le_IccTop hab s)).real_le measurableSet_Iic.compl (isLowerSet_Iic c).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  linarith [hA.2.2.2]

/-- **Lemma 12.11.** Under monotonicity and Assumption 12.1, for bounded measurable
nondecreasing `f`: `εf(c) + (1 - ε)f(a) ≤ (Tᴺf)(s) ≤ εf(c) + (1 - ε)f(b)`. -/
theorem lemma_12_11 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    {f : Icc a b → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ s, |f s| ≤ M) (hm : Monotone f)
    (s : Icc a b) :
    ε * f c + (1 - ε) * f (IccBot hab) ≤ markovOpR (kpow κ N) f s ∧
      markovOpR (kpow κ N) f s ≤ ε * f c + (1 - ε) * f (IccTop hab) := by
  have := ex_8_4a κ N
  obtain ⟨hp, hq⟩ := ex_12_14 hM hA s
  set ν := kpow κ N s
  have hfi : Integrable f ν := integrable_of_bounded hf hb
  have hI : ∀ (A : Set (Icc a b)), MeasurableSet A → Integrable (A.indicator (1 : Icc a b → ℝ)) ν :=
    fun A hA => by exact (integrable_const (1 : ℝ)).indicator hA
  constructor
  · have hle : ∀ t, f (IccBot hab) + (f c - f (IccBot hab)) * (Ici c).indicator 1 t ≤ f t :=
      fun t => by
        by_cases ht : t ∈ Ici c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, add_zero]; exact hm (IccBot_le hab t)
    have := integral_mono ((integrable_const _).add ((hI _ measurableSet_Ici).const_mul _)) hfi hle
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_const _) ((hI _ measurableSet_Ici).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Ici] at this
    have hca : f (IccBot hab) ≤ f c := hm (IccBot_le hab c)
    change _ ≤ ∫ t, f t ∂ν
    nlinarith
  · have hle : ∀ t, f t ≤ f (IccTop hab) - (f (IccTop hab) - f c) * (Iic c).indicator 1 t :=
      fun t => by
        by_cases ht : t ∈ Iic c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, sub_zero]; exact hm (le_IccTop hab t)
    have := integral_mono hfi ((integrable_const _).sub ((hI _ measurableSet_Iic).const_mul _)) hle
    simp only [Pi.sub_apply] at this
    rw [integral_sub (integrable_const _) ((hI _ measurableSet_Iic).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Iic] at this
    have hcb : f c ≤ f (IccTop hab) := hm (le_IccTop hab c)
    change ∫ t, f t ∂ν ≤ _
    nlinarith

/-- **Theorem 12.12.** On `[a, b]`, a monotone Feller transition function satisfying Assumption
12.1 has a unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hA : Assumption12_1 hab κ c ε N) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  obtain ⟨-, -, ⟨μa, hμa, hca, hia⟩, ⟨μb, hμb, hcb, hib⟩⟩ := ex_12_12 hab κ hM hF
  set lo := IccBot hab
  set hi := IccTop hab
  have hε1 : ε ≤ 1 := by
    have := ex_8_4a κ N
    exact hA.2.2.1.trans measureReal_le_one
  -- the limits along `Tⁿf` at the two ends
  have hT : ∀ (s : Icc a b) (f : Icc a b →ᵇ ℝ) (n : ℕ),
      ∫ t, f t ∂(adjointOp κ)^[n] (Measure.dirac s) = markovOpR (kpow κ n) f s :=
    fun s f n => by rw [iterate_dirac]; rfl
  have heq : μa = μb := by
    refine ex_12_5b μa μb fun f hfm => ?_
    have hfb := bcf_abs_le_norm f
    have hfmeas := f.continuous.measurable
    set d : ℕ → ℝ := fun n => markovOpR (kpow κ n) f hi - markovOpR (kpow κ n) f lo
    have hdlim : Tendsto d atTop (𝓝 (∫ t, f t ∂μb - ∫ t, f t ∂μa)) := by
      have h1 := hcb f; have h2 := hca f
      simp only [hT] at h1 h2
      exact h1.sub h2
    have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.2
      (isMonotoneTF_kpow hM n f hfmeas ⟨_, hfb⟩ hfm (IccBot_le hab hi))
    have hdN : ∀ m, d (N * m) ≤ (1 - ε) ^ m * (f hi - f lo) := fun m => by
      induction m with
      | zero =>
        simp only [d, mul_zero, pow_zero, one_mul, markovOpR_kpow_zero κ hfmeas]; rfl
      | succ m ih =>
        have := ex_8_4a κ (N * m)
        have hg := theorem_8_1_cor (kpow κ (N * m)) hfmeas hfb
        have hgm := isMonotoneTF_kpow hM (N * m) f hfmeas ⟨_, hfb⟩ hfm
        have hsplit : markovOpR (kpow κ (N * (m + 1))) f =
            markovOpR (kpow κ N) (markovOpR (kpow κ (N * m)) f) := by
          rw [show N * (m + 1) = N + N * m by ring, markovOpR_kpow_add κ N (N * m) hfmeas hfb]
        have hup := (lemma_12_11 hM hA hg.1 hg.2 hgm hi).2
        have hlo := (lemma_12_11 hM hA hg.1 hg.2 hgm lo).1
        simp only [d, hsplit]
        have h1ε : 0 ≤ 1 - ε := by linarith
        calc _ ≤ (1 - ε) * d (N * m) := by simp only [d]; linarith
          _ ≤ (1 - ε) * ((1 - ε) ^ m * (f hi - f lo)) := mul_le_mul_of_nonneg_left ih h1ε
          _ = _ := by ring
    have hNm : Tendsto (fun m => N * m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hA.2.1) tendsto_id
    have hup : ∫ t, f t ∂μb - ∫ t, f t ∂μa ≤ 0 := by
      have hbound : Tendsto (fun m : ℕ => (1 - ε) ^ m * (f hi - f lo)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith [hA.1])
          ).mul_const (f hi - f lo)
      exact le_of_tendsto_of_tendsto' (hdlim.comp hNm) hbound hdN
    have hlow : 0 ≤ ∫ t, f t ∂μb - ∫ t, f t ∂μa := ge_of_tendsto' hdlim hd0
    linarith
  subst heq
  have hglob : ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μa := fun lam₀ _ => by
    have : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] n,
        IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun ν _ n => isProbabilityMeasure_iterate ν n
    exact ex_12_10 (fun n => (adjointOp κ)^[n] (Measure.dirac lo))
      (fun n => (adjointOp κ)^[n] (Measure.dirac hi)) (fun n => (adjointOp κ)^[n] lam₀) μa
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).1 n)
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).2 n) hca hcb
  refine ⟨μa, hμa, hia, fun ν _ hν => ?_, hglob⟩
  have hconst : ConvWeak (fun n => (adjointOp κ)^[n] ν) ν := fun f => by
    simp only [Function.iterate_fixed hν]; exact tendsto_const_nhds
  have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun n =>
    isProbabilityMeasure_iterate ν n
  exact convWeak_unique hconst (hglob ν inferInstance)

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 12.12 on real intervals and on rectangles

Copied from `RecursiveMethods/ConvergenceApplications` (module `RealIntervals`),
namespace renamed to `Miao.IncompleteMarkets.SIWC`.

Theorem 12.12 (`theorem_12_12`) is stated for order intervals `[a, b]` of `ℝˡ = Fin l → ℝ`. The
models of Chapter 13 live on a real interval `[a, b] ⊆ ℝ` (§§13.3, 13.5) or on a rectangle
`[a, b] ⊆ ℝ × ℝ` (§§13.4, 13.8). This file transports the theorem along an order isomorphism
that is a homeomorphism.

* `transportK`: the kernel `κ′(t) = κ(e⁻¹t) ∘ e⁻¹` on `T` of a kernel `κ` on `S`.
* `theorem_12_12_of_orderIso`: Theorem 12.12 on any `S` order-isomorphic and homeomorphic to an
  order interval of `ℝˡ`, with Assumption 12.1 at the images of the endpoints.
* `theorem_12_12_real` (`S = [a, b] ⊆ ℝ`, through `ℝ¹`) and `theorem_12_12_prod`
  (`S = [a, b] ⊆ ℝ × ℝ` with the coordinatewise order, through `ℝ²`).
-/

namespace Miao.IncompleteMarkets.SIWC

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- The kernel on `T` of a kernel `κ` on `S`, transported along `e : S → T` with inverse `e'`:
`κ′(t) = κ(e′ t)` pushed forward by `e`. -/
noncomputable def transportK (e : S → T) (e' : T → S) (he' : Measurable e') (κ : Kernel S S) :
    Kernel T T :=
  Kernel.map (κ.comap e' he') e

variable {e : S → T} {e' : T → S} (he : Measurable e) (he' : Measurable e')
  (hl : ∀ s, e' (e s) = s) (hr : ∀ t, e (e' t) = t) (κ : Kernel S S)

include he in
theorem transportK_apply (t : T) : transportK e e' he' κ t = (κ (e' t)).map e := by
  rw [transportK, Kernel.map_apply _ he, Kernel.comap_apply]

include he in
theorem isMarkovKernel_transportK [IsMarkovKernel κ] : IsMarkovKernel (transportK e e' he' κ) :=
  Kernel.IsMarkovKernel.map _ he

include he hl in
/-- `T′*(ν ∘ e⁻¹) = (T*ν) ∘ e⁻¹`. -/
theorem adjointOp_transportK_map (ν : Measure S) :
    adjointOp (transportK e e' he' κ) (ν.map e) = (adjointOp κ ν).map e := by
  ext A hA
  rw [adjointOp_apply _ _ hA, Measure.map_apply he hA, adjointOp_apply _ _ (he hA),
    lintegral_map (Kernel.measurable_coe _ hA) he]
  refine lintegral_congr fun s => ?_
  rw [transportK_apply he he' κ, hl, Measure.map_apply he hA]

include he hl in
theorem iterate_transportK_map (ν : Measure S) (n : ℕ) :
    (adjointOp (transportK e e' he' κ))^[n] (ν.map e) = ((adjointOp κ)^[n] ν).map e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      adjointOp_transportK_map he he' hl]

include he hl hr in
theorem kpow_transportK (n : ℕ) (t : T) :
    kpow (transportK e e' he' κ) n t = (kpow κ n (e' t)).map e := by
  rw [← iterate_dirac, ← iterate_dirac,
    show Measure.dirac t = (Measure.dirac (e' t)).map e by rw [Measure.map_dirac' he, hr],
    iterate_transportK_map he he' hl]

include he in
theorem markovOpR_transportK {f : T → ℝ} (hf : Measurable f) (t : T) :
    markovOpR (transportK e e' he' κ) f t = markovOpR κ (f ∘ e) (e' t) := by
  rw [markovOpR, markovOpR, transportK_apply he he' κ,
    integral_map he.aemeasurable hf.aestronglyMeasurable]
  rfl

variable [MetricSpace S] [BorelSpace S] [PartialOrder S] {l : ℕ} {a b : Fin l → ℝ}

/-- **Theorem 12.12**, transported. Let `S` be order-isomorphic and homeomorphic to an order
interval `[a, b]` of `ℝˡ` by `e`. If `P` on `S` is monotone and Feller, and for some `c`, `ε > 0`,
`N ≥ 1`, `Pᴺ(e⁻¹a, [c, ∞)) ≥ ε` and `Pᴺ(e⁻¹b, (−∞, c]) ≥ ε` (Assumption 12.1), then `P` has a
unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12_of_orderIso (hab : a ≤ b) (e : S ≃o Icc a b) (he : Continuous e)
    (he' : Continuous e.symm) (κ : Kernel S S) [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    (hF : IsFeller κ) {c : S} {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N (e.symm (IccBot hab))).real (Ici c))
    (htop : ε ≤ (kpow κ N (e.symm (IccTop hab))).real (Iic c)) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure S, IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure S, IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  have hem := he.measurable
  have hem' := he'.measurable
  have hl : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  have hr : ∀ t, e (e.symm t) = t := e.apply_symm_apply
  set κ' := transportK e e.symm hem' κ
  have := isMarkovKernel_transportK hem hem' κ
  -- monotone and Feller transfer
  have hM' : IsMonotoneTF κ' := fun f hf hb hm t t' htt' => by
    rw [markovOpR_transportK hem hem' κ hf, markovOpR_transportK hem hem' κ hf]
    obtain ⟨B, hB⟩ := hb
    exact hM (f ∘ e) (hf.comp hem) ⟨B, fun s => hB _⟩ (hm.comp e.monotone) (e.symm.monotone htt')
  have hF' : IsFeller κ' := fun f hf hb => by
    have hfun : markovOpR κ' f = markovOpR κ (f ∘ e) ∘ e.symm :=
      funext fun t => markovOpR_transportK hem hem' κ hf.measurable t
    rw [hfun]
    obtain ⟨B, hB⟩ := hb
    exact (hF (f ∘ e) (hf.comp he) ⟨B, fun s => hB _⟩).comp he'
  -- Assumption 12.1 transfers
  have hpre : ∀ (n : ℕ) (t : Icc a b) {A : Set (Icc a b)}, MeasurableSet A →
      (kpow κ' n t).real A = (kpow κ n (e.symm t)).real (e ⁻¹' A) := fun n t A hA => by
    rw [kpow_transportK hem hem' hl hr κ, measureReal_def, Measure.map_apply hem hA,
      measureReal_def]
  have hA : Assumption12_1 hab κ' (e c) ε N := by
    refine ⟨hε, hN, ?_, ?_⟩
    · rw [hpre N _ measurableSet_Ici]
      convert hbot using 2
      ext s; simp
    · rw [hpre N _ measurableSet_Iic]
      convert htop using 2
      ext s; simp
  obtain ⟨μ', hμ', hfix', huniq', hconv'⟩ := theorem_12_12 hab κ' hM' hF' hA
  have hmap : ∀ ν : Measure S, (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hem' hem]
    have : (e.symm ∘ e) = id := funext hl
    rw [this, Measure.map_id]
  set μ := μ'.map e.symm
  have hμe : μ.map e = μ' := by
    rw [Measure.map_map hem hem']
    have : (e ∘ e.symm) = id := funext hr
    rw [this, Measure.map_id]
  have hμ : IsProbabilityMeasure μ := inferInstance
  have hfix : adjointOp κ μ = μ := by
    have h1 := adjointOp_transportK_map hem hem' hl κ μ
    rw [hμe, hfix'] at h1
    rw [← hmap (adjointOp κ μ), ← h1]
  refine ⟨μ, hμ, hfix, fun ν hν hνfix => ?_, fun lam₀ hlam₀ f => ?_⟩
  · have : IsProbabilityMeasure (ν.map e) := inferInstance
    have h1 := adjointOp_transportK_map hem hem' hl κ ν
    rw [hνfix] at h1
    rw [← hmap ν, huniq' _ this h1]
  · have : IsProbabilityMeasure (lam₀.map e) := inferInstance
    set g : Icc a b →ᵇ ℝ := f.compContinuous ⟨e.symm, he'⟩
    have hlim := hconv' _ this g
    have hg : ∀ ν : Measure S, ∫ t, g t ∂(ν.map e) = ∫ s, f s ∂ν := fun ν => by
      rw [integral_map hem.aemeasurable g.continuous.measurable.aestronglyMeasurable]
      simp [g, hl]
    have heq : ∀ n, ∫ t, g t ∂((adjointOp κ')^[n] (lam₀.map e)) =
        ∫ s, f s ∂((adjointOp κ)^[n] lam₀) := fun n => by
      rw [iterate_transportK_map hem hem' hl κ, hg]
    rw [← hμe, hg] at hlim
    exact hlim.congr heq

/-! ### Real intervals -/

/-- `[a, b] ⊆ ℝ` is order-isomorphic to the order interval `[a, b]` of `ℝ¹`. -/
def realToFin1 (a b : ℝ) : Icc a b ≃o Icc (fun _ : Fin 1 => a) (fun _ => b) where
  toFun x := ⟨fun _ => x.1, fun _ => x.2.1, fun _ => x.2.2⟩
  invFun t := ⟨t.1 0, t.2.1 0, t.2.2 0⟩
  left_inv x := rfl
  right_inv t := by ext i; fin_cases i; rfl
  map_rel_iff' {x y} := by
    change ((fun _ : Fin 1 => x.1) ≤ fun _ => y.1) ↔ x ≤ y
    rw [Pi.le_def]
    exact ⟨fun h => h 0, fun h _ => h⟩

theorem continuous_realToFin1 (a b : ℝ) : Continuous (realToFin1 a b) :=
  Continuous.subtype_mk (continuous_pi fun _ => continuous_subtype_val) _

theorem continuous_realToFin1_symm (a b : ℝ) : Continuous (realToFin1 a b).symm :=
  Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _

/-- **Theorem 12.12** on a real interval `[a, b]`: a monotone Feller `P` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε` (`ε > 0`, `N ≥ 1`) has a unique invariant probability measure `λ*`, and
`T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12_real {a b : ℝ} (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b))
    [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N ⟨a, left_mem_Icc.2 hab⟩).real (Ici c))
    (htop : ε ≤ (kpow κ N ⟨b, right_mem_Icc.2 hab⟩).real (Iic c)) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ :=
  theorem_12_12_of_orderIso (a := fun _ : Fin 1 => a) (b := fun _ => b) (fun _ => hab)
    (realToFin1 a b) (continuous_realToFin1 a b) (continuous_realToFin1_symm a b) κ hM hF hε hN
    hbot htop

/-! ### Rectangles in `ℝ × ℝ` -/

/-- `[a, b] ⊆ ℝ × ℝ` (coordinatewise order) is order-isomorphic to the order interval
`[(a₁, a₂), (b₁, b₂)]` of `ℝ²`. -/
def prodToFin2 (a b : ℝ × ℝ) : Icc a b ≃o Icc ![a.1, a.2] ![b.1, b.2] where
  toFun x := ⟨![x.1.1, x.1.2], fun i => by fin_cases i <;> simp [x.2.1.1, x.2.1.2],
    fun i => by fin_cases i <;> simp [x.2.2.1, x.2.2.2]⟩
  invFun t := ⟨(t.1 0, t.1 1), ⟨by simpa using t.2.1 0, by simpa using t.2.1 1⟩,
    ⟨by simpa using t.2.2 0, by simpa using t.2.2 1⟩⟩
  left_inv x := rfl
  right_inv t := by ext i; fin_cases i <;> rfl
  map_rel_iff' {x y} := by
    change (![x.1.1, x.1.2] ≤ ![y.1.1, y.1.2]) ↔ x ≤ y
    rw [Pi.le_def, Fin.forall_fin_two, Subtype.mk_le_mk, Prod.le_def]
    simp

theorem continuous_prodToFin2 (a b : ℝ × ℝ) : Continuous (prodToFin2 a b) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  fin_cases i
  · exact continuous_fst.comp continuous_subtype_val
  · exact continuous_snd.comp continuous_subtype_val

theorem continuous_prodToFin2_symm (a b : ℝ × ℝ) : Continuous (prodToFin2 a b).symm :=
  Continuous.subtype_mk (((continuous_apply 0).comp continuous_subtype_val).prodMk
    ((continuous_apply 1).comp continuous_subtype_val)) _

/-- **Theorem 12.12** on a rectangle `[a, b] ⊆ ℝ × ℝ` with the coordinatewise order. -/
theorem theorem_12_12_prod {a b : ℝ × ℝ} (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b))
    [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (hbot : ε ≤ (kpow κ N ⟨a, left_mem_Icc.2 hab⟩).real (Ici c))
    (htop : ε ≤ (kpow κ N ⟨b, right_mem_Icc.2 hab⟩).real (Iic c)) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  have hab' : ![a.1, a.2] ≤ ![b.1, b.2] := by
    rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨by simpa using hab.1, by simpa using hab.2⟩
  exact theorem_12_12_of_orderIso hab' (prodToFin2 a b) (continuous_prodToFin2 a b)
    (continuous_prodToFin2_symm a b) κ hM hF hε hN hbot htop

end Miao.IncompleteMarkets.SIWC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §8.3.2, Case 1: Proposition 8.3.1 (a unique stable stationary distribution)

Copied from `EconomicDynamics/Applications` (module `SIStationary`), namespace renamed.

Miao, §8.3.2, pp. 254–256. Let `βR < 1`, `y_min < y_max`, the relative risk aversion be below
`γ` for large `c`, and income be iid with `μ([a, b]) ≥ α(b − a)` on `[y_min, y_max]` (`α > 0`).

* `kernel xf`: the transition function `P` of `x_{t+1} = Râ(x_t) + y_{t+1} − rb` on
  `[x_min, x_f]` (`P(x, A) = μ{y : Râ(x) + y − rb ∈ A}` for `A ⊆ [x_min, x_f]`, `kernel_apply`);
  on `[x_min, x_max]` the clamp in its definition is never active (`mapsTo_Icc`).
* `isMonotoneTF_kernel`, `isFeller_kernel`: `P` is monotone and Feller ("we can easily verify",
  p. 255), from Lemma 8.3.1 (`â` nondecreasing and continuous).
* `phi`: `φₙ(x, y)` (p. 255), the cash on hand after `n` periods of constant income `y`;
  `phi_mono` (increasing in `x` and `y`), `phi_mem`, `continuousOn_phi`.
* `kpow_ge`: **the displayed bounds of p. 255**,
  `Pⁿ(x, [φₙ(x, a), φₙ(x, b)]) ≥ μ([a, b])ⁿ ≥ αⁿ(b − a)ⁿ` for `[a, b] ⊆ [y_min, y_max]`,
  in particular `[a, b] = [y_max − δ, y_max]` and `[y_min, y_min + δ]` (`kpow_ge_real`).
* `next_low_lt`, `phi_low_tendsto`: with income `y_min` forever, cash on hand falls strictly and
  `φₙ(x_f, y_min) ↓ x_min`. This is what the book's "a similar argument applies to `x₀ = x_max`"
  needs; it is proved from the Euler equation (`βR < 1`).
* `mixing`: the mixing condition (Assumption 12.1 of SLP, Miao's Theorems 3.3.5–3.3.6) at
  `x̄ = x_min + (y_max − y_min)/2`.
* **Proposition 8.3.1** (`proposition_8_3_1`): `P` on `[x_min, x_max]` has a unique invariant
  probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every initial distribution `λ₀` (SLP Theorem
  12.12, `SIWC.theorem_12_12_real`).

**Departures.** (1) The book takes `x̄ = lim φₙ(x_min, Ey)`; any `x̄` strictly between
`x_min = lim φₙ(x_max, y_min)` and `φ₁(x_min, y_max − δ) ≥ y_max − δ − rb` works, and we take
the midpoint, which avoids the limit `ξ` and the comparison `ξ > x̄`. (2) The book says
`φₙ(x_min, y_max)` is strictly increasing; it is only nondecreasing (`phi_high_monotone`): if
`y_max − rb ≤ x̂` (Lemma 8.3.2) then `φ₂ = φ₁` (`phi_two_eq_one`). (3) The continuity of the
stationary distribution in `(R, b)` is not formalised: it needs the policy `â` to be jointly
continuous in `(x, R, b)`, which the book's assumption (a solution `V` for each parameter) does
not provide, and the state space `[x_min, x_max]` itself moves with `(R, b)`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- The clamp of `Râ(x) + y − rb` to `[x_min, x_f]`. -/
noncomputable def kmap (xf : ℝ) (p : Set.Icc M.xmin xf × ℝ) : Set.Icc M.xmin xf :=
  ⟨max M.xmin (min xf (M.next (S.sav p.1) p.2)),
    ⟨le_max_left _ _, max_le (p.1.2.1.trans p.1.2.2) (min_le_left _ _)⟩⟩

theorem continuous_kmap (xf : ℝ) : Continuous (S.kmap xf) := by
  have hs : Continuous fun x : Set.Icc M.xmin xf => S.sav x :=
    S.continuousOn_sav.comp_continuous continuous_subtype_val fun x => Set.mem_Ici.2 x.2.1
  refine Continuous.subtype_mk ?_ _
  refine continuous_const.max (continuous_const.min ?_)
  simp only [SIModel.next]
  exact ((continuous_const.mul (hs.comp continuous_fst)).add continuous_snd).sub continuous_const

theorem continuous_kmap_y (xf : ℝ) (x : Set.Icc M.xmin xf) :
    Continuous fun y => S.kmap xf (x, y) :=
  (S.continuous_kmap xf).comp (Continuous.prodMk_right x)

/-- The **transition function** `P(x, ·)` of `x_{t+1} = Râ(x_t) + y_{t+1} − rb` on
`[x_min, x_f]` (Miao, p. 255). -/
noncomputable def kernel (xf : ℝ) : Kernel (Set.Icc M.xmin xf) (Set.Icc M.xmin xf) where
  toFun x := M.law.map fun y => S.kmap xf (x, y)
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have : ∀ x, (M.law.map fun y => S.kmap xf (x, y)) A =
        M.law (Prod.mk x ⁻¹' (S.kmap xf ⁻¹' A)) := fun x =>
      Measure.map_apply (S.continuous_kmap_y xf x).measurable hA
    simp_rw [this]
    exact measurable_measure_prodMk_left ((S.continuous_kmap xf).measurable hA)

theorem kernel_eq (xf : ℝ) (x : Set.Icc M.xmin xf) :
    S.kernel xf x = M.law.map fun y => S.kmap xf (x, y) := rfl

/-- `P(x, A) = μ{y : clamp(Râ(x) + y − rb) ∈ A}`. -/
theorem kernel_apply (xf : ℝ) (x : Set.Icc M.xmin xf) {A : Set (Set.Icc M.xmin xf)}
    (hA : MeasurableSet A) : S.kernel xf x A = M.law {y | S.kmap xf (x, y) ∈ A} :=
  Measure.map_apply (S.continuous_kmap_y xf x).measurable hA

theorem isMarkovKernel_kernel (xf : ℝ) : IsMarkovKernel (S.kernel xf) where
  isProbabilityMeasure x := by
    rw [kernel_eq]
    infer_instance

/-- `(Tf)(x) = ∫ f(clamp(Râ(x) + y − rb)) μ(dy)`. -/
theorem markovOpR_kernel (xf : ℝ) {f : Set.Icc M.xmin xf → ℝ} (hf : Measurable f)
    (x : Set.Icc M.xmin xf) :
    SIWC.markovOpR (S.kernel xf) f x = ∫ y, f (S.kmap xf (x, y)) ∂M.law := by
  rw [SIWC.markovOpR, kernel_eq, integral_map (S.continuous_kmap_y xf x).measurable.aemeasurable
    hf.aestronglyMeasurable]

theorem kmap_mono (xf : ℝ) {x x' : Set.Icc M.xmin xf} (hxx : x ≤ x') (y : ℝ) :
    S.kmap xf (x, y) ≤ S.kmap xf (x', y) := by
  have h1 := S.sav_mono (Set.mem_Ici.2 x.2.1) (Set.mem_Ici.2 x'.2.1) hxx
  have h2 : M.next (S.sav x) y ≤ M.next (S.sav x') y := by
    simp only [SIModel.next]; nlinarith [M.R_pos]
  change max M.xmin (min xf (M.next (S.sav x) y)) ≤ max M.xmin (min xf (M.next (S.sav x') y))
  exact max_le_max le_rfl (min_le_min le_rfl h2)

/-- `P` is **monotone** (Miao, p. 255). -/
theorem isMonotoneTF_kernel (xf : ℝ) : SIWC.IsMonotoneTF (S.kernel xf) := by
  intro f hf ⟨C, hC⟩ hmono x x' hxx
  rw [S.markovOpR_kernel xf hf, S.markovOpR_kernel xf hf]
  refine integral_mono ?_ ?_ fun y => hmono (S.kmap_mono xf hxx y)
  · exact Integrable.of_bound (hf.comp (S.continuous_kmap_y xf x).measurable).aestronglyMeasurable
      C (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC _)
  · exact Integrable.of_bound (hf.comp (S.continuous_kmap_y xf x').measurable).aestronglyMeasurable
      C (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC _)

/-- `P` has the **Feller property** (Miao, p. 255). -/
theorem isFeller_kernel (xf : ℝ) : SIWC.IsFeller (S.kernel xf) := by
  intro f hf ⟨C, hC⟩
  have heq : SIWC.markovOpR (S.kernel xf) f = fun x => ∫ y, f (S.kmap xf (x, y)) ∂M.law :=
    funext (S.markovOpR_kernel xf hf.measurable)
  rw [heq]
  have hc := hf.comp (S.continuous_kmap xf)
  exact continuous_of_dominated (bound := fun _ => C)
    (fun x => (hc.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => by rw [Real.norm_eq_abs]; exact hC _)
    (integrable_const _) (Eventually.of_forall fun y => hc.comp (Continuous.prodMk_left y))

/-! ### The paths `φₙ(x, y)` -/

/-- `φₙ(x, y)` (Miao, p. 255): cash on hand at the start of period `n` from `x` when income is
`y` every period and `â` is followed: `φ₀ = x`, `φₙ₊₁ = Râ(φₙ) + y − rb`. -/
noncomputable def phi (y x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => M.next (S.sav (phi y x n)) y

theorem phi_zero (y x : ℝ) : S.phi y x 0 = x := rfl

theorem phi_succ (y x : ℝ) (n : ℕ) : S.phi y x (n + 1) = M.next (S.sav (S.phi y x n)) y := rfl

theorem phi_ge {y x : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (n : ℕ) : M.xmin ≤ S.phi y x n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact M.next_ge (S.sav_mem _ ih).1 hy

/-- `φₙ(x, y) ≥ y − rb` for `n ≥ 1`. -/
theorem phi_succ_ge {y x : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (n : ℕ) :
    y - M.r * M.b ≤ S.phi y x (n + 1) := by
  have := mul_nonneg M.R_pos.le (S.sav_mem _ (S.phi_ge hy hx n)).1
  rw [phi_succ]; simp only [SIModel.next]; linarith

/-- `φₙ(x, y)` is nondecreasing in `x` and in `y` (Miao, p. 255). -/
theorem phi_mono {y y' x x' : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (hyy : y ≤ y')
    (hxx : x ≤ x') (n : ℕ) : S.phi y x n ≤ S.phi y' x' n := by
  induction n with
  | zero => exact hxx
  | succ n ih =>
    have h1 := S.sav_mono (Set.mem_Ici.2 (S.phi_ge hy hx n))
      (Set.mem_Ici.2 ((S.phi_ge hy hx n).trans ih)) ih
    rw [phi_succ, phi_succ]; simp only [SIModel.next]; nlinarith [M.R_pos]

/-- `φₙ(x, y) ∈ [x_min, x_f]` for `x ∈ [x_min, x_f]`, `y ∈ [y_min, y_max]`, when `x_f ≥ x_min`
is a fixed point of `x ↦ Râ(x) + y_max − rb`. -/
theorem phi_mem {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) {x y : ℝ}
    (hx : x ∈ Set.Icc M.xmin xf) (hy : y ∈ Set.Icc M.ymin M.ymax) (n : ℕ) :
    S.phi y x n ∈ Set.Icc M.xmin xf := by
  induction n with
  | zero => exact hx
  | succ n ih => exact S.mapsTo_Icc hxf hfix ih hy

/-- `y ↦ φₙ(x, y)` is continuous on `[y_min, ∞)`. -/
theorem continuousOn_phi {x : ℝ} (hx : M.xmin ≤ x) (n : ℕ) :
    ContinuousOn (fun y => S.phi y x n) (Set.Ici M.ymin) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have h1 : ContinuousOn (fun y => S.sav (S.phi y x n)) (Set.Ici M.ymin) :=
      S.continuousOn_sav.comp ih fun y hy => Set.mem_Ici.2 (S.phi_ge hy hx n)
    simp only [phi_succ, SIModel.next]
    exact ((continuousOn_const.mul h1).add continuousOn_id).sub continuousOn_const

/-- The book's claim that `φₙ(x_min, y_max)` increases: it is nondecreasing. -/
theorem phi_high_monotone : Monotone (S.phi M.ymax M.xmin) := by
  have hy : M.ymin ≤ M.ymax := M.ymin_le_ymax
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero =>
    have := M.next_ge (S.sav_mem M.xmin le_rfl).1 hy
    exact this
  | succ n ih =>
    rw [phi_succ, phi_succ (n := n + 1)]
    have h1 := S.sav_mono (Set.mem_Ici.2 (S.phi_ge hy le_rfl n))
      (Set.mem_Ici.2 (S.phi_ge hy le_rfl (n + 1))) ih
    simp only [SIModel.next]; nlinarith [M.R_pos]

/-- **"Strictly increasing" is false in general** (p. 256): if the borrowing constraint binds
at `φ₁(x_min, y_max) = y_max − rb + Râ(x_min)` and at `x_min`, then `φ₂ = φ₁`. -/
theorem phi_two_eq_one (h0 : S.sav M.xmin = 0) (h1 : S.sav (S.phi M.ymax M.xmin 1) = 0) :
    S.phi M.ymax M.xmin 2 = S.phi M.ymax M.xmin 1 := by
  rw [phi_succ, h1, phi_succ, phi_zero, h0]

/-! ### Lower bounds on `Pⁿ` (Miao, p. 255) -/

/-- If `P(x₀, B₀) ≥ p` and `P(z, Bₙ₊₁) ≥ p` for all `z ∈ Bₙ`, then `Pⁿ⁺¹(x₀, Bₙ) ≥ pⁿ⁺¹`
(adapted from `RecursiveMethods/ConvergenceApplications`, `kpow_succ_ge_pow`). -/
theorem si_kpow_succ_ge_pow {X : Type*} [MeasurableSpace X] (κ : Kernel X X) {B : ℕ → Set X}
    (hB : ∀ n, MeasurableSet (B n)) {p : ℝ≥0∞} {x₀ : X} (h0 : p ≤ κ x₀ (B 0))
    (hstep : ∀ n, ∀ z ∈ B n, p ≤ κ z (B (n + 1))) (n : ℕ) :
    p ^ (n + 1) ≤ SIWC.kpow κ (n + 1) x₀ (B n) := by
  induction n with
  | zero => simpa [SIWC.kpow_one] using h0
  | succ n ih =>
    rw [SIWC.kpow_add κ (n + 1) 1, SIWC.kpow_one, Kernel.comp_apply' _ _ _ (hB (n + 1))]
    calc p ^ (n + 1 + 1) = p * p ^ (n + 1) := pow_succ' _ _
      _ ≤ p * SIWC.kpow κ (n + 1) x₀ (B n) := by gcongr
      _ = ∫⁻ z, (B n).indicator (fun _ => p) z ∂(SIWC.kpow κ (n + 1) x₀) :=
          (lintegral_indicator_const (hB n) p).symm
      _ ≤ ∫⁻ z, κ z (B (n + 1)) ∂(SIWC.kpow κ (n + 1) x₀) := lintegral_mono fun z => by
          by_cases hz : z ∈ B n
          · rw [Set.indicator_of_mem hz]; exact hstep n z hz
          · rw [Set.indicator_of_notMem hz]; exact zero_le

/-- The clamp keeps a value between two bounds in `[x_min, x_f]`. -/
theorem si_clamp_mem {lo xf L U w : ℝ} (hL : L ≤ xf) (hU : lo ≤ U) (hw : w ∈ Set.Icc L U) :
    L ≤ max lo (min xf w) ∧ max lo (min xf w) ≤ U :=
  ⟨le_max_of_le_right (le_min hL hw.1), max_le hU ((min_le_right _ _).trans hw.2)⟩

/-- **The bounds of p. 255**: for `x₀ ∈ [x_min, x_f]` and `[a, b] ⊆ [y_min, y_max]`,
`Pⁿ⁺¹(x₀, [φₙ₊₁(x₀, a), φₙ₊₁(x₀, b)]) ≥ μ([a, b])ⁿ⁺¹`. -/
theorem kpow_ge {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf)
    (x₀ : Set.Icc M.xmin xf) {a b : ℝ} (ha : M.ymin ≤ a) (hab : a ≤ b) (hb : b ≤ M.ymax)
    (n : ℕ) :
    M.law (Set.Icc a b) ^ (n + 1) ≤ SIWC.kpow (S.kernel xf) (n + 1) x₀
      {z | S.phi a x₀ (n + 1) ≤ z.1 ∧ z.1 ≤ S.phi b x₀ (n + 1)} := by
  have haI : a ∈ Set.Icc M.ymin M.ymax := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Set.Icc M.ymin M.ymax := ⟨ha.trans hab, hb⟩
  have hmeas : ∀ m, MeasurableSet {z : Set.Icc M.xmin xf |
      S.phi a x₀ (m + 1) ≤ z.1 ∧ z.1 ≤ S.phi b x₀ (m + 1)} := fun m =>
    measurable_subtype_coe measurableSet_Icc
  -- one step from any `z` in the band
  have hstep : ∀ m, ∀ z : Set.Icc M.xmin xf, S.phi a x₀ m ≤ z.1 → z.1 ≤ S.phi b x₀ m →
      M.law (Set.Icc a b) ≤ S.kernel xf z
        {w | S.phi a x₀ (m + 1) ≤ w.1 ∧ w.1 ≤ S.phi b x₀ (m + 1)} := by
    intro m z hza hzb
    rw [S.kernel_apply xf z (hmeas m)]
    refine measure_mono fun y hy => ?_
    have hza' := S.phi_ge ha x₀.2.1 m
    have h1 := S.sav_mono (Set.mem_Ici.2 hza') (Set.mem_Ici.2 z.2.1) hza
    have h2 := S.sav_mono (Set.mem_Ici.2 z.2.1)
      (Set.mem_Ici.2 (z.2.1.trans hzb)) hzb
    have hw : M.next (S.sav z) y ∈ Set.Icc (S.phi a x₀ (m + 1)) (S.phi b x₀ (m + 1)) := by
      rw [phi_succ, phi_succ]
      simp only [SIModel.next]
      constructor <;> nlinarith [M.R_pos, hy.1, hy.2]
    exact si_clamp_mem (S.phi_mem hxf hfix x₀.2 haI (m + 1)).2
      (S.phi_mem hxf hfix x₀.2 hbI (m + 1)).1 hw
  refine si_kpow_succ_ge_pow (S.kernel xf) hmeas ?_ (fun m z hz => hstep (m + 1) z hz.1 hz.2) n
  exact hstep 0 x₀ le_rfl le_rfl

/-- The bounds of p. 255 with `μ([a, b]) ≥ α(b − a)`: for `n ≥ 1`,
`Pⁿ(x₀, [φₙ(x₀, a), φₙ(x₀, b)]) ≥ αⁿ(b − a)ⁿ`; in particular (`a, b = y_max − δ, y_max` and
`y_min, y_min + δ`) the two displayed inequalities with `αⁿδⁿ`. -/
theorem kpow_ge_real {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf)
    {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b))
    (x₀ : Set.Icc M.xmin xf) {a b : ℝ} (ha : M.ymin ≤ a) (hab : a ≤ b) (hb : b ≤ M.ymax)
    {n : ℕ} (hn : 1 ≤ n) :
    (α * (b - a)) ^ n ≤ (SIWC.kpow (S.kernel xf) n x₀).real
      {z | S.phi a x₀ n ≤ z.1 ∧ z.1 ≤ S.phi b x₀ n} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := S.isMarkovKernel_kernel xf
  have := SIWC.ex_8_4a (S.kernel xf) (m + 1)
  have h0 : 0 ≤ α * (b - a) := mul_nonneg hα.le (by linarith)
  have h1 : ENNReal.ofReal (α * (b - a)) ≤ M.law (Set.Icc a b) :=
    ENNReal.ofReal_le_of_le_toReal (hμ a b ha hab hb)
  have h2 := S.kpow_ge hxf hfix x₀ ha hab hb m
  rw [measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
    ENNReal.ofReal_pow h0]
  exact (pow_le_pow_left' h1 _).trans h2

/-! ### Income `y_min` forever -/

/-- With `βR < 1`, at the lowest income cash on hand falls strictly:
`Râ(x) + y_min − rb < x` for `x > x_min`. -/
theorem next_low_lt (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin < x) :
    M.next (S.sav x) M.ymin < x := by
  have hx0 : M.xmin ≤ x := hx.le
  rcases (S.sav_mem x hx0).1.lt_or_eq with hpos | hz
  · by_contra hcon
    push Not at hcon
    have he' := (S.euler hx0).2 hpos
    have he : S.dV x = M.β * M.R * S.D (S.sav x) := by rw [S.envelope x hx0]; exact he'
    have hD := S.D_le_low (S.sav_mem x hx0).1
    have h1 := S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hcon))
      hcon
    have hdV := S.dV_pos hx0
    have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have : S.dV x ≤ M.β * M.R * S.dV x :=
      he.le.trans (mul_le_mul_of_nonneg_left (hD.trans h1) hβR0.le)
    nlinarith
  · rw [← hz, M.next_ymin, mul_zero, zero_add]; exact hx

/-- `Râ(x) + y_min − rb ≤ x` for `x ≥ x_min` (`βR < 1`). -/
theorem next_low_le (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin ≤ x) :
    M.next (S.sav x) M.ymin ≤ x := by
  rcases hx.lt_or_eq with hlt | heq
  · exact (S.next_low_lt hβR hlt).le
  · subst heq
    rw [(S.sav_xmin hβR).1, M.next_ymin, mul_zero, zero_add]

/-- With `βR < 1` and income `y_min` forever, cash on hand decreases to `x_min`:
`φₙ(x, y_min) ↓ x_min`. -/
theorem phi_low_tendsto (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin ≤ x) :
    Antitone (S.phi M.ymin x) ∧ Tendsto (S.phi M.ymin x) atTop (𝓝 M.xmin) := by
  have hge := S.phi_ge le_rfl hx
  have hanti : Antitone (S.phi M.ymin x) := antitone_nat_of_succ_le fun n => by
    rw [phi_succ]; exact S.next_low_le hβR (hge n)
  refine ⟨hanti, ?_⟩
  have hbdd : BddBelow (Set.range (S.phi M.ymin x)) := ⟨M.xmin, by
    rintro _ ⟨n, rfl⟩; exact hge n⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, S.phi M.ymin x n
  have hL : M.xmin ≤ L := le_ciInf hge
  have hT : Tendsto (fun n => M.next (S.sav (S.phi M.ymin x n)) M.ymin) atTop
      (𝓝 (M.next (S.sav L) M.ymin)) :=
    ((M.continuous_next M.ymin).continuousAt.tendsto.comp
      ((S.continuousOn_sav L (Set.mem_Ici.2 hL)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => Set.mem_Ici.2 (hge n)⟩)))
  have hS : Tendsto (fun n => S.phi M.ymin x (n + 1)) atTop (𝓝 L) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hfix : M.next (S.sav L) M.ymin = L := tendsto_nhds_unique hT hS
  rcases hL.lt_or_eq with hlt | heq
  · exact absurd hfix (S.next_low_lt hβR hlt).ne
  · rw [← heq] at hlim; exact hlim

/-! ### The mixing condition and Proposition 8.3.1 -/

/-- **The mixing condition** (Miao, p. 255; SLP Assumption 12.1) on `[x_min, x_f]`, `x_f` a
fixed point of `x ↦ Râ(x) + y_max − rb`: with `x̄ = x_min + (y_max − y_min)/2` there are
`N ≥ 1` and `ε > 0` with `Pᴺ(x_min, [x̄, x_f]) ≥ ε` and `Pᴺ(x_f, [x_min, x̄]) ≥ ε`. -/
theorem mixing (hβR : M.β * M.R < 1) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b))
    {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) :
    ∃ (c : Set.Icc M.xmin xf) (ε : ℝ) (N : ℕ), 0 < ε ∧ 1 ≤ N ∧
      ε ≤ (SIWC.kpow (S.kernel xf) N ⟨M.xmin, Set.left_mem_Icc.2 hxf⟩).real (Set.Ici c) ∧
      ε ≤ (SIWC.kpow (S.kernel xf) N ⟨xf, Set.right_mem_Icc.2 hxf⟩).real (Set.Iic c) := by
  set Δ := (M.ymax - M.ymin) / 2
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  set cbar := M.xmin + Δ
  -- `N`: from `x_f` with income `y_min`, cash on hand drops below `x̄`
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((S.phi_low_tendsto hβR hxf).2.eventually
    (gt_mem_nhds (show M.xmin < cbar by simp only [cbar]; linarith)))
  set N := N₀ + 1
  have hN : S.phi M.ymin xf N < cbar := hN₀ N (by omega)
  -- `δ`: by continuity in `y`
  have hcw : ContinuousWithinAt (fun y => S.phi y xf N) (Set.Ici M.ymin) M.ymin :=
    S.continuousOn_phi hxf N M.ymin (Set.mem_Ici.2 le_rfl)
  have hev : {y | S.phi y xf N < cbar} ∈ 𝓝[≥] M.ymin :=
    hcw.tendsto.eventually (gt_mem_nhds hN)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  set δ := min (u - M.ymin) Δ
  have hδ : 0 < δ := lt_min (by linarith) hΔ
  have hδΔ : δ ≤ Δ := min_le_right _ _
  have hδu : M.ymin + δ ≤ u := by have := min_le_left (u - M.ymin) Δ; linarith
  have hδy : δ ≤ M.ymax - M.ymin := by simp only [Δ] at hδΔ; linarith
  -- the lower end
  have hlow : cbar ≤ S.phi (M.ymax - δ) M.xmin N := by
    have := S.phi_succ_ge (y := M.ymax - δ) (x := M.xmin) (by linarith) le_rfl N₀
    simp only [cbar, SIModel.xmin, Δ] at this ⊢
    simp only [Δ] at hδΔ
    linarith
  have hhighI : M.ymax - δ ∈ Set.Icc M.ymin M.ymax := ⟨by linarith, by linarith⟩
  have hcmem : cbar ∈ Set.Icc M.xmin xf := ⟨by simp only [cbar]; linarith,
    hlow.trans (S.phi_mem hxf hfix (Set.left_mem_Icc.2 hxf) hhighI N).2⟩
  refine ⟨⟨cbar, hcmem⟩, (α * δ) ^ N, N, pow_pos (mul_pos hα hδ) N, by omega, ?_, ?_⟩
  · have h := S.kpow_ge_real hxf hfix hα hμ ⟨M.xmin, Set.left_mem_Icc.2 hxf⟩
      (a := M.ymax - δ) (b := M.ymax) (by linarith) (by linarith) le_rfl (n := N) (by omega)
    rw [show M.ymax - (M.ymax - δ) = δ by ring] at h
    have := S.isMarkovKernel_kernel xf
    have := SIWC.ex_8_4a (S.kernel xf) N
    refine h.trans (measureReal_mono fun z hz => ?_)
    exact hlow.trans hz.1
  · have h := S.kpow_ge_real hxf hfix hα hμ ⟨xf, Set.right_mem_Icc.2 hxf⟩
      (a := M.ymin) (b := M.ymin + δ) le_rfl (by linarith) (by linarith) (n := N) (by omega)
    rw [show M.ymin + δ - M.ymin = δ by ring] at h
    have := S.isMarkovKernel_kernel xf
    have := SIWC.ex_8_4a (S.kernel xf) N
    refine h.trans (measureReal_mono fun z hz => ?_)
    have : S.phi (M.ymin + δ) xf N < cbar := hsub ⟨by linarith, hδu⟩
    exact hz.2.trans this.le

/-- **Proposition 8.3.1** (Schechtman and Escudero (1977), Clarida (1987), Aiyagari (1994);
Miao, p. 254). Let `βR < 1`, `y_min < y_max`, `−cu′′(c)/u′(c) < γ` for large `c` (`γ > 0`), and
let `y_t` be iid with law `μ` satisfying `μ([a, b]) ≥ α(b − a)` for `[a, b] ⊆ [y_min, y_max]`.
Then the cash-on-hand process `x_{t+1} = Râ(x_t) + y_{t+1} − rb` has a unique stationary
distribution `λ*` on `[x_min, x_max]`, and it is stable: `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem proposition_8_3_1 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃ lam : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam ∧
      SIWC.adjointOp (S.kernel S.xmax) lam = lam ∧
      (∀ ν : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure ν →
        SIWC.adjointOp (S.kernel S.xmax) ν = ν → ν = lam) ∧
      ∀ lam₀ : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam₀ →
        SIWC.ConvWeak (fun n => (SIWC.adjointOp (S.kernel S.xmax))^[n] lam₀) lam := by
  obtain ⟨hgt, ⟨hmem, -⟩, -, -⟩ := S.ex_8_9 hβR hddu hγ0 hγ hy
  have hxf : M.xmin ≤ S.xmax := hgt.le
  have := S.isMarkovKernel_kernel S.xmax
  obtain ⟨c, ε, N, hε, hN, hbot, htop⟩ := S.mixing hβR hy hα hμ hxf hmem.2
  exact SIWC.theorem_12_12_real hxf (S.kernel S.xmax) (S.isMonotoneTF_kernel _)
    (S.isFeller_kernel _) hε hN hbot htop

end SIModel.Solution

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.1: the income fluctuation problem of the Aiyagari model

Miao, §17.1.1, pp. 560–562. An agent with asset holdings `a_t ≥ −b` and labour endowment shock
`l_t ∈ [l_min, l_max]` (a Markov process with transition function `Q`) takes the interest rate
`r` and the wage `w` as given and maximises `E Σ βᵗ u(c_t)` subject to
`c_t + a_{t+1} = (1 + r)a_t + wl_t` (17.1)–(17.2).

* `ay_Budget`, `eq_17_2`: the budget (17.2) is the budget (8.3) of §8.3 with gross return
  `1 + r` and income `wl_t`.
* `ay_natural_limit`: Theorem 8.3.1 (in its corrected converse form, `theorem_8_3_1_converse`)
  gives the natural borrowing constraint `a_t ≥ −wl_min/r` for `r > 0`.
* `ay_phi`, `eq_17_3b`, `eq_17_3a`: the borrowing limit `φ` of (17.3b) and the constraint
  `a_t ≥ −φ` of (17.3a), which is at least as tight as both `−b` and the natural limit.
* `ay_cash_on_hand`: cash on hand `x_t = (1 + r)a_t + wl_t + φ`, `â_t = a_t + φ`:
  `c_t + â_{t+1} = x_t`, `x_{t+1} = (1 + r)â_{t+1} + wl_{t+1} − rφ`, `â_{t+1} ∈ [0, x_t]`.
* `ay_BellmanCoh` (the Bellman equation in cash on hand, p. 561), `ay_Bellman` (17.4) and
  `eq_17_4`: a solution in cash on hand gives a solution of (17.4) with
  `g(a, l) = A(x, l) − φ`.
* `ay_P`, `ay_P_apply`: the transition function `P(A × B, (a, l)) = 1_{g(a,l) ∈ A} Q(B, l)`
  of the joint process `(a_t, l_t)` (p. 562), a Markov kernel; `ay_lamSeq`, `ay_lamSeq_succ`:
  the sequence of distributions `λ_{t+1}(A × B) = ∫ P(A × B, (a, l)) dλ_t`.
* `ay_Stationary` and `eq_17_7`: the stationarity condition (17.7) on rectangles is equivalent
  to `λ* = λ*P` (`T*λ* = λ*`).
* `ay_stationary_fst`, `ay_stationary_snd`, `ay_stationary_snd_iid`, `ay_Ea`, `ay_Ea_eq_mean`:
  under (17.7) the asset marginal of `λ*` is the image of `λ*` under `g`, so the long-run average
  assets `Ea = ∫ g dλ*` equal the mean of current assets; the labour marginal is `Q`-invariant
  (and equals the iid law when `Q` does not depend on `l`).

**Departures.** (1) (17.3b) defines `φ` for `r > 0` and `r < 0` only; `ay_phi` sets `φ = b`
for `r = 0` as well. (2) The book's Theorem 8.3.1 needs a support hypothesis (the income process
can stay low with positive probability), as corrected in the Chapter 8 project; `ay_natural_limit`
carries it. (3) `eq_17_4` needs `1 + r ≥ 0` so that `a ≥ −φ` implies `x ≥ wl − rφ`.
(4) The joint state is `(a, l) ∈ ℝ × ℝ` with the policy `g` a function of the pair.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Miao, (17.2), p. 560: the budget constraint `c_t + a_{t+1} = (1 + r)a_t + wl_t`. -/
def ay_Budget (r w : ℝ) (l c a : ℕ → ℝ) : Prop :=
  ∀ t, c t + a (t + 1) = (1 + r) * a t + w * l t

/-- Miao, (17.2), p. 560: the budget (17.2) is the budget (8.3) of §8.3 with gross return
`R = 1 + r` and income `y_t = wl_t`. -/
theorem eq_17_2 (r w : ℝ) (l c a : ℕ → ℝ) :
    ay_Budget r w l c a ↔ cd_Budget (1 + r) (fun t => w * l t) c a := Iff.rfl

/-- Miao, p. 560, the natural borrowing constraint: by Theorem 8.3.1, for `r > 0` the
no-Ponzi-scheme condition `lim a_t/(1 + r)ᵗ ≥ 0` and nonnegative consumption imply
`a_t ≥ −wl_min/r` almost surely. The support hypothesis `hsupp` (the corrected hypothesis of
`theorem_8_3_1_converse`): the labour shock can stay near `l_min` for any number of periods after
any event of positive probability. -/
theorem ay_natural_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r w lmin lmax : ℝ}
    (hr : 0 < r) (hw : 0 ≤ w) (hlmin : 0 ≤ lmin) {l c a : ℕ → Ω → ℝ}
    (hl : ∀ t ω, lmin ≤ l t ω ∧ l t ω ≤ lmax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, ay_Budget r w (fun t => l t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi (1 + r) (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -(w * lmin) / r - ε} →
      0 < μ ({ω | a t ω < -(w * lmin) / r - ε} ∩
        {ω | ∀ k < N, w * l (t + k) ω ≤ w * lmin + δ})) :
    ∀ t, ∀ᵐ ω ∂μ, -(w * lmin) / r ≤ a t ω := by
  have hr' : (1 + r) - 1 = r := by ring
  have h := theorem_8_3_1_converse μ (R := 1 + r) (ymin := w * lmin) (ymax := w * lmax)
    (y := fun t ω => w * l t ω) (c := c) (a := a) (by linarith) (mul_nonneg hw hlmin)
    (fun t ω => ⟨mul_le_mul_of_nonneg_left (hl t ω).1 hw,
      mul_le_mul_of_nonneg_left (hl t ω).2 hw⟩) hc hbud hNP
    (fun t ε δ N hε hδ hpos => by rw [hr'] at hpos ⊢; exact hsupp t ε δ N hε hδ hpos)
  rw [hr'] at h
  exact h

/-- Miao, (17.3b), p. 560: the borrowing limit `φ = min{b, wl_min/r}` for `r > 0` and `φ = b`
for `r < 0` (and, as a convention not in the book, for `r = 0`). -/
noncomputable def ay_phi (b w lmin r : ℝ) : ℝ := if 0 < r then min b (w * lmin / r) else b

/-- Miao, (17.3b), p. 560: `φ ≤ b`; for `r > 0`, `φ = min{b, wl_min/r} ≤ wl_min/r`; for
`r < 0`, `φ = b`. -/
theorem eq_17_3b (b w lmin r : ℝ) :
    ay_phi b w lmin r ≤ b ∧
      (0 < r → ay_phi b w lmin r = min b (w * lmin / r) ∧ ay_phi b w lmin r ≤ w * lmin / r) ∧
      (r < 0 → ay_phi b w lmin r = b) := by
  refine ⟨?_, fun hr => ?_, fun hr => ?_⟩
  · unfold ay_phi
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  · have h : ay_phi b w lmin r = min b (w * lmin / r) := by
      unfold ay_phi; simp only [hr, ↓reduceIte]
    exact ⟨h, h ▸ min_le_right _ _⟩
  · unfold ay_phi; simp only [not_lt.2 hr.le, ↓reduceIte]

/-- Miao, (17.3a), p. 560: the constraint `a ≥ −φ` implies `a ≥ −b` and, for `r > 0`, the
natural borrowing constraint `a ≥ −wl_min/r`, so it may be imposed in their place. -/
theorem eq_17_3a {b w lmin r a : ℝ} (ha : -ay_phi b w lmin r ≤ a) :
    -b ≤ a ∧ (0 < r → -(w * lmin) / r ≤ a) := by
  obtain ⟨h1, h2, -⟩ := eq_17_3b b w lmin r
  refine ⟨by linarith, fun hr => ?_⟩
  have := (h2 hr).2
  rw [neg_div]
  linarith

/-- Miao, p. 561: with cash on hand `x = (1 + r)a + wl + φ` and `â′ = a′ + φ`, the budget
`c + a′ = (1 + r)a + wl` becomes `c + â′ = x`; next period's cash on hand is
`x′ = (1 + r)â′ + wl′ − rφ`; the constraints `a′ ≥ −φ`, `c ≥ 0` become `â′ ∈ [0, x]`. -/
theorem ay_cash_on_hand {r w φ a a' l l' c : ℝ} (hbud : c + a' = (1 + r) * a + w * l) :
    c + (a' + φ) = (1 + r) * a + w * l + φ ∧
      (1 + r) * a' + w * l' + φ = (1 + r) * (a' + φ) + w * l' - r * φ ∧
      (-φ ≤ a' ↔ 0 ≤ a' + φ) ∧ (0 ≤ c ↔ a' + φ ≤ (1 + r) * a + w * l + φ) := by
  refine ⟨by linarith, by ring, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- Miao, p. 561: the **Bellman equation in cash on hand**
`V(x, l) = max_{â′ ∈ [0, x]} u(x − â′) + β ∫ V((1 + r)â′ + wl′ − rφ, l′) Q(dl′, l)`, attained at
the policy `â′ = A(x, l)`, on the states `x ≥ wl − rφ` (from `a ≥ −φ`), `l ∈ [l_min, l_max]`. -/
def ay_BellmanCoh (u : ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ)
    (W A : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, w * p.2 - r * φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    A p ∈ Set.Icc 0 p.1 ∧
    W p = u (p.1 - A p) + β * ∫ l', W ((1 + r) * A p + w * l' - r * φ, l') ∂Q p.2 ∧
    ∀ s ∈ Set.Icc 0 p.1, u (p.1 - s) + β * ∫ l', W ((1 + r) * s + w * l' - r * φ, l') ∂Q p.2
      ≤ W p

/-- Miao, (17.4), p. 561: the Bellman equation in assets
`V(a, l) = max_{a′ ≥ −φ} u(c) + β ∫ V(a′, l′) Q(dl′, l)`, `c = (1 + r)a + wl − a′ ≥ 0`, attained
at the policy `a′ = g(a, l)`, on the states `a ≥ −φ`, `l ∈ [l_min, l_max]`. -/
def ay_Bellman (u : ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ) (V g : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, -φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    g p ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2) ∧
    V p = u ((1 + r) * p.1 + w * p.2 - g p) + β * ∫ l', V (g p, l') ∂Q p.2 ∧
    ∀ a' ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2),
      u ((1 + r) * p.1 + w * p.2 - a') + β * ∫ l', V (a', l') ∂Q p.2 ≤ V p

/-- Miao, (17.4), p. 561: a solution `(V, A)` of the Bellman equation in cash on hand gives a
solution of (17.4): `V(a, l) = V((1 + r)a + wl + φ, l)` with policy `g(a, l) = A(x, l) − φ`
(for `1 + r ≥ 0`). -/
theorem eq_17_4 {u : ℝ → ℝ} {β r w φ lmin lmax : ℝ} {Q : Kernel ℝ ℝ} {W A : ℝ × ℝ → ℝ}
    (hr : 0 ≤ 1 + r) (hW : ay_BellmanCoh u β r w φ lmin lmax Q W A) :
    ay_Bellman u β r w φ lmin lmax Q (fun p => W ((1 + r) * p.1 + w * p.2 + φ, p.2))
      (fun p => A ((1 + r) * p.1 + w * p.2 + φ, p.2) - φ) := by
  intro p ha hl
  set x := (1 + r) * p.1 + w * p.2 + φ with hx
  have hxlo : w * p.2 - r * φ ≤ x := by
    have := mul_le_mul_of_nonneg_left ha hr
    simp only [hx]; nlinarith
  obtain ⟨hA, hV, hmax⟩ := hW (x, p.2) hxlo hl
  have hint : ∀ s : ℝ, (fun l' => W ((1 + r) * (s - φ) + w * l' + φ, l')) =
      fun l' => W ((1 + r) * s + w * l' - r * φ, l') := fun s => by
    funext l'
    rw [show (1 + r) * (s - φ) + w * l' + φ = (1 + r) * s + w * l' - r * φ by ring]
  refine ⟨⟨by linarith [hA.1], by linarith [hA.2]⟩, ?_, fun a' ha' => ?_⟩
  · simp only
    rw [hint, hV]
    congr 2
    ring
  · have hs : a' + φ ∈ Set.Icc 0 x := ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
    have h := hmax (a' + φ) hs
    have h2 := hint (a' + φ)
    simp only [add_sub_cancel_right] at h2
    simp only
    rw [h2, show (1 + r) * p.1 + w * p.2 - a' = x - (a' + φ) by ring]
    exact h

/-- Miao, p. 562: the **transition function** of the joint process `(a_t, l_t)`,
`P(·, (a, l)) = δ_{g(a,l)} ⊗ Q(·, l)`. -/
noncomputable def ay_P (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  Kernel.deterministic g hg ×ₖ Kernel.comap Q Prod.snd measurable_snd

/-- Miao, p. 562: `P(A × B, (a, l)) = 1_{g(a,l) ∈ A} Q(B, l)`. -/
theorem ay_P_apply (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (p : ℝ × ℝ) {A B : Set ℝ} (hA : MeasurableSet A) :
    ay_P Q g hg p (A ×ˢ B) = A.indicator 1 (g p) * Q p.2 B := by
  rw [ay_P, Kernel.prod_apply_prod, Kernel.deterministic_apply' hg p hA, Kernel.comap_apply]
  rfl

/-- Miao, p. 562: `P` is a Markov kernel (a transition function). -/
theorem ay_P_markov (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    IsMarkovKernel (ay_P Q g hg) := by
  unfold ay_P; infer_instance

/-- Miao, p. 562: the sequence of distributions `λ_{t+1} = ∫ P(·, (a, l)) dλ_t`. -/
noncomputable def ay_lamSeq (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (lam0 : Measure (ℝ × ℝ)) (t : ℕ) : Measure (ℝ × ℝ) :=
  (fun m : Measure (ℝ × ℝ) => m.bind (ay_P Q g hg))^[t] lam0

/-- Miao, p. 562: `λ_{t+1}(A × B) = ∫ P(A × B, (a, l)) dλ_t(a, l)
= ∫ 1_{g(a,l) ∈ A} Q(B, l) dλ_t(a, l)`. -/
theorem ay_lamSeq_succ (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) (lam0 : Measure (ℝ × ℝ)) (t : ℕ) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ay_lamSeq Q g hg lam0 (t + 1) (A ×ˢ B) =
      ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂ay_lamSeq Q g hg lam0 t := by
  rw [ay_lamSeq, Function.iterate_succ_apply',
    Measure.bind_apply (hA.prod hB) (ay_P Q g hg).aemeasurable]
  exact lintegral_congr fun p => ay_P_apply Q hg p hA

/-- Miao, (17.7), p. 563: `λ*` is a **stationary distribution**:
`λ*(A × B) = ∫ 1_{g(a,l) ∈ A} Q(B, l) dλ*(a, l)` for all Borel `A`, `B`. -/
def ay_Stationary (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (lam : Measure (ℝ × ℝ)) : Prop :=
  ∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
    lam (A ×ˢ B) = ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂lam

/-- Miao, (17.7), p. 563: for a probability measure `λ*`, (17.7) on rectangles is equivalent to
invariance under the transition function, `λ* = ∫ P(·, (a, l)) dλ*` (rectangles generate the
Borel sets of `ℝ × ℝ` and form a π-system). -/
theorem eq_17_7 (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (lam : Measure (ℝ × ℝ)) [IsProbabilityMeasure lam] :
    ay_Stationary Q g lam ↔ lam.bind (ay_P Q g hg) = lam := by
  have hrect : ∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
      lam.bind (ay_P Q g hg) (A ×ˢ B) = ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂lam :=
    fun A B hA hB => by
      rw [Measure.bind_apply (hA.prod hB) (ay_P Q g hg).aemeasurable]
      exact lintegral_congr fun p => ay_P_apply Q hg p hA
  constructor
  · intro hst
    have hC : ∀ s ∈ Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s}
        {t : Set ℝ | MeasurableSet t}, lam s = lam.bind (ay_P Q g hg) s := by
      rintro s ⟨A, hA, B, hB, rfl⟩
      rw [hrect A B hA hB, hst A B hA hB]
    refine (ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod hC ?_).symm
    rw [← Set.univ_prod_univ, hrect _ _ MeasurableSet.univ MeasurableSet.univ,
      hst _ _ MeasurableSet.univ MeasurableSet.univ]
  · intro h A B hA hB
    rw [← hrect A B hA hB, h]

/-- Miao, p. 562: under (17.7) the asset marginal of `λ*` is the image of `λ*` under the policy
`g`: `λ*(A × ℝ) = λ*{(a, l) : g(a, l) ∈ A}`. -/
theorem ay_stationary_fst {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    lam.map Prod.fst = lam.map g := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.map_apply hg hA, ← Set.prod_univ,
    hst A Set.univ hA MeasurableSet.univ, ← lintegral_indicator_one (hg hA)]
  refine lintegral_congr fun p => ?_
  rw [measure_univ, mul_one]
  rfl

/-- Miao, p. 563: under (17.7) the labour marginal of `λ*` is invariant under `Q`. -/
theorem ay_stationary_snd {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    (lam.map Prod.snd).bind Q = lam.map Prod.snd := by
  ext B hB
  rw [Measure.bind_apply hB Q.aemeasurable, Measure.map_apply measurable_snd hB,
    lintegral_map (Q.measurable_coe hB) measurable_snd, ← Set.univ_prod,
    hst Set.univ B MeasurableSet.univ hB]
  refine lintegral_congr fun p => ?_
  simp

/-- Miao, p. 563: with iid shocks (`Q(·, l) = ν` for every `l`) the labour marginal of a
stationary `λ*` is `ν`, so aggregate labour `∫ l dλ*` is the mean of `l_t`. -/
theorem ay_stationary_snd_iid {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ × ℝ → ℝ}
    {lam : Measure (ℝ × ℝ)} [IsProbabilityMeasure lam]
    (hst : ay_Stationary (Kernel.const ℝ ν) g lam) :
    lam.map Prod.snd = ν ∧ ∫ p, p.2 ∂lam = ∫ l, l ∂ν := by
  have hm : lam.map Prod.snd = ν := by
    ext B hB
    rw [Measure.map_apply measurable_snd hB, ← Set.univ_prod,
      hst Set.univ B MeasurableSet.univ hB]
    simp
  refine ⟨hm, ?_⟩
  have h : ∫ x, x ∂(lam.map Prod.snd) = ∫ p, p.2 ∂lam :=
    integral_map measurable_snd.aemeasurable aestronglyMeasurable_id
  rw [← h, hm]

/-- Miao, p. 562: the long-run average assets `Ea(r, w) = ∫ g(a, l) dλ*(a, l)`. -/
noncomputable def ay_Ea (g : ℝ × ℝ → ℝ) (lam : Measure (ℝ × ℝ)) : ℝ := ∫ p, g p ∂lam

/-- Miao, p. 562: under (17.7), `Ea = ∫ g dλ*` is also the mean of current assets
`∫ a dλ*(a, l)`. -/
theorem ay_Ea_eq_mean {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    ∫ p, p.1 ∂lam = ay_Ea g lam := by
  have h1 : ∫ x, x ∂(lam.map Prod.fst) = ∫ p, p.1 ∂lam :=
    integral_map measurable_fst.aemeasurable aestronglyMeasurable_id
  have h2 : ∫ x, x ∂(lam.map g) = ∫ p, g p ∂lam :=
    integral_map hg.aemeasurable aestronglyMeasurable_id
  rw [ay_Ea, ← h1, ← h2, ay_stationary_fst hg hst]

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.1 with iid shocks: the cash-on-hand process, `Ea(r, w)` and `r < 1/β − 1`

Miao, §17.1.1, p. 561, and §17.1.3, p. 564. With iid labour shocks the agent's problem is the
income fluctuation problem of §8.3.2 (the copied `SIModel`, with gross return `R = 1 + r`,
borrowing limit `b = φ` and income `y = wl`), and the cash-on-hand process
`x_{t+1} = (1 + r)A(x_t) + wl_{t+1} − rφ` is a Markov process.

* `ay_bellmanCoh_of_SI`: "if `l_t` is iid we can remove `l_t` as a state variable": a solution
  of the §8.3.2 Bellman equation solves the two-state Bellman equation in cash on hand.
* `ay_IsStationaryCoh`: `λ*` is a stationary distribution of the cash-on-hand process on
  `[x_min, ∞)` (`∫ f dλ* = ∫∫ f((1 + r)A(x) + y − rφ) μ(dy) λ*(dx)` for bounded continuous `f`).
* `ay_stationary_exists`: if `β(1 + r) < 1` (with the hypotheses of Proposition 8.3.1), the
  invariant measure of Proposition 8.3.1 on `[x_min, x_max]` is such a distribution.
* `ay_EaIid`, `ay_EaIid_bounds`: the long-run average assets `Ea(r, w) = E_{λ*}[A(x)] − φ`
  (p. 561), with `−φ ≤ Ea ≤ x_max − φ`.
* `ay_beta_R_lt_one`, `ay_r_lt_rho`: if income is not almost surely constant, **every**
  stationary distribution of the cash-on-hand process has `β(1 + r) < 1`, i.e.
  `r < ρ = 1/β − 1`. This is the precise form of the book's "if `β(1 + r) ≥ 1`, `x_t` and `a_t`
  converge to infinity" (p. 561) used for "the equilibrium interest rate is less than `ρ`"
  (p. 564). Proof: integrating the Euler inequality `u′(c(x)) ≥ β(1 + r) E u′(c(x′))` against
  `λ*` gives `β(1 + r) ≤ 1`; if `β(1 + r) = 1`, `m = u′ ∘ c` is harmonic `λ*`-a.e., and then
  `∫∫ (m(x′) − m(x))² = ∫ m² − ∫ m² = 0`, so `m(x′) = m(x)`, hence `x′ = x` a.s., which forces
  income to be constant.

**Departures.** The book derives `r < ρ` from the claim that assets diverge when
`β(1 + r) ≥ 1` (whose almost-sure form is not formalised in the Chapter 8 project); the
integrated-Euler argument above is a different proof of the consequence used in §17.1.3.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Miao, p. 561: "if `l_t` is iid, then we can remove `l_t` as a state variable": a solution
`(V, â)` of the §8.3.2 problem with `R = 1 + r`, `b = φ`, income `y = wl` (`l ~ ν` iid,
`y_min = wl_min`) solves the Bellman equation in cash on hand with `Q(·, l) = ν`. -/
theorem ay_bellmanCoh_of_SI (M : SIModel) (S : M.Solution) {r w φ lmin lmax : ℝ}
    {ν : Measure ℝ} (hR : M.R = 1 + r) (hb : M.b = φ) (hw : 0 ≤ w) (hymin : M.ymin = w * lmin)
    (hlaw : M.law = ν.map (fun l => w * l)) :
    ay_BellmanCoh M.u M.β r w φ lmin lmax (Kernel.const ℝ ν) (fun p => S.V p.1)
      (fun p => S.sav p.1) := by
  have hr : M.r = r := by simp only [SIModel.r, hR]; ring
  have hI : ∀ s, 0 ≤ s → ∫ y, S.V (M.next s y) ∂M.law =
      ∫ l', S.V ((1 + r) * s + w * l' - r * φ) ∂ν := fun s hs => by
    have hm := (S.integrable_V hs).aestronglyMeasurable
    rw [hlaw] at hm ⊢
    rw [integral_map (measurable_const_mul w).aemeasurable hm]
    simp only [SIModel.next, hR, hr, hb]
  intro p hx hl
  have hxm : M.xmin ≤ p.1 := by
    have := mul_le_mul_of_nonneg_left hl.1 hw
    simp only [SIModel.xmin, hymin, hr, hb]
    linarith
  refine ⟨S.sav_mem p.1 hxm, ?_, fun s hs => ?_⟩
  · simp only [Kernel.const_apply]
    rw [← hI _ (S.sav_mem p.1 hxm).1]
    exact S.bellman p.1 hxm
  · simp only [Kernel.const_apply]
    rw [← hI _ hs.1]
    exact S.bellman_le p.1 hxm s hs

/-- Miao, p. 561: `λ*` is a **stationary distribution of the cash-on-hand process**
`x′ = (1 + r)A(x) + y′ − rφ` (iid income `y′ ~ μ`): it lives on `[x_min, ∞)` and
`∫ f dλ* = ∫ (∫ f((1 + r)A(x) + y − rφ) μ(dy)) λ*(dx)` for bounded continuous `f`. -/
def ay_IsStationaryCoh {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : Prop :=
  lam (Set.Ici M.xmin)ᶜ = 0 ∧ ∀ f : ℝ → ℝ, Continuous f → ∀ C : ℝ, (∀ x, |f x| ≤ C) →
    ∫ x, f x ∂lam = ∫ x, (∫ y, f (M.next (S.sav x) y) ∂M.law) ∂lam

/-- Miao, p. 561: "if `β(1 + r) < 1`, `{x_t}` has a unique invariant measure `λ*`": under the
hypotheses of Proposition 8.3.1 its invariant measure on `[x_min, x_max]`, viewed on `ℝ`, is a
stationary distribution of the cash-on-hand process. -/
theorem ay_stationary_exists {M : SIModel} (S : M.Solution) (hβR : M.β * M.R < 1)
    {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃ lam : Measure ℝ, IsProbabilityMeasure lam ∧ lam (Set.Icc M.xmin S.xmax)ᶜ = 0 ∧
      ay_IsStationaryCoh S lam := by
  obtain ⟨lam, hprob, hinv, -, -⟩ := S.proposition_8_3_1 hβR hddu hγ0 hγ hy hα hμ
  obtain ⟨hgt, ⟨⟨-, hfix⟩, -⟩, -⟩ := S.ex_8_9 hβR hddu hγ0 hγ hy
  have hxf : M.xmin ≤ S.xmax := hgt.le
  have := S.isMarkovKernel_kernel S.xmax
  have emb : MeasurableEmbedding (Subtype.val : Set.Icc M.xmin S.xmax → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hnull : lam.map Subtype.val (Set.Icc M.xmin S.xmax)ᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val : Set.Icc M.xmin S.xmax → ℝ) ⁻¹' (Set.Icc M.xmin S.xmax)ᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [this, measure_empty]
  refine ⟨lam.map Subtype.val,
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 hprob,
    hnull, measure_mono_null (Set.compl_subset_compl.2 Set.Icc_subset_Ici_self) hnull,
    fun f hf C hC => ?_⟩
  rw [emb.integral_map, emb.integral_map]
  have hfm : Measurable fun z : Set.Icc M.xmin S.xmax => f z :=
    (hf.comp continuous_subtype_val).measurable
  have h1 := SIWC.theorem_8_3_cor (S.kernel S.xmax) lam hfm (M := C) fun z => hC z
  rw [hinv] at h1
  rw [← h1]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [S.markovOpR_kernel S.xmax hfm s]
  refine integral_congr_ae ?_
  filter_upwards [M.supp] with y hy
  have hmem := S.mapsTo_Icc hxf hfix s.2 hy
  simp only [SIModel.Solution.kmap, min_eq_right hmem.2, max_eq_right hmem.1]

/-- Miao, p. 561: the long-run average assets with iid shocks, `Ea(r, w) = E_{λ*}[A(x)] − φ`
(next period's assets are `a′ = A(x) − φ`). -/
noncomputable def ay_EaIid {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : ℝ :=
  ∫ x, S.sav x ∂lam - M.b

/-- Miao, p. 561: for a stationary distribution on `[x_min, x_f]`, `Ea(r, w)` is finite with
`−φ ≤ Ea(r, w) ≤ x_f − φ`, and it is the mean of next period's assets `A(x) − φ`. -/
theorem ay_EaIid_bounds {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] {xf : ℝ} (hsupp : lam (Set.Icc M.xmin xf)ᶜ = 0) :
    -M.b ≤ ay_EaIid S lam ∧ ay_EaIid S lam ≤ xf - M.b ∧
      ay_EaIid S lam = ∫ x, (S.sav x - M.b) ∂lam := by
  have hae : ∀ᵐ x ∂lam, x ∈ Set.Icc M.xmin xf := ae_iff.2 hsupp
  have hcont : Continuous fun x => S.sav (max x M.xmin) :=
    S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
      fun x => Set.mem_Ici.2 (le_max_right _ _)
  have heq : (fun x => S.sav (max x M.xmin)) =ᵐ[lam] S.sav := by
    filter_upwards [hae] with x hx
    rw [max_eq_left hx.1]
  have hb : ∀ᵐ x ∂lam, 0 ≤ S.sav x ∧ S.sav x ≤ xf := by
    filter_upwards [hae] with x hx
    exact ⟨(S.sav_mem x hx.1).1, (S.sav_mem x hx.1).2.trans hx.2⟩
  have hint : Integrable S.sav lam := by
    refine Integrable.of_bound (hcont.aestronglyMeasurable.congr heq) xf ?_
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have h0 : 0 ≤ ∫ x, S.sav x ∂lam := integral_nonneg_of_ae (hb.mono fun x hx => hx.1)
  have h1 : ∫ x, S.sav x ∂lam ≤ xf := by
    have := integral_mono_ae hint (integrable_const xf) (hb.mono fun x hx => hx.2)
    simpa using this
  refine ⟨by unfold ay_EaIid; linarith, by unfold ay_EaIid; linarith, ?_⟩
  rw [integral_sub hint (integrable_const _)]
  simp [ay_EaIid]

/-- Miao, pp. 561 and 564: if income is not almost surely constant, every stationary
distribution `λ*` of the cash-on-hand process has `β(1 + r) < 1`. -/
theorem ay_beta_R_lt_one {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.β * M.R < 1 := by
  obtain ⟨hsupp, hstat⟩ := hst
  have hae : ∀ᵐ x ∂lam, x ∈ Set.Ici M.xmin := ae_iff.2 hsupp
  set m : ℝ → ℝ := fun x => M.du (S.cons (max x M.xmin)) with hmdef
  have hmc : Continuous m :=
    (M.du_cont.comp S.continuousOn_cons fun x hx => S.cons_pos hx).comp_continuous
      (continuous_id.max continuous_const) fun x => Set.mem_Ici.2 (le_max_right _ _)
  set m0 := M.du (S.cons M.xmin)
  have hmpos : ∀ x, 0 < m x := fun x => M.du_pos _ (S.cons_pos (le_max_right _ _))
  have hmle : ∀ x, m x ≤ m0 := fun x =>
    M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos le_rfl))
      (Set.mem_Ioi.2 (S.cons_pos (le_max_right x M.xmin)))
      (S.cons_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right x M.xmin))
        (le_max_right _ _))
  have hmabs : ∀ x, |m x| ≤ m0 := fun x => by rw [abs_of_pos (hmpos x)]; exact hmle x
  have hmeq : ∀ x, M.xmin ≤ x → m x = M.du (S.cons x) := fun x hx => by
    simp only [hmdef, max_eq_left hx]
  have hminj : ∀ x x', M.xmin ≤ x → M.xmin ≤ x' → m x = m x' → x = x' := by
    intro x x' hx hx' h
    rw [hmeq x hx, hmeq x' hx'] at h
    rcases lt_trichotomy x x' with hlt | heq | hgt
    · have hc := S.lemma_8_3_1.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hx') hlt
      have := M.du_anti (Set.mem_Ioi.2 (S.cons_pos hx)) (Set.mem_Ioi.2 (S.cons_pos hx')) hc
      linarith
    · exact heq
    · have hc := S.lemma_8_3_1.1 (Set.mem_Ici.2 hx') (Set.mem_Ici.2 hx) hgt
      have := M.du_anti (Set.mem_Ioi.2 (S.cons_pos hx')) (Set.mem_Ioi.2 (S.cons_pos hx)) hc
      linarith
  -- integrability of the conditional expectations of bounded continuous functions
  have hsc : Continuous fun x => S.sav (max x M.xmin) :=
    S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
      fun x => Set.mem_Ici.2 (le_max_right _ _)
  have key : ∀ f : ℝ → ℝ, Continuous f → ∀ C, (∀ x, |f x| ≤ C) →
      (∀ s, Integrable (fun y => f (M.next s y)) M.law) ∧
      Integrable (fun x => ∫ y, f (M.next (S.sav x) y) ∂M.law) lam := by
    intro f hf C hC
    have hi : ∀ s, Integrable (fun y => f (M.next s y)) M.law := fun s =>
      Integrable.of_bound (hf.comp (M.continuous_next_y s)).aestronglyMeasurable C
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law := by
      refine continuous_of_dominated (bound := fun _ => C)
        (fun x => (hi _).aestronglyMeasurable)
        (fun x => ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
        (integrable_const C) (ae_of_all _ fun y => ?_)
      exact hf.comp ((M.continuous_next y).comp hsc)
    have heq : (fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law) =ᵐ[lam]
        fun x => ∫ y, f (M.next (S.sav x) y) ∂M.law := by
      filter_upwards [hae] with x hx
      rw [max_eq_left (Set.mem_Ici.1 hx)]
    refine Integrable.of_bound (hcont.aestronglyMeasurable.congr heq) C (ae_of_all _ fun x => ?_)
    have := norm_integral_le_of_norm_le_const (μ := M.law) (C := C)
      (f := fun y => f (M.next (S.sav x) y))
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
    simpa using this
  obtain ⟨hmy, hGi⟩ := key m hmc m0 hmabs
  have hmi : Integrable m lam :=
    Integrable.of_bound hmc.aestronglyMeasurable m0
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hmabs x)
  set G := fun x => ∫ y, m (M.next (S.sav x) y) ∂M.law with hGdef
  have hst1 : ∫ x, m x ∂lam = ∫ x, G x ∂lam := hstat m hmc m0 hmabs
  -- the Euler inequality, λ*-a.e.
  have heul : ∀ᵐ x ∂lam, M.β * M.R * G x ≤ m x := by
    filter_upwards [hae] with x hx
    have hx' : M.xmin ≤ x := hx
    have h := (S.eq_8_7 hx').1
    have hG : G x = ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law := by
      refine integral_congr_ae ?_
      filter_upwards [M.ae_next (S.sav_mem x hx').1] with y hy
      exact hmeq _ hy.1
    rw [hG, hmeq x hx']
    exact h
  have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hIpos : 0 < ∫ x, m x ∂lam := si_integral_pos hmi (ae_of_all _ hmpos)
  have hle : M.β * M.R * ∫ x, m x ∂lam ≤ ∫ x, m x ∂lam := by
    calc M.β * M.R * ∫ x, m x ∂lam = ∫ x, M.β * M.R * G x ∂lam := by
          rw [hst1, integral_const_mul]
      _ ≤ ∫ x, m x ∂lam := integral_mono_ae (hGi.const_mul _) hmi heul
  have hle1 : M.β * M.R ≤ 1 := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hIpos
    linarith
  rcases hle1.lt_or_eq with hlt | heq1
  · exact hlt
  exfalso
  -- β(1 + r) = 1: m is harmonic λ*-a.e.
  have hGm : ∀ᵐ x ∂lam, G x = m x := by
    have hnn : 0 ≤ᵐ[lam] fun x => m x - G x :=
      heul.mono fun x hx => by rw [heq1, one_mul] at hx; simp only [Pi.zero_apply]; linarith
    have hz : ∫ x, (m x - G x) ∂lam = 0 := by rw [integral_sub hmi hGi, hst1, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hmi.sub hGi)).1 hz
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- the squares
  have hm2c : Continuous fun x => m x ^ 2 := hmc.pow 2
  have hm2abs : ∀ x, |m x ^ 2| ≤ m0 ^ 2 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hmpos x).le (hmle x) 2
  obtain ⟨hm2y, hHi⟩ := key (fun x => m x ^ 2) hm2c (m0 ^ 2) hm2abs
  have hm2i : Integrable (fun x => m x ^ 2) lam :=
    Integrable.of_bound hm2c.aestronglyMeasurable (m0 ^ 2)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm2abs x)
  set H := fun x => ∫ y, m (M.next (S.sav x) y) ^ 2 ∂M.law with hHdef
  have hst2 : ∫ x, m x ^ 2 ∂lam = ∫ x, H x ∂lam := hstat _ hm2c (m0 ^ 2) hm2abs
  set Var := fun x => ∫ y, (m (M.next (S.sav x) y) - m x) ^ 2 ∂M.law with hVdef
  have hsqid : ∀ x, (fun y => (m (M.next (S.sav x) y) - m x) ^ 2) = fun y =>
      (m (M.next (S.sav x) y) ^ 2 - 2 * m x * m (M.next (S.sav x) y)) + m x ^ 2 :=
    fun x => by funext y; ring
  have hVyi : ∀ x, Integrable (fun y => (m (M.next (S.sav x) y) - m x) ^ 2) M.law := by
    intro x
    have h1 : Integrable (fun y => m (M.next (S.sav x) y) ^ 2) M.law := hm2y _
    rw [hsqid x]
    exact (h1.sub ((hmy _).const_mul _)).add (integrable_const _)
  have hexp : ∀ x, Var x = H x - 2 * m x * G x + m x ^ 2 := by
    intro x
    have h1 : Integrable (fun y => m (M.next (S.sav x) y) ^ 2) M.law := hm2y _
    have h2 := (hmy (S.sav x)).const_mul (2 * m x)
    simp only [hVdef, hHdef, hGdef]
    rw [hsqid x, integral_add (f := fun y => m (M.next (S.sav x) y) ^ 2 -
        2 * m x * m (M.next (S.sav x) y)) (h1.sub h2) (integrable_const _),
      integral_sub h1 h2, integral_const_mul, integral_const]
    simp
  have hVae : Var =ᵐ[lam] fun x => H x - m x ^ 2 := by
    filter_upwards [hGm] with x hx
    rw [hexp x, hx]
    ring
  have hVi : Integrable Var lam := (hHi.sub hm2i).congr hVae.symm
  have hV0 : ∫ x, Var x ∂lam = 0 := by
    rw [integral_congr_ae hVae, integral_sub hHi hm2i, hst2, sub_self]
  have hVnn : 0 ≤ᵐ[lam] Var := ae_of_all _ fun x => integral_nonneg fun y => sq_nonneg _
  have hVz := (integral_eq_zero_iff_of_nonneg_ae hVnn hVi).1 hV0
  obtain ⟨x, hx, hVx⟩ := (hae.and hVz).exists
  have hx' : M.xmin ≤ x := hx
  simp only [Pi.zero_apply, hVdef] at hVx
  have hsq := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) (hVyi x)).1 hVx
  apply hnd (x - M.R * S.sav x + M.r * M.b)
  refine ae_iff.1 (?_ : ∀ᵐ y ∂M.law, y = x - M.R * S.sav x + M.r * M.b)
  filter_upwards [hsq, M.supp] with y hy hys
  simp only [Pi.zero_apply] at hy
  have h0 : m (M.next (S.sav x) y) = m x := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hy
    linarith
  have hnx := hminj _ _ (M.next_ge (S.sav_mem x hx').1 hys.1) hx' h0
  simp only [SIModel.next] at hnx
  linarith

/-- Miao, p. 564: in terms of the interest rate, every stationary distribution has
`r < ρ = 1/β − 1` (the complete-markets rate). -/
theorem ay_r_lt_rho {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.r < 1 / M.β - 1 := by
  have h := ay_beta_R_lt_one S hst hnd
  have hβ := M.β_pos
  have : M.R < 1 / M.β := by rw [lt_div_iff₀ hβ]; linarith
  simp only [SIModel.r]
  linarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.2: production, the firm's first-order conditions and capital demand

Miao, §17.1.2, p. 562, with the capital demand curve `K^d(r)` of §17.1.3 (p. 564) and Steps 1,
2 and 5 of the algorithm of §17.1.4 (pp. 564–566). A representative firm with constant returns
to scale technology `Y = F(K, L)` maximises `F(K, L) − (r + δ)K − wL`.

* `ay_CRS`, `ay_profit`: constant returns to scale (on the nonnegative orthant), profits.
* `ay_isLocalMax_of_max`, `eq_17_5_17_6`: at an interior profit maximum, `F_K = r + δ` (17.5) and
  `F_L = w` (17.6).
* `ay_euler_crs`, `ay_zero_profit`: Euler's theorem `F = F_K K + F_L L` for CRS technologies,
  hence zero profits at the optimum.
* Cobb–Douglas `F(K, L) = AK^αL^{1−α}` (`ay_cdF`, used in Example 17.1.1 and footnote 2):
  `ay_cd_crs`, the partial derivatives `ay_cd_hasDerivAt_K`, `ay_cd_hasDerivAt_L`; the capital
  demand `K^d(r) = F_K^{-1}(r + δ)` (Step 5) `ay_Kd`, with `ay_Kd_foc` (it solves (17.5)),
  `ay_Kd_unique`, `ay_Kd_strictAnti` (the demand curve slopes down), `ay_Kd_continuousOn`,
  `ay_Kd_tendsto` (`K^d → ∞` as `r ↓ −δ`, the lower bound of Step 1), `ay_FK_pos_rate`
  (`r = F_K − δ > −δ`); the wage `w(r) = F_L(K^d(r), L)` of Step 2 with `ay_wage_continuousOn`
  ("`w` is a continuous function of `r`", p. 564).
* `ay_saving_rate`, `ay_saving_rate_misprint`: footnote 2, p. 568: the saving rate is
  `δK/F(K, L) = δα/(r + δ)`; the printed `δK/(AF(K, L))` with `F = AK^αL^{1−α}` equals
  `δα/((r + δ)A)`, which differs unless `A = 1`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, p. 562: `F` has **constant returns to scale** on the nonnegative orthant:
`F(tK, tL) = tF(K, L)` for `t > 0`, `K, L ≥ 0`. -/
def ay_CRS (F : ℝ × ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ p : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ p.2 → F (t • p) = t * F p

/-- Miao, p. 562: the firm's profit `F(K, L) − (r + δ)K − wL` (the rental rate of capital is
`r + δ`). -/
def ay_profit (F : ℝ × ℝ → ℝ) (r δ w : ℝ) (p : ℝ × ℝ) : ℝ := F p - (r + δ) * p.1 - w * p.2

/-- Miao, p. 562: a profit maximum over `K, L ≥ 0` at an interior point `K, L > 0` is a local
maximum. -/
theorem ay_isLocalMax_of_max {F : ℝ × ℝ → ℝ} {r δ w : ℝ} {p : ℝ × ℝ} (hK : 0 < p.1)
    (hL : 0 < p.2)
    (hmax : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit F r δ w q ≤ ay_profit F r δ w p) :
    IsLocalMax (ay_profit F r δ w) p := by
  have hn : Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ∈ 𝓝 p :=
    prod_mem_nhds (Ioi_mem_nhds hK) (Ioi_mem_nhds hL)
  filter_upwards [hn] with q hq
  exact hmax q (Set.mem_Ioi.1 hq.1).le (Set.mem_Ioi.1 hq.2).le

/-- Miao, (17.5)–(17.6), p. 562: static profit maximisation implies `F_K(K, L) = r + δ` and
`F_L(K, L) = w` (with `F_K = F′(1, 0)`, `F_L = F′(0, 1)` for the derivative `F′` at `(K, L)`). -/
theorem eq_17_5_17_6 {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {r δ w : ℝ} {p : ℝ × ℝ}
    (hF : HasFDerivAt F F' p) (hmax : IsLocalMax (ay_profit F r δ w) p) :
    F' (1, 0) = r + δ ∧ F' (0, 1) = w := by
  have hd : HasFDerivAt (ay_profit F r δ w)
      (F' - (r + δ) • ContinuousLinearMap.fst ℝ ℝ ℝ - w • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hF.sub ((hasFDerivAt_fst).const_mul (r + δ))).sub ((hasFDerivAt_snd).const_mul w)
  have h0 := hmax.hasFDerivAt_eq_zero hd
  have h1 := congrArg (fun f : ℝ × ℝ →L[ℝ] ℝ => f (1, 0)) h0
  have h2 := congrArg (fun f : ℝ × ℝ →L[ℝ] ℝ => f (0, 1)) h0
  simp at h1 h2
  constructor <;> linarith

/-- Miao, p. 562 (Euler's theorem): for a CRS technology differentiable at `(K, L)`, `K, L > 0`,
`F(K, L) = F_K K + F_L L`. -/
theorem ay_euler_crs {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ} (hcrs : ay_CRS F)
    (hK : 0 < p.1) (hL : 0 < p.2) (hF : HasFDerivAt F F' p) :
    F p = F' (1, 0) * p.1 + F' (0, 1) * p.2 := by
  have hs : HasDerivAt (fun t : ℝ => t • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have hF1 : HasFDerivAt F F' ((fun t : ℝ => t • p) 1) := by simpa using hF
  have h1 := hF1.comp_hasDerivAt (1 : ℝ) hs
  have hmul : HasDerivAt (fun t : ℝ => t * F p) (F p) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F p)
  have hev : (fun t : ℝ => t * F p) =ᶠ[𝓝 1] F ∘ fun t : ℝ => t • p := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (hcrs t ht p hK.le hL.le).symm
  have h2 := hmul.congr_of_eventuallyEq hev.symm
  have hu := h1.unique h2
  have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [← hu, hp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  ring

/-- Miao, p. 562: with constant returns to scale, the first-order conditions (17.5)–(17.6)
imply zero profits, `F(K, L) = (r + δ)K + wL`. -/
theorem ay_zero_profit {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {r δ w : ℝ} {p : ℝ × ℝ}
    (hcrs : ay_CRS F) (hK : 0 < p.1) (hL : 0 < p.2) (hF : HasFDerivAt F F' p)
    (h5 : F' (1, 0) = r + δ) (h6 : F' (0, 1) = w) :
    ay_profit F r δ w p = 0 := by
  rw [ay_profit, ay_euler_crs hcrs hK hL hF, h5, h6]
  ring

/-- Miao, p. 568: the **Cobb–Douglas** technology `F(K, L) = AK^αL^{1−α}`. -/
noncomputable def ay_cdF (A α : ℝ) (p : ℝ × ℝ) : ℝ := A * p.1 ^ α * p.2 ^ (1 - α)

/-- The Cobb–Douglas marginal product of capital `F_K = αA(K/L)^{α−1}`. -/
noncomputable def ay_cdFK (A α K L : ℝ) : ℝ := α * A * (K / L) ^ (α - 1)

/-- The Cobb–Douglas marginal product of labour `F_L = (1 − α)A(K/L)^α`. -/
noncomputable def ay_cdFL (A α K L : ℝ) : ℝ := (1 - α) * A * (K / L) ^ α

/-- Miao, p. 568: the Cobb–Douglas technology has constant returns to scale. -/
theorem ay_cd_crs (A α : ℝ) : ay_CRS (ay_cdF A α) := by
  intro t ht p hK hL
  simp only [ay_cdF, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [Real.mul_rpow ht.le hK, Real.mul_rpow ht.le hL]
  have : t ^ α * t ^ (1 - α) = t := by
    rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_one]
  calc A * (t ^ α * p.1 ^ α) * (t ^ (1 - α) * p.2 ^ (1 - α))
      = (t ^ α * t ^ (1 - α)) * (A * p.1 ^ α * p.2 ^ (1 - α)) := by ring
    _ = t * (A * p.1 ^ α * p.2 ^ (1 - α)) := by rw [this]

/-- `K^{α−1}L^{1−α} = (K/L)^{α−1}` for `K, L > 0`. -/
theorem ay_rpow_ratio {K L : ℝ} (hK : 0 < K) (hL : 0 < L) (α : ℝ) :
    K ^ (α - 1) * L ^ (1 - α) = (K / L) ^ (α - 1) := by
  rw [Real.div_rpow hK.le hL.le, show 1 - α = -(α - 1) by ring, Real.rpow_neg hL.le, div_eq_mul_inv]

/-- Miao, (17.5): the Cobb–Douglas partial derivative in `K` is `F_K = αA(K/L)^{α−1}`. -/
theorem ay_cd_hasDerivAt_K (A α : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    HasDerivAt (fun k => ay_cdF A α (k, L)) (ay_cdFK A α K L) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul A).mul_const
    (L ^ (1 - α))
  simp only [ay_cdF]
  convert h using 1
  rw [ay_cdFK, ← ay_rpow_ratio hK hL]
  ring

/-- Miao, (17.6): the Cobb–Douglas partial derivative in `L` is `F_L = (1 − α)A(K/L)^α`. -/
theorem ay_cd_hasDerivAt_L (A α : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    HasDerivAt (fun l => ay_cdF A α (K, l)) (ay_cdFL A α K L) L := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul (A * K ^ α)
  simp only [ay_cdF]
  convert h using 1
  rw [ay_cdFL, Real.div_rpow hK.le hL.le, show 1 - α - 1 = -α by ring, Real.rpow_neg hL.le,
    div_eq_mul_inv]
  ring

/-- Miao, p. 564 and Step 5, p. 566: the **capital demand** `K^d(r) = F_K^{-1}(r + δ)`, for the
Cobb–Douglas technology `K^d(r) = L(αA/(r + δ))^{1/(1−α)}`. -/
noncomputable def ay_Kd (A α δ L r : ℝ) : ℝ := L * (α * A / (r + δ)) ^ (1 / (1 - α))

/-- Miao, (17.5), Step 5: `K^d(r)` solves `F_K(K, L) = r + δ` (`r > −δ`). -/
theorem ay_Kd_foc {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) : ay_cdFK A α (ay_Kd A α δ L r) L = r + δ := by
  have hrd : 0 < r + δ := by linarith
  have hx : 0 < α * A / (r + δ) := div_pos (mul_pos hα0 hA) hrd
  rw [ay_cdFK, ay_Kd, mul_div_cancel_left₀ _ hL.ne', ← Real.rpow_mul hx.le,
    show 1 / (1 - α) * (α - 1) = -1 by field_simp [(sub_pos.2 hα1).ne']; ring,
    Real.rpow_neg_one, inv_div]
  field_simp

/-- Miao, (17.5): `F_K(·, L)` is strictly decreasing in `K` (`0 < α < 1`). -/
theorem ay_cdFK_strictAnti {A α L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    StrictAntiOn (fun K => ay_cdFK A α K L) (Set.Ioi 0) := by
  intro K hK K' _ hKK
  simp only [ay_cdFK]
  have := Real.rpow_lt_rpow_of_neg (div_pos (Set.mem_Ioi.1 hK) hL)
    (div_lt_div_of_pos_right hKK hL) (by linarith : α - 1 < 0)
  exact mul_lt_mul_of_pos_left this (mul_pos hα0 hA)

/-- Miao, Step 5, p. 566: `K^d(r)` is the unique `K > 0` with `F_K(K, L) = r + δ`. -/
theorem ay_Kd_unique {A α δ L r K : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) (hK : 0 < K) (hfoc : ay_cdFK A α K L = r + δ) : K = ay_Kd A α δ L r := by
  have hx : 0 < α * A / (r + δ) := div_pos (mul_pos hα0 hA) (by linarith)
  have hKd : 0 < ay_Kd A α δ L r := mul_pos hL (Real.rpow_pos_of_pos hx _)
  refine (ay_cdFK_strictAnti hA hα0 hα1 hL).injOn hK hKd ?_
  rw [hfoc, ay_Kd_foc hA hα0 hα1 hL hr]

/-- Miao, p. 564: the capital demand curve `K^d(r)` is downward sloping on `(−δ, ∞)`. -/
theorem ay_Kd_strictAnti {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    StrictAntiOn (ay_Kd A α δ L) (Set.Ioi (-δ)) := by
  intro r hr r' hr' hrr
  have h1 : 0 < r + δ := by linarith [Set.mem_Ioi.1 hr]
  have hxy : α * A / (r' + δ) < α * A / (r + δ) :=
    div_lt_div_of_pos_left (mul_pos hα0 hA) h1 (by linarith)
  have := Real.rpow_lt_rpow (div_pos (mul_pos hα0 hA) (by linarith)).le hxy
    (one_div_pos.2 (sub_pos.2 hα1))
  exact mul_lt_mul_of_pos_left this hL

/-- Miao, p. 564: `K^d` is continuous on `(−δ, ∞)`. -/
theorem ay_Kd_continuousOn {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) :
    ContinuousOn (ay_Kd A α δ L) (Set.Ioi (-δ)) := by
  have hpos : ∀ r ∈ Set.Ioi (-δ), 0 < α * A / (r + δ) := fun r hr =>
    div_pos (mul_pos hα0 hA) (by linarith [Set.mem_Ioi.1 hr])
  have hc : ContinuousOn (fun r => α * A / (r + δ)) (Set.Ioi (-δ)) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      fun r hr => by linarith [Set.mem_Ioi.1 hr]
  exact continuousOn_const.mul (hc.rpow_const fun r hr => Or.inl (hpos r hr).ne')

/-- Miao, Step 1, p. 564: `K^d(r) → ∞` as `r ↓ −δ`. -/
theorem ay_Kd_tendsto {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    Tendsto (ay_Kd A α δ L) (𝓝[>] (-δ)) atTop := by
  have h1 : Tendsto (fun r : ℝ => r + δ) (𝓝[>] (-δ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun r : ℝ => r + δ) (𝓝 (-δ)) (𝓝 (-δ + δ)) :=
        (continuous_id.add continuous_const).tendsto _
      rw [neg_add_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact Set.mem_Ioi.2 (by linarith [Set.mem_Ioi.1 hr])
  have h2 : Tendsto (fun r : ℝ => α * A / (r + δ)) (𝓝[>] (-δ)) atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (mul_pos hα0 hA)
    simpa [div_eq_mul_inv] using this
  have h3 := (tendsto_rpow_atTop (one_div_pos.2 (sub_pos.2 hα1))).comp h2
  exact h3.const_mul_atTop hL

/-- Miao, Step 1, p. 564: since `F_K > 0`, (17.5) forces `r = F_K − δ > −δ`. -/
theorem ay_FK_pos_rate {A α K L r δ : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hK : 0 < K) (hL : 0 < L)
    (h5 : ay_cdFK A α K L = r + δ) : -δ < r := by
  have : 0 < ay_cdFK A α K L := mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos (div_pos hK hL) _)
  linarith

/-- Miao, Step 2, p. 566: the wage implied by (17.5)–(17.6), `w(r) = F_L(K^d(r), L)`. -/
noncomputable def ay_wage (A α δ L r : ℝ) : ℝ := ay_cdFL A α (ay_Kd A α δ L r) L

/-- Miao, p. 564: "given (17.5) and (17.6), `w` is a continuous function of `r`". -/
theorem ay_wage_continuousOn {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) :
    ContinuousOn (ay_wage A α δ L) (Set.Ioi (-δ)) := by
  have hc : ContinuousOn (fun r => ay_Kd A α δ L r / L) (Set.Ioi (-δ)) :=
    (ay_Kd_continuousOn hA hα0).div_const L
  exact continuousOn_const.mul (hc.rpow_const fun _ _ => Or.inr hα0.le)

/-- Miao, footnote 2, p. 568, corrected: at the capital demand `K = K^d(r)` the aggregate
saving rate is `δK/F(K, L) = δα/(r + δ)`. -/
theorem ay_saving_rate {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) :
    δ * ay_Kd A α δ L r / ay_cdF A α (ay_Kd A α δ L r, L) = δ * α / (r + δ) := by
  set K := ay_Kd A α δ L r
  have hrd : 0 < r + δ := by linarith
  have hK : 0 < K := mul_pos hL (Real.rpow_pos_of_pos (div_pos (mul_pos hα0 hA) hrd) _)
  have hfoc := ay_Kd_foc hA hα0 hα1 hL hr
  have hF : ay_cdF A α (K, L) * α = (r + δ) * K := by
    rw [← hfoc, ay_cdFK, ← ay_rpow_ratio hK hL, ay_cdF]
    simp only
    rw [Real.rpow_sub_one hK.ne']
    field_simp
  have hFpos : 0 < ay_cdF A α (K, L) := by
    simp only [ay_cdF]
    exact mul_pos (mul_pos hA (Real.rpow_pos_of_pos hK _)) (Real.rpow_pos_of_pos hL _)
  rw [div_eq_div_iff hFpos.ne' hrd.ne']
  linear_combination -δ * hF

/-- Miao, footnote 2, p. 568: the printed `δK/(AF(K, L))` with `F = AK^αL^{1−α}` equals
`δα/((r + δ)A)`, which is not `δα/(r + δ)` unless `A = 1` (for `δ > 0`). -/
theorem ay_saving_rate_misprint {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hr : -δ < r) (hδ : 0 < δ) (hA1 : A ≠ 1) :
    δ * ay_Kd A α δ L r / (A * ay_cdF A α (ay_Kd A α δ L r, L)) ≠ δ * α / (r + δ) := by
  have h := ay_saving_rate hA hα0 hα1 hL hr
  rw [mul_comm A, ← div_div, h]
  intro heq
  have hpos : 0 < δ * α / (r + δ) := div_pos (mul_pos hδ hα0) (by linarith)
  rw [div_eq_iff hA.ne'] at heq
  exact hA1 (mul_left_cancel₀ hpos.ne' (heq.symm.trans (mul_one _).symm))

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.3: stationary recursive competitive equilibrium (Definition 17.1.1)

Miao, §17.1.3, pp. 562–563.

* `AYEconomy`: the primitives `(β, δ, b, l_min, l_max, u, F, Q)`.
* `AYStationaryEqm`: **Definition 17.1.1**, a value function `V`, policies `g` and `c`, the
  firm's choices `K`, `L`, prices `r`, `w` and a stationary measure `λ*` such that (i) `V`, `g`
  solve the household's Bellman equation (17.4) (with `c = (1 + r)a + wl − g` on the state space
  `a ≥ −φ`, `l ∈ [l_min, l_max]`, which carries `λ*`), (ii) `(K, L)` maximises profits, (iii)
  `L = ∫ l dλ*`, (iv) `K = ∫ g dλ*`, (v) `∫ c dλ* + δK = F(K, L)`, (vi) (17.7).
* `definition_17_1_1`: the conditions in the book's form: (17.5)–(17.6) (when `F` is
  differentiable at `(K, L)`), `c ≥ 0` on the state space, (iii)–(v), and (17.7) as invariance
  `λ* = λ*P`.
* `ay_resource_redundant`: "the resource constraint is redundant given the other equilibrium
  conditions" (p. 563), for CRS technologies (Euler's theorem gives zero profits).
* `ay_labor_iid`: "aggregate labor is ... determined by the mean of `l_t`" (p. 563) for iid
  shocks.
* `ay_exampleEconomy`, `ay_exampleEqm`, `ay_example_exists`: a concrete stationary equilibrium
  (so the definition is not vacuous): linear utility, `F(K, L) = √(KL)`, `β = 1/2`, `δ = 1/8`,
  `l ≡ 1`, `b = −4` (a saving requirement `a ≥ 4`), `r = 1/8`, `w = 1`, `K = 4`, `L = 1`,
  `V(a, l) = 9a/8 − 3/2`, `g ≡ 4`, `λ* = δ_{(4, 1)}`.

**Departures.** (1) Condition (i) is read as: `V`, `g` solve the Bellman equation (17.4) with
the maximum attained at `g` (the book's dynamic programming formulation of the household's
problem). (2) Condition (ii) is profit maximisation over `K, L ≥ 0`; the first-order conditions
(17.5)–(17.6) follow at the interior optimum when `F` is differentiable (`definition_17_1_1`).
(3) The redundancy of (v) needs the integrability of `a`, `l`, `g` under `λ*` and constant
returns to scale (the book's standing assumption on `F`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The primitives of the Aiyagari economy of Miao §17.1 (pp. 560–563). -/
structure AYEconomy where
  β : ℝ
  δ : ℝ
  b : ℝ
  lmin : ℝ
  lmax : ℝ
  u : ℝ → ℝ
  F : ℝ × ℝ → ℝ
  Q : Kernel ℝ ℝ
  Q_markov : IsMarkovKernel Q

/-- **Definition 17.1.1** (Miao, p. 563): a **stationary recursive competitive equilibrium**. -/
structure AYStationaryEqm (E : AYEconomy) where
  V : ℝ × ℝ → ℝ
  g : ℝ × ℝ → ℝ
  c : ℝ × ℝ → ℝ
  K : ℝ
  L : ℝ
  r : ℝ
  w : ℝ
  lam : Measure (ℝ × ℝ)
  lam_prob : IsProbabilityMeasure lam
  g_meas : Measurable g
  supp : ∀ᵐ p ∂lam, -ay_phi E.b w E.lmin r ≤ p.1 ∧ p.2 ∈ Set.Icc E.lmin E.lmax
  household : ay_Bellman E.u E.β r w (ay_phi E.b w E.lmin r) E.lmin E.lmax E.Q V g
  cons_eq : ∀ p, c p = (1 + r) * p.1 + w * p.2 - g p
  K_pos : 0 < K
  L_pos : 0 < L
  firm : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit E.F r E.δ w q ≤ ay_profit E.F r E.δ w (K, L)
  labor : L = ∫ p, p.2 ∂lam
  asset : K = ∫ p, g p ∂lam
  resource : ∫ p, c p ∂lam + E.δ * K = E.F (K, L)
  stationary : ay_Stationary E.Q g lam

/-- **Definition 17.1.1** (Miao, p. 563), in the book's form: in a stationary recursive
competitive equilibrium (with `F` differentiable at `(K, L)`), (17.5) `F_K = r + δ` and (17.6)
`F_L = w` hold; `c ≥ 0` on the state space; the labour market, asset market and resource
constraints hold; and `λ*` is invariant under the transition function (17.7). -/
theorem definition_17_1_1 {E : AYEconomy} (e : AYStationaryEqm E) {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hF : HasFDerivAt E.F F' (e.K, e.L)) :
    (F' (1, 0) = e.r + E.δ ∧ F' (0, 1) = e.w) ∧
      (∀ p : ℝ × ℝ, -ay_phi E.b e.w E.lmin e.r ≤ p.1 → p.2 ∈ Set.Icc E.lmin E.lmax →
        0 ≤ e.c p) ∧
      e.L = ∫ p, p.2 ∂e.lam ∧ e.K = ∫ p, e.g p ∂e.lam ∧
      ∫ p, e.c p ∂e.lam + E.δ * e.K = E.F (e.K, e.L) ∧
      e.lam.bind (ay_P E.Q e.g e.g_meas) = e.lam := by
  have := E.Q_markov
  have := e.lam_prob
  refine ⟨eq_17_5_17_6 hF (ay_isLocalMax_of_max e.K_pos e.L_pos e.firm), fun p ha hl => ?_,
    e.labor, e.asset, e.resource, (eq_17_7 E.Q e.g_meas e.lam).1 e.stationary⟩
  have := ((e.household p ha hl).1).2
  rw [e.cons_eq]
  linarith

/-- Miao, p. 563: "the resource constraint is redundant given the other equilibrium
conditions": with constant returns to scale and the first-order conditions (17.5)–(17.6), the
budget `c = (1 + r)a + wl − g`, labour and asset market clearing and stationarity (17.7) imply
`∫ c dλ* + δK = F(K, L)`. -/
theorem ay_resource_redundant {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {Q : Kernel ℝ ℝ}
    [IsMarkovKernel Q] {r δ w K L : ℝ} {g c : ℝ × ℝ → ℝ} {lam : Measure (ℝ × ℝ)}
    (hcrs : ay_CRS F) (hK : 0 < K) (hL : 0 < L) (hF : HasFDerivAt F F' (K, L))
    (h5 : F' (1, 0) = r + δ) (h6 : F' (0, 1) = w) (hg : Measurable g)
    (hst : ay_Stationary Q g lam) (hlab : L = ∫ p, p.2 ∂lam) (hass : K = ∫ p, g p ∂lam)
    (hc : ∀ p, c p = (1 + r) * p.1 + w * p.2 - g p)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1) lam) (h2 : Integrable (fun p : ℝ × ℝ => p.2) lam)
    (h3 : Integrable g lam) :
    ∫ p, c p ∂lam + δ * K = F (K, L) := by
  have hmean : ∫ p, p.1 ∂lam = K := by rw [ay_Ea_eq_mean hg hst, ay_Ea, hass]
  have hcint : ∫ p, c p ∂lam = (1 + r) * K + w * L - K := by
    have hA : Integrable (fun p : ℝ × ℝ => (1 + r) * p.1 + w * p.2) lam :=
      (h1.const_mul _).add (h2.const_mul _)
    calc ∫ p, c p ∂lam = ∫ p, ((1 + r) * p.1 + w * p.2) ∂lam - ∫ p, g p ∂lam := by
          simp only [hc]; exact integral_sub hA h3
      _ = (1 + r) * K + w * L - K := by
          rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
            integral_const_mul, hmean, ← hlab, ← hass]
  have hzero := ay_zero_profit hcrs hK hL hF h5 h6
  simp only [ay_profit] at hzero
  rw [hcint]
  linarith

/-- Miao, p. 563: with iid shocks `Q(·, l) = ν`, aggregate labour in a stationary equilibrium is
the mean of `l_t`: `L = ∫ l dν`. -/
theorem ay_labor_iid {E : AYEconomy} (e : AYStationaryEqm E) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hQ : E.Q = Kernel.const ℝ ν) : e.L = ∫ l, l ∂ν := by
  have := e.lam_prob
  have hst := e.stationary
  rw [hQ] at hst
  rw [e.labor]
  exact (ay_stationary_snd_iid hst).2

/-- The concrete economy of `ay_exampleEqm`: `u(c) = c`, `F(K, L) = √(KL)`, `β = 1/2`,
`δ = 1/8`, `b = −4`, `l ≡ 1`. -/
noncomputable def ay_exampleEconomy : AYEconomy where
  β := 1 / 2
  δ := 1 / 8
  b := -4
  lmin := 1
  lmax := 1
  u := fun c => c
  F := fun p => Real.sqrt (p.1 * p.2)
  Q := Kernel.const ℝ (Measure.dirac 1)
  Q_markov := inferInstance

theorem ay_example_phi : ay_phi (-4) 1 1 (1 / 8) = -4 := by
  rw [ay_phi]
  norm_num

/-- A concrete **stationary recursive competitive equilibrium** (Definition 17.1.1):
`r = 1/8`, `w = 1`, `K = 4`, `L = 1`, `V(a, l) = 9a/8 − 3/2`, `g ≡ 4`,
`c(a, l) = 9a/8 + l − 4`, `λ* = δ_{(4, 1)}`. -/
noncomputable def ay_exampleEqm : AYStationaryEqm ay_exampleEconomy where
  V := fun p => 9 / 8 * p.1 - 3 / 2
  g := fun _ => 4
  c := fun p => (1 + 1 / 8) * p.1 + 1 * p.2 - 4
  K := 4
  L := 1
  r := 1 / 8
  w := 1
  lam := Measure.dirac (4, 1)
  lam_prob := inferInstance
  g_meas := measurable_const
  supp := by
    rw [ae_dirac_eq]
    simp only [ay_exampleEconomy, ay_example_phi, Filter.eventually_pure]
    norm_num
  household := by
    intro p ha hl
    simp only [ay_exampleEconomy, ay_example_phi] at ha hl ⊢
    have hl1 : p.2 = 1 := le_antisymm hl.2 hl.1
    simp only [Kernel.const_apply, integral_const, probReal_univ, one_smul]
    refine ⟨⟨by norm_num, by rw [hl1]; linarith⟩, by rw [hl1]; ring, fun a' ha' => ?_⟩
    have := ha'.1
    rw [hl1]
    linarith
  cons_eq := fun _ => rfl
  K_pos := by norm_num
  L_pos := by norm_num
  firm := by
    intro q hq1 hq2
    simp only [ay_profit, ay_exampleEconomy]
    have h4 : Real.sqrt (4 * 1) = 2 := by
      rw [show (4 : ℝ) * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hq : Real.sqrt (q.1 * q.2) ≤ q.1 / 4 + q.2 :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (q.1 / 4 - q.2)]⟩
    rw [h4]
    linarith
  labor := by rw [integral_dirac]
  asset := by rw [integral_dirac]
  resource := by
    simp only [ay_exampleEconomy]
    rw [integral_dirac, show (4 : ℝ) * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  stationary := by
    intro A B hA hB
    simp only [ay_exampleEconomy, Kernel.const_apply]
    rw [lintegral_dirac, Measure.dirac_apply' _ (hA.prod hB), Set.indicator_prod_one,
      Measure.dirac_apply' _ hB]

/-- Definition 17.1.1 is not vacuous: the example economy has a stationary recursive competitive
equilibrium, with interest rate `r = 1/8 < ρ = 1/β − 1 = 1`. -/
theorem ay_example_exists :
    Nonempty (AYStationaryEqm ay_exampleEconomy) ∧
      ay_exampleEqm.r < 1 / ay_exampleEconomy.β - 1 := by
  refine ⟨⟨ay_exampleEqm⟩, ?_⟩
  simp only [ay_exampleEqm, ay_exampleEconomy]
  norm_num

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.3: existence of a stationary equilibrium by the crossing argument (Figure 17.1)

Miao, §17.1.3, pp. 563–564, and §17.1.4, p. 568. The aggregate capital supply `Ea(r)` (the
long-run average assets) is continuous, tends to infinity as `r ↑ ρ = 1/β − 1` and lies below
the capital demand `K^d(r)` for `r` near `−δ`; by the Intermediate Value Theorem the curves
cross.

* `ay_rho`, `ay_complete_markets_rate`: under complete markets (constant consumption satisfying
  the Euler equation `u′(c) = β(1 + r)u′(c)`) the interest rate is `ρ = 1/β − 1`.
* `ay_existence`: the abstract crossing argument: `Ea` continuous on `[r₀, ρ)`, `Ea → ∞` as
  `r ↑ ρ`, `K^d` continuous on `[r₀, ρ]`, `Ea(r₀) < K^d(r₀)` ⇒ `Ea(r*) = K^d(r*)` for some
  `r* ∈ (r₀, ρ)`; in particular `r* < ρ`.
* `ay_existence_cd`: with the Cobb–Douglas capital demand `K^d(r) = F_K^{-1}(r + δ)`, `Ea`
  continuous on `(−δ, ρ)`, bounded above near `−δ` (the book's "when `r < 0`, `Ea(r)`
  approaches `−b`") and tending to infinity at `ρ`: there is an equilibrium `r* ∈ (−δ, ρ)`.
* `ay_overaccumulation`: at any crossing `r* < ρ`, capital exceeds the complete-markets level
  `K^d(ρ)` (where `F_K = ρ + δ`), and the saving rate `δα/(r* + δ)` exceeds the complete-markets
  saving rate `δα/(ρ + δ)` (§17.1.4: precautionary saving).
* `ay_existence_example`: the hypotheses of `ay_existence_cd` hold for a concrete supply curve
  (`Ea(r) = 1/(1 − r)`, `β = 1/2`, `δ = 1/8`, `A = L = 1`, `α = 1/2`), so the theorem is not
  vacuous.

**Departures.** The continuity of `Ea` in `r` (via continuity of the policy and of the
stationary distribution in `r`), its divergence as `r ↑ ρ`, and its behaviour as `r ↓ −δ` are
asserted, not proved, in the book ("we can show"); they are hypotheses of `ay_existence` and
`ay_existence_cd` (the Chapter 8 project likewise leaves the continuity of the stationary
distribution in `R` unformalised). The book's possible multiplicity of crossings and "this case
seldom happens" carry no precise claim and are not formalised. That `r < ρ` holds at every
stationary distribution (not only at the crossing constructed here) is `ay_r_lt_rho`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, p. 564: `ρ = 1/β − 1`, the equilibrium interest rate under complete markets. -/
noncomputable def ay_rho (β : ℝ) : ℝ := 1 / β - 1

/-- Miao, p. 564: under complete markets consumption is constant at `c` and the Euler equation
`u′(c) = β(1 + r)u′(c)` with `u′(c) > 0` forces `r = ρ = 1/β − 1`. -/
theorem ay_complete_markets_rate {β r duc : ℝ} (hβ : 0 < β) (hdu : 0 < duc)
    (heul : duc = β * (1 + r) * duc) : r = ay_rho β := by
  have h1 : β * (1 + r) = 1 := by
    have := mul_right_cancel₀ hdu.ne' (heul.symm.trans (one_mul duc).symm)
    exact this
  rw [ay_rho]
  field_simp
  linarith

/-- Miao, pp. 563–564 (Figure 17.1): the **crossing argument**. If the capital supply `Ea` is
continuous on `[r₀, ρ)` with `Ea(r) → ∞` as `r ↑ ρ`, the capital demand `K^d` is continuous on
`[r₀, ρ]`, and `Ea(r₀) < K^d(r₀)`, then `Ea(r*) = K^d(r*)` for some `r* ∈ (r₀, ρ)`. -/
theorem ay_existence {Ea Kd : ℝ → ℝ} {r0 ρ : ℝ} (hr0 : r0 < ρ)
    (hEa : ContinuousOn Ea (Set.Ico r0 ρ)) (hKd : ContinuousOn Kd (Set.Icc r0 ρ))
    (hlim : Tendsto Ea (𝓝[<] ρ) atTop) (hlow : Ea r0 < Kd r0) :
    ∃ r ∈ Set.Ioo r0 ρ, Ea r = Kd r := by
  obtain ⟨rm, -, hrm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hr0.le) hKd
  obtain ⟨r1, hr1E, hr1⟩ :=
    ((hlim.eventually (eventually_gt_atTop (Kd rm))).and (Ioo_mem_nhdsLT hr0)).exists
  have hsub : Set.Icc r0 r1 ⊆ Set.Ico r0 ρ := fun r hr => ⟨hr.1, hr.2.trans_lt hr1.2⟩
  have hcont : ContinuousOn (fun r => Kd r - Ea r) (Set.Icc r0 r1) :=
    (hKd.mono fun r hr => ⟨hr.1, (hr.2.trans_lt hr1.2).le⟩).sub (hEa.mono hsub)
  have hK1 : Kd r1 ≤ Kd rm := hrm ⟨hr1.1.le, hr1.2.le⟩
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Icc' hr1.1.le hcont
    (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Set.Icc _ _)
  simp only at hzero
  have hne : r ≠ r0 := by rintro rfl; linarith
  exact ⟨r, ⟨lt_of_le_of_ne hr.1 hne.symm, hr.2.trans_lt hr1.2⟩, by linarith⟩

/-- Miao, pp. 563–564: existence of a stationary equilibrium interest rate with the
Cobb–Douglas capital demand: if `Ea` is continuous on `(−δ, ρ)`, bounded above on some
`(−δ, r′]`, and `Ea(r) → ∞` as `r ↑ ρ`, then `Ea(r*) = K^d(r*)` for some `r* ∈ (−δ, ρ)`. -/
theorem ay_existence_cd {A α δ L β : ℝ} {Ea : ℝ → ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hEa : ContinuousOn Ea (Set.Ioo (-δ) (ay_rho β)))
    (hlim : Tendsto Ea (𝓝[<] ay_rho β) atTop)
    (hbdd : ∃ r' ∈ Set.Ioo (-δ) (ay_rho β), ∃ B, ∀ r ∈ Set.Ioc (-δ) r', Ea r ≤ B) :
    ∃ r ∈ Set.Ioo (-δ) (ay_rho β), Ea r = ay_Kd A α δ L r := by
  obtain ⟨r', hr', B, hB⟩ := hbdd
  obtain ⟨r0, hr0K, hr0⟩ :=
    (((ay_Kd_tendsto hA hα0 hα1 hL).eventually (eventually_gt_atTop B)).and
      (Ioc_mem_nhdsGT hr'.1)).exists
  have hρ : -δ < ay_rho β := hr'.1.trans hr'.2
  have hr0ρ : r0 < ay_rho β := hr0.2.trans_lt hr'.2
  obtain ⟨r, hr, heq⟩ := ay_existence (Ea := Ea) (Kd := ay_Kd A α δ L) hr0ρ
    (hEa.mono fun r hr => ⟨hr0.1.trans_le hr.1, hr.2⟩)
    ((ay_Kd_continuousOn hA hα0).mono fun r hr => Set.mem_Ioi.2 (hr0.1.trans_le hr.1))
    hlim ((hB r0 hr0).trans_lt hr0K)
  exact ⟨r, ⟨hr0.1.trans hr.1, hr.2⟩, heq⟩

/-- Miao, p. 564 and §17.1.4, p. 568: at an incomplete-markets equilibrium rate `r* < ρ`, the
capital stock exceeds the complete-markets capital stock `K^d(ρ)` (which solves
`F_K = ρ + δ`), and the aggregate saving rate `δα/(r* + δ)` exceeds the complete-markets rate
`δα/(ρ + δ)`: households hold extra assets for precautionary motives. -/
theorem ay_overaccumulation {A α δ L ρ r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hδ : 0 < δ) (hr : -δ < r) (hrρ : r < ρ) :
    ay_Kd A α δ L ρ < ay_Kd A α δ L r ∧ ay_cdFK A α (ay_Kd A α δ L ρ) L = ρ + δ ∧
      δ * α / (ρ + δ) < δ * α / (r + δ) := by
  refine ⟨ay_Kd_strictAnti hA hα0 hα1 hL (Set.mem_Ioi.2 hr)
      (Set.mem_Ioi.2 (hr.trans hrρ)) hrρ, ay_Kd_foc hA hα0 hα1 hL (hr.trans hrρ), ?_⟩
  exact div_lt_div_of_pos_left (mul_pos hδ hα0) (by linarith) (by linarith)

/-- The crossing argument is not vacuous: with `β = 1/2` (`ρ = 1`), `δ = 1/8`, `A = L = 1`,
`α = 1/2`, the supply curve `Ea(r) = 1/(1 − r)` satisfies the hypotheses of `ay_existence_cd`,
so it crosses the capital demand curve at some `r* ∈ (−1/8, 1)`. -/
theorem ay_existence_example :
    ∃ r ∈ Set.Ioo (-(1 / 8 : ℝ)) (ay_rho (1 / 2)),
      1 / (1 - r) = ay_Kd 1 (1 / 2) (1 / 8) 1 r := by
  have hρ : ay_rho (1 / 2) = 1 := by rw [ay_rho]; norm_num
  refine ay_existence_cd (Ea := fun r => 1 / (1 - r)) one_pos (by norm_num) (by norm_num)
    one_pos ?_ ?_ ?_
  · rw [hρ]
    exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      fun r hr => by linarith [hr.2]
  · rw [hρ]
    have h1 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto _
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact Set.mem_Ioi.2 (by linarith [Set.mem_Iio.1 hr])
    exact Tendsto.congr (fun r => by simp [one_div]) (tendsto_inv_nhdsGT_zero.comp h1)
  · refine ⟨0, ⟨by norm_num, by rw [hρ]; norm_num⟩, 1, fun r hr => ?_⟩
    have h : 1 ≤ 1 - r := by linarith [hr.2]
    rw [div_le_one (by linarith)]
    exact h

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.1.4: the computation algorithm and the Lorenz curve and Gini coefficient

Miao, §17.1.4, pp. 564–569. The algorithm's numerical steps (solving the dynamic programme on a
grid, simulating 100,000 households, Aiyagari's calibrated numbers, Example 17.1.1 and
Figure 17.2) are computational and not formalised; the precise mathematical claims they contain
are proved here.

* `ay_bisect`, `ay_bisect_direction`, `ay_bisect_fixed` (Step 6): the update
  `r¹ = ½(r⁰ + F_K(Ea(r⁰), 1) − δ)` lowers `r` when `Ea(r⁰) > K(r⁰)` and raises it when
  `Ea(r⁰) < K(r⁰)`; `r¹ = r⁰` iff the asset market clears, `Ea(r⁰) = K(r⁰)`.
* `ay_gridUpdate`, `ay_gridUpdate_rect`, `ay_gridUpdate_mass` (Step 4, first method): the grid
  iteration `λ_{t+1}(a′, l′) = Σ_l Σ_{a : g(a,l) = a′} λ_t(a, l)π(l, l′)` is the discrete form
  of (17.7) on rectangles and preserves total mass.
* `ay_damp`, `ay_damp_fixed`, `ay_damp_between` (Ljungqvist–Sargent, p. 567): the damped update
  `K² = ξK¹ + (1 − ξ)K⁰` lies between `K⁰` and `K¹`, and `K² = K⁰` iff `K¹ = K⁰`.
* `ay_lorenz`, `ay_gini`, `ay_gini_eq_area` (p. 568): the Lorenz curve `z_i = Σ_{j≤i} y_j/Σ y_j`
  and the Gini coefficient, twice the area between the 45 degree line and the piecewise linear
  Lorenz curve.
* `ay_lorenz_zero`, `ay_lorenz_n`, `ay_lorenz_mono`, `ay_lorenz_le_diag`: `z` increases to
  `z_n = 1` and lies below the diagonal (`z_i ≤ i/n`) for sorted data.
* `ay_gini_nonneg`, `ay_gini_le`, `ay_gini_equal`: for `x_i ≥ 0` with positive total,
  `0 ≤ G ≤ 1 − 1/n ≤ 1`; complete equality gives `G = 0`.
* `ay_gini_concentrated`, `ay_gini_concentrated_ne_one`, `ay_gini_concentrated_tendsto`:
  complete concentration gives `G = 1 − 1/n`, **not** `1` as the book states; `G → 1` as
  `n → ∞`.

Indexing: the book's sorted sample `y_1 ≤ … ≤ y_n` is `y 0 ≤ … ≤ y (n − 1)` and its `z_i` is
`ay_lorenz y n i = (y 0 + … + y (i − 1))/(y 0 + … + y (n − 1))`, `i = 0, …, n`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, Step 6, p. 566: the bisection update `r¹ = ½(r⁰ + F_K(Ea(r⁰), 1) − δ)`
(Cobb–Douglas, `L = 1`). -/
noncomputable def ay_bisect (A α δ r0 Ea : ℝ) : ℝ := (r0 + (ay_cdFK A α Ea 1 - δ)) / 2

/-- Miao, Step 6, p. 566: if `Ea(r⁰) > K(r⁰)` then `r¹ < r⁰`; if `Ea(r⁰) < K(r⁰)` then
`r¹ > r⁰` (`K(r⁰) = K^d(r⁰)` with `L = 1`, `Ea(r⁰) > 0`). -/
theorem ay_bisect_direction {A α δ r0 Ea : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hr : -δ < r0) (hE : 0 < Ea) :
    (ay_Kd A α δ 1 r0 < Ea → ay_bisect A α δ r0 Ea < r0) ∧
      (Ea < ay_Kd A α δ 1 r0 → r0 < ay_bisect A α δ r0 Ea) := by
  have hx : 0 < α * A / (r0 + δ) := div_pos (mul_pos hα0 hA) (by linarith)
  have hKd : 0 < ay_Kd A α δ 1 r0 := mul_pos one_pos (Real.rpow_pos_of_pos hx _)
  have hfoc := ay_Kd_foc hA hα0 hα1 one_pos hr
  have hanti := ay_cdFK_strictAnti hA hα0 hα1 (one_pos : (0 : ℝ) < 1)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hanti hKd hE h
    simp only at this
    rw [ay_bisect]
    linarith
  · have := hanti hE hKd h
    simp only at this
    rw [ay_bisect]
    linarith

/-- Miao, Steps 6–7, p. 566: the bisection update has `r¹ = r⁰` exactly when the asset market
clears, `Ea(r⁰) = K(r⁰)`. -/
theorem ay_bisect_fixed {A α δ r0 Ea : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hr : -δ < r0) (hE : 0 < Ea) : ay_bisect A α δ r0 Ea = r0 ↔ Ea = ay_Kd A α δ 1 r0 := by
  constructor
  · intro h
    have : ay_cdFK A α Ea 1 = r0 + δ := by rw [ay_bisect] at h; linarith
    exact ay_Kd_unique hA hα0 hα1 one_pos hr hE this
  · intro h
    rw [ay_bisect, h, ay_Kd_foc hA hα0 hα1 one_pos hr]
    ring

/-- Miao, p. 567: the grid iteration
`λ_{t+1}(a′, l′) = Σ_l Σ_{a : g(a,l) = a′} λ_t(a, l)π(l, l′)` on finite grids. -/
def ay_gridUpdate {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (g : α × ι → α)
    (pr : ι → ι → ℝ) (lam : α × ι → ℝ) (q : α × ι) : ℝ :=
  ∑ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) = q.1), lam (a, l) * pr l q.2

/-- Miao, p. 567: the grid iteration is the discrete form of (17.7):
`λ_{t+1}(A × B) = Σ_{(a,l)} 1_{g(a,l) ∈ A} π(l, B) λ_t(a, l)`. -/
theorem ay_gridUpdate_rect {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (g : α × ι → α) (pr : ι → ι → ℝ) (lam : α × ι → ℝ) (A : Finset α) (B : Finset ι) :
    ∑ a' ∈ A, ∑ l' ∈ B, ay_gridUpdate g pr lam (a', l') =
      ∑ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) ∈ A), lam (a, l) * ∑ l' ∈ B, pr l l' := by
  simp only [ay_gridUpdate]
  have hR : ∀ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) ∈ A),
      lam (a, l) * ∑ l' ∈ B, pr l l' = ∑ a' ∈ A,
        ∑ a ∈ Finset.univ.filter (fun a => g (a, l) = a'), ∑ l' ∈ B, lam (a, l) * pr l l' :=
    fun l => by
      rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ A (fun a => g (a, l))]
      simp_rw [Finset.mul_sum]
  simp_rw [hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]

/-- Miao, p. 567: if each row of `π` sums to one, the grid iteration preserves total mass. -/
theorem ay_gridUpdate_mass {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (g : α × ι → α) (pr : ι → ι → ℝ) (hpr : ∀ l, ∑ l', pr l l' = 1) (lam : α × ι → ℝ) :
    ∑ q, ay_gridUpdate g pr lam q = ∑ q, lam q := by
  classical
  have h := ay_gridUpdate_rect g pr lam Finset.univ Finset.univ
  rw [Fintype.sum_prod_type, h, Fintype.sum_prod_type]
  simp only [hpr, mul_one, Finset.mem_univ, Finset.filter_true]
  rw [Finset.sum_comm]

/-- Miao, p. 567 (Ljungqvist–Sargent): the damped update `K² = ξK¹ + (1 − ξ)K⁰`. -/
def ay_damp (ξ K0 K1 : ℝ) : ℝ := ξ * K1 + (1 - ξ) * K0

/-- Miao, p. 567: for `ξ ∈ (0, 1)`, `K² = K⁰` iff `K¹ = K⁰`: the damped iteration has the same
fixed points (`K¹(K⁰) = K⁰`, market clearing) as the undamped one. -/
theorem ay_damp_fixed {ξ K0 K1 : ℝ} (hξ : 0 < ξ) : ay_damp ξ K0 K1 = K0 ↔ K1 = K0 := by
  rw [ay_damp]
  constructor
  · intro h
    have : ξ * (K1 - K0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  · intro h; rw [h]; ring

/-- Miao, p. 567: for `ξ ∈ (0, 1)`, `K²` lies between `K⁰` and `K¹`. -/
theorem ay_damp_between {ξ K0 K1 : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    min K0 K1 ≤ ay_damp ξ K0 K1 ∧ ay_damp ξ K0 K1 ≤ max K0 K1 := by
  rw [ay_damp]
  have h1 := min_le_left K0 K1
  have h2 := min_le_right K0 K1
  have h3 := le_max_left K0 K1
  have h4 := le_max_right K0 K1
  constructor <;> nlinarith

/-- Miao, p. 568: the **Lorenz curve** `z_i = Σ_{j<i} y_j / Σ_{j<n} y_j` of the sorted sample
`y 0 ≤ … ≤ y (n − 1)`, plotted against `i/n`. -/
noncomputable def ay_lorenz (y : ℕ → ℝ) (n i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range i, y j) / ∑ j ∈ Finset.range n, y j

/-- Miao, p. 568: the **Gini coefficient** of the sample, computed from the Lorenz curve:
`G = 1 − (1/n) Σ_{i<n} (z_i + z_{i+1})`. -/
noncomputable def ay_gini (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - (1 / n) * ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1))

/-- Miao, p. 568: the Gini coefficient is two times the area between the 45 degree line (area
`1/2` beneath it) and the piecewise linear Lorenz curve through `(i/n, z_i)` (trapezoid areas
`(1/n)(z_i + z_{i+1})/2`). -/
theorem ay_gini_eq_area (y : ℕ → ℝ) (n : ℕ) :
    ay_gini y n = 2 * (1 / 2 - ∑ i ∈ Finset.range n,
      (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) := by
  rw [ay_gini]
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem ay_lorenz_zero (y : ℕ → ℝ) (n : ℕ) : ay_lorenz y n 0 = 0 := by simp [ay_lorenz]

/-- Miao, p. 568: `z_n = 1` (positive total). -/
theorem ay_lorenz_n {y : ℕ → ℝ} {n : ℕ} (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_lorenz y n n = 1 := div_self hT.ne'

/-- Miao, p. 568: for `y ≥ 0`, `{z_i}` is an increasing sequence. -/
theorem ay_lorenz_mono {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) (i : ℕ) : ay_lorenz y n i ≤ ay_lorenz y n (i + 1) := by
  rw [ay_lorenz, ay_lorenz, Finset.sum_range_succ]
  exact div_le_div_of_nonneg_right (by linarith [hy i]) hT.le

/-- Miao, p. 568: for sorted data the Lorenz curve lies below the 45 degree line,
`z_i ≤ i/n` for `i ≤ n`. -/
theorem ay_lorenz_le_diag {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i ≤ n) :
    ay_lorenz y n i ≤ i / n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  rcases hi.lt_or_eq with hlt | heq
  · set a := ∑ j ∈ Finset.range i, y j
    set b := ∑ k ∈ Finset.Ico i n, y k
    have hab : a + b = ∑ j ∈ Finset.range n, y j := Finset.sum_range_add_sum_Ico y hi
    have ha : a ≤ (i : ℝ) * y i := by
      have := Finset.sum_le_card_nsmul (Finset.range i) y (y i)
        fun j hj => hsort j i (Finset.mem_range.1 hj).le hlt
      simpa using this
    have hb : ((n - i : ℕ) : ℝ) * y i ≤ b := by
      have := Finset.card_nsmul_le_sum (Finset.Ico i n) y (y i)
        fun k hk => hsort i k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
      simpa using this
    rw [Nat.cast_sub hi] at hb
    have hni : (0 : ℝ) ≤ n - i := by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h1 := mul_le_mul_of_nonneg_left ha hni
    have h2 := mul_le_mul_of_nonneg_left hb hi0
    rw [ay_lorenz, ← hab, div_le_div_iff₀ (by linarith) (by exact_mod_cast hn)]
    nlinarith
  · subst heq
    rw [ay_lorenz_n hT, div_self (by exact_mod_cast hn.ne')]

theorem ay_sum_odd (n : ℕ) : ∑ i ∈ Finset.range n, ((2 * i + 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Miao, p. 568: "if `x_i ≥ 0` for all `i`, then the Gini coefficient is between zero and
one": `G ≥ 0` for sorted data with positive total. -/
theorem ay_gini_nonneg {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) : 0 ≤ ay_gini y n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) ≤ n := by
    calc ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1))
        ≤ ∑ i ∈ Finset.range n, (((2 * i + 1 : ℕ) : ℝ) / n) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have h1 := ay_lorenz_le_diag hsort hT hi'.le
          have h2 := ay_lorenz_le_diag hsort hT (Nat.succ_le_of_lt hi')
          have e : (((2 * i + 1 : ℕ) : ℝ)) / n = i / n + ((i : ℝ) + 1) / n := by
            push_cast; ring
          rw [e]
          simp only [Nat.succ_eq_add_one] at h2
          push_cast at h2
          linarith
      _ = n := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul, ay_sum_odd]
          field_simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ay_gini]
  have : 1 / (n : ℝ) * ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hnpos]
    exact hS
  linarith

/-- Miao, p. 568: for `x_i ≥ 0` with positive total, `G ≤ 1 − 1/n ≤ 1`. -/
theorem ay_gini_le {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) : ay_gini y n ≤ 1 - 1 / n ∧ ay_gini y n ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact ⟨n - 1, by omega⟩
  have hz : ∀ i, 0 ≤ ay_lorenz y (m + 1) i := fun i =>
    div_nonneg (Finset.sum_nonneg fun j _ => hy j) hT.le
  have hS : 1 ≤ ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) := by
    rw [Finset.sum_range_succ, ay_lorenz_n hT]
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range m) =>
      add_nonneg (hz i) (hz (i + 1))
    linarith [hz m]
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have h1 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) := by
    have := mul_le_mul_of_nonneg_left hS (one_div_pos.2 hnpos).le
    simpa using this
  refine ⟨by rw [ay_gini]; linarith, ?_⟩
  rw [ay_gini]
  linarith [one_div_pos.2 hnpos]

/-- Miao, p. 568: "for complete equality of income the Gini coefficient is zero". -/
theorem ay_gini_equal {y : ℕ → ℝ} {n : ℕ} {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hy : ∀ j, j < n → y j = c) : ay_gini y n = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∀ i, i ≤ n → ∑ j ∈ Finset.range i, y j = i * c := fun i hi => by
    have : ∑ j ∈ Finset.range i, y j = ∑ j ∈ Finset.range i, c :=
      Finset.sum_congr rfl fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
    rw [this]
    simp
  have hz : ∀ i, i ≤ n → ay_lorenz y n i = i / n := fun i hi => by
    rw [ay_lorenz, hsum i hi, hsum n le_rfl]
    field_simp
  have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) = n := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [hz i (Finset.mem_range.1 hi).le, hz (i + 1) (Finset.mem_range.1 hi)]]
    have : ∀ i : ℕ, (i : ℝ) / n + ((i + 1 : ℕ) : ℝ) / n = ((2 * i + 1 : ℕ) : ℝ) / n := by
      intro i; push_cast; ring
    simp_rw [this]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ay_sum_odd]
    field_simp
  rw [ay_gini, hS, one_div, inv_mul_cancel₀ hnr.ne', sub_self]

/-- Miao, p. 568, corrected: under complete concentration (the richest of `n = m + 1` people has
all income `Y > 0`) the Gini coefficient is `1 − 1/n`. -/
theorem ay_gini_concentrated {y : ℕ → ℝ} {m : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hy : ∀ j, j < m → y j = 0) (hm : y m = Y) : ay_gini y (m + 1) = 1 - 1 / (m + 1 : ℕ) := by
  have hpre : ∀ i, i ≤ m → ∑ j ∈ Finset.range i, y j = 0 := fun i hi =>
    Finset.sum_eq_zero fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
  have hT : ∑ j ∈ Finset.range (m + 1), y j = Y := by
    rw [Finset.sum_range_succ, hpre m le_rfl, hm, zero_add]
  have hS : ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) = 1 := by
    rw [Finset.sum_range_succ, ay_lorenz_n (hT ▸ hY)]
    have h0 : ∀ i ∈ Finset.range m, ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1) = 0 :=
      fun i hi => by
        have hi' := Finset.mem_range.1 hi
        rw [ay_lorenz, ay_lorenz, hpre i hi'.le, hpre (i + 1) hi', zero_div, add_zero]
    rw [Finset.sum_eq_zero h0, ay_lorenz, hpre m le_rfl, zero_div]
    ring
  rw [ay_gini, hS, mul_one]

/-- Miao, p. 568: the book's "for complete concentration ... the Gini coefficient is `1`" is
false for a finite sample of `n ≥ 1` people. -/
theorem ay_gini_concentrated_ne_one {y : ℕ → ℝ} {m : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hy : ∀ j, j < m → y j = 0) (hm : y m = Y) : ay_gini y (m + 1) ≠ 1 := by
  rw [ay_gini_concentrated hY hy hm]
  have : (0 : ℝ) < 1 / (m + 1 : ℕ) := by positivity
  intro h
  linarith

/-- Miao, p. 568: under complete concentration the Gini coefficient tends to `1` as the sample
size grows. -/
theorem ay_gini_concentrated_tendsto :
    Tendsto (fun m : ℕ => 1 - 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h
  rw [sub_zero] at h2
  refine h2.congr fun m => ?_
  push_cast
  rfl

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 17.4: the Aiyagari model with endogenous leisure

Miao, §17.4, Exercise 4, p. 584: "Introduce endogenous leisure in the Aiyagari (1994) model and
define a stationary equilibrium."

The household chooses hours `n ∈ [0, 1]` (leisure `1 − n`) and assets: utility `u(c, 1 − n)`,
budget `c + a′ = (1 + r)a + wln`, `a′ ≥ −φ`.

* `ay_BellmanLeisure`: the household's Bellman equation
  `V(a, l) = max_{a′ ≥ −φ, n ∈ [0,1]} u((1 + r)a + wln − a′, 1 − n) + β ∫ V(a′, l′) Q(dl′, l)`.
* `ex_17_4_foc`: the intratemporal first-order condition at an interior hours choice with
  positive consumption: `wl u_c(c, 1 − n) = u_{1−n}(c, 1 − n)` (marginal rate of substitution
  between leisure and consumption equals the effective wage).
* `AYLeisureEconomy`, `AYLeisureEqm`: the stationary recursive competitive equilibrium of
  Definition 17.1.1 with endogenous leisure; the labour market clears in efficiency units,
  `L = ∫ l n(a, l) dλ*`.
* `ex_17_4_firm`: the firm's conditions (17.5)–(17.6) carry over unchanged.
* `ex_17_4`: the definition is not vacuous: a concrete equilibrium with
  `u(c, h) = c − (1 − h)²/2`, `F(K, L) = √(KL)`, `β = 1/2`, `δ = 1/4`, `l ≡ 1`, `b = −1/2`,
  `r = 1/4`, `w = 1/2`, `n ≡ 1/2`, `K = L = 1/2`, where the first-order condition
  `wl = n` holds.

**Departures.** The book only asks for the definition; the first-order condition and the
example are added. The borrowing limit `φ` is that of (17.3b).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Exercise 17.4** (Miao, p. 584): the household's Bellman equation with endogenous hours
`n(a, l) ∈ [0, 1]`: `V(a, l) = max u((1 + r)a + wln − a′, 1 − n) + β ∫ V(a′, l′) Q(dl′, l)`
over `n ∈ [0, 1]` and `a′ ∈ [−φ, (1 + r)a + wln]`, attained at `(g, n)`. -/
def ay_BellmanLeisure (u : ℝ × ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ)
    (V g n : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, -φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    n p ∈ Set.Icc 0 1 ∧ g p ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2 * n p) ∧
    V p = u ((1 + r) * p.1 + w * p.2 * n p - g p, 1 - n p) + β * ∫ l', V (g p, l') ∂Q p.2 ∧
    ∀ h a', h ∈ Set.Icc 0 1 → a' ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2 * h) →
      u ((1 + r) * p.1 + w * p.2 * h - a', 1 - h) + β * ∫ l', V (a', l') ∂Q p.2 ≤ V p

/-- **Exercise 17.4** (Miao, p. 584): the intratemporal first-order condition. At a state with
interior hours `n ∈ (0, 1)` and positive consumption `c`, if `u` is differentiable at
`(c, 1 − n)` with derivative `u′`, then `wl·u_c = u_{1−n}`, where `u_c = u′(1, 0)` and
`u_{1−n} = u′(0, 1)`. -/
theorem ex_17_4_foc {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {β r w φ lmin lmax : ℝ}
    {Q : Kernel ℝ ℝ} {V g n : ℝ × ℝ → ℝ} (hB : ay_BellmanLeisure u β r w φ lmin lmax Q V g n)
    {p : ℝ × ℝ} (ha : -φ ≤ p.1) (hl : p.2 ∈ Set.Icc lmin lmax) (hn : n p ∈ Set.Ioo 0 1)
    (hc : 0 < (1 + r) * p.1 + w * p.2 * n p - g p)
    (hu : HasFDerivAt u u' ((1 + r) * p.1 + w * p.2 * n p - g p, 1 - n p)) :
    w * p.2 * u' (1, 0) = u' (0, 1) := by
  obtain ⟨-, hg, hV, hmax⟩ := hB p ha hl
  set f : ℝ → ℝ × ℝ := fun h => ((1 + r) * p.1 + w * p.2 * h - g p, 1 - h) with hf
  have hfd : HasDerivAt f (w * p.2, -1) (n p) := by
    have h1 : HasDerivAt (fun h : ℝ => (1 + r) * p.1 + w * p.2 * h - g p) (w * p.2) (n p) := by
      simpa using (((hasDerivAt_id (n p)).const_mul (w * p.2)).const_add
        ((1 + r) * p.1)).sub_const (g p)
    have h2 : HasDerivAt (fun h : ℝ => 1 - h) (-1) (n p) := by
      simpa using (hasDerivAt_id (n p)).const_sub 1
    exact h1.prodMk h2
  have hcomp := hu.comp_hasDerivAt (n p) hfd
  have hcont : Continuous fun h : ℝ => (1 + r) * p.1 + w * p.2 * h - g p := by fun_prop
  have hloc : IsLocalMax (u ∘ f) (n p) := by
    filter_upwards [Ioo_mem_nhds hn.1 hn.2, hcont.continuousAt.eventually (lt_mem_nhds hc)]
      with h hh hch
    have := hmax h (g p) ⟨hh.1.le, hh.2.le⟩ ⟨hg.1, by linarith⟩
    rw [hV] at this
    simp only [Function.comp_apply, hf]
    linarith
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hdec : ((w * p.2, -1) : ℝ × ℝ) =
      (w * p.2) • ((1 : ℝ), (0 : ℝ)) + (-1 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
  linarith

/-- The primitives of the Aiyagari economy with endogenous leisure (Exercise 17.4):
utility `u(c, 1 − n)` of consumption and leisure. -/
structure AYLeisureEconomy where
  β : ℝ
  δ : ℝ
  b : ℝ
  lmin : ℝ
  lmax : ℝ
  u : ℝ × ℝ → ℝ
  F : ℝ × ℝ → ℝ
  Q : Kernel ℝ ℝ
  Q_markov : IsMarkovKernel Q

/-- **Exercise 17.4** (Miao, p. 584): a **stationary recursive competitive equilibrium with
endogenous leisure**: value function `V`, policies `g` (assets), `n` (hours), `c`
(consumption), firm's choices `K`, `L`, prices `r`, `w` and a stationary measure `λ*` such that
(i) `(V, g, n)` solve the household's problem, `c = (1 + r)a + wln − g`; (ii) `(K, L)`
maximises profits; (iii) the labour market clears in efficiency units, `L = ∫ l n dλ*`;
(iv) `K = ∫ g dλ*`; (v) `∫ c dλ* + δK = F(K, L)`; (vi) (17.7). -/
structure AYLeisureEqm (E : AYLeisureEconomy) where
  V : ℝ × ℝ → ℝ
  g : ℝ × ℝ → ℝ
  n : ℝ × ℝ → ℝ
  c : ℝ × ℝ → ℝ
  K : ℝ
  L : ℝ
  r : ℝ
  w : ℝ
  lam : Measure (ℝ × ℝ)
  lam_prob : IsProbabilityMeasure lam
  g_meas : Measurable g
  supp : ∀ᵐ p ∂lam, -ay_phi E.b w E.lmin r ≤ p.1 ∧ p.2 ∈ Set.Icc E.lmin E.lmax
  household : ay_BellmanLeisure E.u E.β r w (ay_phi E.b w E.lmin r) E.lmin E.lmax E.Q V g n
  cons_eq : ∀ p, c p = (1 + r) * p.1 + w * p.2 * n p - g p
  K_pos : 0 < K
  L_pos : 0 < L
  firm : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit E.F r E.δ w q ≤ ay_profit E.F r E.δ w (K, L)
  labor : L = ∫ p, p.2 * n p ∂lam
  asset : K = ∫ p, g p ∂lam
  resource : ∫ p, c p ∂lam + E.δ * K = E.F (K, L)
  stationary : ay_Stationary E.Q g lam

/-- **Exercise 17.4** (Miao, p. 584): in an equilibrium with endogenous leisure the firm's
first-order conditions (17.5)–(17.6) hold, and `λ*` is invariant under the transition
function. -/
theorem ex_17_4_firm {E : AYLeisureEconomy} (e : AYLeisureEqm E) {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hF : HasFDerivAt E.F F' (e.K, e.L)) :
    (F' (1, 0) = e.r + E.δ ∧ F' (0, 1) = e.w) ∧
      e.lam.bind (ay_P E.Q e.g e.g_meas) = e.lam := by
  have := E.Q_markov
  have := e.lam_prob
  exact ⟨eq_17_5_17_6 hF (ay_isLocalMax_of_max e.K_pos e.L_pos e.firm),
    (eq_17_7 E.Q e.g_meas e.lam).1 e.stationary⟩

/-- The concrete economy of `ay_leisureEqm`: `u(c, h) = c − (1 − h)²/2`, `F(K, L) = √(KL)`,
`β = 1/2`, `δ = 1/4`, `b = −1/2`, `l ≡ 1`. -/
noncomputable def ay_leisureEconomy : AYLeisureEconomy where
  β := 1 / 2
  δ := 1 / 4
  b := -(1 / 2)
  lmin := 1
  lmax := 1
  u := fun p => p.1 - (1 - p.2) ^ 2 / 2
  F := fun p => Real.sqrt (p.1 * p.2)
  Q := Kernel.const ℝ (Measure.dirac 1)
  Q_markov := inferInstance

theorem ay_leisure_phi : ay_phi (-(1 / 2)) (1 / 2) 1 (1 / 4) = -(1 / 2) := by
  rw [ay_phi]
  norm_num

/-- A concrete stationary equilibrium with endogenous leisure: `r = 1/4`, `w = 1/2`,
`K = L = 1/2`, `n ≡ 1/2`, `g ≡ 1/2`, `V(a, l) = 5a/4 − 1/8`, `λ* = δ_{(1/2, 1)}`. -/
noncomputable def ay_leisureEqm : AYLeisureEqm ay_leisureEconomy where
  V := fun p => 5 / 4 * p.1 - 1 / 8
  g := fun _ => 1 / 2
  n := fun _ => 1 / 2
  c := fun p => (1 + 1 / 4) * p.1 + 1 / 2 * p.2 * (1 / 2) - 1 / 2
  K := 1 / 2
  L := 1 / 2
  r := 1 / 4
  w := 1 / 2
  lam := Measure.dirac (1 / 2, 1)
  lam_prob := inferInstance
  g_meas := measurable_const
  supp := by
    rw [ae_dirac_eq]
    simp only [ay_leisureEconomy, ay_leisure_phi, Filter.eventually_pure]
    norm_num
  household := by
    intro p ha hl
    simp only [ay_leisureEconomy, ay_leisure_phi] at ha hl ⊢
    have hl1 : p.2 = 1 := le_antisymm hl.2 hl.1
    simp only [Kernel.const_apply, integral_const, probReal_univ, one_smul]
    refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by rw [hl1]; linarith⟩,
      by rw [hl1]; ring, fun h a' hh ha' => ?_⟩
    have := ha'.1
    rw [hl1]
    nlinarith [sq_nonneg (h - 1 / 2)]
  cons_eq := fun _ => rfl
  K_pos := by norm_num
  L_pos := by norm_num
  firm := by
    intro q hq1 hq2
    simp only [ay_profit, ay_leisureEconomy]
    have h4 : Real.sqrt (1 / 2 * (1 / 2)) = 1 / 2 := by
      rw [show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hq : Real.sqrt (q.1 * q.2) ≤ (q.1 + q.2) / 2 :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (q.1 - q.2)]⟩
    rw [h4]
    linarith
  labor := by rw [integral_dirac]; norm_num
  asset := by rw [integral_dirac]
  resource := by
    simp only [ay_leisureEconomy]
    rw [integral_dirac, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  stationary := by
    intro A B hA hB
    simp only [ay_leisureEconomy, Kernel.const_apply]
    rw [lintegral_dirac, Measure.dirac_apply' _ (hA.prod hB), Set.indicator_prod_one,
      Measure.dirac_apply' _ hB]

/-- **Exercise 17.4** (Miao, p. 584): the equilibrium with endogenous leisure is not vacuous,
and in the example the intratemporal condition `wl·u_c = u_{1−n}` holds: `u_c = 1`,
`u_{1−n} = 1 − (1 − n) = n = 1/2 = wl`. -/
theorem ex_17_4 :
    Nonempty (AYLeisureEqm ay_leisureEconomy) ∧
      ay_leisureEqm.w * 1 * 1 = 1 - (1 - ay_leisureEqm.n (1 / 2, 1)) := by
  refine ⟨⟨ay_leisureEqm⟩, ?_⟩
  simp only [ay_leisureEqm]
  norm_num

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.2.1: the Huggett endowment economy, Definition 17.2.1 and Proposition 17.2.1

Miao, §17.1.1, pp. 560–562 (the household's problem (17.2), (17.4) and the stationary
distribution (17.7)) and §17.2.1, pp. 570–571 (Definition 17.2.1, Proposition 17.2.1).

A household receives the endowment `e(s)` in the idiosyncratic state `s ∈ E`, which follows a
Markov process with transition kernel `Q`. Given the risk-free rate `r` and the debt limit `φ`
it solves the Bellman equation (17.4)
`V(a, s) = max_{a' ∈ [−φ, (1 + r)a + e(s)]} u((1 + r)a + e(s) − a') + β ∫ V(a', s′) Q(ds′, s)`
(the budget (17.2) with `w = 1`, `c ≥ 0`, and the borrowing constraint (17.3a)).

* `BWEconomy`: the primitives `(β, u, Q, e)`. `BWEconomy.Bellman r φ y V g`: `V` solves (17.4)
  for the endowment `y`, the maximum attained by the policy `g`.
* `BWEconomy.Stationary g lam`: the stationarity condition (17.8) (= (17.7)),
  `λ(A × B) = ∫ 1_A(g(a, s)) Q(B, s) dλ(a, s)` for measurable rectangles.
* `BWEconomy.EaSet r φ y`: the set of long-run average asset holdings `Ea(r) = ∫ g dλ` over all
  solutions `(V, g)` of (17.4) and all stationary distributions `λ` of `g` on `S = [−φ, ∞) × E`.
  The book writes `Ea(r)` as a function; we do not assume that the solution and the stationary
  distribution are unique.
* `BWHuggettEqm H φ`: **Definition 17.2.1**; `definition_17_2_1`: `r` is an equilibrium rate iff
  `0 ∈ Ea(r)` ("the intersection of the `Ea(r)` curve with the vertical axis", p. 571).
* The change of variables `â = a + d` (`bw_bellman_shift`, `bw_stationary_shift`,
  `bw_EaSet_shift`): the problem with rate `r`, limit `φ` and endowment `y` is the problem with
  limit `φ − d` and endowment `y − rd`; asset holdings shift by `d`.
* **Proposition 17.2.1** (`proposition_17_2_1`, `proposition_17_2_1_policy`): at `r = 0` the
  shift does not change the endowment, so `Ea(0; b) = Ea(0; 0) − b`.
* `bw_natural_limit`: (17.4) has a solution only if `rφ ≤ e(s)` for every `s` (nonnegative
  consumption at the debt limit), i.e. `φ ≤ e_min/r` for `r > 0`: the natural borrowing limit.

**Departures.** (1) `Ea(r)` is a set (see above). (2) The book's proof of Proposition 17.2.1 ends
with the typo `Ea(0; b) = Ea(0; b) − b`; the statement (`Ea(0; 0) − b`) is what is proved.
(3) The Bellman equation carries the integrability of `V(a′, ·)` under `Q(·, s)`, which the book
leaves implicit.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **Huggett endowment economy** (Miao, §17.2.1, p. 570): discount factor `β`, utility
`u`, the transition kernel `Q` of the idiosyncratic state and the endowment `e(s)` (`w = 1`). -/
structure BWEconomy (E : Type*) [MeasurableSpace E] where
  β : ℝ
  u : ℝ → ℝ
  Q : Kernel E E
  e : E → ℝ

variable {E : Type*} [MeasurableSpace E]

namespace BWEconomy

/-- Miao, (17.2)–(17.4), pp. 560–561: `V` solves the Bellman equation of the household with
rate `r`, debt limit `φ` (`a ≥ −φ`) and endowment `y`, the maximum being attained at `g(a, s)`.
Consumption `c = (1 + r)a + y(s) − a′ ≥ 0` gives the upper bound on `a′`. -/
def Bellman (H : BWEconomy E) (r φ : ℝ) (y : E → ℝ) (V g : ℝ → E → ℝ) : Prop :=
  ∀ a s, -φ ≤ a →
    g a s ∈ Set.Icc (-φ) ((1 + r) * a + y s) ∧
    (∀ a', -φ ≤ a' → Integrable (fun s' => V a' s') (H.Q s)) ∧
    V a s = H.u ((1 + r) * a + y s - g a s) + H.β * ∫ s', V (g a s) s' ∂(H.Q s) ∧
    ∀ a' ∈ Set.Icc (-φ) ((1 + r) * a + y s),
      H.u ((1 + r) * a + y s - a') + H.β * ∫ s', V a' s' ∂(H.Q s) ≤ V a s

/-- Miao, (17.7)–(17.8), pp. 562, 570: `λ` is a **stationary distribution** for the policy `g`,
`λ(A × B) = ∫ 1_A(g(a, s)) Q(B, s) dλ(a, s)` for all measurable `A ⊆ ℝ`, `B ⊆ E`. -/
def Stationary (H : BWEconomy E) (g : ℝ → E → ℝ) (lam : Measure (ℝ × E)) : Prop :=
  ∀ A B, MeasurableSet A → MeasurableSet B →
    lam (A ×ˢ B) = ∫⁻ p, A.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2) * H.Q p.2 B ∂lam

/-- Miao, p. 562: the **long-run average assets** `Ea(r) = ∫ g dλ*`, as the set of values over
all solutions of (17.4) with debt limit `φ` and endowment `y` and all stationary probability
distributions on `S = [−φ, ∞) × E` with integrable `g`. -/
def EaSet (H : BWEconomy E) (r φ : ℝ) (y : E → ℝ) : Set ℝ :=
  {m | ∃ (V g : ℝ → E → ℝ) (lam : Measure (ℝ × E)), IsProbabilityMeasure lam ∧
    lam {p | p.1 < -φ} = 0 ∧ H.Bellman r φ y V g ∧ H.Stationary g lam ∧
    Integrable (fun p => g p.1 p.2) lam ∧ m = ∫ p, g p.1 p.2 ∂lam}

end BWEconomy

/-- The shift `(a, s) ↦ (a + d, s)` of the state space. -/
noncomputable def bw_shift (d : ℝ) : ℝ × E ≃ᵐ ℝ × E :=
  (MeasurableEquiv.addRight d).prodCongr (MeasurableEquiv.refl E)

theorem bw_shift_apply (d : ℝ) (p : ℝ × E) : bw_shift d p = (p.1 + d, p.2) := rfl

/-- Miao, p. 571 (proof of Proposition 17.2.1), for any `r`: with `â = a + d` the budget
`c + a′ = (1 + r)a + y` becomes `c + â′ = (1 + r)â + y − rd` and `a′ ≥ −φ` becomes
`â′ ≥ −(φ − d)`; so `V̂(â) = V(â − d)`, `ĝ(â) = g(â − d) + d` solve the problem with limit
`φ − d` and endowment `y − rd`. -/
theorem bw_bellman_shift {H : BWEconomy E} {r φ d φ' : ℝ} {y y' : E → ℝ} {V g : ℝ → E → ℝ}
    (h : H.Bellman r φ y V g) (hφ : φ' = φ - d) (hy : ∀ s, y' s = y s - r * d) :
    H.Bellman r φ' y' (fun x s => V (x - d) s) (fun x s => g (x - d) s + d) := by
  intro x s hx
  subst hφ
  have hx' : -φ ≤ x - d := by linarith
  obtain ⟨hg, hint, hV, hmax⟩ := h (x - d) s hx'
  have key : (1 + r) * x + y' s = (1 + r) * (x - d) + y s + d := by rw [hy]; ring
  refine ⟨?_, fun a' ha' => hint (a' - d) (by linarith), ?_, fun a' ha' => ?_⟩
  · rw [key]; exact ⟨by linarith [hg.1], by linarith [hg.2]⟩
  · simp only [key, add_sub_cancel_right]
    rw [show (1 + r) * (x - d) + y s + d - (g (x - d) s + d) =
      (1 + r) * (x - d) + y s - g (x - d) s by ring]
    exact hV
  · rw [key] at ha' ⊢
    have := hmax (a' - d) ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
    rwa [show (1 + r) * (x - d) + y s + d - a' = (1 + r) * (x - d) + y s - (a' - d) by ring]

/-- The shift of a solution is reversible: (17.4) with `(φ, y)` has the solution `(V, g)` iff
(17.4) with `(φ − d, y − rd)` has the shifted solution. -/
theorem bw_bellman_shift_iff {H : BWEconomy E} {r φ d : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ} :
    H.Bellman r φ y V g ↔ H.Bellman r (φ - d) (fun s => y s - r * d)
      (fun x s => V (x - d) s) (fun x s => g (x - d) s + d) := by
  refine ⟨fun h => bw_bellman_shift h rfl fun _ => rfl, fun h => ?_⟩
  have := bw_bellman_shift (d := -d) (φ' := φ) (y' := y) h (by ring) (fun s => by ring)
  simpa only [sub_neg_eq_add, add_sub_cancel_right, add_neg_cancel_right] using this

/-- Stationarity is preserved by the shift: if `λ` is stationary for `g`, then its image under
`(a, s) ↦ (a + d, s)` is stationary for `ĝ(â, s) = g(â − d, s) + d`. -/
theorem bw_stationary_shift {H : BWEconomy E} {g : ℝ → E → ℝ} {lam : Measure (ℝ × E)}
    (h : H.Stationary g lam) (d : ℝ) :
    H.Stationary (fun x s => g (x - d) s + d) (lam.map (bw_shift d)) := by
  intro A B hA hB
  have hA' : MeasurableSet ((fun x : ℝ => x + d) ⁻¹' A) := (measurable_id.add_const d) hA
  have hpre : (bw_shift (E := E) d) ⁻¹' (A ×ˢ B) = ((fun x : ℝ => x + d) ⁻¹' A) ×ˢ B := by
    ext p; simp [bw_shift_apply]
  rw [MeasurableEquiv.map_apply, hpre, h _ B hA' hB, lintegral_map_equiv]
  refine lintegral_congr fun p => ?_
  simp only [bw_shift_apply, add_sub_cancel_right]
  by_cases hm : g p.1 p.2 + d ∈ A
  · simp [Set.indicator, hm]
  · simp [Set.indicator, hm]

/-- The support condition `λ{a < −φ} = 0` is preserved by the shift (with limit `φ − d`). -/
theorem bw_supp_shift {lam : Measure (ℝ × E)} {φ : ℝ} (h : lam {p | p.1 < -φ} = 0) (d : ℝ) :
    lam.map (bw_shift d) {p | p.1 < -(φ - d)} = 0 := by
  rw [MeasurableEquiv.map_apply]
  convert h using 2
  ext p
  simp only [Set.mem_preimage, bw_shift_apply, Set.mem_ofPred_eq]
  constructor <;> intro hp <;> linarith

/-- Integrability of the shifted policy. -/
theorem bw_integrable_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {g : ℝ → E → ℝ}
    (h : Integrable (fun p => g p.1 p.2) lam) (d : ℝ) :
    Integrable (fun p : ℝ × E => g (p.1 - d) p.2 + d) (lam.map (bw_shift d)) := by
  rw [integrable_map_equiv]
  simpa [Function.comp_def, bw_shift_apply] using h.add (integrable_const d)

/-- Mean asset holdings shift by `d`: `∫ ĝ d(shift λ) = ∫ g dλ + d`. -/
theorem bw_integral_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {g : ℝ → E → ℝ}
    (h : Integrable (fun p => g p.1 p.2) lam) (d : ℝ) :
    ∫ p, (g (p.1 - d) p.2 + d) ∂(lam.map (bw_shift d)) = ∫ p, g p.1 p.2 ∂lam + d := by
  rw [integral_map_equiv]
  simp only [bw_shift_apply, add_sub_cancel_right]
  rw [integral_add h (integrable_const d)]
  simp

/-- The image of a probability measure under the shift is a probability measure. -/
theorem bw_isProb_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] (d : ℝ) :
    IsProbabilityMeasure (lam.map (bw_shift d)) :=
  (Measure.isProbabilityMeasure_map_iff (bw_shift d).measurable.aemeasurable).2 inferInstance

/-- Miao, p. 571: if `m ∈ Ea(r)` for limit `φ` and endowment `y`, then `m + d ∈ Ea(r)` for
limit `φ − d` and endowment `y − rd`. -/
theorem bw_EaSet_shift {H : BWEconomy E} {r φ d φ' m : ℝ} {y y' : E → ℝ}
    (hm : m ∈ H.EaSet r φ y) (hφ : φ' = φ - d) (hy : ∀ s, y' s = y s - r * d) :
    m + d ∈ H.EaSet r φ' y' := by
  obtain ⟨V, g, lam, hP, hsupp, hB, hS, hI, rfl⟩ := hm
  refine ⟨fun x s => V (x - d) s, fun x s => g (x - d) s + d, lam.map (bw_shift d),
    bw_isProb_shift d, ?_, bw_bellman_shift hB hφ hy, bw_stationary_shift hS d,
    bw_integrable_shift hI d, (bw_integral_shift hI d).symm⟩
  rw [hφ]
  exact bw_supp_shift hsupp d

/-- The change of variables as an identity of sets: `Ea(r; φ − d, y − rd) = Ea(r; φ, y) + d`. -/
theorem bw_EaSet_shift_eq (H : BWEconomy E) (r φ d : ℝ) (y : E → ℝ) :
    H.EaSet r (φ - d) (fun s => y s - r * d) = (fun m => m + d) '' H.EaSet r φ y := by
  ext m
  refine ⟨fun hm => ⟨m - d, ?_, by ring⟩, ?_⟩
  · have := bw_EaSet_shift (d := -d) (φ' := φ) (y' := y) hm (by ring) (fun s => by ring)
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using this
  · rintro ⟨m', hm', rfl⟩
    exact bw_EaSet_shift hm' rfl fun _ => rfl

/-- **Proposition 17.2.1** (Miao, p. 571), policy form. At `r = 0`, with `â = a + b`, the
problem with debt limit `b` is the problem with limit `0` for the same endowment: `(V, g)`
solves (17.4) with limit `b` iff `V̂(â) = V(â − b)`, `ĝ(â) = g(â − b) + b` solve it with limit
`0`. So the optimal policy for `â` is independent of `b`: `g(a; b) + b = ĝ(a + b; 0)`. -/
theorem proposition_17_2_1_policy (H : BWEconomy E) (b : ℝ) (y : E → ℝ) (V g : ℝ → E → ℝ) :
    H.Bellman 0 b y V g ↔
      H.Bellman 0 0 y (fun x s => V (x - b) s) (fun x s => g (x - b) s + b) := by
  rw [bw_bellman_shift_iff (d := b)]
  simp only [sub_self, zero_mul, sub_zero]

/-- **Proposition 17.2.1** (Miao, p. 571). When `r = 0`, `Ea(0; b) = Ea(0; 0) − b`: the set of
long-run average asset holdings with debt limit `b` is that with limit `0` shifted by `−b`. -/
theorem proposition_17_2_1 (H : BWEconomy E) (b : ℝ) (y : E → ℝ) :
    H.EaSet 0 b y = (fun m => m - b) '' H.EaSet 0 0 y := by
  have h := bw_EaSet_shift_eq H 0 b b y
  simp only [sub_self, zero_mul, sub_zero] at h
  rw [h, Set.image_image]
  simp

/-- Miao, (17.3), p. 560: the problem (17.4) has a solution only if consumption can be
nonnegative at the debt limit, `−φ ≤ (1 + r)(−φ) + y(s)`, i.e. `rφ ≤ y(s)` for every state:
with `r > 0` the debt limit cannot exceed the natural borrowing limit `y_min/r`. -/
theorem bw_natural_limit {H : BWEconomy E} {r φ : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ}
    (h : H.Bellman r φ y V g) (s : E) : r * φ ≤ y s := by
  obtain ⟨hg, -⟩ := h (-φ) s le_rfl
  have h1 := hg.1.trans hg.2
  have : (1 + r) * -φ = -φ - r * φ := by ring
  linarith

/-- **Definition 17.2.1** (Miao, p. 570). A **stationary recursive competitive equilibrium** of
the Huggett economy with debt limit `φ`: a value function `V`, an asset policy `g`, a risk-free
rate `r` and a stationary probability measure `λ*` on `S = [−φ, ∞) × E` such that (i) `g` solves
the household's problem (17.4) and `V` is its value function, (ii) the asset market clears,
`∫ g dλ* = 0`, and (iii) `λ*` is stationary, (17.8). -/
structure BWHuggettEqm (H : BWEconomy E) (φ : ℝ) where
  V : ℝ → E → ℝ
  g : ℝ → E → ℝ
  r : ℝ
  lam : Measure (ℝ × E)
  isProb : IsProbabilityMeasure lam
  supp : lam {p | p.1 < -φ} = 0
  bellman : H.Bellman r φ H.e V g
  integrable : Integrable (fun p => g p.1 p.2) lam
  clear : ∫ p, g p.1 p.2 ∂lam = 0
  stationary : H.Stationary g lam

/-- **Definition 17.2.1** (Miao, pp. 570–571): `r` is a stationary equilibrium rate of the Huggett
economy with debt limit `φ` iff `0 ∈ Ea(r)`, i.e. the equilibrium rate is where the `Ea(r)` curve
meets the vertical axis (Figure 17.3). -/
theorem definition_17_2_1 (H : BWEconomy E) (φ r : ℝ) :
    (∃ eqm : BWHuggettEqm H φ, eqm.r = r) ↔ 0 ∈ H.EaSet r φ H.e := by
  constructor
  · rintro ⟨eqm, rfl⟩
    exact ⟨eqm.V, eqm.g, eqm.lam, eqm.isProb, eqm.supp, eqm.bellman, eqm.stationary,
      eqm.integrable, eqm.clear.symm⟩
  · rintro ⟨V, g, lam, hP, hsupp, hB, hS, hI, h0⟩
    exact ⟨⟨V, g, r, lam, hP, hsupp, hB, hI, h0.symm, hS⟩, rfl⟩

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.2.2–17.2.3: fiat money, interest on currency, Propositions 17.2.2 and 17.2.3 (i)

Miao, §17.2.2–17.2.3, pp. 572–577.

* Fiat money (§17.2.2): `bw_fiat_budget` (the mapping `m′/p = a′`, `w = 1`, `b = 0`, `r = 0`),
  `bw_fiat_quantity_theory` (`Ea(0) = M/p` determines `p = M/Ea(0)`, proportional to `M`),
  `bw_fiat_borrowing_raises_price` (with borrowing `b > 0`, `Ea(0; b) = Ea(0; 0) − b` and the
  price level rises), `bw_fiat_driven_out` (`b > Ea(0; 0)` gives `Ea(0; b) < 0`: no positive price
  level values fiat money).
* Explicit interest (§17.2.3): `eq_17_9`, `eq_17_10` (`τ = r̃M/p`), `bw_bewley_budget`,
  `bw_bewley_mapping` (`m′/p = â′`, `φ = M/p`, `r = r̃` maps the problem into (17.2));
  `BWBewleyEqm`: the stationary equilibrium with interest on currency financed by lump-sum taxes
  ((17.10), (17.11)); `eq_17_11` (market clearing `E m′/p = M/p` iff `Ea(r̃) = 0`).
* **Proposition 17.2.2** (`proposition_17_2_2`, `BWBewleyEqm.toHuggett`): a Bewley equilibrium
  has the allocation and interest rate of a Huggett equilibrium with `φ = M/p`.
* The back-solving method (`bw_backSolve`, `bw_backsolving`): from a Huggett equilibrium with
  limit `φ > 0` and any `M > 0`, `p = M/φ` and `τ = r̃M/p` give a Bewley equilibrium.
* `bw_bewley_real_balances_le`: real balances satisfy `r̃M/p ≤ e(s)` for every `s` (the largest
  supportable `M/p` is the natural limit `wl_min/r̃`).
* **Proposition 17.2.3**, first part (`proposition_17_2_3_rates`): the rates supportable by
  paying interest on currency are exactly the Huggett equilibrium rates for debt limits
  `0 < φ ≤ e_min/r̃`. The second part (the rate is below `1/β − 1`) is in `BWRate`.
* Implicit interest (`bw_implicit_*`): `1 + r = 1/(1 + g)`, `τ = (M_t/p_{t−1})r`, the budget is the
  Huggett budget with `φ = M_t/p_{t−1}`, money is retired at the rate `r/(1 + r)`.

**Departures.** (1) "The highest interest rate … equals that associated with the Huggett model
with the natural borrowing limit" relies on the `Ea(r)` curves shifting left as the limit rises
(Figure 17.3), a numerical finding; it is not proved. What is proved is the characterisation of
the supportable rates and the bound `φ ≤ e_min/r̃` (corrections).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-! ### §17.2.2 Fiat money -/

/-- Miao, p. 572: with `m_{t+1}/p = a_{t+1}`, `w = 1`, `b = 0` and `r = 0`, the budget
`m′/p + c = m/p + l` with `m′ ≥ 0` is (17.2), `c + a′ = (1 + r)a + wl`, `a′ ≥ −b`. -/
theorem bw_fiat_budget (m m' p c l : ℝ) :
    (m' / p + c = m / p + l ∧ 0 ≤ m' / p) ↔
      (c + m' / p = (1 + 0) * (m / p) + 1 * l ∧ -0 ≤ m' / p) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by linarith, by simpa using h2⟩

/-- Miao, p. 573 (the quantity theory of money): with `M > 0` and `Ea(0) > 0`, the market-clearing
condition `Ea(0) = M/p` determines the price level `p = M/Ea(0)`, proportional to `M`. -/
theorem bw_fiat_quantity_theory {M m p : ℝ} (hM : 0 < M) (hm : 0 < m) :
    (0 < p ∧ m = M / p) ↔ p = M / m := by
  constructor
  · rintro ⟨hp, rfl⟩; field_simp
  · rintro rfl; exact ⟨div_pos hM hm, by field_simp⟩

/-- Miao, p. 573: doubling (scaling) the money stock scales the price level `p = M/Ea(0)`. -/
theorem bw_fiat_neutral (M m k : ℝ) : (k * M) / m = k * (M / m) := by ring

/-- Miao, p. 573: permitting borrowing `b > 0` lowers `Ea(0)` by `b` (Proposition 17.2.1) and,
when fiat money is still valued, raises the price level `p = M/Ea(0; b)`. -/
theorem bw_fiat_borrowing_raises_price (H : BWEconomy E) {M m0 b : ℝ}
    (hm0 : m0 ∈ H.EaSet 0 0 H.e) (hM : 0 < M) (hb : 0 < b) (hpos : 0 < m0 - b) :
    m0 - b ∈ H.EaSet 0 b H.e ∧ M / m0 < M / (m0 - b) := by
  refine ⟨?_, div_lt_div_of_pos_left hM hpos (by linarith)⟩
  rw [proposition_17_2_1]
  exact ⟨m0, hm0, rfl⟩

/-- Miao, p. 573: if `b > Ea(0; 0)` then `Ea(0; b) < 0` (Proposition 17.2.1), so no positive price
level clears the money market: inside money drives fiat money out. -/
theorem bw_fiat_driven_out (H : BWEconomy E) {M m0 b : ℝ} (hm0 : m0 ∈ H.EaSet 0 0 H.e)
    (hM : 0 < M) (hb : m0 < b) :
    m0 - b ∈ H.EaSet 0 b H.e ∧ m0 - b < 0 ∧ ∀ p, 0 < p → M / p ≠ m0 - b := by
  refine ⟨?_, by linarith, fun p hp h => ?_⟩
  · rw [proposition_17_2_1]; exact ⟨m0, hm0, rfl⟩
  · have := div_pos hM hp; linarith

/-! ### §17.2.3 Interest on currency: explicit interest -/

/-- Miao, (17.9), p. 573: the government budget constraint `τp_t + M_{t+1} = M_t + r̃M_t`. -/
def eq_17_9 (τ p M M' rt : ℝ) : Prop := τ * p + M' = M + rt * M

/-- Miao, (17.10), p. 574: with a constant money stock `M_t = M_{t+1} = M` and price level `p > 0`,
(17.9) is equivalent to `τ = r̃M/p`. -/
theorem eq_17_10 {τ p M rt : ℝ} (hp : 0 < p) : eq_17_9 τ p M M rt ↔ τ = rt * M / p := by
  unfold eq_17_9
  constructor
  · intro h; field_simp; linarith
  · rintro rfl; field_simp; ring

/-- Miao, p. 574: substituting `τ = r̃M/p` into the household budget
`m′/p + c ≤ (1 + r̃)m/p + wl − τ`. -/
theorem bw_bewley_budget {m m' p c w l rt M τ : ℝ} (hτ : τ = rt * M / p) :
    (m' / p + c ≤ (1 + rt) * m / p + w * l - τ) ↔
      (m' / p + c ≤ (1 + rt) * m / p + w * l - rt * M / p) := by
  rw [hτ]

/-- Miao, pp. 574–575: with `â = m/p`, `â′ = m′/p ≥ 0`, `φ = M/p` and `r = r̃`, the Bewley budget
`c + â′ = (1 + r̃)â + wl − r̃φ` is the Huggett budget (17.2) `c + a′ = (1 + r)a + wl` in
`a = â − φ`, and `â′ ≥ 0` is `a′ ≥ −φ`. -/
theorem bw_bewley_mapping (q q' c w l rt φ : ℝ) :
    (c + q' = (1 + rt) * q + w * l - rt * φ ↔
      c + (q' - φ) = (1 + rt) * (q - φ) + w * l) ∧ (0 ≤ q' ↔ -φ ≤ q' - φ) := by
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- The **Bewley economy with interest on currency** (Miao, §17.2.3, pp. 573–575): a stationary
equilibrium with a constant money stock `M > 0`, a constant price level `p > 0`, nominal interest
`r̃` on currency financed by the lump-sum tax `τ = r̃M/p` (17.10), real balances `q = m/p ≥ 0`
with the policy `h(q, s) = m′/p`, the household's Bellman equation for
`c + q′ = (1 + r̃)q + e(s) − τ`, `q′ ≥ 0`, market clearing (17.11) `∫ h dλ = M/p` and a stationary
distribution `λ` on `[0, ∞) × E`. -/
structure BWBewleyEqm (H : BWEconomy E) where
  M : ℝ
  p : ℝ
  τ : ℝ
  rt : ℝ
  V : ℝ → E → ℝ
  h : ℝ → E → ℝ
  lam : Measure (ℝ × E)
  M_pos : 0 < M
  p_pos : 0 < p
  gov : τ = rt * M / p
  isProb : IsProbabilityMeasure lam
  supp : lam {q | q.1 < -0} = 0
  bellman : H.Bellman rt 0 (fun s => H.e s - τ) V h
  integrable : Integrable (fun q => h q.1 q.2) lam
  clear : ∫ q, h q.1 q.2 ∂lam = M / p
  stationary : H.Stationary h lam

/-- Miao, (17.11), p. 574 and p. 575: for a stationary `λ` on real balances, market clearing
`E m′/p = M/p` is equivalent to `Ea(r̃) = 0` for the Huggett distribution `λ` shifted by `−φ`,
`φ = M/p`. -/
theorem eq_17_11 {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {h : ℝ → E → ℝ}
    (hI : Integrable (fun q => h q.1 q.2) lam) (φ : ℝ) :
    ∫ q, h q.1 q.2 ∂lam = φ ↔
      ∫ p, (h (p.1 - -φ) p.2 + -φ) ∂(lam.map (bw_shift (-φ))) = 0 := by
  rw [bw_integral_shift hI]
  constructor <;> intro hh <;> linarith

/-- Real balances in a Bewley equilibrium: `φ = M/p > 0`. -/
theorem BWBewleyEqm.phi_pos {H : BWEconomy E} (B : BWBewleyEqm H) : 0 < B.M / B.p :=
  div_pos B.M_pos B.p_pos

/-- The tax in a Bewley equilibrium is `τ = r̃φ` with `φ = M/p`. -/
theorem BWBewleyEqm.tau_eq {H : BWEconomy E} (B : BWBewleyEqm H) : B.τ = B.rt * (B.M / B.p) := by
  rw [B.gov]; ring

/-- The Huggett equilibrium of **Proposition 17.2.2**: debt limit `φ = M/p`, rate `r̃`,
`V_H(a) = V(a + φ)`, `g(a) = h(a + φ) − φ`, distribution `λ` shifted by `−φ`. -/
noncomputable def BWBewleyEqm.toHuggett {H : BWEconomy E} (B : BWBewleyEqm H) :
    BWHuggettEqm H (B.M / B.p) where
  V := fun x s => B.V (x - -(B.M / B.p)) s
  g := fun x s => B.h (x - -(B.M / B.p)) s + -(B.M / B.p)
  r := B.rt
  lam := B.lam.map (bw_shift (-(B.M / B.p)))
  isProb := @bw_isProb_shift E _ _ B.isProb _
  supp := by
    have := @bw_supp_shift E _ B.lam 0 B.supp (-(B.M / B.p))
    simpa using this
  bellman := bw_bellman_shift B.bellman (by ring) (fun s => by rw [B.tau_eq]; ring)
  integrable := @bw_integrable_shift E _ B.lam B.isProb _ B.integrable _
  clear := by
    have := @bw_integral_shift E _ B.lam B.isProb _ B.integrable (-(B.M / B.p))
    rw [this, B.clear]; ring
  stationary := bw_stationary_shift B.stationary _

/-- **Proposition 17.2.2** (Miao, p. 575). A stationary equilibrium of the Bewley model with
interest on currency financed by lump-sum taxes has the same allocation and interest rate as an
equilibrium of Huggett's model with debt limit `φ = M/p`, the equilibrium real balances: the
rate is `r̃`, the asset policy is `g(q − φ) = h(q) − φ`, consumption agrees at corresponding
states, `c_H(q − φ, s) = c_B(q, s)`, and the distribution is that of real balances shifted
by `−φ`. -/
theorem proposition_17_2_2 {H : BWEconomy E} (B : BWBewleyEqm H) :
    B.toHuggett.r = B.rt ∧
    (∀ q s, B.toHuggett.g (q - B.M / B.p) s = B.h q s - B.M / B.p) ∧
    (∀ q s, (1 + B.toHuggett.r) * (q - B.M / B.p) + H.e s - B.toHuggett.g (q - B.M / B.p) s =
      (1 + B.rt) * q + (H.e s - B.τ) - B.h q s) ∧
    B.toHuggett.lam = B.lam.map (bw_shift (-(B.M / B.p))) := by
  refine ⟨rfl, fun q s => ?_, fun q s => ?_, rfl⟩
  · simp only [BWBewleyEqm.toHuggett, sub_neg_eq_add, sub_add_cancel]; ring
  · simp only [BWBewleyEqm.toHuggett, sub_neg_eq_add, sub_add_cancel]
    rw [B.tau_eq]; ring

/-- **The back-solving method** (Miao, p. 575, Steps 1–3): given a Huggett equilibrium with debt
limit `φ > 0` (Step 1 chooses `φ`; Step 2 is the Huggett equilibrium rate `r̃`, `Ea(r̃) = 0`) and a
money stock `M > 0`, set `p = M/φ` and `τ = r̃M/p` (Step 3). -/
noncomputable def bw_backSolve {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (hφ : 0 < φ)
    (M : ℝ) (hM : 0 < M) : BWBewleyEqm H where
  M := M
  p := M / φ
  τ := Q.r * M / (M / φ)
  rt := Q.r
  V := fun x s => Q.V (x - φ) s
  h := fun x s => Q.g (x - φ) s + φ
  lam := Q.lam.map (bw_shift φ)
  M_pos := hM
  p_pos := div_pos hM hφ
  gov := rfl
  isProb := @bw_isProb_shift E _ _ Q.isProb _
  supp := by
    have := @bw_supp_shift E _ Q.lam φ Q.supp φ
    simpa using this
  bellman := bw_bellman_shift Q.bellman (by ring) (fun s => by field_simp)
  integrable := @bw_integrable_shift E _ Q.lam Q.isProb _ Q.integrable _
  clear := by
    have := @bw_integral_shift E _ Q.lam Q.isProb _ Q.integrable φ
    rw [this, Q.clear, zero_add]; field_simp
  stationary := bw_stationary_shift Q.stationary _

/-- Miao, p. 575: the back-solved Bewley equilibrium has `p = M/φ`, `τ = r̃M/p = r̃φ`, the Huggett
rate `r̃`, and real balances `M/p = φ`. -/
theorem bw_backsolving {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (hφ : 0 < φ) (M : ℝ)
    (hM : 0 < M) :
    (bw_backSolve Q hφ M hM).p = M / φ ∧ (bw_backSolve Q hφ M hM).rt = Q.r ∧
      (bw_backSolve Q hφ M hM).τ = Q.r * φ ∧
      (bw_backSolve Q hφ M hM).M / (bw_backSolve Q hφ M hM).p = φ := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Q.r * M / (M / φ) = Q.r * φ; field_simp
  · change M / (M / φ) = φ; field_simp

/-- Miao, p. 575, Step 1: in a Bewley equilibrium the tax is payable in every state,
`τ = r̃M/p ≤ e(s)`; so real balances cannot exceed `e_min/r̃` when `r̃ > 0` ("the largest level of
real balances … is `wl_min/r̃`, the natural borrowing limit"). -/
theorem bw_bewley_real_balances_le {H : BWEconomy E} (B : BWBewleyEqm H) (s : E) :
    B.rt * (B.M / B.p) ≤ H.e s := by
  have := bw_natural_limit B.bellman s
  rw [B.tau_eq] at this
  linarith

/-- **Proposition 17.2.3**, first part (Miao, p. 576), in the precise form the argument gives: a
rate `r̃` is supported by paying interest on currency iff it is the equilibrium rate of the
Huggett economy for some debt limit `φ > 0`; any such `φ` satisfies `r̃φ ≤ e(s)` for all `s`
(it is at most the natural limit). -/
theorem proposition_17_2_3_rates (H : BWEconomy E) (r : ℝ) :
    (∃ B : BWBewleyEqm H, B.rt = r) ↔ ∃ φ, 0 < φ ∧ ∃ Q : BWHuggettEqm H φ, Q.r = r := by
  constructor
  · rintro ⟨B, rfl⟩; exact ⟨_, B.phi_pos, B.toHuggett, rfl⟩
  · rintro ⟨φ, hφ, Q, rfl⟩; exact ⟨bw_backSolve Q hφ 1 one_pos, rfl⟩

/-- Proposition 17.2.3 (support): a Huggett equilibrium with debt limit `φ > 0` has
`rφ ≤ e(s)` in every state. -/
theorem bw_huggett_limit_le_natural {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (s : E) :
    Q.r * φ ≤ H.e s :=
  bw_natural_limit Q.bellman s

/-! ### §17.2.3 Interest on currency: implicit interest -/

/-- Miao, p. 576: `M_{t+1} = M_t(1 + g)` is equivalent to
`M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t)(1 + g)`. -/
theorem bw_implicit_money {M M' p p₀ g : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) :
    M' = M * (1 + g) ↔ M' / p = M / p₀ * (p₀ / p) * (1 + g) := by
  constructor
  · rintro rfl; field_simp
  · intro h; field_simp at h; linarith

/-- Miao, p. 576: in a steady state with constant real balances `M_{t+1}/p_t = M_t/p_{t−1} > 0`
and `p_t/p_{t−1} = 1/(1 + r)`, `M_{t+1} = M_t(1 + g)` forces `1 + r = 1/(1 + g)`. -/
theorem bw_implicit_rate {M M' p p₀ g r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hM : 0 < M)
    (hg : M' = M * (1 + g)) (hreal : M' / p = M / p₀) (hinfl : p / p₀ = 1 / (1 + r)) :
    1 + r = 1 / (1 + g) := by
  have h1 : p₀ / p = 1 + r := by
    rw [← one_div_one_div (1 + r), ← hinfl]; field_simp
  have h2 := (bw_implicit_money hp hp₀).1 hg
  rw [hreal, h1] at h2
  have hM₀ : M / p₀ ≠ 0 := (div_pos hM hp₀).ne'
  have h3 : M / p₀ * ((1 + r) * (1 + g) - 1) = 0 := by linear_combination -h2
  have h4 : (1 + r) * (1 + g) = 1 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hM₀
    · linarith
  exact eq_one_div_of_mul_eq_one_left h4

/-- Miao, p. 576: by (17.9) with `r̃ = 0`, the lump-sum tax is `τ = −gM_t/p_t`, and with
`p_{t−1}/p_t = 1 + r`, `1 + g = 1/(1 + r)` it equals `(M_t/p_{t−1}) r`. -/
theorem bw_implicit_tax {τ M M' p p₀ g r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hr : 0 < 1 + r)
    (hgov : eq_17_9 τ p M M' 0) (hg : M' = M * (1 + g)) (hg' : 1 + g = 1 / (1 + r))
    (hinfl : p₀ / p = 1 + r) : τ = -(g * M / p) ∧ τ = M / p₀ * r := by
  unfold eq_17_9 at hgov
  have h1 : τ = -(g * M / p) := by
    rw [hg] at hgov; field_simp; linarith
  refine ⟨h1, ?_⟩
  have hg2 : g = -r / (1 + r) := by field_simp at hg' ⊢; linarith
  have hp' : p = p₀ / (1 + r) := by field_simp at hinfl ⊢; linarith
  rw [h1, hg2, hp']
  field_simp

/-- Miao, p. 576: with these taxes, the budget `m_{t+1}/p_t + c ≤ m_t/p_t + wl − (M_t/p_{t−1})r`
in the real balances `q_t = m_t/p_{t−1}` (so `m_t/p_t = (1 + r)q_t`) is the Bewley/Huggett budget
`c + q_{t+1} ≤ (1 + r)q_t + wl − rφ` with `φ = M_t/p_{t−1}`. -/
theorem bw_implicit_budget {m m' p p₀ c w l M r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀)
    (hinfl : p₀ / p = 1 + r) :
    (m' / p + c ≤ m / p + w * l - M / p₀ * r) ↔
      (c + m' / p ≤ (1 + r) * (m / p₀) + w * l - r * (M / p₀)) := by
  have this : m / p = (1 + r) * (m / p₀) := by
    rw [← hinfl]; field_simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- Miao, p. 577: for `r > 0` the government retires money at the rate `r/(1 + r)`,
`M_{t+1} − M_t = −(r/(1 + r))M_t`, and prices fall, `p_t/p_{t−1} = 1/(1 + r) < 1`. -/
theorem bw_implicit_deflation {M M' g r : ℝ} (hr : 0 < r) (hg : M' = M * (1 + g))
    (hg' : 1 + g = 1 / (1 + r)) : M' - M = -(r / (1 + r)) * M ∧ 1 / (1 + r) < 1 := by
  have hr1 : (0 : ℝ) < 1 + r := by linarith
  refine ⟨?_, by rw [div_lt_one hr1]; linarith⟩
  have hg2 : g = 1 / (1 + r) - 1 := by linarith
  rw [hg, hg2]; field_simp; ring

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A concrete endowment economy with valued fiat money (instances for §17.2)

Witnesses that Definition 17.2.1, the Bewley equilibrium with interest on currency
(`BWBewleyEqm`) and the fiat-money equilibrium of §17.2.2 are not vacuous.

The economy `bw_cycle`: the idiosyncratic state `s ∈ Bool` alternates deterministically
(`Q(·, s) = δ_{¬s}`, a two-state Markov chain), the endowment is `e(true) = 2`, `e(false) = 1`,
`β = 1/2` and `u(c) = min(c, 3/2)` (concave, nondecreasing, satiated at `3/2`). With `r = 0` and no
borrowing the household consumes `3/2` in the high state and saves the rest, and consumes up to
`3/2` in the low state:
`V(a, true) = 3`, `V(a, false) = min(a + 1, 3/2) + 3/2`,
`g(a, true) = a + 1/2`, `g(a, false) = a + 1 − min(a + 1, 3/2)` (`bw_cycle_bellman`).
The distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}` is stationary (`bw_cycle_stationary`) with
mean asset holdings `1/4` (`bw_cycle_mean`), so `1/4 ∈ Ea(0; 0)` (`bw_cycle_EaSet`).

* `bw_cycle_fiat`: fiat money is valued, `p = 4M` (§17.2.2).
* `bw_cycle_huggett`: a Huggett equilibrium (Definition 17.2.1) with debt limit `1/4` and `r = 0`,
  obtained from Proposition 17.2.1.
* `bw_cycle_bewley`: a Bewley equilibrium with interest on currency (back-solving).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The two-state cycle economy. -/
noncomputable def bw_cycle : BWEconomy Bool where
  β := 1 / 2
  u := fun c => min c (3 / 2)
  Q := Kernel.deterministic (fun s => !s) (Measurable.of_discrete)
  e := fun s => if s then 2 else 1

/-- The value function of the cycle economy. -/
noncomputable def bw_cycleV (a : ℝ) (s : Bool) : ℝ := if s then 3 else min (a + 1) (3 / 2) + 3 / 2

/-- The asset policy of the cycle economy. -/
noncomputable def bw_cycleG (a : ℝ) (s : Bool) : ℝ :=
  if s then a + 1 / 2 else a + 1 - min (a + 1) (3 / 2)

theorem bw_cycle_Q (s : Bool) : bw_cycle.Q s = Measure.dirac (!s) := by
  simp [bw_cycle, Kernel.deterministic_apply]

theorem bw_cycle_integral (f : Bool → ℝ) (s : Bool) : ∫ s', f s' ∂(bw_cycle.Q s) = f (!s) := by
  rw [bw_cycle_Q, integral_dirac]

/-- The household's problem (17.4) of the cycle economy at `r = 0`, `φ = 0`. -/
theorem bw_cycle_bellman : bw_cycle.Bellman 0 0 bw_cycle.e bw_cycleV bw_cycleG := by
  intro a s ha
  rw [neg_zero] at ha
  refine ⟨?_, fun a' _ => by rw [bw_cycle_Q]; exact Integrable.of_finite, ?_, fun a' ha' => ?_⟩
  · cases s <;> simp only [bw_cycleG, bw_cycle, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc,
      neg_zero]
    · have := min_le_left (a + 1) (3 / 2)
      have : 0 ≤ min (a + 1) (3 / 2) := le_min (by linarith) (by norm_num)
      constructor <;> linarith
    · constructor <;> linarith
  · rw [bw_cycle_integral]
    cases s <;> simp only [bw_cycleG, bw_cycleV, bw_cycle, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true]
    · have : (1 + 0) * a + 1 - (a + 1 - min (a + 1) (3 / 2)) = min (a + 1) (3 / 2) := by ring
      rw [this, min_eq_left (min_le_right _ _)]
      norm_num
    · have h1 : (1 + 0) * a + 2 - (a + 1 / 2) = 3 / 2 := by ring
      have h2 : min (a + 1 / 2 + 1) (3 / 2 : ℝ) = 3 / 2 := min_eq_right (by linarith)
      rw [h1, h2, min_self]
      norm_num
  · rw [bw_cycle_integral]
    obtain ⟨h0, h1⟩ := ha'
    rw [neg_zero] at h0
    cases s <;> simp only [bw_cycleV, bw_cycle, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true] at h1 ⊢
    · have : min ((1 + 0) * a + 1 - a') (3 / 2) ≤ min (a + 1) (3 / 2) :=
        min_le_min (by linarith) le_rfl
      linarith
    · have := min_le_right ((1 + 0) * a + 2 - a') (3 / 2 : ℝ)
      have := min_le_right (a' + 1) (3 / 2 : ℝ)
      linarith

/-- The stationary distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}` of the cycle economy. -/
noncomputable def bw_cycleLam : Measure (ℝ × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac ((0 : ℝ), true) + (2⁻¹ : ℝ≥0∞) • Measure.dirac ((1 / 2 : ℝ), false)

theorem bw_cycleLam_isProb : IsProbabilityMeasure bw_cycleLam :=
  ⟨by simp [bw_cycleLam, ENNReal.inv_two_add_inv_two]⟩

theorem bw_cycleLam_supp : bw_cycleLam {p | p.1 < -0} = 0 := by
  simp [bw_cycleLam, Measure.dirac_apply]

/-- (17.8) for the cycle economy. -/
theorem bw_cycle_stationary : bw_cycle.Stationary bw_cycleG bw_cycleLam := by
  intro A B _ _
  simp only [bw_cycleLam, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, bw_cycle_Q, smul_eq_mul]
  have g1 : bw_cycleG 0 true = 1 / 2 := by norm_num [bw_cycleG]
  have g2 : bw_cycleG (1 / 2) false = 0 := by
    simp only [bw_cycleG, Bool.false_eq_true, ↓reduceIte]
    rw [min_eq_right (by norm_num)]; norm_num
  rw [g1, g2]
  by_cases hA0 : (0 : ℝ) ∈ A <;> by_cases hA1 : (1 / 2 : ℝ) ∈ A <;>
    by_cases hBt : true ∈ B <;> by_cases hBf : false ∈ B <;>
    simp only [Set.indicator, Set.mem_prod, Bool.not_false, Bool.not_true, hA0, hA1, hBt, hBf] <;>
    simp [add_comm]

theorem bw_cycle_integrable : Integrable (fun p : ℝ × Bool => bw_cycleG p.1 p.2) bw_cycleLam :=
  ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

/-- Mean asset holdings (money demand) in the cycle economy: `∫ g dλ = 1/4`. -/
theorem bw_cycle_mean : ∫ p, bw_cycleG p.1 p.2 ∂bw_cycleLam = 1 / 4 := by
  rw [bw_cycleLam, integral_add_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  · have g2 : bw_cycleG (1 / 2) false = 0 := by
      simp only [bw_cycleG, Bool.false_eq_true, ↓reduceIte]
      rw [min_eq_right (by norm_num)]; norm_num
    simp only [g2]
    norm_num [bw_cycleG]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- `1/4 ∈ Ea(0; 0)` in the cycle economy. -/
theorem bw_cycle_EaSet : (1 / 4 : ℝ) ∈ bw_cycle.EaSet 0 0 bw_cycle.e :=
  ⟨bw_cycleV, bw_cycleG, bw_cycleLam, bw_cycleLam_isProb, bw_cycleLam_supp, bw_cycle_bellman,
    bw_cycle_stationary, bw_cycle_integrable, bw_cycle_mean.symm⟩

/-- §17.2.2 (Miao, pp. 572–573) is not vacuous: in the cycle economy fiat money is valued; for any
money stock `M > 0` the price level `p = 4M` clears the money market, `Ea(0) = M/p`. -/
theorem bw_cycle_fiat (M : ℝ) (hM : 0 < M) :
    0 < 4 * M ∧ (1 / 4 : ℝ) = M / (4 * M) ∧ (1 / 4 : ℝ) ∈ bw_cycle.EaSet 0 0 bw_cycle.e := by
  refine ⟨by linarith, ?_, bw_cycle_EaSet⟩
  field_simp

/-- Definition 17.2.1 is not vacuous: the cycle economy with debt limit `1/4` has a stationary
recursive competitive equilibrium with `r = 0` (from Proposition 17.2.1). -/
theorem bw_cycle_huggett : ∃ eqm : BWHuggettEqm bw_cycle (1 / 4), eqm.r = 0 := by
  rw [definition_17_2_1]
  have := bw_EaSet_shift (d := -(1 / 4)) (φ' := 1 / 4) (y' := bw_cycle.e) bw_cycle_EaSet
    (by ring) (fun s => by ring)
  norm_num at this
  exact this

/-- `BWBewleyEqm` is not vacuous: the cycle economy has a Bewley equilibrium with (zero) interest
on currency, by back-solving. -/
theorem bw_cycle_bewley : ∃ B : BWBewleyEqm bw_cycle, B.rt = 0 := by
  rw [proposition_17_2_3_rates]
  obtain ⟨eqm, h⟩ := bw_cycle_huggett
  exact ⟨1 / 4, by norm_num, eqm, h⟩

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Proposition 17.2.3: the equilibrium rate is below the rate of time preference

Miao, §17.1.1, p. 561, and §17.2.1–17.2.3, pp. 571, 575–576. "In Section 8.3.3, we have shown
that if `β(1 + r) ≥ 1`, `x_t` and `a_t` converge to infinity" (p. 561); hence the interest rate
of any stationary equilibrium, in particular the highest one, the natural-limit rate, is "lower
than `1/β − 1`" (p. 571) and "less than the rate of time preference" (Proposition 17.2.3).

We prove this in the setting in which the book's supporting results are stated: the
income-fluctuation problem of §8.3.2 in cash on hand (`SIModel`, `SIModel.Solution`; debt limit
`b`, iid income), where Ea is computed from a stationary distribution `λ` of cash on hand
`x_{t+1} = Râ(x_t) + y_{t+1} − rb` (`bw_cohStationary`, the form (17.7) of p. 562).

* `bw_coh_lintegral`, `bw_coh_integral`: stationarity of `λ` for sets gives
  `∫ f dλ = ∫∫ f(Râ(x) + y − rb) dμ(y) dλ(x)` for measurable (bounded) `f`.
* `proposition_17_2_3_lt`: **if income is not almost surely constant and cash on hand has a
  stationary distribution, then `βR < 1`**, i.e. `r < 1/β − 1`. The proof: the Euler inequality
  `u′(c(x)) ≥ βR E u′(c(x′))` integrated against `λ` gives `βR ≤ 1`; if `βR = 1`, `u′(c(x_t))` is a
  stationary bounded martingale, so `E(u′(c(x′)) − u′(c(x)))² = 0`; as `u′ ∘ c` is strictly
  decreasing, `x′ = x` almost surely, which forces income to be constant.

**Departures.** The book's argument is the divergence of `x_t` (Proposition 8.3.2, and the
case `βR = 1` of p. 258); we replace it by the stationary-martingale argument above, which
needs only the Euler inequality, stationarity and non-degenerate income (the book's divergence
statements are almost-sure path statements, not formalised in the copied §8.3.2).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Miao, (17.7), p. 562, for the cash-on-hand chain of §17.1.1 (iid income): `λ` is a
stationary distribution of `x_{t+1} = Râ(x_t) + y_{t+1} − rb`,
`λ(A) = ∫ μ{y : Râ(x) + y − rb ∈ A} dλ(x)` for every measurable `A`. -/
def bw_cohStationary {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : Prop :=
  ∀ A, MeasurableSet A → lam A = ∫⁻ x, M.law {y | M.next (S.sav x) y ∈ A} ∂lam

/-- The saving policy extended continuously below `x_min`. -/
theorem bw_savc_continuous {M : SIModel} (S : M.Solution) :
    Continuous fun x => S.sav (max x M.xmin) :=
  S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
    fun _ => Set.mem_Ici.2 (le_max_right _ _)

theorem bw_next_continuous {M : SIModel} (S : M.Solution) :
    Continuous fun p : ℝ × ℝ => M.next (S.sav (max p.1 M.xmin)) p.2 := by
  simp only [SIModel.next]
  exact ((continuous_const.mul ((bw_savc_continuous S).comp continuous_fst)).add
    continuous_snd).sub continuous_const

/-- `x ↦ ∫ f(Râ(x) + y − rb) dμ(y)` is strongly measurable for measurable `f`. -/
theorem bw_sm_integral {M : SIModel} (S : M.Solution) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law :=
  StronglyMeasurable.integral_prod_right
    (f := fun x y => f (M.next (S.sav (max x M.xmin)) y))
    (hf.comp (bw_next_continuous S).measurable).stronglyMeasurable

theorem bw_ae_ge {M : SIModel} {lam : Measure ℝ} (hsupp : lam (Set.Iio M.xmin) = 0) :
    ∀ᵐ x ∂lam, M.xmin ≤ x := by
  rw [ae_iff]
  convert hsupp using 2
  ext x
  simp [not_le]

/-- Stationarity for measurable `[0, ∞]`-valued functions:
`∫⁻ f dλ = ∫⁻∫⁻ f(Râ(x) + y − rb) dμ(y) dλ(x)`. -/
theorem bw_coh_lintegral {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂lam = ∫⁻ x, ∫⁻ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law ∂lam := by
  set F : ℝ → Measure ℝ := fun x => M.law.map fun y => M.next (S.sav (max x M.xmin)) y
  have hF : Measurable F := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : (fun x => F x A) = fun x =>
        M.law (Prod.mk x ⁻¹' {p : ℝ × ℝ | M.next (S.sav (max p.1 M.xmin)) p.2 ∈ A}) := by
      funext x
      simp only [F]
      rw [Measure.map_apply (M.continuous_next_y _).measurable hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left ((bw_next_continuous S).measurable hA)
  have hbind : lam = lam.bind F := by
    ext A hA
    rw [Measure.bind_apply hA hF.aemeasurable, hst A hA]
    refine lintegral_congr_ae ?_
    filter_upwards [bw_ae_ge hsupp] with x hx
    simp only [F, max_eq_left hx]
    rw [Measure.map_apply (M.continuous_next_y _).measurable hA]
    rfl
  calc ∫⁻ x, f x ∂lam = ∫⁻ x, f x ∂(lam.bind F) := by rw [← hbind]
    _ = ∫⁻ x, ∫⁻ y, f y ∂(F x) ∂lam := Measure.lintegral_bind hF.aemeasurable hf.aemeasurable
    _ = _ := lintegral_congr fun x => lintegral_map hf (M.continuous_next_y _).measurable

/-- Stationarity for bounded nonnegative measurable functions:
`∫ f dλ = ∫∫ f(Râ(x) + y − rb) dμ(y) dλ(x)`. -/
theorem bw_coh_integral {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    ∫ x, f x ∂lam = ∫ x, ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law ∂lam := by
  have hn := (bw_next_continuous S).measurable
  have hI : ∀ x, Integrable (fun y => f (M.next (S.sav (max x M.xmin)) y)) M.law := fun x =>
    Integrable.of_bound ((hf.comp ((bw_next_continuous S).comp
      (Continuous.prodMk_right x)).measurable).aestronglyMeasurable) C
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hC _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => integral_nonneg fun y => h0 _)
      (bw_sm_integral S hf).aestronglyMeasurable,
    bw_coh_lintegral S hsupp hst hf.ennreal_ofReal]
  congr 1
  refine lintegral_congr fun x => ?_
  exact (ofReal_integral_eq_lintegral_ofReal (hI x) (ae_of_all _ fun y => h0 _)).symm

/-- **Proposition 17.2.3**, second part (Miao, p. 576; also pp. 561, 571). In the income
fluctuation problem with iid income that is not almost surely constant, if cash on hand has a
stationary distribution `λ` on `[x_min, ∞)` (as any stationary equilibrium requires), then
`βR < 1`: the interest rate `r = R − 1` is below the rate of time preference `1/β − 1`. -/
theorem proposition_17_2_3_lt {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam)
    (hnd : ∀ c, ¬ ∀ᵐ y ∂M.law, y = c) : M.β * M.R < 1 := by
  by_contra hge
  have hge : 1 ≤ M.β * M.R := not_lt.1 hge
  set hf : ℝ → ℝ := fun x => M.du (S.cons (max x M.xmin)) with hhf
  have hcons : ∀ x, 0 < S.cons (max x M.xmin) := fun x => S.cons_pos (le_max_right _ _)
  have hcont : Continuous hf :=
    M.du_cont.comp_continuous (S.continuousOn_cons.comp_continuous
      (continuous_id.max continuous_const) fun x => Set.mem_Ici.2 (le_max_right _ _))
      fun x => Set.mem_Ioi.2 (hcons x)
  have hmeas : Measurable hf := hcont.measurable
  set C := M.du (S.cons M.xmin)
  have hpos : ∀ x, 0 < hf x := fun x => M.du_pos _ (hcons x)
  have hle : ∀ x, hf x ≤ C := fun x => by
    have h1 : S.cons M.xmin ≤ S.cons (max x M.xmin) :=
      S.cons_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)
    have h2 : 0 < S.cons M.xmin := by simpa using hcons M.xmin
    exact M.du_anti.antitoneOn (Set.mem_Ioi.2 h2) (Set.mem_Ioi.2 (hcons x)) h1
  set n : ℝ → ℝ → ℝ := fun x y => M.next (S.sav (max x M.xmin)) y with hn
  have hncont : Continuous fun p : ℝ × ℝ => n p.1 p.2 := bw_next_continuous S
  have hIy : ∀ {f : ℝ → ℝ}, Measurable f → ∀ {D : ℝ}, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ x, Integrable (fun y => f (n x y)) M.law := fun {f} hfm {D} h0 hD x =>
    Integrable.of_bound ((hfm.comp (hncont.comp (Continuous.prodMk_right x)).measurable
      ).aestronglyMeasurable) D
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hD _)
  set K : ℝ → ℝ := fun x => ∫ y, hf (n x y) ∂M.law with hK
  have hK0 : ∀ x, 0 ≤ K x := fun x => integral_nonneg fun y => (hpos _).le
  have hKC : ∀ x, K x ≤ C := fun x => by
    have : K x ≤ ∫ _y, C ∂M.law :=
      integral_mono (hIy hmeas (fun z => (hpos z).le) hle x) (integrable_const _) fun y => hle _
    simpa using this
  have hKm : StronglyMeasurable K := bw_sm_integral S hmeas
  have hbdd : ∀ {f : ℝ → ℝ}, StronglyMeasurable f → ∀ {D : ℝ}, (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ D) → Integrable f lam := fun {f} hfm {D} h0 hD =>
    Integrable.of_bound hfm.aestronglyMeasurable D
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hD _)
  have hIh : Integrable hf lam := hbdd hmeas.stronglyMeasurable (fun x => (hpos x).le) hle
  have hIK : Integrable K lam := hbdd hKm hK0 hKC
  -- the Euler inequality, almost everywhere
  have heuler : ∀ᵐ x ∂lam, M.β * M.R * K x ≤ hf x := by
    filter_upwards [bw_ae_ge hsupp] with x hx
    have hs0 := (S.sav_mem x hx).1
    have hE := S.euler_le hx
    rw [S.D_eq hs0] at hE
    have hKx : K x = ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law := by
      refine integral_congr_ae ?_
      filter_upwards [M.ae_next hs0] with y hy
      simp only [hn, hhf, max_eq_left hx, max_eq_left hy.1]
    simpa only [hKx, hhf, max_eq_left hx] using hE
  have hstat1 : ∫ x, hf x ∂lam = ∫ x, K x ∂lam :=
    bw_coh_integral S hsupp hst hmeas (fun x => (hpos x).le) hle
  have hIpos : 0 < ∫ x, hf x ∂lam := si_integral_pos hIh (ae_of_all _ hpos)
  have hmono : M.β * M.R * ∫ x, K x ∂lam ≤ ∫ x, hf x ∂lam := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hIK.const_mul _) hIh heuler
  have hβR : M.β * M.R = 1 := by
    refine le_antisymm ?_ hge
    rw [← hstat1] at hmono
    by_contra hlt
    have := mul_lt_mul_of_pos_right (not_le.1 hlt) hIpos
    linarith
  -- `K = h` almost everywhere
  have hKh : ∀ᵐ x ∂lam, K x = hf x := by
    have hnn : 0 ≤ᵐ[lam] fun x => hf x - K x := by
      filter_upwards [heuler] with x hx
      rw [hβR, one_mul] at hx
      simp only [Pi.zero_apply]; linarith
    have hint : ∫ x, (hf x - K x) ∂lam = 0 := by
      rw [integral_sub hIh hIK, hstat1, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hIh.sub hIK)).1 hint
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- the stationary martingale has zero increments in `L²`
  have hmeas2 : Measurable fun x => hf x ^ 2 := hmeas.pow_const 2
  have h20 : ∀ x, 0 ≤ hf x ^ 2 := fun x => sq_nonneg _
  have h2C : ∀ x, hf x ^ 2 ≤ C ^ 2 := fun x =>
    pow_le_pow_left₀ (hpos x).le (hle x) 2
  set K2 : ℝ → ℝ := fun x => ∫ y, hf (n x y) ^ 2 ∂M.law with hK2
  have hstat2 : ∫ x, hf x ^ 2 ∂lam = ∫ x, K2 x ∂lam :=
    bw_coh_integral S hsupp hst hmeas2 h20 h2C
  have hK20 : ∀ x, 0 ≤ K2 x := fun x => integral_nonneg fun y => h20 _
  have hK2C : ∀ x, K2 x ≤ C ^ 2 := fun x => by
    have : K2 x ≤ ∫ _y, C ^ 2 ∂M.law :=
      integral_mono (hIy hmeas2 h20 h2C x) (integrable_const _) fun y => h2C _
    simpa using this
  have hIK2 : Integrable K2 lam := hbdd (bw_sm_integral S hmeas2) hK20 hK2C
  have hIh2 : Integrable (fun x => hf x ^ 2) lam := hbdd hmeas2.stronglyMeasurable h20 h2C
  set J : ℝ → ℝ := fun x => ∫ y, (hf (n x y) - hf x) ^ 2 ∂M.law with hJ
  have hJeq : ∀ x, J x = K2 x - 2 * hf x * K x + hf x ^ 2 := fun x => by
    have i1 := hIy hmeas2 h20 h2C x
    have i2 := hIy hmeas (fun z => (hpos z).le) hle x
    have : (fun y => (hf (n x y) - hf x) ^ 2) =
        fun y => hf (n x y) ^ 2 - 2 * hf x * hf (n x y) + hf x ^ 2 := by
      funext y; ring
    simp only [hJ, this]
    rw [integral_add (f := fun y => hf (n x y) ^ 2 - 2 * hf x * hf (n x y))
      (g := fun _ => hf x ^ 2) (i1.sub (i2.const_mul _)) (integrable_const _),
      integral_sub (f := fun y => hf (n x y) ^ 2) (g := fun y => 2 * hf x * hf (n x y)) i1
        (i2.const_mul _), integral_const_mul]
    simp
    rfl
  have hJae : J =ᵐ[lam] fun x => K2 x - hf x ^ 2 := by
    filter_upwards [hKh] with x hx
    rw [hJeq, hx]; ring
  have hJ0 : ∀ x, 0 ≤ J x := fun x => integral_nonneg fun y => sq_nonneg _
  have hIJ : Integrable J lam := (hIK2.sub hIh2).congr hJae.symm
  have hintJ : ∫ x, J x ∂lam = 0 := by
    rw [integral_congr_ae hJae, integral_sub hIK2 hIh2, hstat2, sub_self]
  have hJz := (integral_eq_zero_iff_of_nonneg (fun x => hJ0 x) hIJ).1 hintJ
  have hne : (ae lam).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero lam)
  obtain ⟨x, hx0, hx⟩ := (hJz.and (bw_ae_ge hsupp)).exists
  simp only [Pi.zero_apply] at hx0
  have hs0 := (S.sav_mem x hx).1
  have hy0 := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (hf (n x y) - hf x))
    ((hIy hmeas2 h20 h2C x).sub ((hIy hmeas (fun z => (hpos z).le) hle x).const_mul (2 * hf x))
      |>.add (integrable_const (hf x ^ 2)) |>.congr (ae_of_all _ fun y => by
        simp only [Pi.add_apply, Pi.sub_apply]; ring))).1 hx0
  -- `u′ ∘ c` is strictly decreasing, so `x′ = x` almost surely
  have hanti : StrictAntiOn hf (Set.Ici M.xmin) := by
    intro u hu v hv huv
    simp only [hhf, max_eq_left (Set.mem_Ici.1 hu), max_eq_left (Set.mem_Ici.1 hv)]
    exact M.du_anti (Set.mem_Ioi.2 (S.cons_pos hu)) (Set.mem_Ioi.2 (S.cons_pos hv))
      (S.lemma_8_3_1.1 hu hv huv)
  apply hnd (x - M.R * S.sav x + M.r * M.b)
  filter_upwards [hy0, M.ae_next hs0] with y hy hyn
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    sub_eq_zero] at hy
  have hnx : n x y = M.next (S.sav x) y := by simp only [hn, max_eq_left hx]
  rw [hnx] at hy
  have := hanti.injOn (Set.mem_Ici.2 hyn.1) (Set.mem_Ici.2 hx) hy
  simp only [SIModel.next] at this
  linarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.2.4: seigniorage

Miao, §17.2.4, pp. 577–579. No taxes, no borrowing (`φ = b = 0`); the government finances real
purchases `G` by printing money, `M_{t+1}/p_t = M_t/p_t + G`.

* `bw_seign_budget`: the budget in the form `M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t) + G`.
* `bw_seign_mbar`: in a stationary equilibrium with `p_{t−1}/p_t = 1 + r` and `M_{t+1}/p_t = m̄`,
  `m̄ = −G/r`; `bw_seign_neg_rate`: with `G > 0` and valued money `m̄ > 0`, `r < 0` (the inflation
  tax `−r`), and the curve `m̄ = −G/r` lies in the south-east quadrant.
* `bw_seign_initial_price`, `bw_seign_quantity_theory`: `m̄ = M₀/p₀ + G` determines
  `p₀ = M₀/(m̄ − G)`; scaling `M₀` scales `p₀` and all later prices `p_t = p₀(1 + r)^{−t}`.
* `bw_seign_comparative_statics`: the selection by the highest return on currency gives the
  standard comparative statics. If `Ea` is continuous on `[r₂, 0]` and `r₂ < 0` is an equilibrium
  for the deficit `G₂`, then for every smaller deficit `0 < G₁ < G₂` there is an equilibrium
  `r₁ ∈ (r₂, 0)`; so raising `G` lowers the highest equilibrium return and raises inflation.

Multiplicity of stationary equilibria (Figure 17.4) and the effects of `b > 0` (the `Ea` curve
shifting left, possibly eliminating all equilibria) are read from figures and not formalised.
-/

namespace Miao.IncompleteMarkets

/-- Miao, p. 577: the government budget `M_{t+1}/p_t = M_t/p_t + G` written as
`M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t) + G`. -/
theorem bw_seign_budget {M M' p p₀ G : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) :
    M' / p = M / p + G ↔ M' / p = M / p₀ * (p₀ / p) + G := by
  have : M / p₀ * (p₀ / p) = M / p := by field_simp
  rw [this]

/-- Miao, p. 577: in a stationary equilibrium with `p_{t−1}/p_t = 1 + r` and constant real
balances `M_{t+1}/p_t = m̄`, the budget `m̄ = m̄(1 + r) + G` gives `m̄ = −G/r` (`r ≠ 0`). -/
theorem bw_seign_mbar {mbar r G : ℝ} (hst : mbar = mbar * (1 + r) + G) (hr : r ≠ 0) :
    mbar = -G / r := by
  field_simp
  linarith

/-- Miao, p. 577: for `G > 0` a stationary equilibrium with valued money `m̄ > 0` has `r ≠ 0` and
`r < 0` ("`−r` can be regarded as an inflation tax"); conversely each `r < 0` gives a point
`(m̄, r) = (−G/r, r)` in the south-east quadrant. -/
theorem bw_seign_neg_rate {mbar r G : ℝ} (hG : 0 < G) (hst : mbar = mbar * (1 + r) + G)
    (hm : 0 < mbar) : r < 0 ∧ mbar = -G / r := by
  have hmr : mbar * r = -G := by linarith
  have hr : r < 0 := by
    by_contra h
    have := mul_nonneg hm.le (not_lt.1 h)
    linarith
  exact ⟨hr, bw_seign_mbar hst hr.ne⟩

/-- Miao, p. 577: the curve `m̄ = −G/r` lies in the south-east quadrant for `G > 0`, `r < 0`. -/
theorem bw_seign_hyperbola {r G : ℝ} (hG : 0 < G) (hr : r < 0) : 0 < -G / r :=
  div_pos_of_neg_of_neg (by linarith) hr

/-- Miao, pp. 577–578: the initial government budget `m̄ = M₀/p₀ + G` (with `m̄ > G`) determines
`p₀ = M₀/(m̄ − G)`. -/
theorem bw_seign_initial_price {mbar M₀ p₀ G : ℝ} (hp₀ : 0 < p₀) (hm : G < mbar) :
    mbar = M₀ / p₀ + G ↔ p₀ = M₀ / (mbar - G) := by
  have h : mbar - G ≠ 0 := by linarith
  constructor
  · intro h1
    have h2 : M₀ / p₀ = mbar - G := by linarith
    rw [eq_div_iff h, ← h2]
    field_simp
  · intro h1
    have hM : M₀ ≠ 0 := by
      rintro rfl
      rw [zero_div] at h1
      linarith
    rw [h1]
    field_simp
    ring

/-- Miao, p. 578 (a version of the quantity theory): with `p_{t−1}/p_t = 1 + r`,
`p_t = p₀(1 + r)^{−t}`; an increase of `M₀` by the factor `k` increases `p₀` and all subsequent
prices proportionately. -/
theorem bw_seign_quantity_theory (mbar M₀ G k r : ℝ) (t : ℕ) :
    k * M₀ / (mbar - G) / (1 + r) ^ t = k * (M₀ / (mbar - G) / (1 + r) ^ t) := by
  ring

/-- Miao, p. 578: **the comparative statics of the highest-return selection**. Let `Ea` be
continuous on `[r₂, 0]` and `r₂ < 0` a stationary equilibrium for the deficit `G₂`,
`Ea(r₂) = −G₂/r₂`. Then for every deficit `0 < G₁ < G₂` there is an equilibrium `r₁ ∈ (r₂, 0)`,
`Ea(r₁) = −G₁/r₁`. Hence the highest equilibrium return falls when `G` rises. -/
theorem bw_seign_comparative_statics {Ea : ℝ → ℝ} {r₂ G₁ G₂ : ℝ} (hr₂ : r₂ < 0)
    (hEa : ContinuousOn Ea (Set.Icc r₂ 0)) (heq : Ea r₂ = -G₂ / r₂) (hG₁ : 0 < G₁)
    (hG : G₁ < G₂) : ∃ r₁, r₂ < r₁ ∧ r₁ < 0 ∧ Ea r₁ = -G₁ / r₁ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := r₂) (b := 0)).exists_bound_of_continuousOn hEa
  set B' := max B 0
  set c := max (r₂ / 2) (-G₁ / (2 * (B' + 1)))
  have hB' : 0 ≤ B' := le_max_right _ _
  have hc0 : c < 0 := max_lt (by linarith) (div_neg_of_neg_of_pos (by linarith) (by linarith))
  have hrc : r₂ < c := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set f : ℝ → ℝ := fun r => Ea r + G₁ / r
  have hfc : ContinuousOn f (Set.Icc r₂ c) := by
    refine (hEa.mono (Set.Icc_subset_Icc le_rfl hc0.le)).add ?_
    exact continuousOn_const.div continuousOn_id fun r hr => (hr.2.trans_lt hc0).ne
  have hf2 : 0 < f r₂ := by
    simp only [f, heq]
    rw [← add_div]
    exact div_pos_of_neg_of_neg (by linarith) hr₂
  have hfcneg : f c < 0 := by
    have hEc : Ea c ≤ B' := by
      have := hB c ⟨hrc.le, hc0.le⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hge : -G₁ / (2 * (B' + 1)) ≤ c := le_max_right _ _
    have hdiv : G₁ / c ≤ -(2 * (B' + 1)) := by
      rw [div_le_iff_of_neg hc0]
      have h1 : -G₁ ≤ c * (2 * (B' + 1)) := by
        rwa [div_le_iff₀ (by linarith)] at hge
      linarith
    simp only [f]
    linarith
  obtain ⟨r₁, hr₁, hf1⟩ :=
    intermediate_value_Icc' hrc.le hfc ⟨hfcneg.le, hf2.le⟩
  have hne : r₁ ≠ r₂ := by rintro rfl; linarith
  refine ⟨r₁, lt_of_le_of_ne hr₁.1 hne.symm, hr₁.2.trans_lt hc0, ?_⟩
  simp only [f] at hf1
  have hr0 : r₁ ≠ 0 := (hr₁.2.trans_lt hc0).ne
  rw [neg_div]
  linarith

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.3.1: recursive competitive equilibrium with aggregate shocks (Definition 17.3.1)

Miao, §17.3.1, pp. 579–581. The Aiyagari economy with aggregate productivity `z`:
`Y = zF(K, L)`, the joint process `(z_t, l_t)` is Markov with transition `Q(·, ·; z, l)` (a kernel
on `Z × L`), the individual state is `(a, l)` and the aggregate state is `(λ, z)`, `λ` a measure
on `ℝ × L`.

* `BWAggEconomy`: the primitives, with `F_K`, `F_L` the partial derivatives of `F`, and the
  marginal transition `π(z′ | z) = Q({z′} × L; z, l)` of the aggregate shock, which is required not
  to depend on `l` (the aggregate shock is an exogenous Markov chain).
* `BWAggEconomy.Bellman`: condition (i), the household's Bellman equation with `λ′ = G(λ, z; z′)`.
* `BWRecEqm`: **Definition 17.3.1**, (i) the Bellman equation, (ii) the firm's first-order
  conditions `zF_K(K, L) = r + δ`, `zF_L(K, L) = w`, (iii) market clearing `K = ∫ a dλ`,
  `L = ∫ l dλ` (built into `bw_aggK`, `bw_aggL`), (iv) the law of motion
  `π(z′|z) G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) dλ` (corrected, see below).
* `bw_book_law_mass`, `bw_book_law_not_prob`: **the book's (iv) as printed**,
  `G(λ, z; z′)(A × B) = ∫ 1_A(g) Q(z′, B; z, l) dλ`, gives `G(λ, z; z′)` total mass
  `π(z′|z)`; so `G`
  is not a probability measure whenever `π(z′|z) < 1`. The corrected law divides by `π(z′|z)`
  (`bw_law_isProb`: then `G(λ, z; z′)` has mass one).
* `bw_law_indep`: with independent shocks, `Q(z′, B; z, l) = π(z′|z)Q_l(B, l)`, the law of motion
  does not depend on `z′` (Miao, p. 580).
* `bw_next_capital_indep`: tomorrow's capital `K′ = ∫ a dG(λ, z; z′)` never depends on `z′`
  ("capital is predetermined", p. 582), with or without independence.
* `bw_sequential_of_recursive`: a recursive equilibrium induces a sequential competitive
  equilibrium (p. 580): prices `w_t = z_tF_L(K_t, L_t)`, `r_t = z_tF_K(K_t, L_t) − δ`,
  `λ_{t+1} = G(λ_t, z_t; z_{t+1})`, and feasible individual
  choices `a_{t+1} = g(a_t, l_t; λ_t, z_t)`.
* `bw_recEqm_example`: a concrete recursive equilibrium (linear technology, linear utility,
  `β(1 + r) = 1`), so Definition 17.3.1 is not vacuous.

The existence of a recursive equilibrium in general is "an open question" (p. 581); Miao (2006)
and Kubler–Schmedders (2002) are cited, not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **Aiyagari economy with aggregate shocks** (Miao, §17.3.1, p. 579). -/
structure BWAggEconomy (Z L : Type*) [MeasurableSpace Z] [MeasurableSpace L] where
  β : ℝ
  u : ℝ → ℝ
  F : ℝ → ℝ → ℝ
  FK : ℝ → ℝ → ℝ
  FL : ℝ → ℝ → ℝ
  δ : ℝ
  zval : Z → ℝ
  lab : L → ℝ
  Q : Kernel (Z × L) (Z × L)
  πz : Z → Z → ℝ≥0∞
  hasDerivAt_K : ∀ K Lb, HasDerivAt (fun k => F k Lb) (FK K Lb) K
  hasDerivAt_L : ∀ K Lb, HasDerivAt (fun l => F K l) (FL K Lb) Lb
  marg : ∀ z l z', Q (z, l) ({z'} ×ˢ Set.univ) = πz z z'

variable {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L]

/-- Aggregate capital `K = ∫ a dλ` (Definition 17.3.1 (iii)). -/
noncomputable def bw_aggK (lam : Measure (ℝ × L)) : ℝ := ∫ p, p.1 ∂lam

/-- Aggregate labour `L = ∫ l dλ` (Definition 17.3.1 (iii)). -/
noncomputable def bw_aggL (lab : L → ℝ) (lam : Measure (ℝ × L)) : ℝ := ∫ p, lab p.2 ∂lam

namespace BWAggEconomy

/-- Definition 17.3.1 (i) (Miao, pp. 579–580): given `G`, `r`, `w`, the functions `g` and `V`
solve `V(a, l; λ, z) = max_{a′} u(c) + β ∫ V(a′, l′; λ′, z′) Q(dz′, dl′; z, l)` subject to
`c + a′ = (1 + r(λ, z))a + w(λ, z)l`, `a′ ≥ 0`, `c ≥ 0`, `λ′ = G(λ, z; z′)`. -/
def Bellman (A : BWAggEconomy Z L) (V g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) (r w : Measure (ℝ × L) → Z → ℝ) : Prop :=
  ∀ a l lam z, 0 ≤ a →
    g a l lam z ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l) ∧
    (∀ a', 0 ≤ a' → Integrable (fun p : Z × L => V a' p.2 (G lam z p.1) p.1) (A.Q (z, l))) ∧
    V a l lam z = A.u ((1 + r lam z) * a + w lam z * A.lab l - g a l lam z) +
      A.β * ∫ p, V (g a l lam z) p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ∧
    ∀ a' ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l),
      A.u ((1 + r lam z) * a + w lam z * A.lab l - a') +
        A.β * ∫ p, V a' p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ≤ V a l lam z

/-- Definition 17.3.1 (iv) **as printed** (Miao, p. 580):
`G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) λ(da, dl)`. -/
def BookLaw (A : BWAggEconomy Z L) (g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) : Prop :=
  ∀ lam z z' (S : Set ℝ) (B : Set L), MeasurableSet S → MeasurableSet B →
    G lam z z' (S ×ˢ B) =
      ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * A.Q (z, p.2) ({z'} ×ˢ B) ∂lam

/-- Definition 17.3.1 (iv), corrected: the distribution tomorrow conditional on `z′`,
`π(z′|z) G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) λ(da, dl)`. -/
def Law (A : BWAggEconomy Z L) (g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) : Prop :=
  ∀ lam z z' (S : Set ℝ) (B : Set L), MeasurableSet S → MeasurableSet B →
    G lam z z' (S ×ˢ B) * A.πz z z' =
      ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * A.Q (z, p.2) ({z'} ×ˢ B) ∂lam

end BWAggEconomy

/-- **Definition 17.3.1** (Miao, pp. 579–580). A **recursive competitive equilibrium** with
aggregate shocks: a value function `V(a, l; λ, z)`, a policy `g(a, l; λ, z)`, a law of motion
`G(λ, z; z′)` and pricing functions `r(λ, z)`, `w(λ, z)` such that (i) `g`, `V` solve the Bellman
equation, (ii) firms maximise profits, `zF_K(K, L) = r(λ, z) + δ`, `zF_L(K, L) = w(λ, z)`,
(iii) markets clear, `K = ∫ a dλ`, `L = ∫ l dλ`, and (iv) `G` is generated by `g` (corrected
form `BWAggEconomy.Law`). -/
structure BWRecEqm (A : BWAggEconomy Z L) where
  V : ℝ → L → Measure (ℝ × L) → Z → ℝ
  g : ℝ → L → Measure (ℝ × L) → Z → ℝ
  G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)
  r : Measure (ℝ × L) → Z → ℝ
  w : Measure (ℝ × L) → Z → ℝ
  bellman : A.Bellman V g G r w
  firmK : ∀ lam z, A.zval z * A.FK (bw_aggK lam) (bw_aggL A.lab lam) = r lam z + A.δ
  firmL : ∀ lam z, A.zval z * A.FL (bw_aggK lam) (bw_aggL A.lab lam) = w lam z
  law : A.Law g G

/-- **Correction to Definition 17.3.1 (iv).** Under the book's law of motion as printed, for a
probability measure `λ`, `G(λ, z; z′)` has total mass `π(z′|z)`. -/
theorem bw_book_law_mass {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.BookLaw g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] (z z' : Z) :
    G lam z z' Set.univ = A.πz z z' := by
  have h := hG lam z z' Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [Set.univ_prod_univ] at h
  rw [h]
  simp [A.marg]

/-- **Counterexample to Definition 17.3.1 (iv) as printed.** Whenever the aggregate shock moves
to `z′` with probability `π(z′|z) < 1`, the book's `G(λ, z; z′)` is not a probability measure. -/
theorem bw_book_law_not_prob {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.BookLaw g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] {z z' : Z} (hz : A.πz z z' < 1) :
    ¬ IsProbabilityMeasure (G lam z z') := by
  intro hP
  have := bw_book_law_mass hG lam z z'
  rw [measure_univ] at this
  rw [← this] at hz
  exact lt_irrefl _ hz

/-- With the corrected law (iv), `G(λ, z; z′)` is a probability measure whenever
`0 < π(z′|z) < ∞` and `λ` is. -/
theorem bw_law_isProb {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] {z z' : Z} (h0 : A.πz z z' ≠ 0)
    (htop : A.πz z z' ≠ ∞) : G lam z z' Set.univ = 1 := by
  have h := hG lam z z' Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [Set.univ_prod_univ] at h
  simp only [Set.indicator_univ, Pi.one_apply, one_mul, A.marg, lintegral_const,
    measure_univ, mul_one] at h
  have := (ENNReal.mul_left_inj h0 htop).1 (h.trans (one_mul _).symm)
  exact this

/-- The corrected law (iv) with `0 < π(z′|z) < ∞` gives the a-marginal of tomorrow's distribution,
`G(λ, z; z′)(A × L) = ∫ 1_A(g) dλ`, which does not involve `z′`. -/
theorem bw_law_marginal {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) {z z' : Z} (h0 : A.πz z z' ≠ 0) (htop : A.πz z z' ≠ ∞) {S : Set ℝ}
    (hS : MeasurableSet S) :
    G lam z z' (S ×ˢ Set.univ) = ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) ∂lam := by
  have h := hG lam z z' S Set.univ hS MeasurableSet.univ
  simp only [A.marg] at h
  rw [lintegral_mul_const' _ _ htop] at h
  exact (ENNReal.mul_left_inj h0 htop).1 h

/-- Miao, p. 582: **capital is predetermined**. Tomorrow's aggregate capital
`K′ = ∫ a dG(λ, z; z′)` is the same for all `z′` with `0 < π(z′|z) < ∞`, so the law of motion of
`K` does not depend on `z′`. -/
theorem bw_next_capital_indep {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) {z z₁ z₂ : Z} (h1 : A.πz z z₁ ≠ 0) (h1' : A.πz z z₁ ≠ ∞)
    (h2 : A.πz z z₂ ≠ 0) (h2' : A.πz z z₂ ≠ ∞) :
    (G lam z z₁).map Prod.fst = (G lam z z₂).map Prod.fst ∧
      bw_aggK (G lam z z₁) = bw_aggK (G lam z z₂) := by
  have hmap : (G lam z z₁).map Prod.fst = (G lam z z₂).map Prod.fst := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS, Measure.map_apply measurable_fst hS,
      ← Set.prod_univ, bw_law_marginal hG lam h1 h1' hS, bw_law_marginal hG lam h2 h2' hS]
  refine ⟨hmap, ?_⟩
  have e : ∀ m : Measure (ℝ × L), bw_aggK m = ∫ x, x ∂(m.map Prod.fst) := fun m =>
    (integral_map (f := fun x : ℝ => x) measurable_fst.aemeasurable
      aestronglyMeasurable_id).symm
  rw [e, e, hmap]

/-- Miao, p. 580: if the aggregate and the idiosyncratic shocks are independent,
`Q(z′, B; z, l) = π(z′|z) Q_l(B, l)`, then the law of motion does not depend on `z′`:
`G(λ, z; z′)(A × B) = ∫ 1_A(g) Q_l(B, l) dλ` for every `z′` with `0 < π(z′|z) < ∞`. -/
theorem bw_law_indep {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G) (Ql : Kernel L L)
    (hind : ∀ z l z' B, A.Q (z, l) ({z'} ×ˢ B) = A.πz z z' * Ql l B)
    (lam : Measure (ℝ × L)) {z z' : Z} (h0 : A.πz z z' ≠ 0) (htop : A.πz z z' ≠ ∞) {S : Set ℝ}
    {B : Set L} (hS : MeasurableSet S) (hB : MeasurableSet B) :
    G lam z z' (S ×ˢ B) = ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * Ql p.2 B ∂lam := by
  have h := hG lam z z' S B hS hB
  simp only [hind] at h
  have : (fun p : ℝ × L => S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * (A.πz z z' * Ql p.2 B))
      = fun p => (S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * Ql p.2 B) * A.πz z z' := by
    funext p; ring
  rw [this, lintegral_mul_const' _ _ htop] at h
  exact (ENNReal.mul_left_inj h0 htop).1 h

/-- The path of distributions `λ_{t+1} = G(λ_t, z_t; z_{t+1})` generated by a recursive equilibrium
along the aggregate shock path `z`. -/
noncomputable def bw_distPath {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z)
    (lam₀ : Measure (ℝ × L)) : ℕ → Measure (ℝ × L)
  | 0 => lam₀
  | t + 1 => E.G (bw_distPath E zs lam₀ t) (zs t) (zs (t + 1))

/-- An individual's asset path `a_{t+1} = g(a_t, l_t; λ_t, z_t)`. -/
noncomputable def bw_assetPath {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z) (ls : ℕ → L)
    (lam₀ : Measure (ℝ × L)) (a₀ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => E.g (bw_assetPath E zs ls lam₀ a₀ t) (ls t) (bw_distPath E zs lam₀ t) (zs t)

/-- Miao, pp. 580–581: **a recursive equilibrium induces a sequential competitive equilibrium**.
Along any shock path, with `λ_t` the distribution path and `K_t = ∫ a dλ_t`, `L_t = ∫ l dλ_t`:
`w_t = z_tF_L(K_t, L_t)`, `r_t = z_tF_K(K_t, L_t) − δ`, `λ_{t+1} = G(λ_t, z_t; z_{t+1})`; and an
individual starting from `a₀ ≥ 0` has `a_t ≥ 0`, nonnegative consumption
`c_t = (1 + r_t)a_t + w_tl_t − a_{t+1} ≥ 0`, and `a_{t+1} = g(a_t, l_t; λ_t, z_t)` attains the
Bellman equation at each date. -/
theorem bw_sequential_of_recursive {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z)
    (ls : ℕ → L) (lam₀ : Measure (ℝ × L)) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (t : ℕ) :
    let lam := bw_distPath E zs lam₀
    let a := bw_assetPath E zs ls lam₀ a₀
    E.w (lam t) (zs t) = A.zval (zs t) * A.FL (bw_aggK (lam t)) (bw_aggL A.lab (lam t)) ∧
    E.r (lam t) (zs t) = A.zval (zs t) * A.FK (bw_aggK (lam t)) (bw_aggL A.lab (lam t)) - A.δ ∧
    lam (t + 1) = E.G (lam t) (zs t) (zs (t + 1)) ∧
    0 ≤ a t ∧ a (t + 1) = E.g (a t) (ls t) (lam t) (zs t) ∧
    0 ≤ (1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) - a (t + 1) ∧
    E.V (a t) (ls t) (lam t) (zs t) =
      A.u ((1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) - a (t + 1)) +
        A.β * ∫ p, E.V (a (t + 1)) p.2 (E.G (lam t) (zs t) p.1) p.1 ∂(A.Q (zs t, ls t)) := by
  intro lam a
  have hnn : ∀ s, 0 ≤ a s := by
    intro s
    induction s with
    | zero => exact ha₀
    | succ s ih => exact ((E.bellman _ (ls s) (lam s) (zs s) ih).1).1
  have hB := E.bellman (a t) (ls t) (lam t) (zs t) (hnn t)
  refine ⟨(E.firmL _ _).symm, by linarith [E.firmK (lam t) (zs t)], rfl, hnn t, rfl, ?_, hB.2.2.1⟩
  have := hB.1.2
  change 0 ≤ (1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) -
    E.g (a t) (ls t) (lam t) (zs t)
  linarith

/-- The concrete economy of `bw_recEqm_example`: one aggregate and one idiosyncratic state,
`β = 1/2`, `u(c) = c`, `F(K, L) = (3/2)K + L`, `δ = 1/2`. -/
noncomputable def bw_aggExample : BWAggEconomy Unit Unit where
  β := 1 / 2
  u := fun c => c
  F := fun K Lb => 3 / 2 * K + Lb
  FK := fun _ _ => 3 / 2
  FL := fun _ _ => 1
  δ := 1 / 2
  zval := fun _ => 1
  lab := fun _ => 1
  Q := Kernel.const _ (Measure.dirac ((), ()))
  πz := fun _ _ => 1
  hasDerivAt_K := fun K Lb => by
    have := (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id K)).add_const Lb
    simpa using this
  hasDerivAt_L := fun K Lb => by
    have := HasDerivAt.const_add (3 / 2 * K) (hasDerivAt_id Lb)
    simpa using this
  marg := fun z l z' => by simp [Kernel.const_apply]

theorem bw_aggExample_Q (x : Unit × Unit) : bw_aggExample.Q x = Measure.dirac ((), ()) := by
  simp [bw_aggExample, Kernel.const_apply]

/-- **Definition 17.3.1 is not vacuous**: in `bw_aggExample`, `V(a) = 2a + 2`, `g(a) = a`,
`G(λ, z; z′) = λ`, `r = 1`, `w = 1` is a recursive competitive equilibrium (`β(1 + r) = 1`). -/
noncomputable def bw_recEqm_example : BWRecEqm bw_aggExample where
  V := fun a _ _ _ => 2 * a + 2
  g := fun a _ _ _ => a
  G := fun lam _ _ => lam
  r := fun _ _ => 1
  w := fun _ _ => 1
  bellman := by
    intro a l lam z ha
    simp only [bw_aggExample_Q, integral_dirac]
    refine ⟨⟨ha, ?_⟩, fun a' _ => Integrable.of_finite, ?_, fun a' _ => ?_⟩
    · simp only [bw_aggExample]; linarith
    · simp only [bw_aggExample]; ring
    · simp only [bw_aggExample]; linarith
  firmK := fun _ _ => by simp only [bw_aggExample]; norm_num
  firmL := fun _ _ => by simp only [bw_aggExample]; norm_num
  law := by
    intro lam z z' S B hS hB
    simp only [bw_aggExample_Q]
    simp only [bw_aggExample, mul_one]
    have key : ∀ p : ℝ × Unit, S.indicator (1 : ℝ → ℝ≥0∞) p.1 *
        Measure.dirac ((), ()) ({()} ×ˢ B) = (S ×ˢ B).indicator 1 p := by
      rintro ⟨x, ⟨⟩⟩
      by_cases hx : x ∈ S <;> by_cases hb : () ∈ B <;>
        simp [Set.indicator, Measure.dirac_apply, Set.mem_prod, hx, hb]
    rw [lintegral_congr key, lintegral_indicator_one (hS.prod hB)]

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §17.3.2: the Krusell–Smith method; Exercise 17.5

Miao, §17.3.2, pp. 581–583, and Exercise 17.5, p. 584.

* `bw_moments`: the vector `m = (m₁, …, m_I)` of the first `I` (raw) moments of the wealth
  marginal of `λ`; `bw_moments_first`: `m₁ = K`. A law of motion `m′ = H_I(m, z)` is any map.
* `bw_ksLaw`, `eq_17_12`: the log-linear law (17.12) `ln K′ = b_{0z} + b_{1z} ln K` (`K′ > 0`).
* `bw_ksR`, `bw_ksW`: prices from the firm's conditions `zF_K(K, L) = r + δ`, `zF_L(K, L) = w`.
* `bw_ksBellman`: the agent's problem (17.13) with aggregate state `(K, z)` and perceived law
  (17.12).
* Steps 3–5 as a fixed-point problem: `bw_olsSlope`, `bw_olsIntercept` (the regression of
  Step 4 on the periods `t` with `z_t = z`), `bw_ksUpdate` (the map from the coefficients
  `(b₀, b₁)` to the estimated `(β₀, β₁)`, given the simulated capital path), `bw_ksConsistent`
  (Step 5: `(β₀, β₁) = (b₀, b₁)`, a fixed point).
* `bw_ols_exact`, `bw_rsq_exact`: if the aggregated path obeys the perceived law exactly, OLS
  returns its coefficients and `R² = 1`; hence `bw_ks_fixed_point_of_exact`: such a law is a
  fixed point (consistent).
* **Exercise 17.5** (`BWLeisureEqm`): endogenous leisure in the Krusell–Smith model, a recursive
  equilibrium with labour supply `n(a, l; λ, z) ∈ [0, 1]` and `L = ∫ l n dλ`; `ex_17_5` gives a
  concrete instance.

The simulation itself (Step 3, `N = 100000`, `T = 2000`, `T₀ = 500`), Step 6 (`R²` and added
moments) and the approximate-aggregation explanations are computational and not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L]

/-- Miao, p. 581: the vector of the first `I` moments `m_i = ∫ aⁱ dλ` of the wealth distribution
(the marginal of `λ` in `a`); the book's list (mean, variance, skewness, kurtosis) is the
corresponding central/standardised version of the same information. -/
noncomputable def bw_moments (I : ℕ) (lam : Measure (ℝ × L)) : Fin I → ℝ :=
  fun i => ∫ p, p.1 ^ (i.val + 1) ∂lam

/-- Miao, p. 581: the first moment is aggregate capital, `m₁ = K`. -/
theorem bw_moments_first (I : ℕ) (lam : Measure (ℝ × L)) :
    bw_moments (I + 1) lam 0 = bw_aggK lam := by
  simp [bw_moments, bw_aggK]

/-- The Krusell–Smith law of motion (17.12), `K′ = exp(b_{0z} + b_{1z} ln K)`. -/
noncomputable def bw_ksLaw (b0 b1 : Z → ℝ) (z : Z) (K : ℝ) : ℝ :=
  Real.exp (b0 z + b1 z * Real.log K)

omit [MeasurableSpace Z] in
/-- Miao, (17.12), p. 581: `ln K′ = b_{0z} + b_{1z} ln K`, with `K′ > 0`, and `K′` depends on
`(K, z)` only, not on `z′`. -/
theorem eq_17_12 (b0 b1 : Z → ℝ) (z : Z) (K : ℝ) :
    Real.log (bw_ksLaw b0 b1 z K) = b0 z + b1 z * Real.log K ∧ 0 < bw_ksLaw b0 b1 z K :=
  ⟨Real.log_exp _, Real.exp_pos _⟩

/-- The interest rate `r(K, L, z) = zF_K(K, L) − δ` (Miao, p. 582). -/
def bw_ksR (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) : ℝ := A.zval z * A.FK K Lb - A.δ

/-- The wage `w(K, L, z) = zF_L(K, L)` (Miao, p. 582). -/
def bw_ksW (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) : ℝ := A.zval z * A.FL K Lb

/-- Miao, p. 582: the prices satisfy the firm's conditions. -/
theorem bw_ks_prices (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) :
    A.zval z * A.FK K Lb = bw_ksR A K Lb z + A.δ ∧ A.zval z * A.FL K Lb = bw_ksW A K Lb z := by
  constructor
  · unfold bw_ksR; ring
  · rfl

/-- Miao, (17.13), p. 582: the agent's problem with the perceived law (17.12),
`V(a, l; K, z) = max_{a′} u(c) + β E[V(a′, l′; K′, z′) | z, l]`, `K′ = exp(b_{0z} + b_{1z} ln K)`,
`c + a′ = (1 + r(K, L_z, z))a + w(K, L_z, z)l`, `a′ ≥ 0` (`L_z` the aggregate labour in `z`). -/
def bw_ksBellman (A : BWAggEconomy Z L) (Lz : Z → ℝ) (b0 b1 : Z → ℝ)
    (V g : ℝ → L → ℝ → Z → ℝ) : Prop :=
  ∀ a l K z, 0 ≤ a →
    g a l K z ∈ Set.Icc 0 ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l) ∧
    V a l K z = A.u ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l -
        g a l K z) +
      A.β * ∫ p, V (g a l K z) p.2 (bw_ksLaw b0 b1 z K) p.1 ∂(A.Q (z, l)) ∧
    ∀ a' ∈ Set.Icc 0 ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l),
      A.u ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l - a') +
        A.β * ∫ p, V a' p.2 (bw_ksLaw b0 b1 z K) p.1 ∂(A.Q (z, l)) ≤ V a l K z

/-- The sample mean over a finite set of periods. -/
noncomputable def bw_mean (s : Finset ℕ) (x : ℕ → ℝ) : ℝ := (∑ t ∈ s, x t) / s.card

/-- Step 4 (Miao, p. 582): the OLS slope of `y` on `x` over the periods `s`. -/
noncomputable def bw_olsSlope (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  (∑ t ∈ s, (x t - bw_mean s x) * (y t - bw_mean s y)) / ∑ t ∈ s, (x t - bw_mean s x) ^ 2

/-- Step 4: the OLS intercept. -/
noncomputable def bw_olsIntercept (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  bw_mean s y - bw_olsSlope s x y * bw_mean s x

/-- Step 6 (Miao, p. 583): the `R²` of the regression. -/
noncomputable def bw_rsq (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  1 - (∑ t ∈ s, (y t - (bw_olsIntercept s x y + bw_olsSlope s x y * x t)) ^ 2) /
    ∑ t ∈ s, (y t - bw_mean s y) ^ 2

/-- If `y_t = b₀ + b₁x_t` on `s` and `x` is not constant on `s`, OLS returns `(b₀, b₁)`. -/
theorem bw_ols_exact {s : Finset ℕ} {x y : ℕ → ℝ} {b0 b1 : ℝ}
    (hy : ∀ t ∈ s, y t = b0 + b1 * x t) (hvar : ∑ t ∈ s, (x t - bw_mean s x) ^ 2 ≠ 0) :
    bw_olsSlope s x y = b1 ∧ bw_olsIntercept s x y = b0 := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp at hvar
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hmy : bw_mean s y = b0 + b1 * bw_mean s x := by
    unfold bw_mean
    rw [Finset.sum_congr rfl hy, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hslope : bw_olsSlope s x y = b1 := by
    unfold bw_olsSlope
    have : ∑ t ∈ s, (x t - bw_mean s x) * (y t - bw_mean s y) =
        b1 * ∑ t ∈ s, (x t - bw_mean s x) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hy t ht, hmy]; ring
    rw [this]
    field_simp
  refine ⟨hslope, ?_⟩
  unfold bw_olsIntercept
  rw [hslope, hmy]; ring

/-- If the data obey `y_t = b₀ + b₁x_t` exactly on `s`, the regression fits perfectly: `R² = 1`. -/
theorem bw_rsq_exact {s : Finset ℕ} {x y : ℕ → ℝ} {b0 b1 : ℝ}
    (hy : ∀ t ∈ s, y t = b0 + b1 * x t) (hvar : ∑ t ∈ s, (x t - bw_mean s x) ^ 2 ≠ 0) :
    bw_rsq s x y = 1 := by
  obtain ⟨h1, h0⟩ := bw_ols_exact hy hvar
  unfold bw_rsq
  rw [h1, h0]
  have : ∑ t ∈ s, (y t - (b0 + b1 * x t)) ^ 2 = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hy t ht]; ring
  rw [this, zero_div, sub_zero]

/-- The periods of the regression sample `[T₀, T)` in which the aggregate state is `z`. -/
noncomputable def bw_ksSample [DecidableEq Z] (zs : ℕ → Z) (T0 T : ℕ) (z : Z) : Finset ℕ :=
  (Finset.Ico T0 T).filter fun t => zs t = z

/-- Steps 3–4 (Miao, p. 582) as a map: given the capital path `Kbar` simulated under the
coefficients `(b₀, b₁)` (`sim b0 b1`), regress `ln K̄_{t+1}` on `ln K̄_t` separately for each `z`
over the sample `[T₀, T)`, giving the new coefficients `(β₀, β₁)`. -/
noncomputable def bw_ksUpdate [DecidableEq Z] (sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ) (zs : ℕ → Z)
    (T0 T : ℕ) (b0 b1 : Z → ℝ) : (Z → ℝ) × (Z → ℝ) :=
  (fun z => bw_olsIntercept (bw_ksSample zs T0 T z) (fun t => Real.log (sim b0 b1 t))
      (fun t => Real.log (sim b0 b1 (t + 1))),
    fun z => bw_olsSlope (bw_ksSample zs T0 T z) (fun t => Real.log (sim b0 b1 t))
      (fun t => Real.log (sim b0 b1 (t + 1))))

/-- Step 5 (Miao, p. 583): the perceived law (17.12) is **consistent** with the law generated by
aggregating individual choices iff `(b₀, b₁)` is a fixed point of the update. -/
def bw_ksConsistent [DecidableEq Z] (sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ) (zs : ℕ → Z) (T0 T : ℕ)
    (b0 b1 : Z → ℝ) : Prop :=
  bw_ksUpdate sim zs T0 T b0 b1 = (b0, b1)

omit [MeasurableSpace Z] in
/-- Miao, pp. 582–583: if the simulated aggregate path obeys the perceived law (17.12) exactly,
`K̄_{t+1} = exp(b_{0z_t} + b_{1z_t} ln K̄_t)` on the sample, and `ln K̄_t` varies within each
`z`-subsample, then `(b₀, b₁)` is a fixed point of the Krusell–Smith iteration (consistent). -/
theorem bw_ks_fixed_point_of_exact [DecidableEq Z] {sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ}
    {zs : ℕ → Z} {T0 T : ℕ} {b0 b1 : Z → ℝ}
    (hlaw : ∀ t, T0 ≤ t → t < T → sim b0 b1 (t + 1) = bw_ksLaw b0 b1 (zs t) (sim b0 b1 t))
    (hvar : ∀ z, ∑ t ∈ bw_ksSample zs T0 T z,
      (Real.log (sim b0 b1 t) - bw_mean (bw_ksSample zs T0 T z)
        (fun t => Real.log (sim b0 b1 t))) ^ 2 ≠ 0) :
    bw_ksConsistent sim zs T0 T b0 b1 := by
  have key : ∀ z, ∀ t ∈ bw_ksSample zs T0 T z,
      Real.log (sim b0 b1 (t + 1)) = b0 z + b1 z * Real.log (sim b0 b1 t) := by
    intro z t ht
    simp only [bw_ksSample, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [hlaw t ht.1.1 ht.1.2, (eq_17_12 b0 b1 _ _).1, ht.2]
  unfold bw_ksConsistent bw_ksUpdate
  ext z
  · exact (bw_ols_exact (key z) (hvar z)).2
  · exact (bw_ols_exact (key z) (hvar z)).1

/-- **Exercise 17.5** (Miao, p. 584): **a recursive equilibrium of the Krusell–Smith model with
endogenous leisure**. Utility `v(c, 1 − n)` over consumption and leisure; the household chooses
`a′ ≥ 0` and hours `n ∈ [0, 1]` with `c + a′ = (1 + r(λ, z))a + w(λ, z)ln`, `c ≥ 0`;
aggregate labour is `L(λ, z) = ∫ l n(a, l; λ, z) dλ`; firms' conditions
hold at `(K, L(λ, z))`; and the law of motion is generated by the asset
policy (corrected form (iv) of Definition 17.3.1). -/
structure BWLeisureEqm (A : BWAggEconomy Z L) (v : ℝ → ℝ → ℝ) where
  V : ℝ → L → Measure (ℝ × L) → Z → ℝ
  g : ℝ → L → Measure (ℝ × L) → Z → ℝ
  n : ℝ → L → Measure (ℝ × L) → Z → ℝ
  G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)
  r : Measure (ℝ × L) → Z → ℝ
  w : Measure (ℝ × L) → Z → ℝ
  bellman : ∀ a l lam z, 0 ≤ a →
    n a l lam z ∈ Set.Icc 0 1 ∧
    g a l lam z ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l * n a l lam z) ∧
    (∀ a', 0 ≤ a' → Integrable (fun p : Z × L => V a' p.2 (G lam z p.1) p.1) (A.Q (z, l))) ∧
    V a l lam z = v ((1 + r lam z) * a + w lam z * A.lab l * n a l lam z - g a l lam z)
        (1 - n a l lam z) +
      A.β * ∫ p, V (g a l lam z) p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ∧
    ∀ h ∈ Set.Icc (0 : ℝ) 1, ∀ a' ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l * h),
      v ((1 + r lam z) * a + w lam z * A.lab l * h - a') (1 - h) +
        A.β * ∫ p, V a' p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ≤ V a l lam z
  firmK : ∀ lam z, A.zval z * A.FK (bw_aggK lam)
    (∫ p, A.lab p.2 * n p.1 p.2 lam z ∂lam) = r lam z + A.δ
  firmL : ∀ lam z, A.zval z * A.FL (bw_aggK lam)
    (∫ p, A.lab p.2 * n p.1 p.2 lam z ∂lam) = w lam z
  law : A.Law g G

/-- **Exercise 17.5** is not vacuous: in `bw_aggExample` with `v(c, h) = c` (leisure not valued),
`V(a) = 2a + 2`, `g(a) = a`, full-time work `n = 1`, `G(λ, z; z′) = λ`, `r = w = 1` is a recursive
equilibrium with endogenous leisure. -/
noncomputable def ex_17_5 : BWLeisureEqm bw_aggExample (fun c _ => c) where
  V := fun a _ _ _ => 2 * a + 2
  g := fun a _ _ _ => a
  n := fun _ _ _ _ => 1
  G := fun lam _ _ => lam
  r := fun _ _ => 1
  w := fun _ _ => 1
  bellman := by
    intro a l lam z ha
    simp only [bw_aggExample_Q, integral_dirac]
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨ha, ?_⟩, fun a' _ => Integrable.of_finite, ?_,
      fun h hh a' _ => ?_⟩
    · simp only [bw_aggExample]; linarith
    · simp only [bw_aggExample]; ring
    · simp only [bw_aggExample]; linarith [hh.2]
  firmK := fun _ _ => by simp only [bw_aggExample]; norm_num
  firmL := fun _ _ => by simp only [bw_aggExample]; norm_num
  law := bw_recEqm_example.law

end Miao.IncompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 17.6 (Imrohoroglu 1992): the mathematical content

Miao, Exercise 17.6, pp. 584–585. A continuum of households with CRRA utility
`E Σ βᵗ c_t^{1−γ}/(1 − γ)`, a two-state employment process `l ∈ {e, u}` (`true = e`) with
transition `π_{ll′}`, output `y` when employed and `θy` (`0 < θ < 1`) when unemployed, money
balances `m_t`, lump-sum transfers `gM_t`, `M_{t+1} = (1 + g)M_t`, and the budget
`c_t + m_{t+1}/p_t = m_t/p_t + gM_t/p_t + y_t`, `m_{t+1} ≥ 0`.

* `ex_17_6_inflation`: constant real balances `M_{t+1}/p_t = M_t/p_{t−1}` force the inflation rate
  `p_t/p_{t−1} = 1 + g`.
* `ex_17_6_a` (part (a)): in the real balances `q_t = m_t/p_{t−1}`, with `m̄ = M_t/p_{t−1}` and
  `1 + r = 1/(1 + g)`, the budget is `c + q′ = (1 + r)q + y(l) + gm̄/(1 + g)`, `q′ ≥ 0`. The
  household's dynamic programming problem is therefore (17.4) for the economy
  `BWImroParams.toEconomy` with the return `r`, debt limit `0` and income `y(l) + gm̄/(1 + g)`:
  `V(q, l) = max_{q′ ∈ [0, (1+r)q + y(l) + gm̄/(1+g)]} u(c) + β Σ_{l′} π_{ll′} V(q′, l′)`.
* `BWImroEqm` (part (b)): a **stationary equilibrium**: real balances `m̄ > 0`, a solution
  `(V, h)` of the problem in (a), a stationary distribution `λ` on `[0, ∞) × {e, u}` (17.8) and
  money-market clearing `∫ h dλ = m̄`.
* `ex_17_6_b`: an instance (`γ = 1/2`, `β = 1/2`, `y = 2`, `θ = 3/4`, `g = −1/2 = β − 1`, the
  Friedman rule, `π` the identity): `V(q, l) = 4√(q + c_l)`, `h(q, l) = q`, `λ = δ_{(1, e)}`.

Part (c) (computation, welfare cost of inflation) is computational and not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The primitives of Exercise 17.6. -/
structure BWImroParams where
  β : ℝ
  γ : ℝ
  y : ℝ
  θ : ℝ
  g : ℝ
  trans : Kernel Bool Bool

namespace BWImroParams

/-- The household's economy: CRRA utility, employment chain `π`, output `y` or `θy`. -/
noncomputable def toEconomy (P : BWImroParams) : BWEconomy Bool where
  β := P.β
  u := fun c => c ^ (1 - P.γ) / (1 - P.γ)
  Q := P.trans
  e := fun l => if l then P.y else P.θ * P.y

/-- The real return on money `r = 1/(1 + g) − 1`. -/
noncomputable def rate (P : BWImroParams) : ℝ := 1 / (1 + P.g) - 1

/-- Income including the real transfer: `y(l) + gm̄/(1 + g)`. -/
noncomputable def income (P : BWImroParams) (mbar : ℝ) (l : Bool) : ℝ :=
  P.toEconomy.e l + P.g * mbar / (1 + P.g)

end BWImroParams

/-- **Exercise 17.6** (Miao, p. 585): with `M_{t+1} = (1 + g)M_t` and constant real balances
`M_{t+1}/p_t = M_t/p_{t−1}`, prices grow at the money growth rate, `p_t/p_{t−1} = 1 + g`. -/
theorem ex_17_6_inflation {M M' p p₀ g : ℝ} (hM : 0 < M) (hp : 0 < p) (hp₀ : 0 < p₀)
    (hg : M' = (1 + g) * M) (hreal : M' / p = M / p₀) : p / p₀ = 1 + g := by
  rw [hg, div_eq_div_iff hp.ne' hp₀.ne'] at hreal
  rw [div_eq_iff hp₀.ne']
  have := mul_right_cancel₀ hM.ne' (by linarith : (1 + g) * p₀ * M = p * M)
  linarith

/-- **Exercise 17.6 (a)** (Miao, p. 585): with `p_t = (1 + g)p_{t−1}`, real balances
`q = m_t/p_{t−1}`, `q′ = m_{t+1}/p_t`, `m̄ = M_t/p_{t−1}` and `1 + r = 1/(1 + g)`, the budget
`c + m_{t+1}/p_t = m_t/p_t + gM_t/p_t + y` is `c + q′ = (1 + r)q + y + gm̄/(1 + g)`. -/
theorem ex_17_6_a {m m' M p p₀ g c y : ℝ} (hp₀ : 0 < p₀) (hg : 0 < 1 + g)
    (hp : p = (1 + g) * p₀) :
    c + m' / p = m / p + g * M / p + y ↔
      c + m' / p = (1 + (1 / (1 + g) - 1)) * (m / p₀) + y + g * (M / p₀) / (1 + g) := by
  have e1 : m / p = (1 + (1 / (1 + g) - 1)) * (m / p₀) := by rw [hp]; field_simp; ring
  have e2 : g * M / p = g * (M / p₀) / (1 + g) := by rw [hp]; field_simp
  rw [e1, e2]
  constructor <;> intro h <;> linarith

/-- **Exercise 17.6 (b)** (Miao, p. 585): a **stationary equilibrium** of the Imrohoroglu economy:
constant real balances `m̄ = M_{t+1}/p_t > 0`, the household's value function and money policy
`h(q, l) = m_{t+1}/p_t` solving part (a), a stationary distribution `λ` of `(q, l)` on
`[0, ∞) × {e, u}` and market clearing `∫ h dλ = m̄`. -/
structure BWImroEqm (P : BWImroParams) where
  mbar : ℝ
  V : ℝ → Bool → ℝ
  h : ℝ → Bool → ℝ
  lam : Measure (ℝ × Bool)
  β_pos : 0 < P.β
  β_lt_one : P.β < 1
  γ_pos : 0 < P.γ
  γ_ne_one : P.γ ≠ 1
  y_pos : 0 < P.y
  θ_pos : 0 < P.θ
  θ_lt_one : P.θ < 1
  g_gt : -1 < P.g
  mbar_pos : 0 < mbar
  isProb : IsProbabilityMeasure lam
  supp : lam {q | q.1 < -0} = 0
  bellman : P.toEconomy.Bellman P.rate 0 (P.income mbar) V h
  integrable : Integrable (fun q => h q.1 q.2) lam
  clear : ∫ q, h q.1 q.2 ∂lam = mbar
  stationary : P.toEconomy.Stationary h lam

/-- The parameters of the instance `ex_17_6_b`. -/
noncomputable def bw_imroExample : BWImroParams where
  β := 1 / 2
  γ := 1 / 2
  y := 2
  θ := 3 / 4
  g := -1 / 2
  trans := Kernel.deterministic id measurable_id

theorem bw_imroExample_u (c : ℝ) : bw_imroExample.toEconomy.u c = 2 * Real.sqrt c := by
  simp only [BWImroParams.toEconomy, bw_imroExample]
  rw [Real.sqrt_eq_rpow, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  ring

theorem bw_imroExample_Q (l : Bool) : bw_imroExample.toEconomy.Q l = Measure.dirac l := by
  simp [BWImroParams.toEconomy, bw_imroExample, Kernel.deterministic_apply]

theorem bw_imroExample_rate : bw_imroExample.rate = 1 := by
  norm_num [BWImroParams.rate, bw_imroExample]

theorem bw_imroExample_income (l : Bool) :
    bw_imroExample.income 1 l = if l then 1 else 1 / 2 := by
  cases l <;> norm_num [BWImroParams.income, BWImroParams.toEconomy, bw_imroExample]

/-- `√A + √B ≤ 2√((A + B)/2)` in the form used below. -/
theorem bw_sqrt_add_le {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (hAB : A + B = 2 * s) :
    2 * Real.sqrt A + 2 * Real.sqrt B ≤ 4 * Real.sqrt s := by
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  have h3 := Real.sq_sqrt hs
  have p1 := Real.sqrt_nonneg A
  have p2 := Real.sqrt_nonneg B
  have p3 := Real.sqrt_nonneg s
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B), sq_nonneg (Real.sqrt A + Real.sqrt B -
    2 * Real.sqrt s)]

/-- **Exercise 17.6 (b)** is not vacuous: with `β = γ = 1/2`, `y = 2`, `θ = 3/4`, `g = −1/2` (so
`1 + r = 1/(1 + g) = 1/β`, the Friedman rule) and `π` the identity, `m̄ = 1`,
`V(q, l) = 4√(q + c_l)` (`c_e = 1`, `c_u = 1/2`), `h(q, l) = q` and `λ = δ_{(1, e)}` form a
stationary equilibrium. -/
noncomputable def ex_17_6_b : BWImroEqm bw_imroExample where
  mbar := 1
  V := fun q l => 4 * Real.sqrt (q + if l then 1 else 1 / 2)
  h := fun q _ => q
  lam := Measure.dirac ((1 : ℝ), true)
  β_pos := by norm_num [bw_imroExample]
  β_lt_one := by norm_num [bw_imroExample]
  γ_pos := by norm_num [bw_imroExample]
  γ_ne_one := by norm_num [bw_imroExample]
  y_pos := by norm_num [bw_imroExample]
  θ_pos := by norm_num [bw_imroExample]
  θ_lt_one := by norm_num [bw_imroExample]
  g_gt := by norm_num [bw_imroExample]
  mbar_pos := one_pos
  isProb := inferInstance
  supp := by simp [Measure.dirac_apply]
  bellman := by
    intro q l hq
    rw [neg_zero] at hq
    have hc : 0 < (if l then (1 : ℝ) else 1 / 2) := by cases l <;> norm_num
    simp only [bw_imroExample_Q, integral_dirac, bw_imroExample_u, bw_imroExample_rate,
      bw_imroExample_income]
    have hβ : bw_imroExample.toEconomy.β = 1 / 2 := rfl
    rw [hβ]
    refine ⟨⟨by linarith, by linarith⟩, fun a' _ => Integrable.of_finite, ?_, fun a' ha' => ?_⟩
    · rw [show (1 + 1) * q + (if l then (1 : ℝ) else 1 / 2) - q =
        q + (if l then (1 : ℝ) else 1 / 2) by ring]
      ring
    · obtain ⟨h0, h1⟩ := ha'
      rw [neg_zero] at h0
      have := bw_sqrt_add_le (A := (1 + 1) * q + (if l then (1 : ℝ) else 1 / 2) - a')
        (B := a' + if l then (1 : ℝ) else 1 / 2) (s := q + if l then (1 : ℝ) else 1 / 2)
        (by linarith) (by linarith) (by linarith) (by ring)
      linarith
  integrable := integrable_dirac (by simp)
  clear := by rw [integral_dirac]
  stationary := by
    intro A B _ _
    simp only [lintegral_dirac, bw_imroExample_Q, Measure.dirac_apply]
    by_cases hA : (1 : ℝ) ∈ A <;> by_cases hB : true ∈ B <;>
      simp [Set.indicator, Set.mem_prod, hA, hB]

end Miao.IncompleteMarkets

set_option linter.style.longLine false
#print axioms Miao.IncompleteMarkets.IsLHC
#print axioms Miao.IncompleteMarkets.IsUHC
#print axioms Miao.IncompleteMarkets.graph
#print axioms Miao.IncompleteMarkets.continuousAt_of_isUHC_singleton
#print axioms Miao.IncompleteMarkets.isCompact_graph
#print axioms Miao.IncompleteMarkets.markovOpR
#print axioms Miao.IncompleteMarkets.IsFeller
#print axioms Miao.IncompleteMarkets.maxValue
#print axioms Miao.IncompleteMarkets.argmax
#print axioms Miao.IncompleteMarkets.continuousOn_section
#print axioms Miao.IncompleteMarkets.exists_argmax
#print axioms Miao.IncompleteMarkets.le_maxValue
#print axioms Miao.IncompleteMarkets.tendsto_f_graph
#print axioms Miao.IncompleteMarkets.theorem_3_6
#print axioms Miao.IncompleteMarkets.UniqueArgmax
#print axioms Miao.IncompleteMarkets.UniqueArgmax.mk
#print axioms Miao.IncompleteMarkets.UniqueArgmax.nonempty
#print axioms Miao.IncompleteMarkets.UniqueArgmax.compact
#print axioms Miao.IncompleteMarkets.UniqueArgmax.lhc
#print axioms Miao.IncompleteMarkets.UniqueArgmax.uhc
#print axioms Miao.IncompleteMarkets.UniqueArgmax.cont
#print axioms Miao.IncompleteMarkets.UniqueArgmax.unique
#print axioms Miao.IncompleteMarkets.argmaxFn
#print axioms Miao.IncompleteMarkets.UniqueArgmax.argmaxFn_mem
#print axioms Miao.IncompleteMarkets.UniqueArgmax.argmax_eq
#print axioms Miao.IncompleteMarkets.UniqueArgmax.lt_of_ne
#print axioms Miao.IncompleteMarkets.UniqueArgmax.continuous_argmaxFn
#print axioms Miao.IncompleteMarkets.UniqueArgmax.lemma_3_7
#print axioms Miao.IncompleteMarkets.UniqueArgmax.lemma_3_7_uniform
#print axioms Miao.IncompleteMarkets.shortfall_lt
#print axioms Miao.IncompleteMarkets.theorem_3_8
#print axioms Miao.IncompleteMarkets.theorem_3_8_uniform
#print axioms Miao.IncompleteMarkets.IsMeasurableSelection
#print axioms Miao.IncompleteMarkets.IsMeasCorr
#print axioms Miao.IncompleteMarkets.minCoord
#print axioms Miao.IncompleteMarkets.minCoord_mem
#print axioms Miao.IncompleteMarkets.minCoord_le
#print axioms Miao.IncompleteMarkets.measurable_minCoord
#print axioms Miao.IncompleteMarkets.refineCorr
#print axioms Miao.IncompleteMarkets.IsMeasCorr.refine
#print axioms Miao.IncompleteMarkets.lexCorr
#print axioms Miao.IncompleteMarkets.lexCorr_spec
#print axioms Miao.IncompleteMarkets.isMeasCorr_of_uhc
#print axioms Miao.IncompleteMarkets.theorem_7_6
#print axioms Miao.IncompleteMarkets.theorem_7_6_subtype
#print axioms Miao.IncompleteMarkets.theorem_4_10
#print axioms Miao.IncompleteMarkets.ex_4_5
#print axioms Miao.IncompleteMarkets.mop
#print axioms Miao.IncompleteMarkets.PreservesBC
#print axioms Miao.IncompleteMarkets.integrable_of_abs_le
#print axioms Miao.IncompleteMarkets.integral_lt_integral_of_lt
#print axioms Miao.IncompleteMarkets.abs_mop_le
#print axioms Miao.IncompleteMarkets.integrable_section
#print axioms Miao.IncompleteMarkets.lemma_9_5_discrete
#print axioms Miao.IncompleteMarkets.lemma_9_5_compact
#print axioms Miao.IncompleteMarkets.lemma_9_5_comb
#print axioms Miao.IncompleteMarkets.lemma_9_5_comb_strict
#print axioms Miao.IncompleteMarkets.lemma_9_5_mono
#print axioms Miao.IncompleteMarkets.lemma_9_5_strictMono
#print axioms Miao.IncompleteMarkets.lemma_9_5'
#print axioms Miao.IncompleteMarkets.OCModel
#print axioms Miao.IncompleteMarkets.OCModel.mk
#print axioms Miao.IncompleteMarkets.OCModel.X
#print axioms Miao.IncompleteMarkets.OCModel.A
#print axioms Miao.IncompleteMarkets.OCModel.Q
#print axioms Miao.IncompleteMarkets.OCModel.Γ
#print axioms Miao.IncompleteMarkets.OCModel.φ
#print axioms Miao.IncompleteMarkets.OCModel.u
#print axioms Miao.IncompleteMarkets.OCModel.uT
#print axioms Miao.IncompleteMarkets.OCModel.β
#print axioms Miao.IncompleteMarkets.OCModel.T
#print axioms Miao.IncompleteMarkets.OCModel.cont
#print axioms Miao.IncompleteMarkets.OCModel.obj
#print axioms Miao.IncompleteMarkets.OCModel.bellman
#print axioms Miao.IncompleteMarkets.OCModel.W
#print axioms Miao.IncompleteMarkets.OCModel.V
#print axioms Miao.IncompleteMarkets.OCModel.V_T_eq
#print axioms Miao.IncompleteMarkets.OCModel.V_succ
#print axioms Miao.IncompleteMarkets.OCModel.V_succ_apply
#print axioms Miao.IncompleteMarkets.OCModel.G
#print axioms Miao.IncompleteMarkets.OCModel.g
#print axioms Miao.IncompleteMarkets.OCModel.g_mem
#print axioms Miao.IncompleteMarkets.OCModel.path
#print axioms Miao.IncompleteMarkets.OCModel.IsPlan
#print axioms Miao.IncompleteMarkets.OCModel.bolza
#print axioms Miao.IncompleteMarkets.OCModel.policyPath
#print axioms Miao.IncompleteMarkets.OCModel.policyPath_eq
#print axioms Miao.IncompleteMarkets.OCModel.Γs
#print axioms Miao.IncompleteMarkets.OCModel.Gs
#print axioms Miao.IncompleteMarkets.OCModel.Assumption641
#print axioms Miao.IncompleteMarkets.OCModel.Assumption642
#print axioms Miao.IncompleteMarkets.OCModel.Assumption643i
#print axioms Miao.IncompleteMarkets.OCModel.Assumption643ii
#print axioms Miao.IncompleteMarkets.OCModel.Assumption644
#print axioms Miao.IncompleteMarkets.OCModel.Assumption645
#print axioms Miao.IncompleteMarkets.OCModel.Assumption646
#print axioms Miao.IncompleteMarkets.OCModel.Assumption647
#print axioms Miao.IncompleteMarkets.OCModel.Assumption648
#print axioms Miao.IncompleteMarkets.OCModel.Assumption649
#print axioms Miao.IncompleteMarkets.OCModel.Assumption6410
#print axioms Miao.IncompleteMarkets.OCModel.Assumption6411
#print axioms Miao.IncompleteMarkets.OCModel.Assumption6412
#print axioms Miao.IncompleteMarkets.OCModel.Assumption6413
#print axioms Miao.IncompleteMarkets.OCModel.Assumption6414
#print axioms Miao.IncompleteMarkets.continuous_mop_of_compact
#print axioms Miao.IncompleteMarkets.OCModel.ExpCont
#print axioms Miao.IncompleteMarkets.OCModel.lemma_6_4_1_compact
#print axioms Miao.IncompleteMarkets.OCModel.expCont_compact
#print axioms Miao.IncompleteMarkets.OCModel.lemma_6_4_1_countable
#print axioms Miao.IncompleteMarkets.OCModel.expCont_countable
#print axioms Miao.IncompleteMarkets.oc_tent
#print axioms Miao.IncompleteMarkets.oc_spike
#print axioms Miao.IncompleteMarkets.oc_tent_eq_zero
#print axioms Miao.IncompleteMarkets.oc_tent_nonneg
#print axioms Miao.IncompleteMarkets.oc_tent_le_one
#print axioms Miao.IncompleteMarkets.oc_spike_bound
#print axioms Miao.IncompleteMarkets.oc_half
#print axioms Miao.IncompleteMarkets.oc_spikeModel
#print axioms Miao.IncompleteMarkets.lemma_6_4_1_countable_counterexample
#print axioms Miao.IncompleteMarkets.OCModel.objS
#print axioms Miao.IncompleteMarkets.OCModel.maxValue_objS
#print axioms Miao.IncompleteMarkets.OCModel.V_eq_maxValue
#print axioms Miao.IncompleteMarkets.OCModel.Gs_eq_argmax
#print axioms Miao.IncompleteMarkets.OCModel.oc_abs_integral_le
#print axioms Miao.IncompleteMarkets.OCModel.continuousOn_objS
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_1
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_1_compact
#print axioms Miao.IncompleteMarkets.OCModel.V_bounded
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_1_countable
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_1_selection
#print axioms Miao.IncompleteMarkets.OCModel.Standing
#print axioms Miao.IncompleteMarkets.OCModel.Standing.mk
#print axioms Miao.IncompleteMarkets.OCModel.Standing.expCont
#print axioms Miao.IncompleteMarkets.OCModel.Standing.memP
#print axioms Miao.IncompleteMarkets.OCModel.Standing.a644
#print axioms Miao.IncompleteMarkets.OCModel.Standing.a645
#print axioms Miao.IncompleteMarkets.OCModel.Standing.a646
#print axioms Miao.IncompleteMarkets.OCModel.Standing.of_compact
#print axioms Miao.IncompleteMarkets.OCModel.Standing.of_countable
#print axioms Miao.IncompleteMarkets.OCModel.Standing.contV
#print axioms Miao.IncompleteMarkets.OCModel.Standing.integrable
#print axioms Miao.IncompleteMarkets.OCModel.Standing.continuousOn_objS
#print axioms Miao.IncompleteMarkets.OCModel.Standing.obj_le_V
#print axioms Miao.IncompleteMarkets.OCModel.Standing.G_nonempty
#print axioms Miao.IncompleteMarkets.OCModel.Standing.g_mem
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_2
#print axioms Miao.IncompleteMarkets.OCModel.CompConcave
#print axioms Miao.IncompleteMarkets.OCModel.CompStrictA
#print axioms Miao.IncompleteMarkets.OCModel.PhiAffine
#print axioms Miao.IncompleteMarkets.OCModel.PhiInjA
#print axioms Miao.IncompleteMarkets.OCModel.compConcave_of_mono
#print axioms Miao.IncompleteMarkets.OCModel.compStrictA_of_mono
#print axioms Miao.IncompleteMarkets.OCModel.compConcave_of_affine
#print axioms Miao.IncompleteMarkets.OCModel.compStrictA_of_affine
#print axioms Miao.IncompleteMarkets.OCModel.cont_comb
#print axioms Miao.IncompleteMarkets.OCModel.concave_core
#print axioms Miao.IncompleteMarkets.OCModel.G_subsingleton_core
#print axioms Miao.IncompleteMarkets.OCModel.G_eq_singleton_core
#print axioms Miao.IncompleteMarkets.OCModel.continuousOn_g_core
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_3_concave
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_3
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_3_affine
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_3_phi_eq_a
#print axioms Miao.IncompleteMarkets.oc_hasDerivAt_integral_concave
#print axioms Miao.IncompleteMarkets.oc_slope_double
#print axioms Miao.IncompleteMarkets.oc_continuousOn_deriv_of_concave
#print axioms Miao.IncompleteMarkets.OCModel.envRHS
#print axioms Miao.IncompleteMarkets.OCModel.focRHS
#print axioms Miao.IncompleteMarkets.OCModel.LocBounded
#print axioms Miao.IncompleteMarkets.OCModel.InteriorPolicy
#print axioms Miao.IncompleteMarkets.OCModel.Partials
#print axioms Miao.IncompleteMarkets.OCModel.Partials.mk
#print axioms Miao.IncompleteMarkets.OCModel.Partials.uT
#print axioms Miao.IncompleteMarkets.OCModel.Partials.ux
#print axioms Miao.IncompleteMarkets.OCModel.Partials.ua
#print axioms Miao.IncompleteMarkets.OCModel.Partials.φx
#print axioms Miao.IncompleteMarkets.OCModel.Partials.φa
#print axioms Miao.IncompleteMarkets.OCModel.partials_of
#print axioms Miao.IncompleteMarkets.OCModel.oc_concaveOn_of_pos
#print axioms Miao.IncompleteMarkets.OCModel.eventually_mem_Γ
#print axioms Miao.IncompleteMarkets.OCModel.hasDerivAt_cont_x
#print axioms Miao.IncompleteMarkets.OCModel.hasDerivAt_cont_a
#print axioms Miao.IncompleteMarkets.OCModel.envelope_step
#print axioms Miao.IncompleteMarkets.OCModel.foc_step
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_4_core
#print axioms Miao.IncompleteMarkets.OCModel.locBounded_of_compact
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_4
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_4_4_phi_eq_a
#print axioms Miao.IncompleteMarkets.OCModel.euler_equations
#print axioms Miao.IncompleteMarkets.oc_tangent_le
#print axioms Miao.IncompleteMarkets.oc_supergradient
#print axioms Miao.IncompleteMarkets.OCModel.path_measurable
#print axioms Miao.IncompleteMarkets.OCModel.Ha
#print axioms Miao.IncompleteMarkets.OCModel.Hx
#print axioms Miao.IncompleteMarkets.OCModel.hamiltonian
#print axioms Miao.IncompleteMarkets.OCModel.pathHam
#print axioms Miao.IncompleteMarkets.OCModel.MaxPrinciple
#print axioms Miao.IncompleteMarkets.OCModel.MaxPrinciple.mk
#print axioms Miao.IncompleteMarkets.OCModel.MaxPrinciple.foc_a
#print axioms Miao.IncompleteMarkets.OCModel.MaxPrinciple.foc_x
#print axioms Miao.IncompleteMarkets.OCModel.MaxPrinciple.terminal
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.mk
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.u_s
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.u_c
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.uT_s
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.uT_c
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.μΔ
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.ux
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.φx
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.φxΔ
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.ua
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.φa
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.φaΔ
#print axioms Miao.IncompleteMarkets.OCModel.MPIntegrable.uTx
#print axioms Miao.IncompleteMarkets.OCModel.oc_integral_mul_condExp
#print axioms Miao.IncompleteMarkets.OCModel.theorem_6_5_1
#print axioms Miao.IncompleteMarkets.OCModel.pathHam_concave_of_concave
#print axioms Miao.IncompleteMarkets.OCModel.pathHam_concave_of_affine
#print axioms Miao.IncompleteMarkets.OCModel.IsMarkovCond
#print axioms Miao.IncompleteMarkets.OCModel.link_6_38_6_33
#print axioms Miao.IncompleteMarkets.OCModel.link_6_39_6_31
#print axioms Miao.IncompleteMarkets.OCModel.maxPrinciple_of_dp
#print axioms Miao.IncompleteMarkets.OCModel.lam
#print axioms Miao.IncompleteMarkets.OCModel.eq_6_40_a
#print axioms Miao.IncompleteMarkets.OCModel.eq_6_40_b
#print axioms Miao.IncompleteMarkets.OCModel.eq_6_40_terminal
#print axioms Miao.IncompleteMarkets.OCModel.eq_6_40_terminal_misprint
#print axioms Miao.IncompleteMarkets.CSModel
#print axioms Miao.IncompleteMarkets.CSModel.mk
#print axioms Miao.IncompleteMarkets.CSModel.u
#print axioms Miao.IncompleteMarkets.CSModel.β
#print axioms Miao.IncompleteMarkets.CSModel.Q
#print axioms Miao.IncompleteMarkets.CSModel.ρ
#print axioms Miao.IncompleteMarkets.CSModel.w
#print axioms Miao.IncompleteMarkets.cash_on_hand
#print axioms Miao.IncompleteMarkets.CSModel.toOC
#print axioms Miao.IncompleteMarkets.CSModel.v
#print axioms Miao.IncompleteMarkets.CSModel.obj
#print axioms Miao.IncompleteMarkets.CSModel.v_zero
#print axioms Miao.IncompleteMarkets.CSModel.v_succ
#print axioms Miao.IncompleteMarkets.CSModel.W_eq
#print axioms Miao.IncompleteMarkets.CSModel.V_eq
#print axioms Miao.IncompleteMarkets.CSModel.sav
#print axioms Miao.IncompleteMarkets.CSModel.cons
#print axioms Miao.IncompleteMarkets.CSModel.ex_6_5_g0_s0
#print axioms Miao.IncompleteMarkets.CSModel.obj_eq
#print axioms Miao.IncompleteMarkets.CSModel.mem_G
#print axioms Miao.IncompleteMarkets.CSModel.Basic
#print axioms Miao.IncompleteMarkets.CSModel.Basic.mk
#print axioms Miao.IncompleteMarkets.CSModel.Basic.β_pos
#print axioms Miao.IncompleteMarkets.CSModel.Basic.u_cont
#print axioms Miao.IncompleteMarkets.CSModel.Basic.u_mono
#print axioms Miao.IncompleteMarkets.CSModel.Basic.u_conc
#print axioms Miao.IncompleteMarkets.CSModel.Basic.ρ_cont
#print axioms Miao.IncompleteMarkets.CSModel.Basic.ρ_pos
#print axioms Miao.IncompleteMarkets.CSModel.Basic.w_cont
#print axioms Miao.IncompleteMarkets.CSModel.Basic.w_pos
#print axioms Miao.IncompleteMarkets.CSModel.Basic.feller
#print axioms Miao.IncompleteMarkets.CSModel.assumption644
#print axioms Miao.IncompleteMarkets.CSModel.assumption645
#print axioms Miao.IncompleteMarkets.CSModel.assumption646
#print axioms Miao.IncompleteMarkets.CSModel.isFeller_const
#print axioms Miao.IncompleteMarkets.CSModel.standing
#print axioms Miao.IncompleteMarkets.CSModel.contV
#print axioms Miao.IncompleteMarkets.CSModel.integrable_next
#print axioms Miao.IncompleteMarkets.CSModel.obj_le
#print axioms Miao.IncompleteMarkets.CSModel.sav_mem
#print axioms Miao.IncompleteMarkets.CSModel.isMaxOn_sav
#print axioms Miao.IncompleteMarkets.CSModel.not_assumption6410
#print axioms Miao.IncompleteMarkets.cs_exchange
#print axioms Miao.IncompleteMarkets.CSModel.ev
#print axioms Miao.IncompleteMarkets.CSModel.obj_eq_ev
#print axioms Miao.IncompleteMarkets.CSModel.next_nonneg
#print axioms Miao.IncompleteMarkets.CSModel.strictConcaveOn_ev
#print axioms Miao.IncompleteMarkets.CSModel.strictMonoOn_v
#print axioms Miao.IncompleteMarkets.CSModel.strictConcaveOn_v
#print axioms Miao.IncompleteMarkets.CSModel.sav_unique
#print axioms Miao.IncompleteMarkets.CSModel.G_subsingleton
#print axioms Miao.IncompleteMarkets.CSModel.continuousOn_sav
#print axioms Miao.IncompleteMarkets.CSModel.continuousOn_cons
#print axioms Miao.IncompleteMarkets.CSModel.sav_mem'
#print axioms Miao.IncompleteMarkets.CSModel.monotoneOn_sav
#print axioms Miao.IncompleteMarkets.CSModel.monotoneOn_cons
#print axioms Miao.IncompleteMarkets.cs_compare
#print axioms Miao.IncompleteMarkets.CSModel.Smooth
#print axioms Miao.IncompleteMarkets.CSModel.Smooth.mk
#print axioms Miao.IncompleteMarkets.CSModel.Smooth.u_diff
#print axioms Miao.IncompleteMarkets.CSModel.Smooth.inada
#print axioms Miao.IncompleteMarkets.CSModel.evd
#print axioms Miao.IncompleteMarkets.CSModel.detModel
#print axioms Miao.IncompleteMarkets.CSModel.strictAntiOn_deriv_u
#print axioms Miao.IncompleteMarkets.CSModel.cons_pos
#print axioms Miao.IncompleteMarkets.CSModel.hasDerivAt_v
#print axioms Miao.IncompleteMarkets.CSModel.deriv_v
#print axioms Miao.IncompleteMarkets.CSModel.continuousOn_deriv_v
#print axioms Miao.IncompleteMarkets.CSModel.strictAntiOn_deriv_v
#print axioms Miao.IncompleteMarkets.CSModel.hasDerivAt_ev
#print axioms Miao.IncompleteMarkets.CSModel.strictAntiOn_evd
#print axioms Miao.IncompleteMarkets.CSModel.foc
#print axioms Miao.IncompleteMarkets.CSModel.strictMonoOn_cons
#print axioms Miao.IncompleteMarkets.CSModel.exists_sav_eq_zero
#print axioms Miao.IncompleteMarkets.CSModel.not_strictMonoOn_sav
#print axioms Miao.IncompleteMarkets.CSModel.evd_le_evd
#print axioms Miao.IncompleteMarkets.CSModel.cons_succ_le
#print axioms Miao.IncompleteMarkets.CSModel.sav_le_sav_succ
#print axioms Miao.IncompleteMarkets.CSModel.deriv_v_le
#print axioms Miao.IncompleteMarkets.CSModel.exists_cons_succ_eq
#print axioms Miao.IncompleteMarkets.CSModel.Basic.detModel
#print axioms Miao.IncompleteMarkets.CSModel.isMarkovKernel_detModel
#print axioms Miao.IncompleteMarkets.CSModel.evd_detModel
#print axioms Miao.IncompleteMarkets.CSModel.cons_ge_low
#print axioms Miao.IncompleteMarkets.CSModel.cons_le_high
#print axioms Miao.IncompleteMarkets.CSModel.v_indep
#print axioms Miao.IncompleteMarkets.bookModel
#print axioms Miao.IncompleteMarkets.CSUtility
#print axioms Miao.IncompleteMarkets.CSUtility.mk
#print axioms Miao.IncompleteMarkets.CSUtility.cont
#print axioms Miao.IncompleteMarkets.CSUtility.mono
#print axioms Miao.IncompleteMarkets.CSUtility.conc
#print axioms Miao.IncompleteMarkets.CSUtility.diff
#print axioms Miao.IncompleteMarkets.CSUtility.inada
#print axioms Miao.IncompleteMarkets.bookModel_isMarkovKernel
#print axioms Miao.IncompleteMarkets.bookModel_basic
#print axioms Miao.IncompleteMarkets.ex_6_5_value
#print axioms Miao.IncompleteMarkets.ex_6_5_v_deriv_mono
#print axioms Miao.IncompleteMarkets.ex_6_5_policy_x
#print axioms Miao.IncompleteMarkets.ex_6_5_sav_not_strict
#print axioms Miao.IncompleteMarkets.ex_6_5_policy_n
#print axioms Miao.IncompleteMarkets.ex_6_5_n_not_strict
#print axioms Miao.IncompleteMarkets.ex_6_5_foc
#print axioms Miao.IncompleteMarkets.ex_6_5_compare
#print axioms Miao.IncompleteMarkets.markovModel
#print axioms Miao.IncompleteMarkets.ex_6_6
#print axioms Miao.IncompleteMarkets.phelpsModel
#print axioms Miao.IncompleteMarkets.ex_6_7
#print axioms Miao.IncompleteMarkets.cs_budget
#print axioms Miao.IncompleteMarkets.cs_optimal_of_euler
#print axioms Miao.IncompleteMarkets.cs_crra
#print axioms Miao.IncompleteMarkets.cs_crra_tangent
#print axioms Miao.IncompleteMarkets.cs_theta
#print axioms Miao.IncompleteMarkets.cs_wealth
#print axioms Miao.IncompleteMarkets.cs_cstar
#print axioms Miao.IncompleteMarkets.cs_astar
#print axioms Miao.IncompleteMarkets.ex_6_8
#print axioms Miao.IncompleteMarkets.eu_concave_le_fderiv
#print axioms Miao.IncompleteMarkets.eu_le_of_le_add_tendsto_zero
#print axioms Miao.IncompleteMarkets.eu_limsup_le
#print axioms Miao.IncompleteMarkets.eu_supergradient
#print axioms Miao.IncompleteMarkets.eq_7_38
#print axioms Miao.IncompleteMarkets.eu_clm_pair
#print axioms Miao.IncompleteMarkets.eu_dot
#print axioms Miao.IncompleteMarkets.eu_EulerModel
#print axioms Miao.IncompleteMarkets.eu_EulerModel.mk
#print axioms Miao.IncompleteMarkets.eu_EulerModel.X
#print axioms Miao.IncompleteMarkets.eu_EulerModel.Q
#print axioms Miao.IncompleteMarkets.eu_EulerModel.Γ
#print axioms Miao.IncompleteMarkets.eu_EulerModel.u
#print axioms Miao.IncompleteMarkets.eu_EulerModel.β
#print axioms Miao.IncompleteMarkets.eu_EulerModel.uu
#print axioms Miao.IncompleteMarkets.eu_EulerModel.ux
#print axioms Miao.IncompleteMarkets.eu_EulerModel.ua
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_Assumption732
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_Assumption733
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_Assumption734
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_Assumption6411
#print axioms Miao.IncompleteMarkets.eu_EulerModel.concaveOn_of_733
#print axioms Miao.IncompleteMarkets.eu_EulerModel.IsPlan
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_partialJ
#print axioms Miao.IncompleteMarkets.eu_EulerModel.IsOptimal
#print axioms Miao.IncompleteMarkets.eu_EulerModel.IsEuler
#print axioms Miao.IncompleteMarkets.eu_EulerModel.TVC735
#print axioms Miao.IncompleteMarkets.eu_EulerModel.TVC737
#print axioms Miao.IncompleteMarkets.eu_EulerModel.foc_7_21
#print axioms Miao.IncompleteMarkets.eu_EulerModel.euler_functional
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerMarkov
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eq_7_34
#print axioms Miao.IncompleteMarkets.eu_EulerModel.variational_7_5
#print axioms Miao.IncompleteMarkets.eu_EulerModel.theorem_7_5_1_euler
#print axioms Miao.IncompleteMarkets.eu_EulerModel.theorem_7_5_1_euler_seq
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eq_7_36
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eq_7_36_expect
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eq_7_35_iff_7_37
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eq_7_37_is_7_32
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_ux_nonneg
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_strictMono_deriv_zero
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_ux_pos
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.mk
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.r_s
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.r_c
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.uxΔ
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.uaΔ
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.uxn
#print axioms Miao.IncompleteMarkets.eu_EulerModel.EulerInt.uax
#print axioms Miao.IncompleteMarkets.eu_EulerModel.eu_euler_sufficient
#print axioms Miao.IncompleteMarkets.eu_EulerModel.theorem_7_5_2
#print axioms Miao.IncompleteMarkets.eu_EulerModel.theorem_7_5_2_limit
#print axioms Miao.IncompleteMarkets.eu_EulerModel.theorem_7_5_2_eventually
#print axioms Miao.IncompleteMarkets.eq_7_39
#print axioms Miao.IncompleteMarkets.eq_7_39_unique
#print axioms Miao.IncompleteMarkets.example_7_5_1_log
#print axioms Miao.IncompleteMarkets.example_7_5_1_A_mem
#print axioms Miao.IncompleteMarkets.example_7_5_1_tvc_det
#print axioms Miao.IncompleteMarkets.eu_crra_hasDerivAt
#print axioms Miao.IncompleteMarkets.eu_crra_concave
#print axioms Miao.IncompleteMarkets.eu_phelpsModel
#print axioms Miao.IncompleteMarkets.eu_phelps_fderiv
#print axioms Miao.IncompleteMarkets.eu_phelpsCash
#print axioms Miao.IncompleteMarkets.eu_phelpsState
#print axioms Miao.IncompleteMarkets.eu_phelpsCash_pos
#print axioms Miao.IncompleteMarkets.eu_phelps_cash_eq
#print axioms Miao.IncompleteMarkets.eu_phelpsCash_measurable
#print axioms Miao.IncompleteMarkets.example_7_5_1_cash_rpow
#print axioms Miao.IncompleteMarkets.example_7_5_1_condmoment
#print axioms Miao.IncompleteMarkets.example_7_5_1_prod_moment
#print axioms Miao.IncompleteMarkets.example_7_5_1_tvc_formula
#print axioms Miao.IncompleteMarkets.example_7_5_1_tvc
#print axioms Miao.IncompleteMarkets.eu_phelps_derivs
#print axioms Miao.IncompleteMarkets.example_7_5_1_euler
#print axioms Miao.IncompleteMarkets.example_7_5_1
#print axioms Miao.IncompleteMarkets.cd_Utility
#print axioms Miao.IncompleteMarkets.cd_Utility.mk
#print axioms Miao.IncompleteMarkets.cd_Utility.u
#print axioms Miao.IncompleteMarkets.cd_Utility.du
#print axioms Miao.IncompleteMarkets.cd_Utility.hasDerivAt
#print axioms Miao.IncompleteMarkets.cd_Utility.du_pos
#print axioms Miao.IncompleteMarkets.cd_Utility.du_anti
#print axioms Miao.IncompleteMarkets.cd_Utility.du_cont
#print axioms Miao.IncompleteMarkets.cd_Utility.inada_zero
#print axioms Miao.IncompleteMarkets.cd_Utility.inada_top
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_tangent_strict
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_tangent
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_u_strictMono
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_u_strictConcave
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_du_surj
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_duInv
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_duInv_pos
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_du_duInv
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_du_inj
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_duInv_du
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_duInv_anti
#print axioms Miao.IncompleteMarkets.cd_Utility.cd_duInv_cont
#print axioms Miao.IncompleteMarkets.cd_rpow_neg_strictAnti
#print axioms Miao.IncompleteMarkets.cd_crraUtility
#print axioms Miao.IncompleteMarkets.cd_crraUtility_u
#print axioms Miao.IncompleteMarkets.cd_crraUtility_du
#print axioms Miao.IncompleteMarkets.cd_Budget
#print axioms Miao.IncompleteMarkets.cd_NoPonzi
#print axioms Miao.IncompleteMarkets.eq_8_6
#print axioms Miao.IncompleteMarkets.cd_rollover
#print axioms Miao.IncompleteMarkets.cd_summable_pv
#print axioms Miao.IncompleteMarkets.cd_tendsto_div_pow
#print axioms Miao.IncompleteMarkets.theorem_8_3_1
#print axioms Miao.IncompleteMarkets.theorem_8_3_1_pv
#print axioms Miao.IncompleteMarkets.theorem_8_3_1_noPonzi
#print axioms Miao.IncompleteMarkets.cd_telescope
#print axioms Miao.IncompleteMarkets.cd_converse_path
#print axioms Miao.IncompleteMarkets.theorem_8_3_1_converse
#print axioms Miao.IncompleteMarkets.theorem_8_3_1_converse_counterexample
#print axioms Miao.IncompleteMarkets.cd_natural_debt_nonbinding
#print axioms Miao.IncompleteMarkets.cd_IsPath
#print axioms Miao.IncompleteMarkets.cd_change_of_variables
#print axioms Miao.IncompleteMarkets.SIModel
#print axioms Miao.IncompleteMarkets.SIModel.mk
#print axioms Miao.IncompleteMarkets.SIModel.β
#print axioms Miao.IncompleteMarkets.SIModel.R
#print axioms Miao.IncompleteMarkets.SIModel.b
#print axioms Miao.IncompleteMarkets.SIModel.ymin
#print axioms Miao.IncompleteMarkets.SIModel.ymax
#print axioms Miao.IncompleteMarkets.SIModel.μ
#print axioms Miao.IncompleteMarkets.SIModel.u
#print axioms Miao.IncompleteMarkets.SIModel.du
#print axioms Miao.IncompleteMarkets.SIModel.β_pos
#print axioms Miao.IncompleteMarkets.SIModel.β_lt_one
#print axioms Miao.IncompleteMarkets.SIModel.R_pos
#print axioms Miao.IncompleteMarkets.SIModel.b_nonneg
#print axioms Miao.IncompleteMarkets.SIModel.ymin_le_ymax
#print axioms Miao.IncompleteMarkets.SIModel.supp
#print axioms Miao.IncompleteMarkets.SIModel.xmin_pos
#print axioms Miao.IncompleteMarkets.SIModel.u_cont
#print axioms Miao.IncompleteMarkets.SIModel.hasDerivAt_u
#print axioms Miao.IncompleteMarkets.SIModel.du_pos
#print axioms Miao.IncompleteMarkets.SIModel.du_anti
#print axioms Miao.IncompleteMarkets.SIModel.du_cont
#print axioms Miao.IncompleteMarkets.SIModel.inada_zero
#print axioms Miao.IncompleteMarkets.SIModel.inada_top
#print axioms Miao.IncompleteMarkets.si_cash_on_hand
#print axioms Miao.IncompleteMarkets.SIModel.tangent_u
#print axioms Miao.IncompleteMarkets.si_integral_pos
#print axioms Miao.IncompleteMarkets.SIModel.law
#print axioms Miao.IncompleteMarkets.SIModel.r
#print axioms Miao.IncompleteMarkets.SIModel.xmin
#print axioms Miao.IncompleteMarkets.SIModel.next
#print axioms Miao.IncompleteMarkets.SIModel.xmin_pos'
#print axioms Miao.IncompleteMarkets.SIModel.next_ge
#print axioms Miao.IncompleteMarkets.SIModel.next_sub
#print axioms Miao.IncompleteMarkets.SIModel.continuous_next
#print axioms Miao.IncompleteMarkets.SIModel.continuous_next_y
#print axioms Miao.IncompleteMarkets.SIModel.ae_next
#print axioms Miao.IncompleteMarkets.SIModel.integrable_comp
#print axioms Miao.IncompleteMarkets.SIModel.Solution
#print axioms Miao.IncompleteMarkets.SIModel.Solution.mk
#print axioms Miao.IncompleteMarkets.SIModel.Solution.V
#print axioms Miao.IncompleteMarkets.SIModel.Solution.dV
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav
#print axioms Miao.IncompleteMarkets.SIModel.Solution.hasDerivAt_V
#print axioms Miao.IncompleteMarkets.SIModel.Solution.dV_cont
#print axioms Miao.IncompleteMarkets.SIModel.Solution.V_mono
#print axioms Miao.IncompleteMarkets.SIModel.Solution.V_concave
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_mem
#print axioms Miao.IncompleteMarkets.SIModel.Solution.bellman
#print axioms Miao.IncompleteMarkets.SIModel.Solution.bellman_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.envelope
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons
#print axioms Miao.IncompleteMarkets.SIModel.Solution.W
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D
#print axioms Miao.IncompleteMarkets.SIModel.Solution.V_contOn
#print axioms Miao.IncompleteMarkets.SIModel.Solution.dV_strictAnti
#print axioms Miao.IncompleteMarkets.SIModel.Solution.dV_nonneg
#print axioms Miao.IncompleteMarkets.SIModel.Solution.tangent_V
#print axioms Miao.IncompleteMarkets.SIModel.Solution.integrable_V
#print axioms Miao.IncompleteMarkets.SIModel.Solution.integrable_dV
#print axioms Miao.IncompleteMarkets.SIModel.Solution.W_sub_bounds
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_nonneg
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_strictAnti
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_continuousOn
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_eq
#print axioms Miao.IncompleteMarkets.SIModel.Solution.bellman'
#print axioms Miao.IncompleteMarkets.SIModel.Solution.bellman_le'
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_pos
#print axioms Miao.IncompleteMarkets.SIModel.Solution.euler_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.euler_ge
#print axioms Miao.IncompleteMarkets.SIModel.Solution.euler
#print axioms Miao.IncompleteMarkets.SIModel.Solution.dV_pos
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_pos
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_eq
#print axioms Miao.IncompleteMarkets.SIModel.Solution.eq_8_7
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_lt_of_pos
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_lt_of_zero
#print axioms Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_1
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_mono
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_mono
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_sub_bounds
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_sub_bounds
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_lipschitz
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuousOn_sav
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuousOn_cons
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_strictMono_of_pos
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_eq_zero_iff
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_xmin
#print axioms Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_2
#print axioms Miao.IncompleteMarkets.SIModel.next_ymin
#print axioms Miao.IncompleteMarkets.SIModel.next_ymax_sub
#print axioms Miao.IncompleteMarkets.SIModel.footnote_2_mono
#print axioms Miao.IncompleteMarkets.SIModel.footnote_2
#print axioms Miao.IncompleteMarkets.SIModel.du_le_rpow
#print axioms Miao.IncompleteMarkets.SIModel.si_one_add_rpow_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.D_le_low
#print axioms Miao.IncompleteMarkets.SIModel.Solution.high_le_D
#print axioms Miao.IncompleteMarkets.SIModel.Solution.sav_eventually_gt
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_unbounded
#print axioms Miao.IncompleteMarkets.SIModel.Solution.cons_high_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.eq_8_16_identity_false
#print axioms Miao.IncompleteMarkets.SIModel.Solution.eq_8_16
#print axioms Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_3
#print axioms Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_3_all
#print axioms Miao.IncompleteMarkets.SIModel.Solution.fixHigh
#print axioms Miao.IncompleteMarkets.SIModel.Solution.xmax
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuousOn_gap
#print axioms Miao.IncompleteMarkets.SIModel.Solution.ex_8_9
#print axioms Miao.IncompleteMarkets.SIModel.Solution.mapsTo_Icc
#print axioms Miao.IncompleteMarkets.SIWC.IsTransitionFunction
#print axioms Miao.IncompleteMarkets.SIWC.isTransitionFunction_iff
#print axioms Miao.IncompleteMarkets.SIWC.markovOp
#print axioms Miao.IncompleteMarkets.SIWC.markovOpR
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp
#print axioms Miao.IncompleteMarkets.SIWC.markovOp_indicator
#print axioms Miao.IncompleteMarkets.SIWC.theorem_8_1
#print axioms Miao.IncompleteMarkets.SIWC.integrable_of_bounded
#print axioms Miao.IncompleteMarkets.SIWC.theorem_8_1_cor
#print axioms Miao.IncompleteMarkets.SIWC.ex_8_1
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_apply
#print axioms Miao.IncompleteMarkets.SIWC.theorem_8_2
#print axioms Miao.IncompleteMarkets.SIWC.ex_8_2
#print axioms Miao.IncompleteMarkets.SIWC.theorem_8_3
#print axioms Miao.IncompleteMarkets.SIWC.theorem_8_3_cor
#print axioms Miao.IncompleteMarkets.SIWC.pairing
#print axioms Miao.IncompleteMarkets.SIWC.ex_8_3
#print axioms Miao.IncompleteMarkets.SIWC.kpow
#print axioms Miao.IncompleteMarkets.SIWC.kpow_one
#print axioms Miao.IncompleteMarkets.SIWC.ex_8_4a
#print axioms Miao.IncompleteMarkets.SIWC.kpow_add
#print axioms Miao.IncompleteMarkets.SIWC.markovOp_comp
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_comp
#print axioms Miao.IncompleteMarkets.SIWC.ex_8_4b
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_iterate
#print axioms Miao.IncompleteMarkets.SIWC.IsFeller
#print axioms Miao.IncompleteMarkets.SIWC.IsMonotoneTF
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_1
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_2
#print axioms Miao.IncompleteMarkets.SIWC.bump
#print axioms Miao.IncompleteMarkets.SIWC.continuous_bump
#print axioms Miao.IncompleteMarkets.SIWC.bump_mem
#print axioms Miao.IncompleteMarkets.SIWC.bump_eq_one
#print axioms Miao.IncompleteMarkets.SIWC.bump_antitone
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_bump
#print axioms Miao.IncompleteMarkets.SIWC.ConvWeak
#print axioms Miao.IncompleteMarkets.SIWC.lemma_12_1
#print axioms Miao.IncompleteMarkets.SIWC.count_bounds
#print axioms Miao.IncompleteMarkets.SIWC.lemma_12_2
#print axioms Miao.IncompleteMarkets.SIWC.LimsupLe
#print axioms Miao.IncompleteMarkets.SIWC.LiminfGe
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_of_limsup_liminf
#print axioms Miao.IncompleteMarkets.SIWC.toBCF
#print axioms Miao.IncompleteMarkets.SIWC.limsup_closed_of_weak
#print axioms Miao.IncompleteMarkets.SIWC.limsup_integral_of_closed
#print axioms Miao.IncompleteMarkets.SIWC.weak_of_limsup_closed
#print axioms Miao.IncompleteMarkets.SIWC.liminf_open_of_limsup_closed
#print axioms Miao.IncompleteMarkets.SIWC.limsup_closed_of_liminf_open
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_of_null_frontier
#print axioms Miao.IncompleteMarkets.SIWC.limsup_closed_of_null_frontier
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_3
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_finite_union
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_4
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_5
#print axioms Miao.IncompleteMarkets.SIWC.IsConvDetermining
#print axioms Miao.IncompleteMarkets.SIWC.frontier_iInter_fin_subset
#print axioms Miao.IncompleteMarkets.SIWC.ballInters
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_5_cor
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_6
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_6_cor1
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_6_cor2
#print axioms Miao.IncompleteMarkets.SIWC.convWeak_unique
#print axioms Miao.IncompleteMarkets.SIWC.IsConvDetermining.eq
#print axioms Miao.IncompleteMarkets.SIWC.distFun
#print axioms Miao.IncompleteMarkets.SIWC.box
#print axioms Miao.IncompleteMarkets.SIWC.vertex
#print axioms Miao.IncompleteMarkets.SIWC.vertexSum
#print axioms Miao.IncompleteMarkets.SIWC.diag
#print axioms Miao.IncompleteMarkets.SIWC.ContFromAbove
#print axioms Miao.IncompleteMarkets.SIWC.ContFromBelow
#print axioms Miao.IncompleteMarkets.SIWC.Iic_eq_pi
#print axioms Miao.IncompleteMarkets.SIWC.box_indicator_eq
#print axioms Miao.IncompleteMarkets.SIWC.measurableSet_box
#print axioms Miao.IncompleteMarkets.SIWC.vertexSum_eq
#print axioms Miao.IncompleteMarkets.SIWC.distFun_mono
#print axioms Miao.IncompleteMarkets.SIWC.contFromAbove_distFun
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_7a
#print axioms Miao.IncompleteMarkets.SIWC.generateFrom_Iic_pi
#print axioms Miao.IncompleteMarkets.SIWC.distFun_injective
#print axioms Miao.IncompleteMarkets.SIWC.lowerOpen
#print axioms Miao.IncompleteMarkets.SIWC.frontier_Iic_eq
#print axioms Miao.IncompleteMarkets.SIWC.lowerOpen_subset
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_distFun_below
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_7c
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_3
#print axioms Miao.IncompleteMarkets.SIWC.nullCoord
#print axioms Miao.IncompleteMarkets.SIWC.countable_nullCoord_compl
#print axioms Miao.IncompleteMarkets.SIWC.dense_nullCoord
#print axioms Miao.IncompleteMarkets.SIWC.continuousAt_distFun
#print axioms Miao.IncompleteMarkets.SIWC.frontier_null_of_continuousAt
#print axioms Miao.IncompleteMarkets.SIWC.box_inter
#print axioms Miao.IncompleteMarkets.SIWC.box_eq_empty
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_8
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_4
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_5a
#print axioms Miao.IncompleteMarkets.SIWC.ramp
#print axioms Miao.IncompleteMarkets.SIWC.continuous_ramp
#print axioms Miao.IncompleteMarkets.SIWC.ramp_mem
#print axioms Miao.IncompleteMarkets.SIWC.monotone_ramp
#print axioms Miao.IncompleteMarkets.SIWC.tendsto_ramp
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_5b
#print axioms Miao.IncompleteMarkets.SIWC.IsSupport
#print axioms Miao.IncompleteMarkets.SIWC.support_inter
#print axioms Miao.IncompleteMarkets.SIWC.exists_support
#print axioms Miao.IncompleteMarkets.SIWC.exists_convWeak_subseq_of_tight
#print axioms Miao.IncompleteMarkets.SIWC.measure_eq_one_of_convWeak
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_9_cor1
#print axioms Miao.IncompleteMarkets.SIWC.concentrated_iff
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_9
#print axioms Miao.IncompleteMarkets.SIWC.distFun_dirac
#print axioms Miao.IncompleteMarkets.SIWC.not_convWeak_escape
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_9_false_hyp
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_9_false_concl
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_6a
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_6a_false
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_6b
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_6c
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_9_cor2
#print axioms Miao.IncompleteMarkets.SIWC.bcf_abs_le_norm
#print axioms Miao.IncompleteMarkets.SIWC.convWeak_dirac
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_dirac
#print axioms Miao.IncompleteMarkets.SIWC.integral_markovOpR
#print axioms Miao.IncompleteMarkets.SIWC.fellerBCF
#print axioms Miao.IncompleteMarkets.SIWC.fellerBCF_apply
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_7
#print axioms Miao.IncompleteMarkets.SIWC.flipKernel
#print axioms Miao.IncompleteMarkets.SIWC.isMarkovKernel_flipKernel
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_flip
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_flip_dirac
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_8a
#print axioms Miao.IncompleteMarkets.SIWC.iterate_flip_dirac
#print axioms Miao.IncompleteMarkets.SIWC.symm_ne_self
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_8b
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_8c
#print axioms Miao.IncompleteMarkets.SIWC.isProbabilityMeasure_iterate
#print axioms Miao.IncompleteMarkets.SIWC.invariant_of_convWeak
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_10
#print axioms Miao.IncompleteMarkets.SIWC.Dominates
#print axioms Miao.IncompleteMarkets.SIWC.Dominates.trans
#print axioms Miao.IncompleteMarkets.SIWC.Dominates.real_le
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_9a
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_9a_subtype
#print axioms Miao.IncompleteMarkets.SIWC.measure_lower_le
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_9b
#print axioms Miao.IncompleteMarkets.SIWC.real_half_dirac
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_9c
#print axioms Miao.IncompleteMarkets.SIWC.distFun_map_val
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_10
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_11
#print axioms Miao.IncompleteMarkets.SIWC.markovOpR_kpow_zero
#print axioms Miao.IncompleteMarkets.SIWC.markovOpR_kpow_add
#print axioms Miao.IncompleteMarkets.SIWC.isMonotoneTF_kpow
#print axioms Miao.IncompleteMarkets.SIWC.iterate_dirac
#print axioms Miao.IncompleteMarkets.SIWC.dominates_iterate
#print axioms Miao.IncompleteMarkets.SIWC.IccBot
#print axioms Miao.IncompleteMarkets.SIWC.IccTop
#print axioms Miao.IncompleteMarkets.SIWC.IccBot_le
#print axioms Miao.IncompleteMarkets.SIWC.le_IccTop
#print axioms Miao.IncompleteMarkets.SIWC.dominates_dirac_bot_top
#print axioms Miao.IncompleteMarkets.SIWC.exists_subtype_measure
#print axioms Miao.IncompleteMarkets.SIWC.map_val_Icc
#print axioms Miao.IncompleteMarkets.SIWC.convWeak_of_dominance_mono
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_12
#print axioms Miao.IncompleteMarkets.SIWC.Assumption12_1
#print axioms Miao.IncompleteMarkets.SIWC.ex_12_14
#print axioms Miao.IncompleteMarkets.SIWC.lemma_12_11
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_12
#print axioms Miao.IncompleteMarkets.SIWC.transportK
#print axioms Miao.IncompleteMarkets.SIWC.transportK_apply
#print axioms Miao.IncompleteMarkets.SIWC.isMarkovKernel_transportK
#print axioms Miao.IncompleteMarkets.SIWC.adjointOp_transportK_map
#print axioms Miao.IncompleteMarkets.SIWC.iterate_transportK_map
#print axioms Miao.IncompleteMarkets.SIWC.kpow_transportK
#print axioms Miao.IncompleteMarkets.SIWC.markovOpR_transportK
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_12_of_orderIso
#print axioms Miao.IncompleteMarkets.SIWC.realToFin1
#print axioms Miao.IncompleteMarkets.SIWC.continuous_realToFin1
#print axioms Miao.IncompleteMarkets.SIWC.continuous_realToFin1_symm
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_12_real
#print axioms Miao.IncompleteMarkets.SIWC.prodToFin2
#print axioms Miao.IncompleteMarkets.SIWC.continuous_prodToFin2
#print axioms Miao.IncompleteMarkets.SIWC.continuous_prodToFin2_symm
#print axioms Miao.IncompleteMarkets.SIWC.theorem_12_12_prod
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kmap
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuous_kmap
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuous_kmap_y
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kernel
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kernel_eq
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kernel_apply
#print axioms Miao.IncompleteMarkets.SIModel.Solution.isMarkovKernel_kernel
#print axioms Miao.IncompleteMarkets.SIModel.Solution.markovOpR_kernel
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kmap_mono
#print axioms Miao.IncompleteMarkets.SIModel.Solution.isMonotoneTF_kernel
#print axioms Miao.IncompleteMarkets.SIModel.Solution.isFeller_kernel
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_zero
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_succ
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_ge
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_succ_ge
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_mono
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_mem
#print axioms Miao.IncompleteMarkets.SIModel.Solution.continuousOn_phi
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_high_monotone
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_two_eq_one
#print axioms Miao.IncompleteMarkets.SIModel.Solution.si_kpow_succ_ge_pow
#print axioms Miao.IncompleteMarkets.SIModel.Solution.si_clamp_mem
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kpow_ge
#print axioms Miao.IncompleteMarkets.SIModel.Solution.kpow_ge_real
#print axioms Miao.IncompleteMarkets.SIModel.Solution.next_low_lt
#print axioms Miao.IncompleteMarkets.SIModel.Solution.next_low_le
#print axioms Miao.IncompleteMarkets.SIModel.Solution.phi_low_tendsto
#print axioms Miao.IncompleteMarkets.SIModel.Solution.mixing
#print axioms Miao.IncompleteMarkets.SIModel.Solution.proposition_8_3_1
#print axioms Miao.IncompleteMarkets.ay_Budget
#print axioms Miao.IncompleteMarkets.eq_17_2
#print axioms Miao.IncompleteMarkets.ay_natural_limit
#print axioms Miao.IncompleteMarkets.ay_phi
#print axioms Miao.IncompleteMarkets.eq_17_3b
#print axioms Miao.IncompleteMarkets.eq_17_3a
#print axioms Miao.IncompleteMarkets.ay_cash_on_hand
#print axioms Miao.IncompleteMarkets.ay_BellmanCoh
#print axioms Miao.IncompleteMarkets.ay_Bellman
#print axioms Miao.IncompleteMarkets.eq_17_4
#print axioms Miao.IncompleteMarkets.ay_P
#print axioms Miao.IncompleteMarkets.ay_P_apply
#print axioms Miao.IncompleteMarkets.ay_P_markov
#print axioms Miao.IncompleteMarkets.ay_lamSeq
#print axioms Miao.IncompleteMarkets.ay_lamSeq_succ
#print axioms Miao.IncompleteMarkets.ay_Stationary
#print axioms Miao.IncompleteMarkets.eq_17_7
#print axioms Miao.IncompleteMarkets.ay_stationary_fst
#print axioms Miao.IncompleteMarkets.ay_stationary_snd
#print axioms Miao.IncompleteMarkets.ay_stationary_snd_iid
#print axioms Miao.IncompleteMarkets.ay_Ea
#print axioms Miao.IncompleteMarkets.ay_Ea_eq_mean
#print axioms Miao.IncompleteMarkets.ay_bellmanCoh_of_SI
#print axioms Miao.IncompleteMarkets.ay_IsStationaryCoh
#print axioms Miao.IncompleteMarkets.ay_stationary_exists
#print axioms Miao.IncompleteMarkets.ay_EaIid
#print axioms Miao.IncompleteMarkets.ay_EaIid_bounds
#print axioms Miao.IncompleteMarkets.ay_beta_R_lt_one
#print axioms Miao.IncompleteMarkets.ay_r_lt_rho
#print axioms Miao.IncompleteMarkets.ay_CRS
#print axioms Miao.IncompleteMarkets.ay_profit
#print axioms Miao.IncompleteMarkets.ay_isLocalMax_of_max
#print axioms Miao.IncompleteMarkets.eq_17_5_17_6
#print axioms Miao.IncompleteMarkets.ay_euler_crs
#print axioms Miao.IncompleteMarkets.ay_zero_profit
#print axioms Miao.IncompleteMarkets.ay_cdF
#print axioms Miao.IncompleteMarkets.ay_cdFK
#print axioms Miao.IncompleteMarkets.ay_cdFL
#print axioms Miao.IncompleteMarkets.ay_cd_crs
#print axioms Miao.IncompleteMarkets.ay_rpow_ratio
#print axioms Miao.IncompleteMarkets.ay_cd_hasDerivAt_K
#print axioms Miao.IncompleteMarkets.ay_cd_hasDerivAt_L
#print axioms Miao.IncompleteMarkets.ay_Kd
#print axioms Miao.IncompleteMarkets.ay_Kd_foc
#print axioms Miao.IncompleteMarkets.ay_cdFK_strictAnti
#print axioms Miao.IncompleteMarkets.ay_Kd_unique
#print axioms Miao.IncompleteMarkets.ay_Kd_strictAnti
#print axioms Miao.IncompleteMarkets.ay_Kd_continuousOn
#print axioms Miao.IncompleteMarkets.ay_Kd_tendsto
#print axioms Miao.IncompleteMarkets.ay_FK_pos_rate
#print axioms Miao.IncompleteMarkets.ay_wage
#print axioms Miao.IncompleteMarkets.ay_wage_continuousOn
#print axioms Miao.IncompleteMarkets.ay_saving_rate
#print axioms Miao.IncompleteMarkets.ay_saving_rate_misprint
#print axioms Miao.IncompleteMarkets.AYEconomy
#print axioms Miao.IncompleteMarkets.AYEconomy.mk
#print axioms Miao.IncompleteMarkets.AYEconomy.β
#print axioms Miao.IncompleteMarkets.AYEconomy.δ
#print axioms Miao.IncompleteMarkets.AYEconomy.b
#print axioms Miao.IncompleteMarkets.AYEconomy.lmin
#print axioms Miao.IncompleteMarkets.AYEconomy.lmax
#print axioms Miao.IncompleteMarkets.AYEconomy.u
#print axioms Miao.IncompleteMarkets.AYEconomy.F
#print axioms Miao.IncompleteMarkets.AYEconomy.Q
#print axioms Miao.IncompleteMarkets.AYEconomy.Q_markov
#print axioms Miao.IncompleteMarkets.AYStationaryEqm
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.mk
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.V
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.g
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.c
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.K
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.L
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.r
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.w
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.lam
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.lam_prob
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.g_meas
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.supp
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.household
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.cons_eq
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.K_pos
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.L_pos
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.firm
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.labor
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.asset
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.resource
#print axioms Miao.IncompleteMarkets.AYStationaryEqm.stationary
#print axioms Miao.IncompleteMarkets.definition_17_1_1
#print axioms Miao.IncompleteMarkets.ay_resource_redundant
#print axioms Miao.IncompleteMarkets.ay_labor_iid
#print axioms Miao.IncompleteMarkets.ay_exampleEconomy
#print axioms Miao.IncompleteMarkets.ay_example_phi
#print axioms Miao.IncompleteMarkets.ay_exampleEqm
#print axioms Miao.IncompleteMarkets.ay_example_exists
#print axioms Miao.IncompleteMarkets.ay_rho
#print axioms Miao.IncompleteMarkets.ay_complete_markets_rate
#print axioms Miao.IncompleteMarkets.ay_existence
#print axioms Miao.IncompleteMarkets.ay_existence_cd
#print axioms Miao.IncompleteMarkets.ay_overaccumulation
#print axioms Miao.IncompleteMarkets.ay_existence_example
#print axioms Miao.IncompleteMarkets.ay_bisect
#print axioms Miao.IncompleteMarkets.ay_bisect_direction
#print axioms Miao.IncompleteMarkets.ay_bisect_fixed
#print axioms Miao.IncompleteMarkets.ay_gridUpdate
#print axioms Miao.IncompleteMarkets.ay_gridUpdate_rect
#print axioms Miao.IncompleteMarkets.ay_gridUpdate_mass
#print axioms Miao.IncompleteMarkets.ay_damp
#print axioms Miao.IncompleteMarkets.ay_damp_fixed
#print axioms Miao.IncompleteMarkets.ay_damp_between
#print axioms Miao.IncompleteMarkets.ay_lorenz
#print axioms Miao.IncompleteMarkets.ay_gini
#print axioms Miao.IncompleteMarkets.ay_gini_eq_area
#print axioms Miao.IncompleteMarkets.ay_lorenz_zero
#print axioms Miao.IncompleteMarkets.ay_lorenz_n
#print axioms Miao.IncompleteMarkets.ay_lorenz_mono
#print axioms Miao.IncompleteMarkets.ay_lorenz_le_diag
#print axioms Miao.IncompleteMarkets.ay_sum_odd
#print axioms Miao.IncompleteMarkets.ay_gini_nonneg
#print axioms Miao.IncompleteMarkets.ay_gini_le
#print axioms Miao.IncompleteMarkets.ay_gini_equal
#print axioms Miao.IncompleteMarkets.ay_gini_concentrated
#print axioms Miao.IncompleteMarkets.ay_gini_concentrated_ne_one
#print axioms Miao.IncompleteMarkets.ay_gini_concentrated_tendsto
#print axioms Miao.IncompleteMarkets.ay_BellmanLeisure
#print axioms Miao.IncompleteMarkets.ex_17_4_foc
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.mk
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.β
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.δ
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.b
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.lmin
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.lmax
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.u
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.F
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.Q
#print axioms Miao.IncompleteMarkets.AYLeisureEconomy.Q_markov
#print axioms Miao.IncompleteMarkets.AYLeisureEqm
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.mk
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.V
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.g
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.n
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.c
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.K
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.L
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.r
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.w
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.lam
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.lam_prob
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.g_meas
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.supp
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.household
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.cons_eq
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.K_pos
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.L_pos
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.firm
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.labor
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.asset
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.resource
#print axioms Miao.IncompleteMarkets.AYLeisureEqm.stationary
#print axioms Miao.IncompleteMarkets.ex_17_4_firm
#print axioms Miao.IncompleteMarkets.ay_leisureEconomy
#print axioms Miao.IncompleteMarkets.ay_leisure_phi
#print axioms Miao.IncompleteMarkets.ay_leisureEqm
#print axioms Miao.IncompleteMarkets.ex_17_4
#print axioms Miao.IncompleteMarkets.BWEconomy
#print axioms Miao.IncompleteMarkets.BWEconomy.mk
#print axioms Miao.IncompleteMarkets.BWEconomy.β
#print axioms Miao.IncompleteMarkets.BWEconomy.u
#print axioms Miao.IncompleteMarkets.BWEconomy.Q
#print axioms Miao.IncompleteMarkets.BWEconomy.e
#print axioms Miao.IncompleteMarkets.BWEconomy.Bellman
#print axioms Miao.IncompleteMarkets.BWEconomy.Stationary
#print axioms Miao.IncompleteMarkets.BWEconomy.EaSet
#print axioms Miao.IncompleteMarkets.bw_shift
#print axioms Miao.IncompleteMarkets.bw_shift_apply
#print axioms Miao.IncompleteMarkets.bw_bellman_shift
#print axioms Miao.IncompleteMarkets.bw_bellman_shift_iff
#print axioms Miao.IncompleteMarkets.bw_stationary_shift
#print axioms Miao.IncompleteMarkets.bw_supp_shift
#print axioms Miao.IncompleteMarkets.bw_integrable_shift
#print axioms Miao.IncompleteMarkets.bw_integral_shift
#print axioms Miao.IncompleteMarkets.bw_isProb_shift
#print axioms Miao.IncompleteMarkets.bw_EaSet_shift
#print axioms Miao.IncompleteMarkets.bw_EaSet_shift_eq
#print axioms Miao.IncompleteMarkets.proposition_17_2_1_policy
#print axioms Miao.IncompleteMarkets.proposition_17_2_1
#print axioms Miao.IncompleteMarkets.bw_natural_limit
#print axioms Miao.IncompleteMarkets.BWHuggettEqm
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.mk
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.V
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.g
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.r
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.lam
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.isProb
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.supp
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.bellman
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.integrable
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.clear
#print axioms Miao.IncompleteMarkets.BWHuggettEqm.stationary
#print axioms Miao.IncompleteMarkets.definition_17_2_1
#print axioms Miao.IncompleteMarkets.bw_fiat_budget
#print axioms Miao.IncompleteMarkets.bw_fiat_quantity_theory
#print axioms Miao.IncompleteMarkets.bw_fiat_neutral
#print axioms Miao.IncompleteMarkets.bw_fiat_borrowing_raises_price
#print axioms Miao.IncompleteMarkets.bw_fiat_driven_out
#print axioms Miao.IncompleteMarkets.eq_17_9
#print axioms Miao.IncompleteMarkets.eq_17_10
#print axioms Miao.IncompleteMarkets.bw_bewley_budget
#print axioms Miao.IncompleteMarkets.bw_bewley_mapping
#print axioms Miao.IncompleteMarkets.BWBewleyEqm
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.mk
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.M
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.p
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.τ
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.rt
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.V
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.h
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.lam
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.M_pos
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.p_pos
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.gov
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.isProb
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.supp
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.bellman
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.integrable
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.clear
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.stationary
#print axioms Miao.IncompleteMarkets.eq_17_11
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.phi_pos
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.tau_eq
#print axioms Miao.IncompleteMarkets.BWBewleyEqm.toHuggett
#print axioms Miao.IncompleteMarkets.proposition_17_2_2
#print axioms Miao.IncompleteMarkets.bw_backSolve
#print axioms Miao.IncompleteMarkets.bw_backsolving
#print axioms Miao.IncompleteMarkets.bw_bewley_real_balances_le
#print axioms Miao.IncompleteMarkets.proposition_17_2_3_rates
#print axioms Miao.IncompleteMarkets.bw_huggett_limit_le_natural
#print axioms Miao.IncompleteMarkets.bw_implicit_money
#print axioms Miao.IncompleteMarkets.bw_implicit_rate
#print axioms Miao.IncompleteMarkets.bw_implicit_tax
#print axioms Miao.IncompleteMarkets.bw_implicit_budget
#print axioms Miao.IncompleteMarkets.bw_implicit_deflation
#print axioms Miao.IncompleteMarkets.bw_cycle
#print axioms Miao.IncompleteMarkets.bw_cycleV
#print axioms Miao.IncompleteMarkets.bw_cycleG
#print axioms Miao.IncompleteMarkets.bw_cycle_Q
#print axioms Miao.IncompleteMarkets.bw_cycle_integral
#print axioms Miao.IncompleteMarkets.bw_cycle_bellman
#print axioms Miao.IncompleteMarkets.bw_cycleLam
#print axioms Miao.IncompleteMarkets.bw_cycleLam_isProb
#print axioms Miao.IncompleteMarkets.bw_cycleLam_supp
#print axioms Miao.IncompleteMarkets.bw_cycle_stationary
#print axioms Miao.IncompleteMarkets.bw_cycle_integrable
#print axioms Miao.IncompleteMarkets.bw_cycle_mean
#print axioms Miao.IncompleteMarkets.bw_cycle_EaSet
#print axioms Miao.IncompleteMarkets.bw_cycle_fiat
#print axioms Miao.IncompleteMarkets.bw_cycle_huggett
#print axioms Miao.IncompleteMarkets.bw_cycle_bewley
#print axioms Miao.IncompleteMarkets.bw_cohStationary
#print axioms Miao.IncompleteMarkets.bw_savc_continuous
#print axioms Miao.IncompleteMarkets.bw_next_continuous
#print axioms Miao.IncompleteMarkets.bw_sm_integral
#print axioms Miao.IncompleteMarkets.bw_ae_ge
#print axioms Miao.IncompleteMarkets.bw_coh_lintegral
#print axioms Miao.IncompleteMarkets.bw_coh_integral
#print axioms Miao.IncompleteMarkets.proposition_17_2_3_lt
#print axioms Miao.IncompleteMarkets.bw_seign_budget
#print axioms Miao.IncompleteMarkets.bw_seign_mbar
#print axioms Miao.IncompleteMarkets.bw_seign_neg_rate
#print axioms Miao.IncompleteMarkets.bw_seign_hyperbola
#print axioms Miao.IncompleteMarkets.bw_seign_initial_price
#print axioms Miao.IncompleteMarkets.bw_seign_quantity_theory
#print axioms Miao.IncompleteMarkets.bw_seign_comparative_statics
#print axioms Miao.IncompleteMarkets.BWAggEconomy
#print axioms Miao.IncompleteMarkets.BWAggEconomy.mk
#print axioms Miao.IncompleteMarkets.BWAggEconomy.β
#print axioms Miao.IncompleteMarkets.BWAggEconomy.u
#print axioms Miao.IncompleteMarkets.BWAggEconomy.F
#print axioms Miao.IncompleteMarkets.BWAggEconomy.FK
#print axioms Miao.IncompleteMarkets.BWAggEconomy.FL
#print axioms Miao.IncompleteMarkets.BWAggEconomy.δ
#print axioms Miao.IncompleteMarkets.BWAggEconomy.zval
#print axioms Miao.IncompleteMarkets.BWAggEconomy.lab
#print axioms Miao.IncompleteMarkets.BWAggEconomy.Q
#print axioms Miao.IncompleteMarkets.BWAggEconomy.πz
#print axioms Miao.IncompleteMarkets.BWAggEconomy.hasDerivAt_K
#print axioms Miao.IncompleteMarkets.BWAggEconomy.hasDerivAt_L
#print axioms Miao.IncompleteMarkets.BWAggEconomy.marg
#print axioms Miao.IncompleteMarkets.bw_aggK
#print axioms Miao.IncompleteMarkets.bw_aggL
#print axioms Miao.IncompleteMarkets.BWAggEconomy.Bellman
#print axioms Miao.IncompleteMarkets.BWAggEconomy.BookLaw
#print axioms Miao.IncompleteMarkets.BWAggEconomy.Law
#print axioms Miao.IncompleteMarkets.BWRecEqm
#print axioms Miao.IncompleteMarkets.BWRecEqm.mk
#print axioms Miao.IncompleteMarkets.BWRecEqm.V
#print axioms Miao.IncompleteMarkets.BWRecEqm.g
#print axioms Miao.IncompleteMarkets.BWRecEqm.G
#print axioms Miao.IncompleteMarkets.BWRecEqm.r
#print axioms Miao.IncompleteMarkets.BWRecEqm.w
#print axioms Miao.IncompleteMarkets.BWRecEqm.bellman
#print axioms Miao.IncompleteMarkets.BWRecEqm.firmK
#print axioms Miao.IncompleteMarkets.BWRecEqm.firmL
#print axioms Miao.IncompleteMarkets.BWRecEqm.law
#print axioms Miao.IncompleteMarkets.bw_book_law_mass
#print axioms Miao.IncompleteMarkets.bw_book_law_not_prob
#print axioms Miao.IncompleteMarkets.bw_law_isProb
#print axioms Miao.IncompleteMarkets.bw_law_marginal
#print axioms Miao.IncompleteMarkets.bw_next_capital_indep
#print axioms Miao.IncompleteMarkets.bw_law_indep
#print axioms Miao.IncompleteMarkets.bw_distPath
#print axioms Miao.IncompleteMarkets.bw_assetPath
#print axioms Miao.IncompleteMarkets.bw_sequential_of_recursive
#print axioms Miao.IncompleteMarkets.bw_aggExample
#print axioms Miao.IncompleteMarkets.bw_aggExample_Q
#print axioms Miao.IncompleteMarkets.bw_recEqm_example
#print axioms Miao.IncompleteMarkets.bw_moments
#print axioms Miao.IncompleteMarkets.bw_moments_first
#print axioms Miao.IncompleteMarkets.bw_ksLaw
#print axioms Miao.IncompleteMarkets.eq_17_12
#print axioms Miao.IncompleteMarkets.bw_ksR
#print axioms Miao.IncompleteMarkets.bw_ksW
#print axioms Miao.IncompleteMarkets.bw_ks_prices
#print axioms Miao.IncompleteMarkets.bw_ksBellman
#print axioms Miao.IncompleteMarkets.bw_mean
#print axioms Miao.IncompleteMarkets.bw_olsSlope
#print axioms Miao.IncompleteMarkets.bw_olsIntercept
#print axioms Miao.IncompleteMarkets.bw_rsq
#print axioms Miao.IncompleteMarkets.bw_ols_exact
#print axioms Miao.IncompleteMarkets.bw_rsq_exact
#print axioms Miao.IncompleteMarkets.bw_ksSample
#print axioms Miao.IncompleteMarkets.bw_ksUpdate
#print axioms Miao.IncompleteMarkets.bw_ksConsistent
#print axioms Miao.IncompleteMarkets.bw_ks_fixed_point_of_exact
#print axioms Miao.IncompleteMarkets.BWLeisureEqm
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.mk
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.V
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.g
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.n
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.G
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.r
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.w
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.bellman
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.firmK
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.firmL
#print axioms Miao.IncompleteMarkets.BWLeisureEqm.law
#print axioms Miao.IncompleteMarkets.ex_17_5
#print axioms Miao.IncompleteMarkets.BWImroParams
#print axioms Miao.IncompleteMarkets.BWImroParams.mk
#print axioms Miao.IncompleteMarkets.BWImroParams.β
#print axioms Miao.IncompleteMarkets.BWImroParams.γ
#print axioms Miao.IncompleteMarkets.BWImroParams.y
#print axioms Miao.IncompleteMarkets.BWImroParams.θ
#print axioms Miao.IncompleteMarkets.BWImroParams.g
#print axioms Miao.IncompleteMarkets.BWImroParams.trans
#print axioms Miao.IncompleteMarkets.BWImroParams.toEconomy
#print axioms Miao.IncompleteMarkets.BWImroParams.rate
#print axioms Miao.IncompleteMarkets.BWImroParams.income
#print axioms Miao.IncompleteMarkets.ex_17_6_inflation
#print axioms Miao.IncompleteMarkets.ex_17_6_a
#print axioms Miao.IncompleteMarkets.BWImroEqm
#print axioms Miao.IncompleteMarkets.BWImroEqm.mk
#print axioms Miao.IncompleteMarkets.BWImroEqm.mbar
#print axioms Miao.IncompleteMarkets.BWImroEqm.V
#print axioms Miao.IncompleteMarkets.BWImroEqm.h
#print axioms Miao.IncompleteMarkets.BWImroEqm.lam
#print axioms Miao.IncompleteMarkets.BWImroEqm.β_pos
#print axioms Miao.IncompleteMarkets.BWImroEqm.β_lt_one
#print axioms Miao.IncompleteMarkets.BWImroEqm.γ_pos
#print axioms Miao.IncompleteMarkets.BWImroEqm.γ_ne_one
#print axioms Miao.IncompleteMarkets.BWImroEqm.y_pos
#print axioms Miao.IncompleteMarkets.BWImroEqm.θ_pos
#print axioms Miao.IncompleteMarkets.BWImroEqm.θ_lt_one
#print axioms Miao.IncompleteMarkets.BWImroEqm.g_gt
#print axioms Miao.IncompleteMarkets.BWImroEqm.mbar_pos
#print axioms Miao.IncompleteMarkets.BWImroEqm.isProb
#print axioms Miao.IncompleteMarkets.BWImroEqm.supp
#print axioms Miao.IncompleteMarkets.BWImroEqm.bellman
#print axioms Miao.IncompleteMarkets.BWImroEqm.integrable
#print axioms Miao.IncompleteMarkets.BWImroEqm.clear
#print axioms Miao.IncompleteMarkets.BWImroEqm.stationary
#print axioms Miao.IncompleteMarkets.bw_imroExample
#print axioms Miao.IncompleteMarkets.bw_imroExample_u
#print axioms Miao.IncompleteMarkets.bw_imroExample_Q
#print axioms Miao.IncompleteMarkets.bw_imroExample_rate
#print axioms Miao.IncompleteMarkets.bw_imroExample_income
#print axioms Miao.IncompleteMarkets.bw_sqrt_add_le
#print axioms Miao.IncompleteMarkets.ex_17_6_b
