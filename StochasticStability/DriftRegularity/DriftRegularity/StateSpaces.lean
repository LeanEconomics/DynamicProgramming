/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# The three kinds of state space (MT §3.1)

Meyn and Tweedie, §3.1, p. 50, "State space definitions".

* `IsCountableStateSpace`: `X` is countable and every subset is measurable.
* `IsGeneralStateSpace`: the σ-algebra of `X` is countably generated.
* `IsTopologicalStateSpace`: `X` is locally compact, separable and metrizable, with its Borel
  σ-algebra.
* `IsCountableStateSpace.isGeneral`, `IsTopologicalStateSpace.isGeneral`: countable and
  topological state spaces are general state spaces.

None of the results of this chapter need these assumptions: the construction of the chain
(Theorem 3.4.1) and the Markov and strong Markov properties hold on every measurable space.

**Corrections.** None.
-/

namespace MeynTweedie.DriftRegularity

variable (X : Type*) [MeasurableSpace X]

/-- A countable state space (MT p. 50): `X` is countable and `B(X)` is all subsets of `X`. -/
def IsCountableStateSpace : Prop := Countable X ∧ ∀ s : Set X, MeasurableSet s

/-- A general state space (MT p. 50): `B(X)` is countably generated. -/
def IsGeneralStateSpace : Prop := MeasurableSpace.CountablyGenerated X

/-- A topological state space (MT p. 50): a locally compact, separable, metrizable space with
its Borel σ-algebra. -/
def IsTopologicalStateSpace [TopologicalSpace X] : Prop :=
  LocallyCompactSpace X ∧ TopologicalSpace.SeparableSpace X ∧
    TopologicalSpace.MetrizableSpace X ∧ BorelSpace X

variable {X}

/-- A countable state space is a general state space. -/
theorem IsCountableStateSpace.isGeneral (h : IsCountableStateSpace X) :
    IsGeneralStateSpace X := by
  obtain ⟨h1, h2⟩ := h
  have : MeasurableSingletonClass X := ⟨fun x => h2 {x}⟩
  exact inferInstanceAs (MeasurableSpace.CountablyGenerated X)

/-- A topological state space is a general state space. -/
theorem IsTopologicalStateSpace.isGeneral [TopologicalSpace X] (h : IsTopologicalStateSpace X) :
    IsGeneralStateSpace X := by
  obtain ⟨-, h2, h3, h4⟩ := h
  let := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  have := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  exact inferInstanceAs (MeasurableSpace.CountablyGenerated X)

end MeynTweedie.DriftRegularity
