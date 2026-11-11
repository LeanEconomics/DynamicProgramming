/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Transition functions: the Markov operator and the Feller property

Copied from `RecursiveMethods/StochasticDP` (`TransitionFunctions.lean`, excerpt), namespace
renamed.

SLP §8.1, pp. 212–220: the Markov operator `T` on real functions (`markovOpR`) and the Feller
property (`IsFeller`, p. 220). A transition function is a Mathlib Markov kernel `Kernel Z Z`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z] (κ : Kernel Z Z)

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

end Miao.FiniteHorizonDP
