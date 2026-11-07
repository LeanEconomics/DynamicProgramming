/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Deterministic

/-!
# Two ways of building stochastic kernels

Copied from `EconomicDynamics/FiniteHorizonDP` (module `MDPKernelTools`), namespace renamed.

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `KernelTools`),
with the namespace renamed.

Tools for the examples of Miao, §5.2, pp. 143–154.

* `famKernel κ`: for a countable action set with measurable singletons, the kernel
  `P(s, a; ·) = κ_a(s; ·)` built from one kernel per action (the discrete choice, stopping and
  bandit models).
* `pushKernel κ F`: the law of `F(x, ε)` when `ε ~ κ(x, ·)`, i.e. `x ↦ κ(x, ·) ∘ F(x, ·)⁻¹`
  (laws of motion driven by a shock, as in the optimal control model).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {S A S' : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace S']

/-- The kernel `P(s, a; ·) = κ_a(s; ·)` on `S × A` for a countable action set. -/
noncomputable def famKernel [Countable A] [MeasurableSingletonClass A] (κ : A → Kernel S S') :
    Kernel (S × A) S' where
  toFun := fun x => κ x.2 x.1
  measurable' := measurable_from_prod_countable_left fun a => (κ a).measurable

theorem famKernel_apply [Countable A] [MeasurableSingletonClass A] (κ : A → Kernel S S')
    (s : S) (a : A) : famKernel κ (s, a) = κ a s := rfl

theorem isMarkovKernel_famKernel [Countable A] [MeasurableSingletonClass A]
    {κ : A → Kernel S S'} (h : ∀ a, IsMarkovKernel (κ a)) : IsMarkovKernel (famKernel κ) :=
  ⟨fun x => (h x.2).isProbabilityMeasure x.1⟩

variable {E : Type*} [MeasurableSpace E]

/-- The law of `F(x, ε)` with `ε ~ κ(x, ·)`. -/
noncomputable def pushKernel (κ : Kernel S E) (F : S × E → S') : Kernel S S' :=
  (Kernel.deterministic id measurable_id ×ₖ κ).map F

theorem pushKernel_apply (κ : Kernel S E) [IsSFiniteKernel κ] {F : S × E → S'}
    (hF : Measurable F) (x : S) : pushKernel κ F x = (κ x).map fun e => F (x, e) := by
  rw [pushKernel, Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

theorem isMarkovKernel_pushKernel (κ : Kernel S E) [IsMarkovKernel κ] {F : S × E → S'}
    (hF : Measurable F) : IsMarkovKernel (pushKernel κ F) := by
  unfold pushKernel
  exact Kernel.IsMarkovKernel.map _ hF

end Miao.InfiniteHorizonDP
