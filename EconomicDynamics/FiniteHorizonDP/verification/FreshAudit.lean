import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Data.ENat.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Lattice
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.Basic
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
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite histories

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `HistoryTools`),
with the namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (module `Histories`, SLP §8.2), with the namespace
renamed. Histories `sᵗ = (s₁, …, s_t)` are functions `Fin t → S`; `lastState s₀ sᵗ` is the most
recent state (`s₀` for the empty history, otherwise `s_t`). Used for Miao, §5.1, pp. 137–139.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory

variable {S : Type*} [MeasurableSpace S]

theorem measurable_cons (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => (Fin.cons p.1 p.2 : Fin (t + 1) → S) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_snoc (t : ℕ) :
    Measurable fun p : (Fin t → S) × S => (Fin.snoc p.1 p.2 : Fin (t + 1) → S) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

theorem measurable_init (t : ℕ) : Measurable (Fin.init : (Fin (t + 1) → S) → Fin t → S) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The most recent state of a history started at `s₀`: `s₀` for the empty history, otherwise
the last entry. -/
def lastState (s₀ : S) : {t : ℕ} → (Fin t → S) → S
  | 0, _ => s₀
  | t + 1, h => h (Fin.last t)

theorem measurable_lastState (s₀ : S) (t : ℕ) : Measurable (lastState s₀ (t := t)) := by
  cases t with
  | zero => exact measurable_const
  | succ t => exact measurable_pi_apply _

omit [MeasurableSpace S] in
theorem lastState_cons (s₀ s₁ : S) {t : ℕ} (h : Fin t → S) :
    lastState s₀ (Fin.cons s₁ h : Fin (t + 1) → S) = lastState s₁ h := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [lastState]
    rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace S] in
theorem lastState_snoc (s₀ s : S) {t : ℕ} (h : Fin t → S) :
    lastState s₀ (Fin.snoc h s : Fin (t + 1) → S) = s := by
  simp [lastState]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov decision process model

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Basics`),
with the namespace renamed.

Miao, §5.1, pp. 135–138: the Markov decision process (5.1), plans (Definition 5.1.1), feasible
plans (Definition 5.1.2), Assumption 5.1.1 and Lemma 5.1.1.

* `MDP S A`: measurable state space `(S, 𝒮)` and action space `(A, 𝒜)` (the type-class
  arguments), the constraint correspondence `Γ : S ⇉ A`, the stochastic kernels, the one-period
  rewards `u_t`, the terminal reward `u_T` and the discount factor `β`. **Indexing:** the field
  `P t` is the book's `P_{t+1}`, the kernel that moves the state from date `t` to date `t + 1`.
  The horizon `T ≤ ∞` (an element of `ℕ∞`) is not a field: it is an argument of the plan and
  objective definitions, so the same data serve for every horizon.
* `Plan S A`: `π_t : Sᵗ → A`; `π₀` is a function on the one-point space `S⁰`, i.e. an action.
  `IsPlan T π` (Definition 5.1.1) asks `π_t` to be measurable for `t < T`; `IsMarkovian`,
  `IsStationaryPlan` are the two special classes of the definition.
* `IsFeasible M T s₀ π` (Definition 5.1.2), `feasiblePlans` (the set `Π(s₀)`).
* `HasMeasurableSelection` (Assumption 5.1.1), `lemma_5_1_1`. The plan of the book's proof is
  Markovian and stationary (`selectionPlan_markov`). Conversely, when `T ≥ 2` a feasible plan
  exists only if `Γ` has a measurable selection (`selection_of_feasible`), so the assumption is
  also necessary; `no_selection_example` shows that `Π(s₀)` can be empty
  ("Because of the measurability requirement, Π(s₀) may be empty", p. 138).
* `detKernel f` (p. 142): the deterministic transition `P(s, a; B) = 1_B(f(s, a))`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

/-- A **Markov decision process** (Miao (5.1), p. 136): the constraint correspondence `Γ`, the
stochastic kernels (`P t` is the book's `P_{t+1}`), the one-period rewards `u t`, the terminal
reward `uT` and the discount factor `β`. The state and action spaces are the measurable spaces
`S` and `A`. -/
structure MDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  Γ : S → Set A
  P : ℕ → Kernel (S × A) S
  u : ℕ → S × A → ℝ
  uT : S → ℝ
  β : ℝ

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `Γ` is nonempty-valued (Miao, p. 136). -/
def MDP.NonemptyValued (M : MDP S A) : Prop := ∀ s, (M.Γ s).Nonempty

/-- The stochastic kernels are kernels of probability measures (Miao, p. 136: `P_{t+1}(s, a; ·)`
is a probability measure). -/
def MDP.IsMarkov (M : MDP S A) : Prop := ∀ t, IsMarkovKernel (M.P t)

/-- A **stationary** Markov decision process (Miao, p. 136): the kernels and rewards do not
depend on time. -/
def MDP.IsStationary (M : MDP S A) : Prop := ∀ t, M.P t = M.P 0 ∧ M.u t = M.u 0

/-- A **plan** (Miao, Definition 5.1.1, p. 138): `π_t : Sᵗ → A` for each date `t`. -/
abbrev Plan (S A : Type*) := (t : ℕ) → (Fin t → S) → A

/-- **Definition 5.1.1** (Miao, p. 138). `π` is a plan for the horizon `T`: `π_t` is measurable
for `t < T` (for `t = 0`, `S⁰` is a point and `π₀ ∈ A`). -/
def IsPlan (T : ℕ∞) (π : Plan S A) : Prop := ∀ t : ℕ, (t : ℕ∞) < T → Measurable (π t)

/-- **Definition 5.1.1** (Miao, p. 138). A plan is **Markovian** if, for `1 ≤ t < T`, `π_t`
depends on the history only through the current state `s_t`. -/
def IsMarkovian (T : ℕ∞) (π : Plan S A) : Prop :=
  ∃ g : ℕ → S → A, ∀ t : ℕ, ((t + 1 : ℕ) : ℕ∞) < T → ∀ h : Fin (t + 1) → S,
    π (t + 1) h = g (t + 1) (h (Fin.last t))

/-- **Definition 5.1.1** (Miao, p. 138). A (Markovian) plan is **stationary** if the decision
rule `π_t = g(s_t)` does not depend on `t`. -/
def IsStationaryPlan (T : ℕ∞) (π : Plan S A) : Prop :=
  ∃ g : S → A, ∀ t : ℕ, ((t + 1 : ℕ) : ℕ∞) < T → ∀ h : Fin (t + 1) → S,
    π (t + 1) h = g (h (Fin.last t))

/-- **Definition 5.1.2** (Miao, p. 138). `π` is **feasible** from `s₀`: it is a plan,
`π₀ ∈ Γ(s₀)` and `π_t(sᵗ) ∈ Γ(s_t)` for all `sᵗ ∈ Sᵗ`, `1 ≤ t < T`. -/
def IsFeasible (M : MDP S A) (T : ℕ∞) (s₀ : S) (π : Plan S A) : Prop :=
  IsPlan T π ∧ ∀ t : ℕ, (t : ℕ∞) < T → ∀ h : Fin t → S, π t h ∈ M.Γ (lastState s₀ h)

/-- `Π(s₀)`, the set of feasible plans from `s₀` (Miao, p. 138). -/
def feasiblePlans (M : MDP S A) (T : ℕ∞) (s₀ : S) : Set (Plan S A) := {π | IsFeasible M T s₀ π}

/-- **Assumption 5.1.1** (Miao, p. 138). `Γ` has a measurable selection. -/
def HasMeasurableSelection (Γ : S → Set A) : Prop := ∃ g : S → A, Measurable g ∧ ∀ s, g s ∈ Γ s

/-- The plan of the proof of Lemma 5.1.1: `π₀ = g(s₀)`, `π_t(sᵗ) = g(s_t)`. -/
def selectionPlan (g : S → A) (s₀ : S) : Plan S A := fun _ h => g (lastState s₀ h)

theorem selectionPlan_isPlan {g : S → A} (hg : Measurable g) (s₀ : S) (T : ℕ∞) :
    IsPlan T (selectionPlan g s₀) := fun t _ => hg.comp (measurable_lastState s₀ t)

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The plan of the proof of Lemma 5.1.1 is Markovian and stationary. -/
theorem selectionPlan_markov (g : S → A) (s₀ : S) (T : ℕ∞) :
    IsMarkovian T (selectionPlan g s₀) ∧ IsStationaryPlan T (selectionPlan g s₀) :=
  ⟨⟨fun _ => g, fun _ _ _ => rfl⟩, ⟨g, fun _ _ _ => rfl⟩⟩

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- A stationary plan is Markovian. -/
theorem IsStationaryPlan.isMarkovian {T : ℕ∞} {π : Plan S A} (h : IsStationaryPlan T π) :
    IsMarkovian T π := by
  obtain ⟨g, hg⟩ := h
  exact ⟨fun _ => g, hg⟩

/-- **Lemma 5.1.1** (Miao, p. 138). Under Assumption 5.1.1, `Π(s₀)` is nonempty for every
`s₀ ∈ S` and every horizon `T ≤ ∞`; the plan `π_t(sᵗ) = g(s_t)` built from a measurable
selection `g` is feasible. -/
theorem lemma_5_1_1 (M : MDP S A) (hΓ : HasMeasurableSelection M.Γ) (T : ℕ∞) (s₀ : S) :
    (feasiblePlans M T s₀).Nonempty := by
  obtain ⟨g, hg, hgΓ⟩ := hΓ
  exact ⟨selectionPlan g s₀, selectionPlan_isPlan hg s₀ T, fun _ _ h => hgΓ _⟩

/-- The converse of Lemma 5.1.1 (not in the book): when `T ≥ 2`, a feasible plan from any `s₀`
yields a measurable selection, `s ↦ π₁(s)`. So Assumption 5.1.1 is necessary as well as
sufficient for `Π(s₀) ≠ ∅`. -/
theorem selection_of_feasible (M : MDP S A) {T : ℕ∞} (hT : 2 ≤ T) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M T s₀) : HasMeasurableSelection M.Γ := by
  have h1 : ((1 : ℕ) : ℕ∞) < T := lt_of_lt_of_le (by norm_num) hT
  refine ⟨fun s => π 1 fun _ => s, (hπ.1 1 h1).comp (measurable_pi_iff.2 fun _ =>
    measurable_id), fun s => ?_⟩
  exact hπ.2 1 h1 fun _ => s

/-- **Lemma 5.1.1** with its converse: for `T ≥ 2`, `Π(s₀)` is nonempty if and only if `Γ` has a
measurable selection (here `Γ(s₀) ≠ ∅` is implied by the selection). -/
theorem lemma_5_1_1_iff (M : MDP S A) {T : ℕ∞} (hT : 2 ≤ T) (s₀ : S) :
    (feasiblePlans M T s₀).Nonempty ↔ HasMeasurableSelection M.Γ :=
  ⟨fun ⟨_, hπ⟩ => selection_of_feasible M hT hπ, fun h => lemma_5_1_1 M h T s₀⟩

/-- Miao, p. 138: "Because of the measurability requirement, `Π(s₀)` may be empty." With the
trivial σ-algebra `⊥` on the state space `Bool` and the discrete one on the action space `Bool`,
the nonempty-valued correspondence `Γ(s) = {s}` has no measurable selection, so by
`selection_of_feasible` no plan is feasible for any horizon `T ≥ 2`. -/
theorem no_selection_example :
    ¬ @HasMeasurableSelection Bool Bool ⊥ _ fun s => {s} := by
  rintro ⟨g, hg, hgΓ⟩
  have hgid : g = id := funext fun s => hgΓ s
  have hm : @MeasurableSet Bool ⊥ {true} := by
    have := hg (measurableSet_singleton true)
    rwa [hgid, Set.preimage_id] at this
  rcases (MeasurableSpace.measurableSet_bot_iff).1 hm with h | h
  · exact absurd (h ▸ Set.mem_singleton true) (Set.notMem_empty _)
  · have : false ∈ ({true} : Set Bool) := h ▸ Set.mem_univ false
    simp at this

/-- The deterministic transition of Miao, p. 142: `P(s, a; B) = 1` if `f(s, a) ∈ B`, else `0`. -/
noncomputable def detKernel {f : S × A → S} (hf : Measurable f) : Kernel (S × A) S :=
  Kernel.deterministic f hf

/-- Miao, p. 142: the deterministic kernel is `P(s, a; B) = 1_B(f(s, a))`, and it is a stochastic
kernel. -/
theorem detKernel_apply {f : S × A → S} (hf : Measurable f) (x : S × A) {B : Set S}
    (hB : MeasurableSet B) : detKernel hf x B = B.indicator 1 (f x) ∧
      IsMarkovKernel (detKernel hf) := by
  refine ⟨?_, inferInstanceAs (IsMarkovKernel (Kernel.deterministic f hf))⟩
  rw [detKernel, Kernel.deterministic_apply' hf x hB]
  rfl

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The measures on histories induced by a plan

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Histories`),
with the namespace renamed.

Miao, §5.1, (5.2), p. 139. Given an initial state `s₀`, a plan `π` and the stochastic kernels,
`μᵗ(s₀, ·; π)` (`mu M s₀ π t`) is the distribution of the history `sᵗ = (s₁, …, s_t)`, built as
in (5.2): `s₁ ~ P₁(s₀, π₀; ·)`, and given `sᵗ`, `s_{t+1} ~ P_{t+1}(s_t, π_t(sᵗ); ·)`
(`mu_succ_lintegral`). This is the finite-dimensional part of the Ionescu Tulcea theorem
(Miao's Theorem 3.2.4); the infinite-horizon measure `μ^∞` is in `Trajectory`.

* `isProbabilityMeasure_mu`: `μᵗ(s₀, ·; π)` is a probability measure ("well-defined
  probability measure on `Sᵗ`", p. 139).
* `eq_5_2`: (5.2) on measurable rectangles, in its recursive form
  `μᵗ⁺¹(B₁ × ⋯ × B_{t+1}) = ∫_{B₁×⋯×B_t} P_{t+1}(s_t, π_t(sᵗ); B_{t+1}) μᵗ(dsᵗ)`;
  unrolling it gives the iterated integral printed in (5.2).
* `mu_congr`: `μᵗ` depends on the plan only through `π₀, …, π_{t−1}`.
* `integral_mu_succ`: the corresponding identity for integrable functions.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

open Classical in
/-- The kernel of the next state given the history: `sᵗ ↦ P_{t+1}(s_t, π_t(sᵗ); ·)`
(the zero kernel if `π_t` is not measurable, a case that never arises for plans). -/
noncomputable def stepKernel (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) :
    Kernel (Fin t → S) S :=
  if hπ : Measurable (π t) then
    (M.P t).comap (fun h => (lastState s₀ h, π t h)) ((measurable_lastState s₀ t).prodMk hπ)
  else 0

/-- `μᵗ(s₀, ·; π)`, the distribution of the history `(s₁, …, s_t)` (Miao (5.2), p. 139). -/
noncomputable def mu (M : MDP S A) (s₀ : S) (π : Plan S A) : (t : ℕ) → Measure (Fin t → S)
  | 0 => Measure.dirac Fin.elim0
  | t + 1 =>
    ((mu M s₀ π t) ⊗ₘ stepKernel M s₀ π t).map fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → S)

theorem stepKernel_apply (M : MDP S A) (s₀ : S) {π : Plan S A} {t : ℕ} (hπ : Measurable (π t))
    (h : Fin t → S) : stepKernel M s₀ π t h = M.P t (lastState s₀ h, π t h) := by
  simp only [stepKernel, hπ, ↓reduceDIte, Kernel.comap_apply]

theorem isMarkovKernel_stepKernel (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A}
    {t : ℕ} (hπ : Measurable (π t)) : IsMarkovKernel (stepKernel M s₀ π t) := by
  have := hP t
  simp only [stepKernel, hπ, ↓reduceDIte]
  infer_instance

theorem isSFiniteKernel_stepKernel (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (t : ℕ) : IsSFiniteKernel (stepKernel M s₀ π t) := by
  by_cases hπ : Measurable (π t)
  · have := isMarkovKernel_stepKernel M hP s₀ hπ
    infer_instance
  · simp only [stepKernel, hπ, ↓reduceDIte]
    infer_instance

theorem sFinite_mu (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) : SFinite (mu M s₀ π t) := by
  cases t with
  | zero => exact inferInstanceAs (SFinite (Measure.dirac _))
  | succ t => exact inferInstanceAs (SFinite (Measure.map _ _))

/-- `μᵗ(s₀, ·; π)` is a probability measure (Miao, p. 139). -/
theorem isProbabilityMeasure_mu (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A}
    {t : ℕ} (hπ : ∀ j < t, Measurable (π j)) : IsProbabilityMeasure (mu M s₀ π t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ t ih =>
    have := ih fun j hj => hπ j (by omega)
    have := isMarkovKernel_stepKernel M hP s₀ (hπ t (by omega))
    exact inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

theorem mu_zero (M : MDP S A) (s₀ : S) (π : Plan S A) : mu M s₀ π 0 = Measure.dirac Fin.elim0 :=
  rfl

theorem integral_mu_zero (M : MDP S A) (s₀ : S) (π : Plan S A) (f : (Fin 0 → S) → ℝ) :
    ∫ h, f h ∂mu M s₀ π 0 = f Fin.elim0 := by
  rw [mu_zero, integral_dirac]

/-- The last-date decomposition of `μᵗ⁺¹`: `∫ f dμᵗ⁺¹ = ∫ [∫ f(sᵗ, s′) P_{t+1}(s_t, π_t(sᵗ); ds′)]
μᵗ(dsᵗ)`. -/
theorem mu_succ_lintegral (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {f : (Fin (t + 1) → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f h ∂mu M s₀ π (t + 1) =
      ∫⁻ h, ∫⁻ s, f (Fin.snoc h s) ∂M.P t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  have := sFinite_mu M s₀ π t
  have := isMarkovKernel_stepKernel M hP s₀ hπ
  rw [mu, lintegral_map hf (measurable_snoc t),
    Measure.lintegral_compProd (f := fun p : (Fin t → S) × S => f (Fin.snoc p.1 p.2))
      (hf.comp (measurable_snoc t))]
  refine lintegral_congr fun h => ?_
  rw [stepKernel_apply M s₀ hπ]

/-- **Miao (5.2)**, p. 139, on measurable rectangles: `μᵗ⁺¹(s₀, B₁ × ⋯ × B_{t+1}; π)` is the
integral over `B₁ × ⋯ × B_t` of `P_{t+1}(s_t, π_t(sᵗ); B_{t+1})` against `μᵗ(s₀, ·; π)`.
Iterating this identity gives the nested integral printed in (5.2). -/
theorem eq_5_2 (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {B : Fin (t + 1) → Set S} (hB : ∀ i, MeasurableSet (B i)) :
    mu M s₀ π (t + 1) (Set.pi Set.univ B) =
      ∫⁻ h in Set.pi Set.univ (Fin.init B), M.P t (lastState s₀ h, π t h) (B (Fin.last t))
        ∂mu M s₀ π t := by
  have hpi : MeasurableSet (Set.pi Set.univ B) := MeasurableSet.univ_pi hB
  have hpi' : MeasurableSet (Set.pi Set.univ (Fin.init B)) :=
    MeasurableSet.univ_pi fun i => hB _
  rw [← lintegral_indicator_one hpi, mu_succ_lintegral M hP s₀ hπ
    (measurable_one.indicator hpi), ← lintegral_indicator hpi']
  refine lintegral_congr fun h => ?_
  by_cases hh : h ∈ Set.pi Set.univ (Fin.init B)
  · rw [Set.indicator_of_mem hh, ← lintegral_indicator_one (hB _)]
    refine lintegral_congr fun s => ?_
    have : (Fin.snoc h s : Fin (t + 1) → S) ∈ Set.pi Set.univ B ↔ s ∈ B (Fin.last t) := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro H
        simpa using H (Fin.last t)
      · intro H i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using H
        · simpa [Fin.init] using hh j (Set.mem_univ _)
    by_cases hs : s ∈ B (Fin.last t)
    · rw [Set.indicator_of_mem (this.2 hs), Set.indicator_of_mem hs]
      rfl
    · rw [Set.indicator_of_notMem (fun H => hs (this.1 H)), Set.indicator_of_notMem hs]
  · rw [Set.indicator_of_notMem hh]
    refine (lintegral_congr fun s => ?_).trans lintegral_zero
    refine Set.indicator_of_notMem (fun H => hh ?_) _
    intro i _
    simpa [Fin.init] using H (Fin.castSucc i) (Set.mem_univ _)

/-- The integrable version of the last-date decomposition. -/
theorem integral_mu_succ (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s₀ π (t + 1))) :
    ∫ h, f h ∂mu M s₀ π (t + 1) =
      ∫ h, ∫ s, f (Fin.snoc h s) ∂M.P t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  have := sFinite_mu M s₀ π t
  have := isMarkovKernel_stepKernel M hP s₀ hπ
  rw [mu] at hf ⊢
  have hf' := (integrable_map_measure hf.1 (measurable_snoc t).aemeasurable).1 hf
  rw [integral_map (measurable_snoc t).aemeasurable hf.1,
    Measure.integral_compProd (f := fun p : (Fin t → S) × S => f (Fin.snoc p.1 p.2)) hf']
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [stepKernel_apply M s₀ hπ]

/-- `μᵗ(s₀, ·; π)` depends on `π` only through `π₀, …, π_{t−1}` and on the model only through
its kernels. -/
theorem mu_congr {M M' : MDP S A} (hMP : M.P = M'.P) (s₀ : S) {π π' : Plan S A} {t : ℕ}
    (hπ : ∀ j < t, π j = π' j) : mu M s₀ π t = mu M' s₀ π' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hk : stepKernel M s₀ π t = stepKernel M' s₀ π' t := by
      have h1 : π t = π' t := hπ t (by omega)
      unfold stepKernel
      rw [hMP]
      by_cases hm : Measurable (π t)
      · have hm' : Measurable (π' t) := h1 ▸ hm
        simp only [hm, hm', ↓reduceDIte]
        ext x : 1
        simp only [Kernel.comap_apply, h1]
      · have hm' : ¬ Measurable (π' t) := h1 ▸ hm
        simp only [hm, hm', ↓reduceDIte]
    simp only [mu, ih fun j hj => hπ j (by omega), hk]

/-- History measures of two models agree when their next-state kernels agree along the way. -/
theorem mu_eq_of_stepKernel {A' : Type*} [MeasurableSpace A'] {M : MDP S A} {M' : MDP S A'}
    (s₀ : S) {π : Plan S A} {π' : Plan S A'} {t : ℕ}
    (h : ∀ j < t, stepKernel M s₀ π j = stepKernel M' s₀ π' j) : mu M s₀ π t = mu M' s₀ π' t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [mu, ih fun j hj => h j (by omega), h t (by omega)]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Total discounted expected rewards and the value function

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Objective`),
with the namespace renamed.

Miao, §5.1, pp. 139–141: Assumptions 5.1.2–5.1.4, the objectives (5.3)–(5.4), the value
functions (5.5)–(5.6) and their characterisation, and optimal plans.

* `rew M s₀ π t sᵗ = u_t(s_t, π_t(sᵗ))`, the reward process; `measurable_rew` (it is
  measurable on `Sᵗ`, which is what makes the expectations of (5.3)–(5.4) meaningful).
* `J0T M T s₀ π` (5.3) and `J M s₀ π` (5.4), the latter the limit in `[−∞, +∞]` of the partial
  sums `partialSum`; `eq_5_3`, `eq_5_4` show they are the book's expressions.
* `Assumption512`, `Assumption513`, `Assumption514`. Under Assumption 5.1.4 the partial sums
  converge to `J` (`J_spec`), so `J(s, ·)` is well defined on `Π(s)`; with Assumption 5.1.1
  `Π(s)` is nonempty (Lemma 5.1.1), as the text claims on p. 140.
* Sufficient conditions (claims of p. 140, made precise): bounded measurable rewards give
  Assumptions 5.1.3 and 5.1.4 and `|J| ≤ B/(1 − β)` (`assumption_5_1_3_of_bounded`,
  `assumption_5_1_4_of_bounded`, `abs_J_le`); rewards bounded above (below) give the
  existence of the limit in Assumption 5.1.4, with value in `[−∞, ∞)` (`(−∞, ∞]`)
  (`tendsto_partialSum_of_bddAbove`, `tendsto_partialSum_of_bddBelow`).
* `V0` (5.5), `V` (5.6), and the characterisation by the three conditions of p. 141
  (`IsValueOf`, `isValueOf_iff`, `V0_char`, `V_char`): `V₀` is the unique function satisfying
  them. `IsOptimalPlan` is an optimal plan.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The reward at date `t` along the plan: `u_t(s_t, π_t(sᵗ))`. -/
def rew (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) (h : Fin t → S) : ℝ :=
  M.u t (lastState s₀ h, π t h)

/-- The expected reward at date `t`: `∫ u_t(s_t, π_t(sᵗ)) μᵗ(s₀, dsᵗ; π)`. -/
noncomputable def expRew (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) : ℝ :=
  ∫ h, rew M s₀ π t h ∂mu M s₀ π t

/-- The total discounted expected rewards over the horizon `T < ∞` (Miao (5.3), p. 140). -/
noncomputable def J0T (M : MDP S A) (T : ℕ) (s₀ : S) (π : Plan S A) : ℝ :=
  ∑ t ∈ Finset.range T, M.β ^ t * expRew M s₀ π t +
    M.β ^ T * ∫ h, M.uT (lastState s₀ h) ∂mu M s₀ π T

/-- The partial sums `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u(s_t, π_t(sᵗ)) dμᵗ`. -/
noncomputable def partialSum (M : MDP S A) (s₀ : S) (π : Plan S A) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n + 1), M.β ^ t * expRew M s₀ π t

/-- The total discounted expected rewards over an infinite horizon (Miao (5.4), p. 140): the
limit of the partial sums in `[−∞, +∞]`. -/
noncomputable def J (M : MDP S A) (s₀ : S) (π : Plan S A) : EReal :=
  limUnder atTop fun n => (partialSum M s₀ π n : EReal)

/-- **Assumption 5.1.2** (Miao, p. 139). `β ∈ (0, 1)`. -/
def Assumption512 (M : MDP S A) : Prop := 0 < M.β ∧ M.β < 1

/-- **Assumption 5.1.3** (Miao, p. 139). `T < ∞`; the rewards `u_t` (`t < T`) and `u_T` are
measurable, and along every feasible plan each reward is integrable. -/
def Assumption513 (M : MDP S A) (T : ℕ) : Prop :=
  (∀ t < T, Measurable (M.u t)) ∧ Measurable M.uT ∧
    ∀ s₀, ∀ π ∈ feasiblePlans M T s₀,
      (∀ t < T, Integrable (rew M s₀ π t) (mu M s₀ π t)) ∧
        Integrable (fun h => M.uT (lastState s₀ h)) (mu M s₀ π T)

/-- **Assumption 5.1.4** (Miao, p. 139). `T = ∞`; the process is stationary, the rewards along
every feasible plan are integrable and the partial sums of (5.4) have a limit in `[−∞, +∞]`. -/
def Assumption514 (M : MDP S A) : Prop :=
  M.IsStationary ∧ ∀ s₀, ∀ π ∈ feasiblePlans M ⊤ s₀,
    (∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) ∧
      ∃ L : EReal, Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L)

/-- The reward process is measurable on `Sᵗ` when `u_t` and `π_t` are. -/
theorem measurable_rew (M : MDP S A) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hu : Measurable (M.u t)) (hπ : Measurable (π t)) : Measurable (rew M s₀ π t) :=
  hu.comp ((measurable_lastState s₀ t).prodMk hπ)

theorem expRew_zero (M : MDP S A) (s₀ : S) (π : Plan S A) :
    expRew M s₀ π 0 = M.u 0 (s₀, π 0 Fin.elim0) := by
  rw [expRew, integral_mu_zero]
  rfl

/-- **Miao (5.3)**, p. 140. For `T ≥ 1`, `J₀ᵀ(s₀, π) = u₀(s₀, π₀) +
∑_{t=1}^{T−1} βᵗ ∫ u_t(s_t, π_t(sᵗ)) dμᵗ + βᵀ ∫ u_T(s_T) dμᵀ`. -/
theorem eq_5_3 (M : MDP S A) {T : ℕ} (hT : 1 ≤ T) (s₀ : S) (π : Plan S A) :
    J0T M T s₀ π = M.u 0 (s₀, π 0 Fin.elim0) +
      ∑ t ∈ Finset.Ico 1 T, M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t +
        M.β ^ T * ∫ h, M.uT (lastState s₀ h) ∂mu M s₀ π T := by
  rw [J0T, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero, one_mul,
    expRew_zero]
  rfl

/-- The partial sums of (5.4): `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u(s_t, π_t(sᵗ)) dμᵗ`. -/
theorem partialSum_eq (M : MDP S A) (s₀ : S) (π : Plan S A) (n : ℕ) :
    partialSum M s₀ π n = M.u 0 (s₀, π 0 Fin.elim0) +
      ∑ t ∈ Finset.Icc 1 n, M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  rw [partialSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero,
    one_mul, expRew_zero]
  rfl

/-- **Miao (5.4)**, p. 140. If the partial sums `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u dμᵗ` tend to
`L ∈ [−∞, +∞]`, then `J(s₀, π) = L`. -/
theorem eq_5_4 (M : MDP S A) (s₀ : S) (π : Plan S A) {L : EReal}
    (h : Tendsto (fun n => ((M.u 0 (s₀, π 0 Fin.elim0) + ∑ t ∈ Finset.Icc 1 n,
      M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t : ℝ) : EReal)) atTop (𝓝 L)) :
    J M s₀ π = L := by
  simp only [← partialSum_eq] at h
  exact h.limUnder_eq

/-- Miao, p. 140: under Assumption 5.1.4, `J(s₀, π)` is well defined: the partial sums converge
to it. -/
theorem J_spec {M : MDP S A} (h : Assumption514 M) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 (J M s₀ π)) := by
  obtain ⟨L, hL⟩ := (h.2 s₀ π hπ).2
  rw [J, hL.limUnder_eq]
  exact hL

/-- Miao, p. 140: Assumptions 5.1.1 and 5.1.4 make `J(s, ·)` a well-defined function on a
nonempty set `Π(s)`. -/
theorem J_welldefined {M : MDP S A} (hΓ : HasMeasurableSelection M.Γ) (h : Assumption514 M)
    (s : S) : (feasiblePlans M ⊤ s).Nonempty ∧ ∀ π ∈ feasiblePlans M ⊤ s,
      Tendsto (fun n => (partialSum M s π n : EReal)) atTop (𝓝 (J M s π)) :=
  ⟨lemma_5_1_1 M hΓ ⊤ s, fun _ hπ => J_spec h hπ⟩

/-- Rewards bounded by `B` in absolute value (all dates, and the terminal reward). -/
def BoundedRewards (M : MDP S A) (B : ℝ) : Prop :=
  (∀ t x, |M.u t x| ≤ B) ∧ ∀ s, |M.uT s| ≤ B

theorem integrable_of_bounded {t : ℕ} {μ : Measure (Fin t → S)} [IsFiniteMeasure μ]
    {f : (Fin t → S) → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ h, |f h| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun h => by
    simpa [Real.norm_eq_abs] using hB h)

theorem plan_lt {T : ℕ} {s₀ : S} {M : MDP S A} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M T s₀) : ∀ j < T, Measurable (π j) :=
  fun j hj => hπ.1 j (by exact_mod_cast hj)

/-- Miao, p. 140 (made precise): with Markov kernels, measurable rewards bounded by `B`
satisfy Assumption 5.1.3 for every horizon. -/
theorem assumption_5_1_3_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : BoundedRewards M B) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT)
    (T : ℕ) : Assumption513 M T := by
  refine ⟨fun t _ => hu t, huT, fun s₀ π hπ => ⟨fun t ht => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j hj => plan_lt hπ j (by omega)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (plan_lt hπ t ht))
      fun h => hB.1 t _
  · have := isProbabilityMeasure_mu M hP s₀ (t := T) (plan_lt hπ)
    exact integrable_of_bounded (huT.comp (measurable_lastState s₀ T)) fun h => hB.2 _

theorem abs_expRew_le {M : MDP S A} (hP : M.IsMarkov) {B : ℝ} (s₀ : S) {π : Plan S A}
    {t : ℕ} (hB : ∀ h, |rew M s₀ π t h| ≤ B) (hπ : ∀ j < t, Measurable (π j)) :
    |expRew M s₀ π t| ≤ B := by
  have := isProbabilityMeasure_mu M hP s₀ hπ
  have h := norm_integral_le_of_norm_le_const (μ := mu M s₀ π t) (f := rew M s₀ π t) (C := B)
    (Eventually.of_forall fun h => by simpa [Real.norm_eq_abs] using hB h)
  simpa [Real.norm_eq_abs, expRew] using h

/-- Bounded rewards and `0 ≤ β < 1`: the partial sums of (5.4) converge in `ℝ` to
`∑ βᵗ ∫ u dμᵗ`. -/
theorem tendsto_partialSum_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hB : ∀ t h, |rew M s₀ π t h| ≤ B) (hπ : ∀ j, Measurable (π j)) :
    Summable (fun t => M.β ^ t * expRew M s₀ π t) ∧
      Tendsto (partialSum M s₀ π) atTop (𝓝 (∑' t, M.β ^ t * expRew M s₀ π t)) := by
  have hs : Summable (fun t => M.β ^ t * expRew M s₀ π t) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B) ?_
    intro t
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (abs_expRew_le hP s₀ (hB t) fun j _ => hπ j)
      (pow_nonneg hβ0 t)
  refine ⟨hs, ?_⟩
  have := hs.hasSum.tendsto_sum_nat
  exact this.comp (tendsto_add_atTop_nat 1)

/-- Miao, p. 140 (made precise): for a stationary process with Markov kernels, measurable
rewards bounded by `B` and `0 ≤ β < 1`, Assumption 5.1.4 holds. -/
theorem assumption_5_1_4_of_bounded {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary)
    {B : ℝ} (hB : ∀ t x, |M.u t x| ≤ B) (hu : ∀ t, Measurable (M.u t)) (hβ0 : 0 ≤ M.β)
    (hβ1 : M.β < 1) : Assumption514 M := by
  refine ⟨hst, fun s₀ π hπ => ⟨fun t => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ.1 j (WithTop.coe_lt_top j)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (hπ.1 t (WithTop.coe_lt_top t)))
      fun h => by simpa [rew] using hB t _
  · exact ⟨_, (continuous_coe_real_ereal.tendsto _).comp (tendsto_partialSum_of_bounded hP
      hβ0 hβ1 s₀ (fun t h => hB t _) fun j => hπ.1 j (WithTop.coe_lt_top j)).2⟩

/-- The same with rewards bounded only on the graph of `Γ`, `|u_t(s, a)| ≤ B` for `a ∈ Γ(s)`
(the rewards that feasible plans can collect). -/
theorem assumption_5_1_4_of_boundedOn {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary)
    {B : ℝ} (hB : ∀ t s a, a ∈ M.Γ s → |M.u t (s, a)| ≤ B) (hu : ∀ t, Measurable (M.u t))
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) : Assumption514 M := by
  refine ⟨hst, fun s₀ π hπ => ⟨fun t => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ.1 j (WithTop.coe_lt_top j)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (hπ.1 t (WithTop.coe_lt_top t)))
      fun h => hB t _ _ (hπ.2 t (WithTop.coe_lt_top t) h)
  · exact ⟨_, (continuous_coe_real_ereal.tendsto _).comp (tendsto_partialSum_of_bounded hP
      hβ0 hβ1 s₀ (fun t h => hB t _ _ (hπ.2 t (WithTop.coe_lt_top t) h))
        fun j => hπ.1 j (WithTop.coe_lt_top j)).2⟩

/-- With bounded rewards, `J(s₀, π)` is finite: `J(s₀, π) = ∑ βᵗ ∫ u dμᵗ` and
`|J(s₀, π)| ≤ B/(1 − β)`. -/
theorem abs_J_le {M : MDP S A} (hP : M.IsMarkov) {B : ℝ} (hB : ∀ t x, |M.u t x| ≤ B)
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A} (hπ : ∀ j, Measurable (π j)) :
    J M s₀ π = ((∑' t, M.β ^ t * expRew M s₀ π t : ℝ) : EReal) ∧
      |∑' t, M.β ^ t * expRew M s₀ π t| ≤ B / (1 - M.β) := by
  obtain ⟨hs, ht⟩ := tendsto_partialSum_of_bounded hP hβ0 hβ1 s₀ (fun t h => hB t _) hπ
  refine ⟨((continuous_coe_real_ereal.tendsto _).comp ht).limUnder_eq, ?_⟩
  have hg := hasSum_geometric_of_lt_one hβ0 hβ1
  have hgB : HasSum (fun t => M.β ^ t * B) (B / (1 - M.β)) := by
    convert hg.mul_right B using 1
    rw [div_eq_mul_inv, mul_comm]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← hgB.tsum_eq]
  refine Summable.tsum_le_tsum (fun t => ?_) hs.norm hgB.summable
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (abs_expRew_le hP s₀ (fun h => hB t _) fun j _ => hπ j)
    (pow_nonneg hβ0 t)

theorem geom_partial_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (B : ℝ) :
    Tendsto (fun n => ((B * ∑ t ∈ Finset.range (n + 1), β ^ t : ℝ) : EReal)) atTop
      (𝓝 ((B * (1 - β)⁻¹ : ℝ) : EReal)) := by
  refine (continuous_coe_real_ereal.tendsto _).comp ?_
  refine Tendsto.const_mul B ?_
  exact (hasSum_geometric_of_lt_one hβ0 hβ1).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- Miao, p. 139, the limit in Assumption 5.1.4 exists when the rewards are **bounded above**
(the limit then lies in `[−∞, ∞)`). -/
theorem tendsto_partialSum_of_bddAbove {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : ∀ t x, M.u t x ≤ B) (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hπ : ∀ j, Measurable (π j)) (hi : ∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) :
    ∃ L : EReal, L ≠ ⊤ ∧ Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L) := by
  set b : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), M.β ^ t * (expRew M s₀ π t - B)
  have hle : ∀ t, expRew M s₀ π t ≤ B := by
    intro t
    have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ j
    have h := integral_mono (hi t) (integrable_const B) (fun h => hB t _)
    simpa [expRew] using h
  have hanti : Antitone fun n => (b n : EReal) := by
    refine antitone_nat_of_succ_le fun n => ?_
    refine EReal.coe_le_coe_iff.2 ?_
    simp only [b, Finset.sum_range_succ _ (n + 1)]
    have : M.β ^ (n + 1) * (expRew M s₀ π (n + 1) - B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 _) (by linarith [hle (n + 1)])
    linarith
  have hb := tendsto_atTop_iInf hanti
  have hL : (⨅ n, (b n : EReal)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top (b 0)) (iInf_le _ 0)
  refine ⟨(⨅ n, (b n : EReal)) + ((B * (1 - M.β)⁻¹ : ℝ) : EReal), ?_, ?_⟩
  · exact EReal.add_ne_top hL (EReal.coe_ne_top _)
  · have hc := (EReal.continuousAt_add (p := ((⨅ n, (b n : EReal)), ((B * (1 - M.β)⁻¹ : ℝ) :
      EReal))) (Or.inl hL) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
        (hb.prodMk_nhds (geom_partial_tendsto hβ0 hβ1 B))
    refine hc.congr fun n => ?_
    simp only [Function.comp_apply, ← EReal.coe_add, b, partialSum, Finset.mul_sum, ←
      Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => by ring

/-- Miao, p. 139, the limit in Assumption 5.1.4 exists when the rewards are **bounded below**
(the limit then lies in `(−∞, ∞]`). -/
theorem tendsto_partialSum_of_bddBelow {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : ∀ t x, B ≤ M.u t x) (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hπ : ∀ j, Measurable (π j)) (hi : ∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) :
    ∃ L : EReal, L ≠ ⊥ ∧ Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L) := by
  set b : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), M.β ^ t * (expRew M s₀ π t - B)
  have hle : ∀ t, B ≤ expRew M s₀ π t := by
    intro t
    have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ j
    have h := integral_mono (integrable_const B) (hi t) (fun h => hB t _)
    simpa [expRew] using h
  have hmono : Monotone fun n => (b n : EReal) := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine EReal.coe_le_coe_iff.2 ?_
    simp only [b, Finset.sum_range_succ _ (n + 1)]
    have : 0 ≤ M.β ^ (n + 1) * (expRew M s₀ π (n + 1) - B) :=
      mul_nonneg (pow_nonneg hβ0 _) (by linarith [hle (n + 1)])
    linarith
  have hb := tendsto_atTop_iSup hmono
  have hL : (⨆ n, (b n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (b 0))
    (le_iSup (fun n => (b n : EReal)) 0)
  refine ⟨(⨆ n, (b n : EReal)) + ((B * (1 - M.β)⁻¹ : ℝ) : EReal), ?_, ?_⟩
  · exact EReal.add_ne_bot_iff.2 ⟨hL, EReal.coe_ne_bot _⟩
  · have hc := (EReal.continuousAt_add (p := ((⨆ n, (b n : EReal)), ((B * (1 - M.β)⁻¹ : ℝ) :
      EReal))) (Or.inr (EReal.coe_ne_bot _)) (Or.inl hL)).tendsto.comp
        (hb.prodMk_nhds (geom_partial_tendsto hβ0 hβ1 B))
    refine hc.congr fun n => ?_
    simp only [Function.comp_apply, ← EReal.coe_add, b, partialSum, Finset.mul_sum, ←
      Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => by ring

/-- The value function `V₀` of the `T`-horizon problem (Miao (5.5), p. 140). -/
noncomputable def V0 (M : MDP S A) (T : ℕ) (s : S) : EReal :=
  ⨆ π ∈ feasiblePlans M T s, (J0T M T s π : EReal)

/-- The value function `V` of the infinite-horizon problem (Miao (5.6), p. 140). -/
noncomputable def V (M : MDP S A) (s : S) : EReal := ⨆ π ∈ feasiblePlans M ⊤ s, J M s π

/-- The three conditions of Miao, p. 141, for `w` to be the value of the problem with objective
`j` on the feasible set `F`. -/
def IsValueOf {α : Type*} (F : Set α) (j : α → EReal) (w : EReal) : Prop :=
  ((w ≠ ⊤ ∧ w ≠ ⊥) → (∀ x ∈ F, j x ≤ w) ∧ ∀ ε : ℝ, 0 < ε → ∃ x ∈ F, w ≤ j x + ε) ∧
    (w = ⊤ → ∃ x : ℕ → α, (∀ k, x k ∈ F) ∧ Tendsto (j ∘ x) atTop (𝓝 ⊤)) ∧
      (w = ⊥ → ∀ x ∈ F, j x = ⊥)

/-- Miao, p. 141: a value `w` satisfies the three conditions if and only if it is the supremum
`sup_{x ∈ F} j(x)`. -/
theorem isValueOf_iff {α : Type*} (F : Set α) (j : α → EReal) (w : EReal) :
    IsValueOf F j w ↔ w = ⨆ x ∈ F, j x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_ne w ⊤ with hw | hw
    · obtain ⟨x, hxF, hx⟩ := h2 hw
      rw [hw, eq_comm, eq_top_iff]
      refine le_of_tendsto' hx fun k => ?_
      exact le_iSup₂ (f := fun x (_ : x ∈ F) => j x) (x k) (hxF k)
    rcases eq_or_ne w ⊥ with hb | hb
    · rw [hb, eq_comm, eq_bot_iff]
      exact iSup₂_le fun x hx => (h3 hb x hx).le
    obtain ⟨hle, happrox⟩ := h1 ⟨hw, hb⟩
    refine le_antisymm ?_ (iSup₂_le hle)
    lift w to ℝ using ⟨hw, hb⟩
    refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
    by_contra hzw
    push Not at hzw
    have hε : 0 < w - z := sub_pos.2 (EReal.coe_lt_coe_iff.1 hzw)
    obtain ⟨x, hxF, hx⟩ := happrox (w - z) hε
    have hjz : j x < z := lt_of_le_of_lt (le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hxF) hz
    have := EReal.add_lt_add_right_coe hjz (w - z)
    rw [← EReal.coe_add, add_sub_cancel] at this
    exact absurd hx (not_le.2 this)
  · intro hw
    refine ⟨fun hfin => ⟨fun x hx => hw ▸ le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hx,
      fun ε hε => ?_⟩, fun htop => ?_, fun hbot x hx => ?_⟩
    · lift w to ℝ using hfin
      have : ((w - ε : ℝ) : EReal) < ⨆ x ∈ F, j x := by
        rw [← hw]
        exact EReal.coe_lt_coe_iff.2 (by linarith)
      obtain ⟨x, hxF, hx⟩ := lt_biSup_iff.1 this
      refine ⟨x, hxF, ?_⟩
      induction h : j x using EReal.rec with
      | bot => rw [h] at hx; exact absurd hx (not_lt_bot)
      | top => exact le_top
      | coe r =>
        rw [h] at hx
        rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (by linarith [EReal.coe_lt_coe_iff.1 hx])
    · have hk : ∀ k : ℕ, ∃ x ∈ F, ((k : ℝ) : EReal) < j x := fun k =>
        lt_biSup_iff.1 (by rw [← hw, htop]; exact EReal.coe_lt_top _)
      choose x hxF hx using hk
      refine ⟨x, hxF, EReal.tendsto_nhds_top_iff_real.2 fun r => ?_⟩
      filter_upwards [eventually_ge_atTop (Nat.ceil r)] with k hk
      refine lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ?_) (hx k)
      exact (Nat.le_ceil r).trans (by exact_mod_cast hk)
    · exact le_bot_iff.1 (hbot ▸ hw ▸ le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hx)

/-- Miao, p. 141: `V₀` is the unique function satisfying the three conditions (for the
`T`-horizon problem). -/
theorem V0_char (M : MDP S A) (T : ℕ) (W : S → EReal) :
    (∀ s, IsValueOf (feasiblePlans M T s) (fun π => (J0T M T s π : EReal)) (W s)) ↔
      W = V0 M T := by
  simp only [isValueOf_iff, funext_iff, V0]

/-- Miao, p. 141: `V` is the unique function satisfying the three conditions (for the
infinite-horizon problem). -/
theorem V_char (M : MDP S A) (W : S → EReal) :
    (∀ s, IsValueOf (feasiblePlans M ⊤ s) (fun π => J M s π) (W s)) ↔ W = V M := by
  simp only [isValueOf_iff, funext_iff, V]

/-- An **optimal plan** from `s` for the `T`-horizon problem (Miao, p. 141): a feasible plan
attaining the supremum in (5.5). -/
def IsOptimalPlan0 (M : MDP S A) (T : ℕ) (s : S) (π : Plan S A) : Prop :=
  π ∈ feasiblePlans M T s ∧ V0 M T s = J0T M T s π

/-- An **optimal plan** from `s` for the infinite-horizon problem (Miao, p. 141). -/
def IsOptimalPlan (M : MDP S A) (s : S) (π : Plan S A) : Prop :=
  π ∈ feasiblePlans M ⊤ s ∧ V M s = J M s π

/-- Miao, p. 141: if an optimal plan exists, the supremum in (5.5) is a maximum. -/
theorem IsOptimalPlan0.isGreatest {M : MDP S A} {T : ℕ} {s : S} {π : Plan S A}
    (h : IsOptimalPlan0 M T s π) :
    IsGreatest ((fun π => (J0T M T s π : EReal)) '' feasiblePlans M T s) (V0 M T s) :=
  ⟨⟨π, h.1, h.2.symm⟩, by
    rintro _ ⟨π', hπ', rfl⟩
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M T s) => (J0T M T s π : EReal)) π' hπ'⟩

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transporting history measures between models

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Simulation`),
with the namespace renamed.

A tool for the examples of Miao, §5.2, pp. 143–154, where a problem stated in its own terms (a
stopping rule on an exogenous Markov chain, a control problem with a law of motion) is recast as
a Markov decision process. The text asserts that the recast problem *is* the original one; here
this is proved by showing that the MDP's history measure `μᵗ` is the image of the original
history measure under an explicit map of histories.

* `chainMDP Q`: an exogenous Markov chain with (possibly time-varying) transition functions
  `Q t` (the book's `Q_{t+1}`), seen as an MDP with a single action; `chainHist Q z₀ t` is the
  distribution of `(z₁, …, z_t)` (`chainHist_succ_lintegral`).
* `liftHist ψ`: histories `S₁ᵗ → S₂ᵗ` built one date at a time, `s₂,t+1 = ψ_t(s₂ᵗ, s₁,t+1)`.
* `mu_simulation`: if, along lifted histories, the kernel of the second model is the image of
  the kernel of the first under `ψ_t`, then `μ₂ᵗ = μ₁ᵗ ∘ Φ_t⁻¹`.
* `expRew_simulation`: the corresponding identity for expected rewards.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S₁ A₁ S₂ A₂ : Type*} [MeasurableSpace S₁] [MeasurableSpace A₁] [MeasurableSpace S₂]
  [MeasurableSpace A₂]

/-- The histories `Φ_t(s₁ᵗ) ∈ S₂ᵗ` built from the step maps `ψ_t`:
`Φ_{t+1}(s₁ᵗ, s) = (Φ_t(s₁ᵗ), ψ_t(Φ_t(s₁ᵗ), s))`. -/
def liftHist (ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂) : (t : ℕ) → (Fin t → S₁) → Fin t → S₂
  | 0, _ => Fin.elim0
  | t + 1, h => Fin.snoc (liftHist ψ t (Fin.init h)) (ψ t (liftHist ψ t (Fin.init h))
      (h (Fin.last t)))

omit [MeasurableSpace S₁] [MeasurableSpace S₂] in
theorem liftHist_snoc (ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂) {t : ℕ} (h : Fin t → S₁)
    (s : S₁) : liftHist ψ (t + 1) (Fin.snoc h s) =
      Fin.snoc (liftHist ψ t h) (ψ t (liftHist ψ t h) s) := by
  simp [liftHist, Fin.init_snoc]

theorem measurable_liftHist {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂} {t : ℕ}
    (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2) :
    Measurable (liftHist ψ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 := (ih fun j hj => hψ j (by omega)).comp (measurable_init t)
    exact (measurable_snoc t).comp (h1.prodMk ((hψ t (by omega)).comp
      (h1.prodMk (measurable_pi_apply _))))

/-- **Transport of history measures.** If, for every history `h` of the first model, the
second model's kernel at the lifted history is the image under `ψ_t(Φ_t h, ·)` of the first
model's kernel at `h`, then `μ₂ᵗ(s₂, ·; π₂)` is the image of `μ₁ᵗ(s₁, ·; π₁)` under `Φ_t`. -/
theorem mu_simulation (M₁ : MDP S₁ A₁) (M₂ : MDP S₂ A₂) (hP₁ : M₁.IsMarkov) (hP₂ : M₂.IsMarkov)
    (s₁ : S₁) (s₂ : S₂) {π₁ : Plan S₁ A₁} {π₂ : Plan S₂ A₂}
    {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂}
    {t : ℕ} (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2)
    (hπ₁ : ∀ j < t, Measurable (π₁ j)) (hπ₂ : ∀ j < t, Measurable (π₂ j))
    (hstep : ∀ j < t, ∀ h : Fin j → S₁,
      M₂.P j (lastState s₂ (liftHist ψ j h), π₂ j (liftHist ψ j h)) =
        (M₁.P j (lastState s₁ h, π₁ j h)).map (ψ j (liftHist ψ j h))) :
    mu M₂ s₂ π₂ t = (mu M₁ s₁ π₁ t).map (liftHist ψ t) := by
  induction t with
  | zero =>
    rw [mu_zero, mu_zero, Measure.map_dirac' (measurable_liftHist hψ)]
    congr 1
  | succ t ih =>
    have ih := ih (fun j hj => hψ j (by omega)) (fun j hj => hπ₁ j (by omega))
      (fun j hj => hπ₂ j (by omega)) (fun j hj => hstep j (by omega))
    have hm₁ := hπ₁ t (by omega)
    have hm₂ := hπ₂ t (by omega)
    have hΦ : Measurable (liftHist ψ t) := measurable_liftHist fun j hj => hψ j (by omega)
    have hΦ' : Measurable (liftHist ψ (t + 1)) := measurable_liftHist hψ
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have := isMarkovKernel_stepKernel M₂ hP₂ s₂ hm₂
    have hg : Measurable fun g : Fin t → S₂ =>
        ∫⁻ s, f (Fin.snoc g s) ∂stepKernel M₂ s₂ π₂ t g :=
      (hf.comp (measurable_snoc t)).lintegral_kernel_prod_right'
    rw [lintegral_map hf hΦ', mu_succ_lintegral M₂ hP₂ s₂ hm₂ hf,
      mu_succ_lintegral M₁ hP₁ s₁ hm₁ (f := fun h => f (liftHist ψ (t + 1) h)) (hf.comp hΦ')]
    simp_rw [← stepKernel_apply M₂ s₂ hm₂]
    rw [ih, lintegral_map hg hΦ]
    refine lintegral_congr fun h => ?_
    have hψh : Measurable (ψ t (liftHist ψ t h)) :=
      (hψ t (by omega)).comp (measurable_const.prodMk measurable_id)
    rw [stepKernel_apply M₂ s₂ hm₂, hstep t (by omega) h,
      lintegral_map (f := fun s => f (Fin.snoc (liftHist ψ t h) s))
        (hf.comp ((measurable_snoc t).comp (measurable_const.prodMk measurable_id))) hψh]
    refine lintegral_congr fun s => ?_
    rw [liftHist_snoc]

/-- The expected rewards of the second model are expectations over the first model's histories:
`∫ u₂ dμ₂ᵗ = ∫ (u₂ ∘ Φ_t) dμ₁ᵗ`. -/
theorem expRew_simulation (M₁ : MDP S₁ A₁) (M₂ : MDP S₂ A₂) (hP₁ : M₁.IsMarkov)
    (hP₂ : M₂.IsMarkov) (s₁ : S₁) (s₂ : S₂) {π₁ : Plan S₁ A₁} {π₂ : Plan S₂ A₂}
    {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂}
    {t : ℕ} (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2)
    (hπ₁ : ∀ j < t, Measurable (π₁ j)) (hπ₂ : ∀ j < t, Measurable (π₂ j))
    (hstep : ∀ j < t, ∀ h : Fin j → S₁,
      M₂.P j (lastState s₂ (liftHist ψ j h), π₂ j (liftHist ψ j h)) =
        (M₁.P j (lastState s₁ h, π₁ j h)).map (ψ j (liftHist ψ j h)))
    {f : (Fin t → S₂) → ℝ} (hf : Measurable f) :
    ∫ g, f g ∂mu M₂ s₂ π₂ t = ∫ h, f (liftHist ψ t h) ∂mu M₁ s₁ π₁ t := by
  rw [mu_simulation M₁ M₂ hP₁ hP₂ s₁ s₂ hψ hπ₁ hπ₂ hstep,
    integral_map (measurable_liftHist hψ).aemeasurable hf.aestronglyMeasurable]

/-- An exogenous Markov chain with transition functions `Q t` (the book's `Q_{t+1}`), as a
Markov decision process with a single action and no rewards. -/
noncomputable def chainMDP {Z : Type*} [MeasurableSpace Z] (Q : ℕ → Kernel Z Z) : MDP Z Unit where
  Γ := fun _ => Set.univ
  P := fun t => (Q t).comap Prod.fst measurable_fst
  u := fun _ _ => 0
  uT := fun _ => 0
  β := 0

/-- The distribution of `(z₁, …, z_t)` for the chain started at `z₀`. -/
noncomputable def chainHist {Z : Type*} [MeasurableSpace Z] (Q : ℕ → Kernel Z Z) (z₀ : Z)
    (t : ℕ) : Measure (Fin t → Z) :=
  mu (chainMDP Q) z₀ (fun _ _ => ()) t

theorem chainMDP_isMarkov {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) : (chainMDP Q).IsMarkov := fun t => by
  have := hQ t
  exact inferInstanceAs (IsMarkovKernel ((Q t).comap Prod.fst measurable_fst))

theorem isProbabilityMeasure_chainHist {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) (z₀ : Z) (t : ℕ) :
    IsProbabilityMeasure (chainHist Q z₀ t) :=
  isProbabilityMeasure_mu _ (chainMDP_isMarkov hQ) z₀ fun _ _ => measurable_const

/-- The chain's history distribution: `∫ f dμᵗ⁺¹ = ∫ [∫ f(zᵗ, z′) Q_{t+1}(z_t, dz′)] μᵗ(dzᵗ)`. -/
theorem chainHist_succ_lintegral {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) (z₀ : Z) (t : ℕ) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂chainHist Q z₀ (t + 1) =
      ∫⁻ h, ∫⁻ z, f (Fin.snoc h z) ∂Q t (lastState z₀ h) ∂chainHist Q z₀ t :=
  mu_succ_lintegral _ (chainMDP_isMarkov hQ) z₀ measurable_const hf

/-- Miao, p. 137: "The state system is governed by a Markov process `(s_t)`." Under a Markovian
plan `π_t(sᵗ) = g_t(s_t)` (including `π₀ = g₀(s₀)`), the history measure `μᵗ(s₀, ·; π)` is the
distribution of the Markov chain with transition functions `s ↦ P_{t+1}(s, g_t(s); ·)`. -/
theorem mu_markovian (M : MDP S₁ A₁) (hP : M.IsMarkov) (s₀ : S₁) {g : ℕ → S₁ → A₁}
    (hg : ∀ t, Measurable (g t)) {π : Plan S₁ A₁}
    (hπ : ∀ t (h : Fin t → S₁), π t h = g t (lastState s₀ h)) (t : ℕ) :
    mu M s₀ π t = chainHist (fun t => (M.P t).comap (fun s => (s, g t s))
      (measurable_id.prodMk (hg t))) s₀ t := by
  have hπm : ∀ t, Measurable (π t) := fun t => by
    have : π t = fun h => g t (lastState s₀ h) := funext (hπ t)
    rw [this]
    exact (hg t).comp (measurable_lastState s₀ t)
  refine mu_eq_of_stepKernel s₀ fun j _ => ?_
  have := hP j
  ext h : 1
  rw [stepKernel_apply M s₀ (hπm j), stepKernel_apply _ s₀ measurable_const, hπ]
  rfl

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two ways of building stochastic kernels

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `KernelTools`),
with the namespace renamed.

Tools for the examples of Miao, §5.2, pp. 143–154.

* `famKernel κ`: for a countable action set with measurable singletons, the kernel
  `P(s, a; ·) = κ_a(s; ·)` built from one kernel per action (the discrete choice, stopping and
  bandit models).
* `pushKernel κ F`: the law of `F(x, ε)` when `ε ~ κ(x, ·)`, i.e. `x ↦ κ(x, ·) ∘ F(x, ·)⁻¹`
  (laws of motion driven by a shock, as in the optimal control model).
-/

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal stopping as a Markov decision problem

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `OptimalStopping`),
with the namespace renamed.

Miao, §5.2.2, pp. 144–146. An exogenous Markov process `(z_t)` on `Z` with transition functions
`Q_{t+1}` (`StoppingProblem.Q t`); at each date the decision maker continues (`a = 1`), earning
`f_t(z_t)`, or stops (`a = 0`), earning `g_t(z_t)` and nothing afterwards; if he never stops
before `T < ∞` he receives `h(z_T)`. The book recasts this as an MDP on `S = Z ∪ {ŝ}` with an
absorbing stopping state `ŝ` (`toMDP`; `Sum.inr ()` is `ŝ`).

* `stopRule`, `aliveSet`, `stopValue`: the stopping problem in its own terms — a stopping rule
  `d_t(z₁, …, z_t) ∈ {0, 1}`, the event that it has not stopped before `t`, and its expected
  discounted payoff `E[∑_{t<τ∧T} βᵗ f_t(z_t) + βᵗ g_τ(z_τ) 1{τ<T} + βᵀ h(z_T) 1{τ ≥ T}]` written
  date by date.
* `J0T_toMDP`: for every MDP plan `π` from `z₀`, `J₀ᵀ(z₀, π)` is the payoff of the stopping rule
  `d = π ∘ Φ` it induces, and `stopValue_toPlan`: every stopping rule is induced by an MDP plan
  with the same payoff. Hence `V0_toMDP`: **the value of the MDP equals the value of the
  stopping problem**, and the same for the infinite horizon (`J_toMDP`, `V_toMDP`).
* `toMDP_assumptions`: the MDP has stochastic kernels, satisfies Assumption 5.1.1, and, with
  bounded measurable payoffs, Assumption 5.1.3 for every `T` and (if stationary, `β < 1`)
  Assumption 5.1.4.

**Correction.** The book sets `Γ(ŝ) = ∅` (p. 145). Then `Γ` is not nonempty-valued, has no
selection, and no plan is feasible for any horizon `T ≥ 2` (`bookΓ_infeasible`): the problem as
printed is empty. The construction works with `Γ(ŝ) = A` (any action at `ŝ`, with zero reward
and `ŝ` absorbing), which is what `toMDP` uses. Also, the book allows `β ∈ (0, 1]` for stopping
problems (needed for the secretary problem, where `β = 1`), while its optimality criterion and
Assumption 5.1.2 require `β ∈ (0, 1)`; the equivalence theorems here hold for every `β`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter

variable {Z : Type*} [MeasurableSpace Z]

/-- The data of an optimal stopping problem (Miao, p. 145). `Q t` is the book's `Q_{t+1}`. -/
structure StoppingProblem (Z : Type*) [MeasurableSpace Z] where
  Q : ℕ → Kernel Z Z
  f : ℕ → Z → ℝ
  g : ℕ → Z → ℝ
  h : Z → ℝ
  β : ℝ

/-- The stopping state `ŝ`. -/
def sHat : Z ⊕ Unit := Sum.inr ()

/-- The kernel after continuing: `Q_{t+1}(z, ·)` on `Z`, and `ŝ` stays at `ŝ`. -/
noncomputable def contKernel (Q : Kernel Z Z) : Kernel (Z ⊕ Unit) (Z ⊕ Unit) where
  toFun := Sum.elim (Kernel.map Q Sum.inl) fun _ => Measure.dirac sHat
  measurable' := (Kernel.map Q Sum.inl).measurable.sumElim measurable_const

theorem contKernel_inl (Q : Kernel Z Z) (z : Z) :
    contKernel Q (Sum.inl z) = (Q z).map Sum.inl :=
  Kernel.map_apply _ measurable_inl z

theorem contKernel_inr (Q : Kernel Z Z) (u : Unit) :
    contKernel Q (Sum.inr u) = Measure.dirac sHat :=
  rfl

/-- The kernels of the stopping MDP (Miao, p. 146): `P_{t+1}(z, 1; ·) = Q_{t+1}(z, ·)` on `Z`;
after stopping, or at `ŝ`, the next state is `ŝ`. -/
noncomputable def stopKernel (Q : Kernel Z Z) : Kernel ((Z ⊕ Unit) × Fin 2) (Z ⊕ Unit) :=
  famKernel fun a => if a = 1 then contKernel Q else Kernel.const _ (Measure.dirac sHat)

/-- The optimal stopping problem as a Markov decision process (Miao, pp. 145–146), with the
corrected constraint `Γ(ŝ) = {0, 1}`. -/
noncomputable def StoppingProblem.toMDP (sp : StoppingProblem Z) : MDP (Z ⊕ Unit) (Fin 2) where
  Γ := fun _ => Set.univ
  P := fun t => stopKernel (sp.Q t)
  u := fun t x => Sum.elim (fun z => if x.2 = 1 then sp.f t z else sp.g t z) (fun _ => 0) x.1
  uT := Sum.elim sp.h fun _ => 0
  β := sp.β

/-- The constraint correspondence printed in the book (p. 145): `Γ(z) = {0, 1}`, `Γ(ŝ) = ∅`. -/
def bookΓ : Z ⊕ Unit → Set (Fin 2) := Sum.elim (fun _ => Set.univ) fun _ => ∅

/-- **Correction to Miao, p. 145.** With `Γ(ŝ) = ∅` no plan is feasible for any horizon
`T ≥ 2`, from any initial state: a feasible plan would give a measurable selection of `Γ`, but
`Γ(ŝ)` is empty. -/
theorem bookΓ_infeasible (sp : StoppingProblem Z) {T : ℕ∞} (hT : 2 ≤ T) (s₀ : Z ⊕ Unit) :
    feasiblePlans { sp.toMDP with Γ := bookΓ } T s₀ = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun π hπ => ?_
  obtain ⟨g, -, hg⟩ := selection_of_feasible _ hT hπ
  exact hg sHat

/-- A **stopping rule** for the horizon `T` (`T = ⊤` for an infinite horizon): measurable
decisions `d_t(z₁, …, z_t) ∈ {0, 1}` (`1` = continue) for `t < T`. -/
def stopRule (T : ℕ∞) : Set (Plan Z (Fin 2)) := {d | IsPlan T d}

/-- The histories along which the rule `d` has not stopped before date `t`. -/
def aliveSet (d : Plan Z (Fin 2)) : (t : ℕ) → Set (Fin t → Z)
  | 0 => Set.univ
  | t + 1 => Fin.init ⁻¹' (aliveSet d t ∩ {h | d t h = 1})

theorem measurableSet_aliveSet {d : Plan Z (Fin 2)} {t : ℕ} (hd : ∀ j < t, Measurable (d j)) :
    MeasurableSet (aliveSet d t) := by
  induction t with
  | zero => exact MeasurableSet.univ
  | succ t ih =>
    exact (measurable_init t) ((ih fun j hj => hd j (by omega)).inter
      (hd t (by omega) (measurableSet_singleton 1)))

/-- The payoff at date `t` of the stopping rule `d` along `zᵗ`: `f_t(z_t)` or `g_t(z_t)` if it
has not stopped before `t`, else `0`. -/
noncomputable def stopRew (sp : StoppingProblem Z) (z₀ : Z) (d : Plan Z (Fin 2)) (t : ℕ) :
    (Fin t → Z) → ℝ :=
  (aliveSet d t).indicator fun h =>
    if d t h = 1 then sp.f t (lastState z₀ h) else sp.g t (lastState z₀ h)

/-- The terminal payoff `h(z_T)`, received if the rule has not stopped before `T`. -/
noncomputable def stopTerm (sp : StoppingProblem Z) (z₀ : Z) (d : Plan Z (Fin 2)) (T : ℕ) :
    (Fin T → Z) → ℝ :=
  (aliveSet d T).indicator fun h => sp.h (lastState z₀ h)

/-- The expected discounted payoff of the stopping rule `d` over the horizon `T`. -/
noncomputable def stopValue (sp : StoppingProblem Z) (T : ℕ) (z₀ : Z) (d : Plan Z (Fin 2)) :
    ℝ :=
  ∑ t ∈ Finset.range T, sp.β ^ t * ∫ h, stopRew sp z₀ d t h ∂chainHist sp.Q z₀ t +
    sp.β ^ T * ∫ h, stopTerm sp z₀ d T h ∂chainHist sp.Q z₀ T

/-- The infinite-horizon payoff of a stopping rule: the limit of the partial sums. -/
noncomputable def stopValueInf (sp : StoppingProblem Z) (z₀ : Z) (d : Plan Z (Fin 2)) : EReal :=
  limUnder atTop fun n => ((∑ t ∈ Finset.range (n + 1),
    sp.β ^ t * ∫ h, stopRew sp z₀ d t h ∂chainHist sp.Q z₀ t : ℝ) : EReal)

/-- The value of the stopping problem over the horizon `T`. -/
noncomputable def stopV (sp : StoppingProblem Z) (T : ℕ) (z₀ : Z) : EReal :=
  ⨆ d ∈ stopRule (Z := Z) T, (stopValue sp T z₀ d : EReal)

/-- The value of the infinite-horizon stopping problem. -/
noncomputable def stopVInf (sp : StoppingProblem Z) (z₀ : Z) : EReal :=
  ⨆ d ∈ stopRule (Z := Z) ⊤, stopValueInf sp z₀ d

/-- The step map from the exogenous history to the MDP history: the next state is `z′` if the
current state is in `Z` and the plan continues, and `ŝ` otherwise. -/
noncomputable def stopStep (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) (t : ℕ) (g : Fin t → Z ⊕ Unit)
    (z : Z) : Z ⊕ Unit :=
  open Classical in
  if (lastState (Sum.inl z₀) g).isLeft = true ∧ π t g = 1 then Sum.inl z else sHat

/-- The MDP history `Φ_t(z₁, …, z_t)` generated by the plan `π`. -/
noncomputable def stopLift (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) : (t : ℕ) → (Fin t → Z) →
    Fin t → Z ⊕ Unit :=
  liftHist (stopStep z₀ π)

/-- The stopping rule induced by an MDP plan: `d_t = π_t ∘ Φ_t`. -/
noncomputable def inducedRule (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) : Plan Z (Fin 2) :=
  fun t h => π t (stopLift z₀ π t h)

theorem measurable_stopStep (z₀ : Z) {π : Plan (Z ⊕ Unit) (Fin 2)} {t : ℕ}
    (hπ : Measurable (π t)) :
    Measurable fun p : (Fin t → Z ⊕ Unit) × Z => stopStep z₀ π t p.1 p.2 := by
  classical
  have hset : MeasurableSet {g : Fin t → Z ⊕ Unit |
      (lastState (Sum.inl z₀) g).isLeft = true ∧ π t g = 1} := by
    have h1 : MeasurableSet {s : Z ⊕ Unit | s.isLeft = true} := by
      have : {s : Z ⊕ Unit | s.isLeft = true} = Set.range Sum.inl := by
        ext s
        cases s <;> simp
      rw [this]
      exact measurableSet_range_inl
    exact ((measurable_lastState _ t) h1).inter (hπ (measurableSet_singleton 1))
  exact Measurable.ite (hset.preimage measurable_fst) (measurable_inl.comp measurable_snd)
    measurable_const

omit [MeasurableSpace Z] in
/-- The last state of `Φ_t(zᵗ)`: `z_t` while the induced rule has not stopped, `ŝ` after. -/
theorem lastState_stopLift (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) (t : ℕ) (h : Fin t → Z) :
    lastState (Sum.inl z₀) (stopLift z₀ π t h) =
      open Classical in
      if h ∈ aliveSet (inducedRule z₀ π) t then Sum.inl (lastState z₀ h) else sHat := by
  classical
  induction t with
  | zero => simp [aliveSet, lastState]
  | succ t ih =>
    have e : lastState (Sum.inl z₀) (stopLift z₀ π (t + 1) h) =
        stopStep z₀ π t (stopLift z₀ π t (Fin.init h)) (h (Fin.last t)) := by
      simp only [stopLift, liftHist, lastState_snoc]
    rw [e, stopStep, ih (Fin.init h)]
    by_cases ha : Fin.init h ∈ aliveSet (inducedRule z₀ π) t
    · by_cases hd : π t (stopLift z₀ π t (Fin.init h)) = 1
      · have hmem : h ∈ aliveSet (inducedRule z₀ π) (t + 1) := ⟨ha, hd⟩
        simp [ha, hd, hmem, lastState]
      · have hmem : h ∉ aliveSet (inducedRule z₀ π) (t + 1) := fun H => hd H.2
        simp [ha, hd, hmem]
    · have hmem : h ∉ aliveSet (inducedRule z₀ π) (t + 1) := fun H => ha H.1
      simp [ha, hmem, sHat]

theorem isMarkovKernel_contKernel {Q : Kernel Z Z} (hQ : IsMarkovKernel Q) :
    IsMarkovKernel (contKernel Q) := by
  refine ⟨fun x => ?_⟩
  cases x with
  | inl z =>
    rw [contKernel_inl]
    infer_instance
  | inr u =>
    rw [contKernel_inr]
    infer_instance

/-- The stopping MDP has stochastic kernels when the `Q_{t+1}` are transition functions. -/
theorem toMDP_isMarkov (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t)) :
    sp.toMDP.IsMarkov := by
  intro t
  change IsMarkovKernel (stopKernel (sp.Q t))
  refine isMarkovKernel_famKernel fun a => ?_
  by_cases ha : a = 1
  · simp only [ha, ↓reduceIte]
    exact isMarkovKernel_contKernel (hQ t)
  · simp only [ha, ↓reduceIte]
    infer_instance

theorem measurable_toMDP_u (sp : StoppingProblem Z) {t : ℕ} (hf : Measurable (sp.f t))
    (hg : Measurable (sp.g t)) : Measurable (sp.toMDP.u t) := by
  refine measurable_from_prod_countable_left fun a => ?_
  by_cases ha : a = 1
  · simp only [StoppingProblem.toMDP, ha, ↓reduceIte]
    exact hf.sumElim measurable_const
  · simp only [StoppingProblem.toMDP, ha, ↓reduceIte]
    exact hg.sumElim measurable_const

theorem measurable_toMDP_uT (sp : StoppingProblem Z) (hh : Measurable sp.h) :
    Measurable sp.toMDP.uT :=
  hh.sumElim measurable_const

omit [MeasurableSpace Z] in
theorem stopStep_eq (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) (t : ℕ) (g : Fin t → Z ⊕ Unit) :
    stopStep z₀ π t g =
      open Classical in
      if (lastState (Sum.inl z₀) g).isLeft = true ∧ π t g = 1 then Sum.inl
      else fun _ => sHat := by
  classical
  funext z
  unfold stopStep
  split_ifs <;> rfl

/-- The kernels of the stopping MDP along `Φ` are images of the `Q_{t+1}` (the hypothesis of
`mu_simulation`). -/
theorem stop_hstep (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t)) (z₀ : Z)
    (π : Plan (Z ⊕ Unit) (Fin 2)) (j : ℕ) (h : Fin j → Z) :
    sp.toMDP.P j (lastState (Sum.inl z₀) (stopLift z₀ π j h), π j (stopLift z₀ π j h)) =
      ((chainMDP sp.Q).P j (lastState z₀ h, ())).map (stopStep z₀ π j (stopLift z₀ π j h)) := by
  classical
  have := hQ j
  have hc : (chainMDP sp.Q).P j (lastState z₀ h, ()) = sp.Q j (lastState z₀ h) := rfl
  rw [hc, stopStep_eq]
  simp only [StoppingProblem.toMDP, stopKernel]
  rw [lastState_stopLift]
  by_cases ha : h ∈ aliveSet (inducedRule z₀ π) j
  · simp only [ha, ↓reduceIte, Sum.isLeft_inl, true_and]
    by_cases hd : π j (stopLift z₀ π j h) = 1
    · simp only [hd, ↓reduceIte, famKernel_apply, contKernel_inl]
    · simp only [hd, ↓reduceIte, famKernel_apply, Kernel.const_apply, Measure.map_const,
        measure_univ, one_smul]
  · simp only [ha, ↓reduceIte, sHat, Sum.isLeft_inr, Bool.false_eq_true, false_and,
      Measure.map_const, measure_univ, one_smul, famKernel_apply]
    split_ifs
    · rfl
    · rfl

theorem rew_stopLift (sp : StoppingProblem Z) (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) (t : ℕ)
    (h : Fin t → Z) : rew sp.toMDP (Sum.inl z₀) π t (stopLift z₀ π t h) =
      stopRew sp z₀ (inducedRule z₀ π) t h := by
  classical
  simp only [rew, stopRew, StoppingProblem.toMDP]
  rw [lastState_stopLift]
  by_cases ha : h ∈ aliveSet (inducedRule z₀ π) t
  · simp only [ha, ↓reduceIte, Set.indicator_of_mem ha, Sum.elim_inl]
    rfl
  · simp only [ha, ↓reduceIte, Set.indicator_of_notMem ha, sHat, Sum.elim_inr]

theorem term_stopLift (sp : StoppingProblem Z) (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) (T : ℕ)
    (h : Fin T → Z) : sp.toMDP.uT (lastState (Sum.inl z₀) (stopLift z₀ π T h)) =
      stopTerm sp z₀ (inducedRule z₀ π) T h := by
  classical
  simp only [stopTerm, StoppingProblem.toMDP]
  rw [lastState_stopLift]
  by_cases ha : h ∈ aliveSet (inducedRule z₀ π) T
  · simp only [ha, ↓reduceIte, Set.indicator_of_mem ha, Sum.elim_inl]
  · simp only [ha, ↓reduceIte, Set.indicator_of_notMem ha, sHat, Sum.elim_inr]

/-- The expected reward of the stopping MDP at date `t` is that of the induced stopping rule. -/
theorem expRew_toMDP (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (z₀ : Z)
    {π : Plan (Z ⊕ Unit) (Fin 2)} {t : ℕ} (hπ : ∀ j ≤ t, Measurable (π j)) :
    expRew sp.toMDP (Sum.inl z₀) π t =
      ∫ h, stopRew sp z₀ (inducedRule z₀ π) t h ∂chainHist sp.Q z₀ t := by
  rw [expRew, expRew_simulation (chainMDP sp.Q) sp.toMDP (chainMDP_isMarkov hQ)
    (toMDP_isMarkov sp hQ) z₀ (Sum.inl z₀) (π₁ := fun _ _ => ())
    (fun j hj => measurable_stopStep z₀ (hπ j (by omega))) (fun _ _ => measurable_const)
    (fun j hj => hπ j (by omega)) (fun j _ h => stop_hstep sp hQ z₀ π j h)
    (measurable_rew _ _ (measurable_toMDP_u sp (hf t) (hg t)) (hπ t le_rfl))]
  exact integral_congr_ae (Eventually.of_forall fun h => rew_stopLift sp z₀ π t h)

/-- Miao, pp. 145–146: for every plan `π` of the stopping MDP, its objective (5.3) from `z₀` is
the payoff of the stopping rule it induces. -/
theorem J0T_toMDP (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (hh : Measurable sp.h)
    (z₀ : Z) {T : ℕ} {π : Plan (Z ⊕ Unit) (Fin 2)} (hπ : ∀ j < T, Measurable (π j)) :
    J0T sp.toMDP T (Sum.inl z₀) π = stopValue sp T z₀ (inducedRule z₀ π) := by
  rw [J0T, stopValue]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [expRew_toMDP sp hQ hf hg z₀ fun j hj => hπ j (by have := Finset.mem_range.1 ht; omega)]
    rfl
  · rw [expRew_simulation (chainMDP sp.Q) sp.toMDP (chainMDP_isMarkov hQ)
      (toMDP_isMarkov sp hQ) z₀ (Sum.inl z₀) (π₁ := fun _ _ => ())
      (fun j hj => measurable_stopStep z₀ (hπ j hj)) (fun _ _ => measurable_const) hπ
      (fun j _ h => stop_hstep sp hQ z₀ π j h)
      (f := fun g => sp.toMDP.uT (lastState (Sum.inl z₀) g))
      ((measurable_toMDP_uT sp hh).comp (measurable_lastState _ T))]
    exact congrArg _ (integral_congr_ae (Eventually.of_forall fun h => term_stopLift sp z₀ π T h))

/-- Infinite horizon: the objective (5.4) of a plan of the stopping MDP is the payoff of the
induced stopping rule. -/
theorem J_toMDP (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (z₀ : Z)
    {π : Plan (Z ⊕ Unit) (Fin 2)} (hπ : ∀ j, Measurable (π j)) :
    J sp.toMDP (Sum.inl z₀) π = stopValueInf sp z₀ (inducedRule z₀ π) := by
  have e : (fun n => (partialSum sp.toMDP (Sum.inl z₀) π n : EReal)) = fun n =>
      ((∑ t ∈ Finset.range (n + 1), sp.β ^ t *
        ∫ h, stopRew sp z₀ (inducedRule z₀ π) t h ∂chainHist sp.Q z₀ t : ℝ) : EReal) := by
    funext n
    simp only [partialSum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [expRew_toMDP sp hQ hf hg z₀ fun j _ => hπ j]
    rfl
  rw [J, stopValueInf, e]

theorem measurable_inducedRule (z₀ : Z) {π : Plan (Z ⊕ Unit) (Fin 2)} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) : Measurable (inducedRule z₀ π t) :=
  (hπ t le_rfl).comp (measurable_liftHist fun j hj => measurable_stopStep z₀ (hπ j hj.le))

/-- The `Z`-part of an MDP history (`ŝ` replaced by `z₀`). -/
def zOf (z₀ : Z) {t : ℕ} (g : Fin t → Z ⊕ Unit) : Fin t → Z :=
  fun i => Sum.elim id (fun _ => z₀) (g i)

theorem measurable_zOf (z₀ : Z) (t : ℕ) : Measurable (zOf z₀ (t := t)) :=
  measurable_pi_iff.2 fun i => (measurable_id.sumElim measurable_const).comp (measurable_pi_apply i)

/-- The MDP plan that applies the stopping rule `d` to the `Z`-part of the history. -/
def toPlan (z₀ : Z) (d : Plan Z (Fin 2)) : Plan (Z ⊕ Unit) (Fin 2) := fun t g => d t (zOf z₀ g)

omit [MeasurableSpace Z] in
theorem lastState_comp_inl (z₀ : Z) {t : ℕ} (h : Fin t → Z) :
    lastState (Sum.inl z₀ : Z ⊕ Unit) (Sum.inl ∘ h) = Sum.inl (lastState z₀ h) := by
  cases t <;> rfl

omit [MeasurableSpace Z] in
/-- While the induced rule has not stopped, `Φ_t(zᵗ) = (z₁, …, z_t)` (all states in `Z`). -/
theorem stopLift_of_alive (z₀ : Z) (π : Plan (Z ⊕ Unit) (Fin 2)) {t : ℕ} {h : Fin t → Z}
    (ha : h ∈ aliveSet (inducedRule z₀ π) t) : stopLift z₀ π t h = Sum.inl ∘ h := by
  classical
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
    have hi := ih ha.1
    have hd : π t (stopLift z₀ π t (Fin.init h)) = 1 := ha.2
    have e : stopLift z₀ π (t + 1) h = Fin.snoc (stopLift z₀ π t (Fin.init h))
        (stopStep z₀ π t (stopLift z₀ π t (Fin.init h)) (h (Fin.last t))) := rfl
    rw [e, stopStep_eq]
    rw [hi] at hd ⊢
    simp only [lastState_comp_inl, Sum.isLeft_inl, hd, and_self, ↓reduceIte]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.init]

omit [MeasurableSpace Z] in
/-- The plan `toPlan d` induces the stopping rule `d` on the histories where it matters. -/
theorem aliveSet_toPlan (z₀ : Z) (d : Plan Z (Fin 2)) (t : ℕ) :
    aliveSet (inducedRule z₀ (toPlan z₀ d)) t = aliveSet d t ∧
      ∀ h ∈ aliveSet d t, inducedRule z₀ (toPlan z₀ d) t h = d t h := by
  have hag : ∀ t, ∀ h ∈ aliveSet (inducedRule z₀ (toPlan z₀ d)) t,
      inducedRule z₀ (toPlan z₀ d) t h = d t h := by
    intro t h ha
    simp only [inducedRule, stopLift_of_alive z₀ _ ha, toPlan]
    rfl
  have hset : ∀ t, aliveSet (inducedRule z₀ (toPlan z₀ d)) t = aliveSet d t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      ext h
      simp only [aliveSet, Set.mem_preimage, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have h2' : inducedRule z₀ (toPlan z₀ d) t (Fin.init h) = 1 := h2
        exact ⟨ih ▸ h1, (hag t _ h1).symm.trans h2'⟩
      · rintro ⟨h1, h2⟩
        have h1' : Fin.init h ∈ aliveSet (inducedRule z₀ (toPlan z₀ d)) t := ih.symm ▸ h1
        have h2' : d t (Fin.init h) = 1 := h2
        exact ⟨h1', (hag t _ h1').trans h2'⟩
  exact ⟨hset t, fun h ha => hag t h (hset t ▸ ha)⟩

/-- Every stopping rule is induced by an MDP plan with the same payoff. -/
theorem stopValue_toPlan (sp : StoppingProblem Z) (z₀ : Z) (d : Plan Z (Fin 2)) (T : ℕ) :
    stopValue sp T z₀ (inducedRule z₀ (toPlan z₀ d)) = stopValue sp T z₀ d := by
  have hr : ∀ t, stopRew sp z₀ (inducedRule z₀ (toPlan z₀ d)) t = stopRew sp z₀ d t := by
    intro t
    funext h
    obtain ⟨hs, hag⟩ := aliveSet_toPlan z₀ d t
    simp only [stopRew, hs]
    by_cases ha : h ∈ aliveSet d t
    · simp only [Set.indicator_of_mem ha, hag h ha]
    · simp only [Set.indicator_of_notMem ha]
  have ht : stopTerm sp z₀ (inducedRule z₀ (toPlan z₀ d)) T = stopTerm sp z₀ d T := by
    simp only [stopTerm, (aliveSet_toPlan z₀ d T).1]
  simp only [stopValue, hr, ht]

theorem stopValueInf_toPlan (sp : StoppingProblem Z) (z₀ : Z) (d : Plan Z (Fin 2)) :
    stopValueInf sp z₀ (inducedRule z₀ (toPlan z₀ d)) = stopValueInf sp z₀ d := by
  have hr : ∀ t, stopRew sp z₀ (inducedRule z₀ (toPlan z₀ d)) t = stopRew sp z₀ d t := by
    intro t
    funext h
    obtain ⟨hs, hag⟩ := aliveSet_toPlan z₀ d t
    simp only [stopRew, hs]
    by_cases ha : h ∈ aliveSet d t
    · simp only [Set.indicator_of_mem ha, hag h ha]
    · simp only [Set.indicator_of_notMem ha]
  simp only [stopValueInf, hr]

theorem isPlan_toPlan (z₀ : Z) {T : ℕ∞} {d : Plan Z (Fin 2)} (hd : d ∈ stopRule (Z := Z) T) :
    IsPlan T (toPlan z₀ d) := fun t ht => (hd t ht).comp (measurable_zOf z₀ t)

theorem inducedRule_mem (z₀ : Z) {T : ℕ∞} {π : Plan (Z ⊕ Unit) (Fin 2)} (hπ : IsPlan T π) :
    inducedRule z₀ π ∈ stopRule (Z := Z) T := fun t ht =>
  measurable_inducedRule z₀ fun j hj => hπ j (lt_of_le_of_lt (by exact_mod_cast hj) ht)

/-- **The stopping problem is the MDP** (Miao, pp. 145–146): the value of the `T`-horizon
stopping MDP from `z₀` equals the value of the optimal stopping problem. -/
theorem V0_toMDP (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (hh : Measurable sp.h)
    (T : ℕ) (z₀ : Z) : V0 sp.toMDP T (Sum.inl z₀) = stopV sp T z₀ := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun d hd => ?_)
  · rw [J0T_toMDP sp hQ hf hg hh z₀ fun j hj => hπ.1 j (by exact_mod_cast hj)]
    exact le_iSup₂ (f := fun d (_ : d ∈ stopRule (Z := Z) T) => (stopValue sp T z₀ d : EReal))
      _ (inducedRule_mem z₀ hπ.1)
  · have hπ : toPlan z₀ d ∈ feasiblePlans sp.toMDP T (Sum.inl z₀) :=
      ⟨isPlan_toPlan z₀ hd, fun _ _ _ => Set.mem_univ _⟩
    have := le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans sp.toMDP T (Sum.inl z₀)) =>
      (J0T sp.toMDP T (Sum.inl z₀) π : EReal)) _ hπ
    rwa [J0T_toMDP sp hQ hf hg hh z₀ fun j hj => hπ.1 j (by exact_mod_cast hj),
      stopValue_toPlan] at this

/-- **The stopping problem is the MDP**, infinite horizon. -/
theorem V_toMDP (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (z₀ : Z) :
    V sp.toMDP (Sum.inl z₀) = stopVInf sp z₀ := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun d hd => ?_)
  · rw [J_toMDP sp hQ hf hg z₀ fun j => hπ.1 j (WithTop.coe_lt_top j)]
    exact le_iSup₂ (f := fun d (_ : d ∈ stopRule (Z := Z) ⊤) => stopValueInf sp z₀ d)
      _ (inducedRule_mem z₀ hπ.1)
  · have hπ : toPlan z₀ d ∈ feasiblePlans sp.toMDP ⊤ (Sum.inl z₀) :=
      ⟨isPlan_toPlan z₀ hd, fun _ _ _ => Set.mem_univ _⟩
    have := le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans sp.toMDP ⊤ (Sum.inl z₀)) =>
      J sp.toMDP (Sum.inl z₀) π) _ hπ
    rwa [J_toMDP sp hQ hf hg z₀ fun j => hπ.1 j (WithTop.coe_lt_top j),
      stopValueInf_toPlan] at this

/-- Payoffs bounded by `B ≥ 0`. -/
def StoppingProblem.Bounded (sp : StoppingProblem Z) (B : ℝ) : Prop :=
  0 ≤ B ∧ (∀ t z, |sp.f t z| ≤ B) ∧ (∀ t z, |sp.g t z| ≤ B) ∧ ∀ z, |sp.h z| ≤ B

/-- A stationary stopping problem: `Q`, `f` and `g` do not depend on time. -/
def StoppingProblem.IsStationary (sp : StoppingProblem Z) : Prop :=
  ∀ t, sp.Q t = sp.Q 0 ∧ sp.f t = sp.f 0 ∧ sp.g t = sp.g 0

/-- The stopping MDP satisfies the assumptions of §5.1: its kernels are stochastic kernels,
Assumption 5.1.1 holds, and with bounded measurable payoffs Assumption 5.1.3 holds for every
`T`, and Assumption 5.1.4 holds if the problem is stationary and `0 ≤ β < 1`. -/
theorem toMDP_assumptions (sp : StoppingProblem Z) (hQ : ∀ t, IsMarkovKernel (sp.Q t))
    (hf : ∀ t, Measurable (sp.f t)) (hg : ∀ t, Measurable (sp.g t)) (hh : Measurable sp.h)
    {B : ℝ} (hB : sp.Bounded B) :
    sp.toMDP.IsMarkov ∧ HasMeasurableSelection sp.toMDP.Γ ∧ (∀ T, Assumption513 sp.toMDP T) ∧
      (sp.IsStationary → 0 ≤ sp.β → sp.β < 1 → Assumption514 sp.toMDP) := by
  have hP := toMDP_isMarkov sp hQ
  have hu : ∀ t x, |sp.toMDP.u t x| ≤ B := by
    rintro t ⟨s, a⟩
    cases s with
    | inl z =>
      simp only [StoppingProblem.toMDP, Sum.elim_inl]
      split_ifs
      · exact hB.2.1 t z
      · exact hB.2.2.1 t z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1
  have huT : ∀ s, |sp.toMDP.uT s| ≤ B := by
    intro s
    cases s with
    | inl z => exact hB.2.2.2 z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1
  have hmu : ∀ t, Measurable (sp.toMDP.u t) := fun t => measurable_toMDP_u sp (hf t) (hg t)
  refine ⟨hP, ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩,
    fun T => assumption_5_1_3_of_bounded hP ⟨hu, huT⟩ hmu (measurable_toMDP_uT sp hh) T,
    fun hst hβ0 hβ1 => assumption_5_1_4_of_bounded hP (fun t => ?_) hu hmu hβ0 hβ1⟩
  obtain ⟨hQt, hft, hgt⟩ := hst t
  simp only [StoppingProblem.toMDP, hQt, hft, hgt, and_self]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of optimal stopping problems

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `StoppingExamples`),
with the namespace renamed.

Miao, §5.2.2, pp. 146–149, and Exercises 5.1–5.3, p. 155. Each problem is an instance of
`StoppingProblem`, so `V0_toMDP`/`V_toMDP` identify it with its Markov decision problem, and
`toMDP_assumptions` gives the assumptions of §5.1 once the payoffs are bounded.

* Option exercise (5.7)–(5.8): `g_t(z) = y(z) − I`, `f_t = 0` (`optionExercise`,
  `optionExercise_assumptions`); the American call with `β = 1/(1 + r)` (`americanCall_beta`).
  Payoffs are `y(z_t)` for a measurable payoff function `y` (the book takes `y(z) = z`); the
  assumptions are proved for bounded `y`.
* Exit (5.9)–(5.10): `g_t = ξ`, `f_t = ϕ − c_f` (`exitProblem`, `exitProblem_assumptions`).
* Secretary problem (pp. 147–149): `secretary`, with the book's transition function and rewards,
  dates shifted by one (MDP date `t` is the book's `t + 1`). Its kernels are stochastic kernels
  and Assumption 5.1.3 holds (`secretary_assumptions`). The probability `t/N` is derived in
  `Secretary`. **Note:** the criterion is a probability, so `β = 1`, outside Assumption 5.1.2;
  for finite horizons nothing in §5.1 needs `β < 1` (as the book itself remarks on p. 140).
* **Exercise 5.1** (job search): `jobSearch`; accepting `w` is stopping with payoff
  `w/(1 − β) = ∑ βᵗ w` (`ex_5_1_accept`); assumptions (`ex_5_1`).
* **Exercise 5.2** (American put): `americanPut`, finite horizon with terminal payoff
  `max(K − p(z_T), 0)` (`ex_5_2`).
* **Exercise 5.3** (best-two secretary): `secretaryTwo` (`ex_5_3`); the relative-rank state has
  three values and the rewards are the conditional probabilities that a candidate of relative rank
  1 or 2 among the first `k` is among the two best of `N` (their derivation is in the docstring and
  is not formalised).
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z]

/-- The irreversible investment (option exercise) problem (Miao, pp. 146–147). -/
def optionExercise (Q : Kernel Z Z) (y : Z → ℝ) (I β : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ _ => 0
  g := fun _ z => y z - I
  h := fun _ => 0
  β := β

/-- Miao (5.7)–(5.8): `g_t(z_t) = z_t − I`, `f_t(z_t) = 0`. -/
theorem eq_5_7_5_8 (Q : Kernel Z Z) (y : Z → ℝ) (I β : ℝ) (t : ℕ) (z : Z) :
    (optionExercise Q y I β).g t z = y z - I ∧ (optionExercise Q y I β).f t z = 0 :=
  ⟨rfl, rfl⟩

/-- The option exercise problem satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when the payoff is
measurable and bounded and `β ∈ (0, 1)`. -/
theorem optionExercise_assumptions {Q : Kernel Z Z} [IsMarkovKernel Q] {y : Z → ℝ}
    (hy : Measurable y) {B : ℝ} (hB : ∀ z, |y z| ≤ B) {I β : ℝ} (hI : 0 ≤ I) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (optionExercise Q y I β).toMDP.IsMarkov ∧
      HasMeasurableSelection (optionExercise Q y I β).toMDP.Γ ∧
      Assumption512 (optionExercise Q y I β).toMDP ∧
      Assumption514 (optionExercise Q y I β).toMDP := by
  have hb : (optionExercise Q y I β).Bounded (max B 0 + I) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · simp only [optionExercise, abs_zero]
      positivity
    · calc |y z - I| ≤ |y z| + |I| := abs_sub _ _
        _ ≤ max B 0 + I := by rw [abs_of_nonneg hI]; linarith [hB z, le_max_left B 0]
    · simp only [optionExercise, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (optionExercise Q y I β) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => measurable_const) (fun _ => hy.sub_const I) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- Miao, p. 147: for the American call, `β = 1/(1 + r)`, which lies in `(0, 1)` when the
interest rate `r` is positive. -/
theorem americanCall_beta {r : ℝ} (hr : 0 < r) : 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 :=
  ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

/-- The exit problem (Miao, p. 147): staying earns `ϕ(z) − c_f`, exiting earns `ξ`. -/
def exitProblem (Q : Kernel Z Z) (φ : Z → ℝ) (cf ξ β : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ z => φ z - cf
  g := fun _ _ => ξ
  h := fun _ => 0
  β := β

/-- Miao (5.9)–(5.10): `g_t(z_t) = ξ`, `f_t(z_t) = ϕ(z_t) − c_f`. -/
theorem eq_5_9_5_10 (Q : Kernel Z Z) (φ : Z → ℝ) (cf ξ β : ℝ) (t : ℕ) (z : Z) :
    (exitProblem Q φ cf ξ β).g t z = ξ ∧ (exitProblem Q φ cf ξ β).f t z = φ z - cf :=
  ⟨rfl, rfl⟩

/-- The exit problem satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when profits are measurable
and bounded and `β ∈ (0, 1)`. -/
theorem exitProblem_assumptions {Q : Kernel Z Z} [IsMarkovKernel Q] {φ : Z → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ z, |φ z| ≤ B) {cf ξ β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (exitProblem Q φ cf ξ β).toMDP.IsMarkov ∧
      HasMeasurableSelection (exitProblem Q φ cf ξ β).toMDP.Γ ∧
      Assumption512 (exitProblem Q φ cf ξ β).toMDP ∧
      Assumption514 (exitProblem Q φ cf ξ β).toMDP := by
  have hb : (exitProblem Q φ cf ξ β).Bounded (max B 0 + |cf| + |ξ|) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · calc |φ z - cf| ≤ |φ z| + |cf| := abs_sub _ _
        _ ≤ max B 0 + |cf| + |ξ| := by linarith [hB z, le_max_left B 0, abs_nonneg ξ]
    · simp only [exitProblem]
      linarith [le_max_right B 0, abs_nonneg cf]
    · simp only [exitProblem, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (exitProblem Q φ cf ξ β) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => hφ.sub_const cf) (fun _ => measurable_const) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- A two-point law: `1` with probability `p`, `0` with probability `1 − p`. -/
noncomputable def bern (p : ℝ) : Measure (Fin 2) :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

theorem isProbabilityMeasure_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bern p) := by
  refine ⟨?_⟩
  simp only [bern, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem bern_one (p : ℝ) :
    bern p {1} = ENNReal.ofReal p ∧ bern p {0} = ENNReal.ofReal (1 - p) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [bern, h10, h10.symm, Set.indicator]

/-- The secretary problem with `N` candidates (Miao, pp. 147–149), with dates shifted by one:
MDP date `t` is the book's `t + 1` (the `(t + 1)`-th candidate). The state is `1` if the
current candidate is the best seen so far; `Q_{t+1}(z, 1) = 1/(t + 1)` becomes
`Q t = bern (1/(t + 2))`; stopping at the `k`-th candidate when `z = 1` pays `k/N`; the terminal
date is the `N`-th candidate, with `h(1) = 1`, `h(0) = 0`; `β = 1`. (`min k N` replaces `k` so
that the payoff is bounded at dates past the horizon, where it plays no role.) -/
noncomputable def secretary (N : ℕ) : StoppingProblem (Fin 2) where
  Q := fun t => Kernel.const _ (bern (1 / (t + 2)))
  f := fun _ _ => 0
  g := fun t z => if z = 1 then (min (t + 1) N : ℕ) / (N : ℝ) else 0
  h := fun z => if z = 1 then 1 else 0
  β := 1

/-- Miao, p. 148: `Q_{t+1}(z, 1) = 1/(t + 1)` and `Q_{t+1}(z, 0) = t/(t + 1)` (in shifted dates,
`Q t(z, ·)` gives `1` probability `1/(t + 2)`), independent of `z`. -/
theorem secretary_Q (N t : ℕ) (z : Fin 2) :
    (secretary N).Q t z {1} = ENNReal.ofReal (1 / (t + 2)) ∧
      (secretary N).Q t z {0} = ENNReal.ofReal ((t + 1) / (t + 2)) := by
  have h0 : (0 : ℝ) ≤ 1 / (t + 2) := by positivity
  have h1 : 1 / ((t : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  obtain ⟨e1, e0⟩ := bern_one (1 / ((t : ℝ) + 2))
  refine ⟨e1, ?_⟩
  rw [show (secretary N).Q t z = bern (1 / (t + 2)) from rfl, e0]
  congr 1
  field_simp
  ring

/-- The secretary problem: the kernels are stochastic kernels, Assumption 5.1.1 holds, and
Assumption 5.1.3 holds for every horizon (rewards lie in `[0, 1]`). -/
theorem secretary_assumptions (N : ℕ) :
    (secretary N).toMDP.IsMarkov ∧ HasMeasurableSelection (secretary N).toMDP.Γ ∧
      ∀ T, Assumption513 (secretary N).toMDP T := by
  have hQ : ∀ t, IsMarkovKernel ((secretary N).Q t) := fun t => by
    have : IsProbabilityMeasure (bern (1 / ((t : ℝ) + 2))) :=
      isProbabilityMeasure_bern (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
  have hb : (secretary N).Bounded 1 := by
    refine ⟨zero_le_one, fun t z => by simp [secretary], fun t z => ?_, fun z => ?_⟩
    · simp only [secretary]
      split_ifs
      · rcases Nat.eq_zero_or_pos N with hN | hN
        · simp [hN]
        · rw [abs_of_nonneg (by positivity), div_le_one (by exact_mod_cast hN)]
          exact_mod_cast min_le_right _ _
      · simp
    · simp only [secretary]
      split_ifs <;> simp
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (secretary N) hQ (fun _ => measurable_const)
    (fun _ => measurable_of_finite _) (measurable_of_finite _) hb
  exact ⟨h1, h2, h3⟩

/-- The job search problem of **Exercise 5.1** (McCall): offers `w ~ F` i.i.d. on the wage space
`W`, with wage `w(·)`; rejecting pays `c` and continues; accepting pays the wage forever, i.e. the
lump sum `w/(1 − β)` (`ex_5_1_accept`). -/
noncomputable def jobSearch {W : Type*} [MeasurableSpace W] (F : Measure W) (wage : W → ℝ)
    (c β : ℝ) : StoppingProblem W where
  Q := fun _ => Kernel.const _ F
  f := fun _ _ => c
  g := fun _ w => wage w / (1 - β)
  h := fun _ => 0
  β := β

/-- **Exercise 5.1** (Miao, p. 155): accepting the wage `w` yields `∑ βᵗ w = w/(1 − β)`, the
stopping payoff `g` of `jobSearch`. -/
theorem ex_5_1_accept {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (w : ℝ) :
    HasSum (fun t : ℕ => β ^ t * w) (w / (1 - β)) := by
  convert (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right w using 1
  rw [div_eq_mul_inv, mul_comm]

/-- **Exercise 5.1** (Miao, p. 155): with offers in `[0, B]` (a measurable wage bounded by `B`),
`F` a probability measure and `β ∈ (0, 1)`, the job search MDP satisfies Assumptions 5.1.1,
5.1.2 and 5.1.4. -/
theorem ex_5_1 {W : Type*} [MeasurableSpace W] {F : Measure W} [IsProbabilityMeasure F]
    {wage : W → ℝ} (hw : Measurable wage) {B : ℝ} (hB : ∀ w, |wage w| ≤ B) {c β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    (jobSearch F wage c β).toMDP.IsMarkov ∧ HasMeasurableSelection (jobSearch F wage c β).toMDP.Γ ∧
      Assumption512 (jobSearch F wage c β).toMDP ∧ Assumption514 (jobSearch F wage c β).toMDP := by
  have hpos : 0 < 1 - β := by linarith
  have hb : (jobSearch F wage c β).Bounded (|c| + max B 0 / (1 - β)) := by
    refine ⟨by positivity, fun t z => ?_, fun t w => ?_, fun z => ?_⟩
    · simp only [jobSearch]
      linarith [div_nonneg (le_max_right B 0) hpos.le]
    · simp only [jobSearch, abs_div, abs_of_pos hpos]
      have : |wage w| / (1 - β) ≤ max B 0 / (1 - β) :=
        div_le_div_of_nonneg_right ((hB w).trans (le_max_left B 0)) hpos.le
      linarith [abs_nonneg c]
    · simp only [jobSearch, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (jobSearch F wage c β)
    (fun _ => inferInstanceAs (IsMarkovKernel (Kernel.const _ _))) (fun _ => measurable_const)
    (fun _ => hw.div_const _) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- The American put of **Exercise 5.2**: the stock price `p(z_t)` is driven by a Markov process
with transition function `Q`; exercising at `t < T` pays `K − p(z_t)`, holding pays nothing, and
at the expiry date `T` the holder exercises if the option is in the money, `h = max(K − p, 0)`;
`β = 1/(1 + r)`. -/
noncomputable def americanPut (Q : Kernel Z Z) (p : Z → ℝ) (K r : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ _ => 0
  g := fun _ z => K - p z
  h := fun z => max (K - p z) 0
  β := 1 / (1 + r)

/-- **Exercise 5.2** (Miao, p. 155): with a measurable bounded price, the American put's MDP has
stochastic kernels, satisfies Assumption 5.1.1, Assumption 5.1.2 when `r > 0`, and
Assumption 5.1.3 for every expiry date `T`; its value is that of the stopping problem
(`V0_toMDP`). -/
theorem ex_5_2 {Q : Kernel Z Z} [IsMarkovKernel Q] {p : Z → ℝ} (hp : Measurable p) {B : ℝ}
    (hB : ∀ z, |p z| ≤ B) {K r : ℝ} (hr : 0 < r) :
    (americanPut Q p K r).toMDP.IsMarkov ∧ HasMeasurableSelection (americanPut Q p K r).toMDP.Γ ∧
      Assumption512 (americanPut Q p K r).toMDP ∧
      ∀ T, Assumption513 (americanPut Q p K r).toMDP T := by
  have hb : (americanPut Q p K r).Bounded (|K| + max B 0) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · simp only [americanPut, abs_zero]
      positivity
    · calc |K - p z| ≤ |K| + |p z| := abs_sub _ _
        _ ≤ |K| + max B 0 := by linarith [hB z, le_max_left B 0]
    · simp only [americanPut]
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      linarith [le_abs_self K, neg_abs_le (p z), hB z, le_max_left B 0, abs_nonneg (p z)]
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (americanPut Q p K r) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => measurable_const) (fun _ => measurable_const.sub hp)
    ((measurable_const.sub hp).max measurable_const) hb
  exact ⟨h1, h2, americanCall_beta hr, h3⟩

/-- The three-point law of the relative rank of the `(t + 2)`-th candidate among the first
`t + 2`: best so far (`1`) and second best so far (`2`) each with probability `1/(t + 2)`, and
neither (`0`) with probability `t/(t + 2)`. -/
noncomputable def rank3 (t : ℕ) : Measure (Fin 3) :=
  ENNReal.ofReal (1 / (t + 2)) • Measure.dirac 1 + ENNReal.ofReal (1 / (t + 2)) •
    Measure.dirac 2 + ENNReal.ofReal (t / (t + 2)) • Measure.dirac 0

theorem isProbabilityMeasure_rank3 (t : ℕ) : IsProbabilityMeasure (rank3 t) := by
  refine ⟨?_⟩
  simp only [rank3, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 / ((t : ℝ) + 2) + 1 / (t + 2) + t / (t + 2) = 1 by field_simp; ring]
  simp

/-- The best-two secretary problem of **Exercise 5.3**, in shifted dates (date `t` is the
`k = t + 1`-th candidate). The state is the relative rank of the current candidate: `1` (best so
far), `2` (second best so far) or `0`. The first candidate has relative rank `1`; for `t ≥ 1` the
relative rank of the next candidate is `1` or `2` with probability `1/(t + 2)` each (`rank3`; at
`t = 0` the second candidate is best or second best with probability `1/2` each, which `rank3 0`
also gives). Stopping on a candidate of relative rank `1` among the first `k` wins with
probability `k/N + k(N − k)/(N(N − 1)) = k(2N − k − 1)/(N(N − 1))` (it is the best of all, or
the second best with the best among the later `N − k`), on one of relative rank `2` with
probability `k(k − 1)/(N(N − 1))`; at the last candidate (`k = N`) the probabilities are `1`.
(`min k N` keeps the payoffs bounded past the horizon.) -/
noncomputable def secretaryTwo (N : ℕ) : StoppingProblem (Fin 3) where
  Q := fun t => Kernel.const _ (rank3 t)
  f := fun _ _ => 0
  g := fun t z =>
    if z = 1 then ((min (t + 1) N : ℕ) : ℝ) * (2 * N - (min (t + 1) N : ℕ) - 1) / (N * (N - 1))
    else if z = 2 then ((min (t + 1) N : ℕ) : ℝ) * ((min (t + 1) N : ℕ) - 1) / (N * (N - 1))
    else 0
  h := fun z => if z = 0 then 0 else 1
  β := 1

/-- **Exercise 5.3** (Miao, p. 155): the best-two secretary problem is an optimal stopping
problem whose MDP has stochastic kernels and satisfies Assumption 5.1.1 and, for `N ≥ 2`,
Assumption 5.1.3 for every horizon (all payoffs lie in `[0, 1]`). -/
theorem ex_5_3 {N : ℕ} (hN : 2 ≤ N) :
    (secretaryTwo N).toMDP.IsMarkov ∧ HasMeasurableSelection (secretaryTwo N).toMDP.Γ ∧
      ∀ T, Assumption513 (secretaryTwo N).toMDP T := by
  have hQ : ∀ t, IsMarkovKernel ((secretaryTwo N).Q t) := fun t => by
    have := isProbabilityMeasure_rank3 t
    exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * (N - 1) := by nlinarith
  have hb : (secretaryTwo N).Bounded 1 := by
    refine ⟨zero_le_one, fun t z => by simp [secretaryTwo], fun t z => ?_, fun z => ?_⟩
    · set k : ℕ := min (t + 1) N with hk
      have hk1 : 1 ≤ k := le_min (by omega) (by omega)
      have hkN : k ≤ N := min_le_right _ _
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have hcase : (k : ℝ) = N ∨ (k : ℝ) + 1 ≤ N := by
        rcases Nat.lt_or_ge k N with h | h
        · exact Or.inr (by exact_mod_cast h)
        · exact Or.inl (by exact_mod_cast le_antisymm hkN h)
      simp only [secretaryTwo, ← hk]
      split_ifs
      · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
        rcases hcase with h | h
        · rw [h]
          linarith
        · nlinarith
      · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
        nlinarith
      · simp
    · simp only [secretaryTwo]
      split_ifs <;> simp
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (secretaryTwo N) hQ (fun _ => measurable_const)
    (fun _ => measurable_of_finite _) (measurable_of_finite _) hb
  exact ⟨h1, h2, h3⟩

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The probabilities of the secretary problem

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Secretary`),
with the namespace renamed.

Miao, pp. 148–149. `N` objects of distinct quality are observed in a uniformly random order: a
permutation `σ` of `Fin N`, `σ i` being the quality rank (`0` = best) of the object observed at
position `i` (the `(i + 1)`-th object). For the `k`-th object (`1 ≤ k ≤ N`, position `k − 1`):

* `bestOfFirst N k`: it is the best of the first `k` objects; `card_bestOfFirst`: this has
  probability `1/k` (so `Q_{t+1}(z, 1) = 1/(t + 1)`, p. 148, as a marginal probability);
* `bestOfAll N k`: it is the best of all; `card_bestOfAll`: probability `1/N`;
* `secretary_prob`: **Miao, p. 149**, `Pr(best of N | best of first k) = Pr(best of N) /
  Pr(best of first k) = (1/N)/(1/k) = k/N`.

Not formalised: that the indicators of "best so far" are independent (the Markov property of the
book's state process, with a transition function that does not depend on the current state); only
the marginal probabilities are proved.
-/

namespace Miao.FiniteHorizonDP

open Equiv

/-- An equal-size partition: if the `m` pieces of a partition of a finite type have the same
cardinality, each has `1/m` of the elements. -/
theorem card_mul_of_equal_partition {α : Type*} [Fintype α] {m : ℕ}
    (E : Fin m → Finset α) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hcov : ∀ x, ∃ i, x ∈ E i) (heq : ∀ i j, (E i).card = (E j).card) (i₀ : Fin m) :
    (E i₀).card * m = Fintype.card α := by
  classical
  have hu : (Finset.univ : Finset α) = Finset.univ.biUnion E := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_and, true_iff]
    exact hcov x
  rw [← Finset.card_univ, hu, Finset.card_biUnion fun i _ j _ hij => hdisj i j hij]
  rw [Finset.sum_congr rfl fun i _ => heq i i₀, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

/-- The `k`-th object is the best of the first `k` (position `p = k − 1`). -/
def bestOfFirst (N : ℕ) (p : Fin N) : Finset (Perm (Fin N)) :=
  Finset.univ.filter fun σ => ∀ j : Fin N, j.val ≤ p.val → σ p ≤ σ j

/-- The object at position `p` is the best of all `N`. -/
def bestOfAll (N : ℕ) (p : Fin N) : Finset (Perm (Fin N)) :=
  Finset.univ.filter fun σ => σ p = ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) p.2⟩

/-- Miao, p. 149: the object at position `p` is the best of all with probability `1/N`:
`#{σ : σ(p) = 0} · N = N!`. -/
theorem card_bestOfAll (N : ℕ) (p : Fin N) :
    (bestOfAll N p).card * N = Fintype.card (Perm (Fin N)) := by
  let E : Fin N → Finset (Perm (Fin N)) := fun v => Finset.univ.filter fun σ => σ p = v
  have h0 : bestOfAll N p = E ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) p.2⟩ := rfl
  rw [h0]
  refine card_mul_of_equal_partition E (fun v w hvw => ?_) (fun σ => ⟨σ p, by simp [E]⟩)
    (fun v w => ?_) _
  · refine Finset.disjoint_left.2 fun σ h1 h2 => hvw ?_
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [← h1, ← h2]
  · refine Finset.card_nbij' (fun σ => swap v w * σ) (fun σ => swap v w * σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      have hσ' : σ p = v := by simpa [E] using hσ
      simp [E, Perm.mul_apply, hσ']
    · intro σ hσ
      have hσ' : σ p = w := by simpa [E] using hσ
      simp [E, Perm.mul_apply, hσ']
    · intro σ _
      simp [← mul_assoc]
    · intro σ _
      simp [← mul_assoc]

theorem swap_val_le {N : ℕ} {a b j : Fin N} {p : ℕ} (ha : a.val ≤ p) (hb : b.val ≤ p)
    (hj : j.val ≤ p) : (swap a b j).val ≤ p := by
  rw [swap_apply_def]
  split_ifs <;> assumption

/-- Miao, p. 148: the object at position `p` (the `(p + 1)`-th) is the best of the first `p + 1`
with probability `1/(p + 1)`: `#{σ : σ(p) ≤ σ(j) for j ≤ p} · (p + 1) = N!`. -/
theorem card_bestOfFirst (N : ℕ) (p : Fin N) :
    (bestOfFirst N p).card * (p.val + 1) = Fintype.card (Perm (Fin N)) := by
  let ι : Fin (p.val + 1) → Fin N := fun i => ⟨i.val, by omega⟩
  have hι : ∀ i, (ι i).val ≤ p.val := fun i => Nat.lt_succ_iff.1 i.2
  let E : Fin (p.val + 1) → Finset (Perm (Fin N)) := fun i =>
    Finset.univ.filter fun σ => ∀ j : Fin N, j.val ≤ p.val → σ (ι i) ≤ σ j
  have h0 : bestOfFirst N p = E (Fin.last p.val) := by
    have : ι (Fin.last p.val) = p := Fin.ext rfl
    simp only [bestOfFirst, E, this]
  rw [h0]
  refine card_mul_of_equal_partition E (fun i i' hii' => ?_) (fun σ => ?_) (fun i i' => ?_) _
  · refine Finset.disjoint_left.2 fun σ h1 h2 => hii' ?_
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have := le_antisymm (h1 _ (hι i')) (h2 _ (hι i))
    have h' := congrArg Fin.val (σ.injective this)
    exact Fin.ext h'
  · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun j : Fin N =>
      j.val ≤ p.val) σ ⟨p, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
    refine ⟨⟨m.val, Nat.lt_succ_iff.2 hm⟩, ?_⟩
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j hj => hmin j hj
  · refine Finset.card_nbij' (fun σ => σ * swap (ι i) (ι i')) (fun σ => σ * swap (ι i) (ι i'))
      ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [E, Finset.coe_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro j hj
      simp only [Perm.mul_apply, swap_apply_right]
      exact hσ _ (swap_val_le (hι i) (hι i') hj)
    · intro σ hσ
      simp only [E, Finset.coe_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro j hj
      simp only [Perm.mul_apply, swap_apply_left]
      exact hσ _ (swap_val_le (hι i) (hι i') hj)
    · intro σ _
      simp [mul_assoc]
    · intro σ _
      simp [mul_assoc]

/-- The best of all is the best of the first `k`. -/
theorem bestOfAll_subset (N : ℕ) (p : Fin N) : bestOfAll N p ⊆ bestOfFirst N p := by
  intro σ hσ
  simp only [bestOfAll, bestOfFirst, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro j _
  rw [hσ, Fin.le_iff_val_le_val]
  exact Nat.zero_le _

/-- **Miao, p. 149.** For the `k`-th object (`k = p + 1`): `Pr(best of first k) = 1/k`,
`Pr(best of N) = 1/N`, and `Pr(best of N | best of first k) = Pr(best of N)/Pr(best of first k)
= k/N` (uniform probability on the `N!` orders). -/
theorem secretary_prob (N : ℕ) (p : Fin N) :
    ((bestOfFirst N p).card : ℝ) / Fintype.card (Perm (Fin N)) = 1 / (p.val + 1) ∧
      ((bestOfAll N p).card : ℝ) / Fintype.card (Perm (Fin N)) = 1 / N ∧
      ((bestOfAll N p ∩ bestOfFirst N p).card : ℝ) / (bestOfFirst N p).card =
        (p.val + 1) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  have hF : (0 : ℝ) < Fintype.card (Perm (Fin N)) := by exact_mod_cast Fintype.card_pos
  have hB := card_bestOfFirst N p
  have hA := card_bestOfAll N p
  have hB' : ((bestOfFirst N p).card : ℝ) * (p.val + 1) = Fintype.card (Perm (Fin N)) := by
    exact_mod_cast hB
  have hA' : ((bestOfAll N p).card : ℝ) * N = Fintype.card (Perm (Fin N)) := by
    exact_mod_cast hA
  have hBpos : (0 : ℝ) < (bestOfFirst N p).card := by
    have : 0 < (bestOfFirst N p).card := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hB
      exact (Fintype.card_pos (α := Perm (Fin N))).ne hB
    exact_mod_cast this
  have hApos : (0 : ℝ) < (bestOfAll N p).card := by
    have : 0 < (bestOfAll N p).card := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hA
      exact (Fintype.card_pos (α := Perm (Fin N))).ne hA
    exact_mod_cast this
  rw [Finset.inter_eq_left.2 (bestOfAll_subset N p)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hB']
    field_simp
  · rw [← hA']
    field_simp
  · rw [div_eq_div_iff hBpos.ne' hN.ne', hA', ← hB', mul_comm]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Problems from a later date, continuation plans and the first-date split

Tools for Miao, §6.3, pp. 163–165. Everything is stated for date `0` of a Markov decision
process `M`; the problem from date `t` is date `0` of the shifted process `po_shift M t`.

* `po_shift M t`: the process from date `t` on (`P j`, `u j` are `M`'s `P (j + t)`, `u (j + t)`);
  `po_shift_shift` composes shifts.
* `po_cont π s`: the continuation plan `C(π, s₁)` of a plan after the first state `s₁ = s`
  (Miao, p. 163); `po_cont_feasible`: it is feasible from `s₁` for the remaining horizon.
* `po_glue a ρ`: the plan that takes the action `a` now and follows the plan `ρ(s₁)` after `s₁`;
  `po_cont_glue`, `po_glue_feasible` (with `po_JointMeas`, joint measurability of the family
  `ρ` in the state and the history, which is what makes the glued plan a plan).
* The first-date split of the history measures: `po_mu_succ_lintegral`, the kernel
  `po_contKernel` (`s₁ ↦ μᵗ(s₁, ·; C(π, s₁))`), `po_mu_succ_eq`, `po_integral_mu_succ`,
  `po_integrable_cont`, `po_ae_mu_succ`.
* `po_IntPlan`: the rewards along a plan are integrable (what Assumption 5.1.3 gives).
  `po_J0T_succ`: the recursive form of the objective, which is Lemma 6.3.1 at date `0`, and
  `po_integrable_J0T_cont`, `po_ae_IntPlan_cont`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The Markov decision process from date `t` on: its date `j` is date `j + t` of `M`. -/
def po_shift (M : MDP S A) (t : ℕ) : MDP S A where
  Γ := M.Γ
  P := fun j => M.P (j + t)
  u := fun j => M.u (j + t)
  uT := M.uT
  β := M.β

theorem po_shift_zero (M : MDP S A) : po_shift M 0 = M := rfl

theorem po_shift_shift (M : MDP S A) (a b : ℕ) :
    po_shift (po_shift M a) b = po_shift M (a + b) := by
  have h : ∀ j, j + b + a = j + (a + b) := fun j => by omega
  simp only [po_shift, h]

theorem po_shift_isMarkov {M : MDP S A} (hP : M.IsMarkov) (t : ℕ) : (po_shift M t).IsMarkov :=
  fun j => hP (j + t)

/-- The continuation plan `C(π, s₁)` (Miao, p. 163): `C_{j}(sʲ; π, s₁) = π_{j+1}(s₁, sʲ)`. -/
def po_cont (π : Plan S A) (s : S) : Plan S A := fun j h => π (j + 1) (Fin.cons s h)

/-- Take the action `a` now, and follow the plan `ρ(s₁)` from the next state `s₁` on. -/
def po_glue (a : A) (ρ : S → Plan S A) : Plan S A
  | 0, _ => a
  | j + 1, h => ρ (h 0) j (Fin.tail h)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_cont_glue (a : A) (ρ : S → Plan S A) (s : S) : po_cont (po_glue a ρ) s = ρ s := by
  funext j h
  simp [po_cont, po_glue]

/-- A family of plans `s ↦ ρ(s)` is jointly measurable in the state and the history, at the
dates `j < n`. -/
def po_JointMeas (ρ : S → Plan S A) (n : ℕ) : Prop :=
  ∀ j < n, Measurable fun p : S × (Fin j → S) => ρ p.1 j p.2

theorem po_measurable_tail (j : ℕ) :
    Measurable (Fin.tail : (Fin (j + 1) → S) → Fin j → S) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem po_measurable_lastState_prod (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => lastState p.1 p.2 := by
  cases t with
  | zero => exact measurable_fst
  | succ t => exact (measurable_pi_apply _).comp measurable_snd

theorem po_cast_lt {j n : ℕ} : ((j : ℕ) : ℕ∞) < ((n : ℕ) : ℕ∞) ↔ j < n := Nat.cast_lt

/-- The continuation of a feasible plan is feasible for the remaining horizon (Miao, p. 163). -/
theorem po_cont_feasible {M : MDP S A} {n : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s) (s' : S) :
    po_cont π s' ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s' := by
  refine ⟨fun j hj => ?_, fun j hj h => ?_⟩
  · have hj' : ((j + 1 : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := po_cast_lt.2 (by
      have := po_cast_lt.1 hj; omega)
    exact (hπ.1 (j + 1) hj').comp ((measurable_cons j).comp
      (measurable_const.prodMk measurable_id))
  · have hj' : ((j + 1 : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := po_cast_lt.2 (by
      have := po_cast_lt.1 hj; omega)
    have := hπ.2 (j + 1) hj' (Fin.cons s' h)
    rwa [lastState_cons] at this

/-- The glued plan `(a, ρ)` is feasible when `a ∈ Γ(s)`, each `ρ(s₁)` is feasible from `s₁` and
the family is jointly measurable. -/
theorem po_glue_feasible {M : MDP S A} {n : ℕ} {s : S} {a : A} {ρ : S → Plan S A}
    (ha : a ∈ M.Γ s) (hρ : ∀ s', ρ s' ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s')
    (hm : po_JointMeas ρ n) : po_glue a ρ ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s := by
  refine ⟨fun j hj => ?_, fun j hj h => ?_⟩
  · cases j with
    | zero => exact measurable_const
    | succ j =>
      have hj' : j < n := by have := po_cast_lt.1 hj; omega
      exact (hm j hj').comp ((measurable_pi_apply 0).prodMk (po_measurable_tail j))
  · cases j with
    | zero => exact ha
    | succ j =>
      have hj' : ((j : ℕ) : ℕ∞) < ((n : ℕ) : ℕ∞) := po_cast_lt.2 (by
        have := po_cast_lt.1 hj; omega)
      have := (hρ (h 0)).2 j hj' (Fin.tail h)
      have hl : lastState s h = lastState (h 0) (Fin.tail h) := by
        conv_lhs => rw [← Fin.cons_self_tail h]
        exact lastState_cons s (h 0) (Fin.tail h)
      rw [hl]
      exact this

/-- The lower integral of a function of `(s₁, sᵗ)` along `μᵗ(s₁, ·; ρ(s₁))` is measurable in
`s₁` for a jointly measurable family of plans. -/
theorem po_measurable_lintegral_family {M : MDP S A} (hP : M.IsMarkov) {ρ : S → Plan S A}
    {n : ℕ} (hm : po_JointMeas ρ n) :
    ∀ t ≤ n, ∀ {F : S × (Fin t → S) → ℝ≥0∞}, Measurable F →
      Measurable fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) t := by
  intro t
  induction t with
  | zero =>
    intro _ F hF
    have : (fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) 0) = fun s => F (s, Fin.elim0) := by
      funext s
      rw [mu_zero, lintegral_dirac' _ Subsingleton.measurable]
    rw [this]
    exact hF.comp (measurable_id.prodMk measurable_const)
  | succ t ih =>
    intro ht F hF
    have hmt : Measurable fun p : S × (Fin t → S) => ρ p.1 t p.2 := hm t (by omega)
    set κ : Kernel (S × (Fin t → S)) S := (M.P t).comap
      (fun p : S × (Fin t → S) => (lastState p.1 p.2, ρ p.1 t p.2))
      ((po_measurable_lastState_prod t).prodMk hmt) with hκ
    have : IsMarkovKernel (M.P t) := hP t
    have hκM : IsMarkovKernel κ := by rw [hκ]; infer_instance
    have hG : Measurable fun p : S × (Fin t → S) =>
        ∫⁻ s'', F (p.1, Fin.snoc p.2 s'') ∂κ p := by
      refine Measurable.lintegral_kernel_prod_right' (κ := κ)
        (f := fun q : (S × (Fin t → S)) × S => F (q.1.1, Fin.snoc q.1.2 q.2)) ?_
      exact hF.comp (measurable_fst.fst.prodMk ((measurable_snoc t).comp
        (measurable_fst.snd.prodMk measurable_snd)))
    have heq : (fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) (t + 1)) =
        fun s => ∫⁻ h, ∫⁻ s'', F (s, Fin.snoc h s'') ∂κ (s, h) ∂mu M s (ρ s) t := by
      funext s
      have hρt : Measurable (ρ s t) := hmt.comp (measurable_const.prodMk measurable_id)
      rw [mu_succ_lintegral M hP s hρt (f := fun h => F (s, h))
        (hF.comp (measurable_const.prodMk measurable_id))]
      rfl
    rw [heq]
    exact ih (by omega) hG

/-- The first-date split of the history measures, for lower integrals:
`∫ f dμᵗ⁺¹(s, ·; π) = ∫ [∫ f(s₁, sᵗ) μᵗ(s₁, dsᵗ; C(π, s₁))] P₁(s, π₀; ds₁)`, where `μᵗ(s₁, ·; ·)`
is the measure of the process from date `1`. -/
theorem po_mu_succ_lintegral {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} :
    ∀ (t : ℕ), (∀ j ≤ t, Measurable (π j)) → ∀ {f : (Fin (t + 1) → S) → ℝ≥0∞}, Measurable f →
      ∫⁻ h, f h ∂mu M s π (t + 1) =
        ∫⁻ s', ∫⁻ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t
          ∂M.P 0 (s, π 0 Fin.elim0) := by
  intro t
  induction t with
  | zero =>
    intro hπ f hf
    rw [mu_succ_lintegral M hP s (hπ 0 le_rfl) hf, mu_zero,
      lintegral_dirac' _ Subsingleton.measurable]
    refine lintegral_congr fun s' => ?_
    rw [mu_zero, lintegral_dirac' _ Subsingleton.measurable]
    have : (Fin.snoc (Fin.elim0 : Fin 0 → S) s' : Fin 1 → S) = Fin.cons s' Fin.elim0 := by
      funext i
      fin_cases i
      rfl
    rw [this]
  | succ t ih =>
    intro hπ f hf
    have hπt : Measurable (π (t + 1)) := hπ (t + 1) le_rfl
    have := isSFiniteKernel_stepKernel M hP s π (t + 1)
    have hg : Measurable fun h : Fin (t + 1) → S =>
        ∫⁻ s'', f (Fin.snoc h s'') ∂M.P (t + 1) (lastState s h, π (t + 1) h) := by
      have h1 := (hf.comp (measurable_snoc (t + 1))).lintegral_kernel_prod_right'
        (κ := stepKernel M s π (t + 1))
      have h2 : (fun h : Fin (t + 1) → S =>
          ∫⁻ s'', f (Fin.snoc h s'') ∂M.P (t + 1) (lastState s h, π (t + 1) h)) =
          fun h => ∫⁻ s'', (f ∘ fun p : (Fin (t + 1) → S) × S => Fin.snoc p.1 p.2) (h, s'')
            ∂stepKernel M s π (t + 1) h := by
        funext h
        rw [stepKernel_apply M s hπt]
        rfl
      rw [h2]
      exact h1
    rw [mu_succ_lintegral M hP s hπt hf, ih (fun j hj => hπ j (by omega)) hg]
    refine lintegral_congr fun s' => ?_
    have hc : Measurable (po_cont π s' t) :=
      hπt.comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id))
    rw [mu_succ_lintegral (po_shift M 1) (po_shift_isMarkov hP 1) s' hc
      (f := fun h => f (Fin.cons s' h))
      (hf.comp ((measurable_cons (t + 1)).comp (measurable_const.prodMk measurable_id)))]
    refine lintegral_congr fun h' => ?_
    rw [lastState_cons]
    refine lintegral_congr fun s'' => ?_
    rw [Fin.cons_snoc_eq_snoc_cons]

open Classical in
/-- The kernel `s₁ ↦ μᵗ(s₁, ·; C(π, s₁))` of the history after the first state (the zero kernel
if the hypotheses fail, a case that never arises for plans of Markov processes). -/
noncomputable def po_contKernel (M : MDP S A) (π : Plan S A) (t : ℕ) :
    Kernel S (Fin t → S) :=
  if h : M.IsMarkov ∧ ∀ j ≤ t, Measurable (π j) then
    { toFun := fun s' => mu (po_shift M 1) s' (po_cont π s') t
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
        have hm : po_JointMeas (po_cont π) t := fun j hj =>
          (h.2 (j + 1) (by omega)).comp (measurable_cons j)
        have := po_measurable_lintegral_family (po_shift_isMarkov h.1 1) hm t le_rfl
          (F := fun p : S × (Fin t → S) => B.indicator 1 p.2)
          ((measurable_one.indicator hB).comp measurable_snd)
        have hfun : (fun s' => (mu (po_shift M 1) s' (po_cont π s') t) B) = fun s' =>
            ∫⁻ h, (fun p : S × (Fin t → S) => B.indicator 1 p.2) (s', h)
              ∂mu (po_shift M 1) s' (po_cont π s') t := by
          funext s'
          exact (lintegral_indicator_one hB).symm
        rw [hfun]
        exact this }
  else 0

theorem po_contKernel_apply {M : MDP S A} (hP : M.IsMarkov) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) (s' : S) :
    po_contKernel M π t s' = mu (po_shift M 1) s' (po_cont π s') t := by
  unfold po_contKernel
  split_ifs with h
  · rfl
  · exact absurd ⟨hP, hπ⟩ h

theorem po_isMarkovKernel_contKernel {M : MDP S A} (hP : M.IsMarkov) {π : Plan S A}
    {t : ℕ} (hπ : ∀ j ≤ t, Measurable (π j)) : IsMarkovKernel (po_contKernel M π t) := by
  refine ⟨fun s' => ?_⟩
  rw [po_contKernel_apply hP hπ]
  exact isProbabilityMeasure_mu (po_shift M 1) (po_shift_isMarkov hP 1) s'
    fun j hj => (hπ (j + 1) (by omega)).comp
      ((measurable_cons j).comp (measurable_const.prodMk measurable_id))

/-- The first-date split as an identity of measures: `μᵗ⁺¹(s, ·; π)` is the image under
`(s₁, sᵗ) ↦ (s₁, sᵗ)` of `P₁(s, π₀; ·) ⊗ μᵗ(s₁, ·; C(π, s₁))`. -/
theorem po_mu_succ_eq {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) :
    mu M s π (t + 1) = ((M.P 0 (s, π 0 Fin.elim0)) ⊗ₘ po_contKernel M π t).map
      fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → S) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [po_mu_succ_lintegral hP s t hπ hf, lintegral_map hf (measurable_cons t),
    Measure.lintegral_compProd (f := fun p : S × (Fin t → S) => f (Fin.cons p.1 p.2))
      (hf.comp (measurable_cons t))]
  refine lintegral_congr fun s' => ?_
  rw [po_contKernel_apply hP hπ]

/-- The first-date split for integrable functions:
`∫ f dμᵗ⁺¹(s, ·; π) = ∫ [∫ f(s₁, sᵗ) μᵗ(s₁, dsᵗ; C(π, s₁))] P₁(s, π₀; ds₁)`. -/
theorem po_integral_mu_succ {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s π (t + 1))) :
    ∫ h, f h ∂mu M s π (t + 1) =
      ∫ s', ∫ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t
        ∂M.P 0 (s, π 0 Fin.elim0) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ] at hf ⊢
  have hf' := (integrable_map_measure hf.1 (measurable_cons t).aemeasurable).1 hf
  rw [integral_map (measurable_cons t).aemeasurable hf.1,
    Measure.integral_compProd (f := fun p : S × (Fin t → S) => f (Fin.cons p.1 p.2)) hf']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s' => ?_)
  simp only [po_contKernel_apply hP hπ]

/-- For an integrable `f`, the inner integral of the first-date split is integrable in `s₁`,
and `f(s₁, ·)` is integrable for almost every `s₁`. -/
theorem po_integrable_cont {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s π (t + 1))) :
    Integrable (fun s' => ∫ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t)
      (M.P 0 (s, π 0 Fin.elim0)) ∧
    ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
      Integrable (fun h => f (Fin.cons s' h)) (mu (po_shift M 1) s' (po_cont π s') t) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ] at hf
  have hf' := (integrable_map_measure hf.1 (measurable_cons t).aemeasurable).1 hf
  have h1 := MeasureTheory.Integrable.integral_compProd
    (κ := Kernel.const Unit (M.P 0 (s, π 0 Fin.elim0)))
    (η := Kernel.prodMkLeft Unit (po_contKernel M π t)) (a := ()) hf'
  have h2 := ((Measure.integrable_compProd_iff hf'.1).1 hf').1
  refine ⟨?_, ?_⟩
  · refine h1.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [Kernel.prodMkLeft_apply, po_contKernel_apply hP hπ, Function.comp_apply]
  · filter_upwards [h2] with s' hs'
    rw [po_contKernel_apply hP hπ] at hs'
    exact hs'

/-- The first-date split for almost-everywhere statements: if `p` holds for almost every
continuation history after almost every first state, it holds `μᵗ⁺¹`-almost everywhere. -/
theorem po_ae_mu_succ {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {p : (Fin (t + 1) → S) → Prop}
    (hp : MeasurableSet {h | p h})
    (h : ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
      ∀ᵐ h ∂mu (po_shift M 1) s' (po_cont π s') t, p (Fin.cons s' h)) :
    ∀ᵐ h ∂mu M s π (t + 1), p h := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ, ae_map_iff (measurable_cons t).aemeasurable hp]
  refine Measure.ae_compProd_of_ae_ae ((measurable_cons t) hp) ?_
  filter_upwards [h] with s' hs'
  rw [po_contKernel_apply hP hπ]
  exact hs'

/-- The rewards along `π` from `s` are integrable over the horizon `n` (the integrability that
Assumption 5.1.3 grants to every feasible plan). -/
def po_IntPlan (M : MDP S A) (n : ℕ) (s : S) (π : Plan S A) : Prop :=
  (∀ j < n, Integrable (rew M s π j) (mu M s π j)) ∧
    Integrable (fun h => M.uT (lastState s h)) (mu M s π n)

theorem po_intPlan_of_assumption513 {M : MDP S A} {n : ℕ} (h : Assumption513 M n) {s : S}
    {π : Plan S A} (hπ : π ∈ feasiblePlans M (n : ℕ∞) s) : po_IntPlan M n s π :=
  h.2.2 s π hπ

theorem po_rew_cons (M : MDP S A) (s s' : S) (π : Plan S A) (j : ℕ) (h : Fin j → S) :
    rew M s π (j + 1) (Fin.cons s' h) = rew (po_shift M 1) s' (po_cont π s') j h := by
  simp only [rew, lastState_cons]
  rfl

theorem po_plan_meas {M : MDP S A} {n : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s) : ∀ j ≤ n, Measurable (π j) :=
  fun j hj => hπ.1 j (po_cast_lt.2 (by omega))

/-- The objective of the continuation plans, `s₁ ↦ J(s₁, C(π, s₁))`, is integrable against
`P₁(s, π₀; ·)`. -/
theorem po_integrable_J0T_cont {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S}
    {π : Plan S A} (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    Integrable (fun s' => J0T (po_shift M 1) n s' (po_cont π s')) (M.P 0 (s, π 0 Fin.elim0)) := by
  unfold J0T
  refine Integrable.add (integrable_finsetSum _ fun j hj => ?_) ?_
  · refine Integrable.const_mul ?_ _
    have hj : j < n := Finset.mem_range.1 hj
    have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [expRew, po_rew_cons]
  · refine Integrable.const_mul ?_ _
    have := (po_integrable_cont hP s hπ hI.2).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [lastState_cons]
    rfl

/-- For almost every first state `s₁`, the rewards along the continuation plan `C(π, s₁)` are
integrable. -/
theorem po_ae_IntPlan_cont {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S}
    {π : Plan S A} (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0), po_IntPlan (po_shift M 1) n s' (po_cont π s') := by
  have h1 : ∀ j, ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0), j < n →
      Integrable (rew (po_shift M 1) s' (po_cont π s') j)
        (mu (po_shift M 1) s' (po_cont π s') j) := by
    intro j
    by_cases hj : j < n
    · have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).2
      filter_upwards [this] with s' hs' _
      refine hs'.congr (Filter.Eventually.of_forall fun h => ?_)
      exact po_rew_cons M s s' π j h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  have h2 := (po_integrable_cont hP s hπ hI.2).2
  filter_upwards [ae_all_iff.2 h1, h2] with s' hs1 hs2
  refine ⟨fun j hj => hs1 j hj, ?_⟩
  refine hs2.congr (Filter.Eventually.of_forall fun h => ?_)
  simp only [lastState_cons]
  rfl

/-- **The recursive form of the objective** (Miao, Lemma 6.3.1 at date `0`, p. 165):
`J₀ⁿ⁺¹(s, π) = u₀(s, π₀) + β ∫ J₁ⁿ⁺¹(s₁, C(π, s₁)) P₁(s, π₀; ds₁)`, where the objective of the
continuation is that of the process from date `1` over the remaining horizon `n`. -/
theorem po_J0T_succ {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S} {π : Plan S A}
    (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    J0T M (n + 1) s π = M.u 0 (s, π 0 Fin.elim0) +
      M.β * ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) := by
  have hR : ∀ j < n, Integrable (fun s' => expRew (po_shift M 1) s' (po_cont π s') j)
      (M.P 0 (s, π 0 Fin.elim0)) := fun j hj => by
    have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [expRew, po_rew_cons]
  have hR' : ∀ j < n, expRew M s π (j + 1) =
      ∫ s', expRew (po_shift M 1) s' (po_cont π s') j ∂M.P 0 (s, π 0 Fin.elim0) := fun j hj => by
    rw [expRew, po_integral_mu_succ hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))]
    simp only [expRew, po_rew_cons]
  have hTi := (po_integrable_cont hP s hπ hI.2).1
  have hT : ∫ h, M.uT (lastState s h) ∂mu M s π (n + 1) =
      ∫ s', ∫ h, (po_shift M 1).uT (lastState s' h) ∂mu (po_shift M 1) s' (po_cont π s') n
        ∂M.P 0 (s, π 0 Fin.elim0) := by
    rw [po_integral_mu_succ hP s hπ hI.2]
    simp only [lastState_cons]
    rfl
  have hTi' : Integrable (fun s' => ∫ h, (po_shift M 1).uT (lastState s' h)
      ∂mu (po_shift M 1) s' (po_cont π s') n) (M.P 0 (s, π 0 Fin.elim0)) := by
    refine hTi.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [lastState_cons]
    rfl
  unfold J0T
  rw [integral_add (integrable_finsetSum _ fun j hj => (hR j (Finset.mem_range.1 hj)).const_mul _)
    (hTi'.const_mul _), integral_finsetSum _ fun j hj => (hR j (Finset.mem_range.1 hj)).const_mul _,
    integral_const_mul, Finset.sum_range_succ', hT, expRew_zero]
  simp only [integral_const_mul, mul_add, Finset.mul_sum]
  have hs : ∀ j ∈ Finset.range n, M.β ^ (j + 1) * expRew M s π (j + 1) =
      M.β * (M.β ^ j * ∫ s', expRew (po_shift M 1) s' (po_cont π s') j
        ∂M.P 0 (s, π 0 Fin.elim0)) := fun j hj => by
    rw [hR' j (Finset.mem_range.1 hj), pow_succ]
    ring
  rw [Finset.sum_congr rfl hs]
  have : (po_shift M 1).β = M.β := rfl
  simp only [this, pow_zero, one_mul, pow_succ]
  ring

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The principle of optimality: the sequence problem from a history and the Bellman equation

Miao, §6.3, pp. 163–167, in the Markov decision process model (5.1) of Chapter 5 with horizon
`T < ∞`. A history `sᵗ = (s₀, …, s_t)` is a function `Fin (t + 1) → S`.

* Plans from a history (p. 163): a plan from `sᵗ` is a feasible plan of the process from date
  `t` started at `s_t` (`po_plansFrom`): `π_t ∈ Γ(s_t)` and measurable `π_{t+j} : Sʲ → A` with
  `π_{t+j}(s_{t+1}, …, s_{t+j}) ∈ Γ(s_{t+j})`. Continuation plans `C(π, s_{t+1})` are
  `po_cont`, and they are plans from `s^{t+1}` (`po_cont_mem_plansFrom`).
* The measures (6.12) (`po_muFrom`, `eq_6_12`), the objective (6.13) (`po_JFrom`, `eq_6_13`,
  `eq_6_13_terminal`) and the sequence problem (6.14) (`po_VFrom`, `eq_6_14`,
  `po_VFrom_terminal`, `po_VFrom_zero`: the original problem (5.5) is the case `t = 0`).
* **Lemma 6.3.1** (`lemma_6_3_1`): `J_t(sᵗ, π) = u_t(s_t, π_t) + β ∫ J_{t+1}(s^{t+1}, C(π,
  s_{t+1})) P_{t+1}(s_t, π_t; ds_{t+1})`.
* **Assumption 6.3.1** (`Assumption631`) and **Theorem 6.3.1** (`theorem_6_3_1`): the value
  functions satisfy the Bellman equation (6.17), `V_T = u_T`, and `V_t(sᵗ)` depends on `sᵗ`
  only through `s_t`. The Bellman step at one date is `po_bellman_step`.

**Departures from the book.**
1. *Integrability.* The book's Assumption 5.1.3 is stated for the problem from date `0`, but the
   proofs of §6.3 use it for the problems from every date `t` (the plans from `sᵗ` are not plans
   from `s₀`). `po_Assumption513` asks for it at every date. With bounded measurable rewards it
   holds (`po_assumption513_of_bounded`).
2. *Assumption 6.3.1(b).* The book asks the ε-optimal plans `π^{sᵗ}` to be measurable in `sᵗ`
   for each fixed future history `s^{t+j}_{t+1}`, i.e. *separately* measurable. The proof
   glues them into one plan from `s^{t−1}` whose date-`t + j` decision is
   `(s_t, s^{t+j}_{t+1}) ↦ π^{sᵗ}_{t+j}(s^{t+j}_{t+1})`, and Definition 5.1.1 requires that map to
   be measurable on `S^{j+1}`, which separate measurability does not give. `Assumption631` asks
   for *joint* measurability (`po_JointMeas`). The ε-plans are indexed by the current state
   `s_t` rather than the history (by Lemma 6.3.1 and the Markov structure only `s_t` matters).
3. *The integrals in (6.17).* The book takes `∫ V_{t+1} dP_{t+1}(s_t, a_t; ·)` for granted; under
   Assumption 6.3.1 it exists for every `a_t ∈ Γ(s_t)` (part of `theorem_6_3_1`), because
   `J_{t+1}(·, π^{s^{t+1}}) ≤ V_{t+1} ≤ J_{t+1}(·, π^{s^{t+1}}) + ε` with an integrable lower
   bound.
4. *Discounting.* Only `β ≥ 0` is used (Assumption 5.1.2's `β < 1` is not needed for `T < ∞`).
5. *The Markov property* holds by construction: (6.12)–(6.13) involve `sᵗ` only through `s_t`,
   so the book's induction is not needed.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `Π(sᵗ)`, the feasible plans from the history `sᵗ = (s₀, …, s_t)` (Miao, p. 163): feasible
plans of the process from date `t`, started at `s_t`, over the remaining horizon `T − t`. -/
def po_plansFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) : Set (Plan S A) :=
  feasiblePlans (po_shift M t) ((T - t : ℕ) : ℕ∞) (h (Fin.last t))

/-- `μ_t^{t+j}(sᵗ, ·; π)`, the measure on `Sʲ` of the history `(s_{t+1}, …, s_{t+j})` given the
history `sᵗ` and a plan `π` from `sᵗ` (Miao (6.12), p. 163). -/
noncomputable def po_muFrom (M : MDP S A) (t : ℕ) (h : Fin (t + 1) → S) (π : Plan S A)
    (j : ℕ) : Measure (Fin j → S) :=
  mu (po_shift M t) (h (Fin.last t)) π j

/-- **Miao (6.12)**, p. 163, in recursive form on measurable rectangles:
`μ_t^{t+j+1}(sᵗ, B₁ × ⋯ × B_{j+1}; π) =
∫_{B₁×⋯×B_j} P_{t+j+1}(s_{t+j}, π_{t+j}; B_{j+1}) dμ_t^{t+j}`.
Iterating gives the nested integral printed in (6.12). -/
theorem eq_6_12 {M : MDP S A} (hP : M.IsMarkov) (t : ℕ) (h : Fin (t + 1) → S) {π : Plan S A}
    {j : ℕ} (hπ : Measurable (π j)) {B : Fin (j + 1) → Set S} (hB : ∀ i, MeasurableSet (B i)) :
    po_muFrom M t h π (j + 1) (Set.pi Set.univ B) =
      ∫⁻ h' in Set.pi Set.univ (Fin.init B),
        M.P (j + t) (lastState (h (Fin.last t)) h', π j h') (B (Fin.last j))
        ∂po_muFrom M t h π j :=
  eq_5_2 (po_shift M t) (po_shift_isMarkov hP t) _ hπ hB

/-- `J_t^T(sᵗ, π)`, the discounted expected rewards of a plan `π` from the history `sᵗ`
(Miao (6.13), p. 164). -/
noncomputable def po_JFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) (π : Plan S A) : ℝ :=
  J0T (po_shift M t) (T - t) (h (Fin.last t)) π

/-- **Miao (6.13)**, p. 164: for `t < T`, `J_t^T(sᵗ, π) = u_t(s_t, π_t) +
∑_{j=1}^{T−t−1} βʲ ∫ u_{t+j}(s_{t+j}, π_{t+j}) dμ_t^{t+j} + β^{T−t} ∫ u_T(s_T) dμ_t^T`. -/
theorem eq_6_13 (M : MDP S A) {T t : ℕ} (ht : t < T) (h : Fin (t + 1) → S) (π : Plan S A) :
    po_JFrom M T t h π = M.u t (h (Fin.last t), π 0 Fin.elim0) +
      ∑ j ∈ Finset.Ico 1 (T - t), M.β ^ j *
        ∫ h', M.u (j + t) (lastState (h (Fin.last t)) h', π j h') ∂po_muFrom M t h π j +
      M.β ^ (T - t) * ∫ h', M.uT (lastState (h (Fin.last t)) h') ∂po_muFrom M t h π (T - t) := by
  rw [po_JFrom, eq_5_3 (po_shift M t) (by omega)]
  have e : (po_shift M t).u 0 = M.u t := by simp only [po_shift, zero_add]
  rw [e]
  rfl

theorem po_J0T_zero (M : MDP S A) (s : S) (π : Plan S A) : J0T M 0 s π = M.uT s := by
  rw [J0T, Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, integral_mu_zero, zero_add]
  rfl

/-- Miao, p. 164: at the terminal date `J_T^T(s^T) = u_T(s_T)`. -/
theorem eq_6_13_terminal (M : MDP S A) (T : ℕ) (h : Fin (T + 1) → S) (π : Plan S A) :
    po_JFrom M T T h π = M.uT (h (Fin.last T)) := by
  rw [po_JFrom, Nat.sub_self, po_J0T_zero]
  rfl

/-- `V_t(sᵗ) = sup_{π ∈ Π(sᵗ)} J_t^T(sᵗ, π)`, the value of the sequence problem from `sᵗ`
(Miao (6.14), p. 164), in `[−∞, +∞]`. -/
noncomputable def po_VFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) : EReal :=
  ⨆ π ∈ po_plansFrom M T t h, (po_JFrom M T t h π : EReal)

/-- **Miao (6.14)**, p. 164: the value from `sᵗ` is the value (5.5) of the process from date `t`
started at `s_t`. -/
theorem eq_6_14 (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) :
    po_VFrom M T t h = V0 (po_shift M t) (T - t) (h (Fin.last t)) := rfl

/-- Miao, p. 164: the original problem (5.5) is the case `t = 0` of (6.14). -/
theorem po_VFrom_zero (M : MDP S A) (T : ℕ) (s₀ : S) :
    po_VFrom M T 0 (fun _ => s₀) = V0 M T s₀ := by
  rw [eq_6_14, Nat.sub_zero]
  rfl

theorem po_feasible_zero (M : MDP S A) (s : S) (π : Plan S A) :
    π ∈ feasiblePlans M ((0 : ℕ) : ℕ∞) s :=
  ⟨fun _ ht => absurd (po_cast_lt.1 ht) (Nat.not_lt_zero _),
    fun _ ht => absurd (po_cast_lt.1 ht) (Nat.not_lt_zero _)⟩

theorem po_V0_zero [Nonempty A] (M : MDP S A) (s : S) : V0 M 0 s = M.uT s := by
  refine le_antisymm (iSup₂_le fun π _ => by rw [po_J0T_zero]) ?_
  refine le_iSup₂_of_le (f := fun π (_ : π ∈ feasiblePlans M ((0 : ℕ) : ℕ∞) s) =>
    (J0T M 0 s π : EReal)) (fun _ _ => Classical.arbitrary A) (po_feasible_zero M s _) ?_
  rw [po_J0T_zero]

/-- Miao, p. 164: `V_T(s^T) = u_T(s_T)` (there is no decision at the terminal date). -/
theorem po_VFrom_terminal [Nonempty A] (M : MDP S A) (T : ℕ) (h : Fin (T + 1) → S) :
    po_VFrom M T T h = M.uT (h (Fin.last T)) := by
  rw [eq_6_14, Nat.sub_self, po_V0_zero]
  rfl

/-- Miao, p. 163: the continuation `C(π, s_{t+1})` of a plan from `sᵗ` is a plan from
`s^{t+1} = (sᵗ, s_{t+1})`. -/
theorem po_cont_mem_plansFrom {M : MDP S A} {T t : ℕ} (ht : t < T) {h : Fin (t + 1) → S}
    {π : Plan S A} (hπ : π ∈ po_plansFrom M T t h) (s' : S) :
    po_cont π s' ∈ po_plansFrom M T (t + 1) (Fin.snoc h s') := by
  have hn : T - t = (T - (t + 1)) + 1 := by omega
  unfold po_plansFrom at hπ ⊢
  rw [hn] at hπ
  rw [Fin.snoc_last, ← po_shift_shift]
  exact po_cont_feasible hπ s'

theorem po_J_le_V0 {M : MDP S A} {T : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M (T : ℕ∞) s) : (J0T M T s π : EReal) ≤ V0 M T s :=
  le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M (T : ℕ∞) s) => (J0T M T s π : EReal)) π hπ

theorem po_coe_le_of_forall_sub {x : ℝ} {y : EReal}
    (h : ∀ δ : ℝ, 0 < δ → ((x - δ : ℝ) : EReal) ≤ y) : (x : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 (h 1 one_pos)) (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe r =>
    refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun δ hδ => ?_)
    have := EReal.coe_le_coe_iff.1 (h δ hδ)
    linarith

/-- **Assumption 5.1.3 at every date** (used throughout §6.3): the problem from each date
`t ≤ T` satisfies Assumption 5.1.3 over the remaining horizon. -/
def po_Assumption513 (M : MDP S A) (T : ℕ) : Prop :=
  ∀ t ≤ T, Assumption513 (po_shift M t) (T - t)

/-- With stochastic kernels, bounded measurable rewards satisfy Assumption 5.1.3 at every
date. -/
theorem po_assumption513_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : BoundedRewards M B) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT) (T : ℕ) :
    po_Assumption513 M T := fun t _ =>
  assumption_5_1_3_of_bounded (po_shift_isMarkov hP t) ⟨fun j x => hB.1 (j + t) x, hB.2⟩
    (fun j => hu (j + t)) huT (T - t)

theorem po_shift_u0 (M : MDP S A) (t : ℕ) : (po_shift M t).u 0 = M.u t := by
  simp only [po_shift, zero_add]

theorem po_shift_P0 (M : MDP S A) (t : ℕ) : (po_shift M t).P 0 = M.P t := by
  simp only [po_shift, zero_add]

/-- **Lemma 6.3.1** (Miao, p. 165). For a feasible plan `π` from `sᵗ`, `t < T`, under
Assumption 5.1.3 for the problem from date `t`:
`J_t^T(sᵗ, π) = u_t(s_t, π_t) +
β ∫ J_{t+1}^T(s^{t+1}, C(π, s_{t+1})) P_{t+1}(s_t, π_t; ds_{t+1})`. -/
theorem lemma_6_3_1 {M : MDP S A} (hP : M.IsMarkov) {T t : ℕ} (ht : t < T)
    (hI : Assumption513 (po_shift M t) (T - t)) {h : Fin (t + 1) → S} {π : Plan S A}
    (hπ : π ∈ po_plansFrom M T t h) :
    po_JFrom M T t h π = M.u t (h (Fin.last t), π 0 Fin.elim0) +
      M.β * ∫ s', po_JFrom M T (t + 1) (Fin.snoc h s') (po_cont π s')
        ∂M.P t (h (Fin.last t), π 0 Fin.elim0) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  unfold po_JFrom
  simp only [Fin.snoc_last, hn']
  unfold po_plansFrom at hπ
  rw [hn] at hπ hI
  rw [← po_shift_shift, hn, po_J0T_succ (po_shift_isMarkov hP t) (po_plan_meas hπ)
    (po_intPlan_of_assumption513 hI hπ), po_shift_u0, po_shift_P0]
  rfl

/-- **Assumption 6.3.1** (Miao, p. 164), with `w t` the value function at date `t` as a function
of the current state. For `t = 1, …, T − 1`: (a) `V_t` is real-valued, `V_t(sᵗ) = w_t(s_t)`, and
`w_t` is measurable; (b) for every `ε > 0` there is a family of plans `π^{s_t}` from the states
`s_t`, ε-optimal (6.15) and jointly measurable in the state and the history (see the module
docstring for this correction of the book's measurability requirement). -/
def Assumption631 (M : MDP S A) (T : ℕ) (w : ℕ → S → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t < T → Measurable (w t) ∧
    (∀ h : Fin (t + 1) → S, po_VFrom M T t h = w t (h (Fin.last t))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M t) ((T - t : ℕ) : ℕ∞) s) ∧
      (∀ s, w t s ≤ J0T (po_shift M t) (T - t) s (ρ s) + ε) ∧ po_JointMeas ρ (T - t)

/-- **The Bellman step** behind Theorem 6.3.1, at date `0` of a process `M` with horizon `n + 1`:
if the value of the problem from date `1` is a measurable real function `w'` with jointly
measurable ε-optimal plans, then `w'` is integrable against `P₁(s, a; ·)` for `a ∈ Γ(s)` and
`V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a) + β ∫ w' dP₁(s, a; ·)`. -/
theorem po_bellman_step {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 ≤ M.β) {n : ℕ}
    (hI : Assumption513 M (n + 1)) {w' : S → ℝ} (hwm : Measurable w')
    (hwV : ∀ s, V0 (po_shift M 1) n s = w' s)
    (hρ : ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s) ∧
      (∀ s, w' s ≤ J0T (po_shift M 1) n s (ρ s) + ε) ∧ po_JointMeas ρ n) (s : S) :
    (∀ a ∈ M.Γ s, Integrable w' (M.P 0 (s, a))) ∧
      V0 M (n + 1) s =
        ⨆ a ∈ M.Γ s, ((M.u 0 (s, a) + M.β * ∫ s', w' s' ∂M.P 0 (s, a) : ℝ) : EReal) := by
  have hJle : ∀ s' σ, σ ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s' →
      J0T (po_shift M 1) n s' σ ≤ w' s' := by
    intro s' σ hσ
    have := po_J_le_V0 hσ
    rw [hwV] at this
    exact EReal.coe_le_coe_iff.1 this
  have hglue : ∀ a ∈ M.Γ s, ∀ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s) → po_JointMeas ρ n →
      po_glue a ρ ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s ∧
      Integrable (fun s' => J0T (po_shift M 1) n s' (ρ s')) (M.P 0 (s, a)) ∧
      J0T M (n + 1) s (po_glue a ρ) = M.u 0 (s, a) +
        M.β * ∫ s', J0T (po_shift M 1) n s' (ρ s') ∂M.P 0 (s, a) := by
    intro a ha ρ hρF hρm
    have hπ := po_glue_feasible ha hρF hρm
    have hJi := po_integrable_J0T_cont hP (po_plan_meas hπ) (po_intPlan_of_assumption513 hI hπ)
    have hJ := po_J0T_succ hP (po_plan_meas hπ) (po_intPlan_of_assumption513 hI hπ)
    simp only [po_cont_glue] at hJi hJ
    exact ⟨hπ, hJi, hJ⟩
  have hint : ∀ a ∈ M.Γ s, Integrable w' (M.P 0 (s, a)) := by
    intro a ha
    obtain ⟨ρ, hρF, hρε, hρm⟩ := hρ 1 one_pos
    obtain ⟨-, hJi, -⟩ := hglue a ha ρ hρF hρm
    have : IsMarkovKernel (M.P 0) := hP 0
    refine Integrable.mono' (hJi.abs.add (integrable_const 1)) hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' => ?_)
    have h1 := hJle s' (ρ s') (hρF s')
    have h2 := hρε s'
    change ‖w' s'‖ ≤ |J0T (po_shift M 1) n s' (ρ s')| + 1
    rw [Real.norm_eq_abs]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (J0T (po_shift M 1) n s' (ρ s'))]
    · linarith [le_abs_self (J0T (po_shift M 1) n s' (ρ s'))]
  refine ⟨hint, le_antisymm ?_ ?_⟩
  · refine iSup₂_le fun π hπ => ?_
    have hπm := po_plan_meas hπ
    have hIπ := po_intPlan_of_assumption513 hI hπ
    have ha : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 (po_cast_lt.2 (Nat.succ_pos n)) Fin.elim0
    rw [po_J0T_succ hP hπm hIπ]
    refine le_trans ?_ (le_iSup₂_of_le (π 0 Fin.elim0) ha le_rfl)
    refine EReal.coe_le_coe_iff.2 (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_mono (po_integrable_J0T_cont hP hπm hIπ) (hint _ ha)
        fun s' => hJle s' _ (po_cont_feasible hπ s')) hβ))
  · refine iSup₂_le fun a ha => po_coe_le_of_forall_sub fun δ hδ => ?_
    have hβ1 : 0 < M.β + 1 := by linarith
    have hε : 0 < δ / (M.β + 1) := div_pos hδ hβ1
    obtain ⟨ρ, hρF, hρε, hρm⟩ := hρ _ hε
    obtain ⟨hπ, hJi, hJ⟩ := hglue a ha ρ hρF hρm
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (po_J_le_V0 hπ)
    rw [hJ]
    have : IsMarkovKernel (M.P 0) := hP 0
    have h1 : ∫ s', (w' s' - δ / (M.β + 1)) ∂M.P 0 (s, a) ≤
        ∫ s', J0T (po_shift M 1) n s' (ρ s') ∂M.P 0 (s, a) :=
      integral_mono ((hint a ha).sub (integrable_const _)) hJi fun s' => by
        linarith [hρε s']
    rw [integral_sub (hint a ha) (integrable_const _)] at h1
    have hc : ∫ _, δ / (M.β + 1) ∂M.P 0 (s, a) = δ / (M.β + 1) := by simp
    rw [hc] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hβ
    have h3 : M.β * (δ / (M.β + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hβ1]
      nlinarith
    nlinarith

/-- **Theorem 6.3.1** (Miao, p. 166), the dynamic programming principle. Under Assumption 5.1.3
at every date, `β ≥ 0` and Assumption 6.3.1 (with `w_t` the value at date `t`, `w_T = u_T`),
for `t < T` and every history `sᵗ`: `V_{t+1}` is integrable against `P_{t+1}(s_t, a; ·)` for
`a ∈ Γ(s_t)`, and the Bellman equation (6.17) holds,
`V_t(sᵗ) = sup_{a ∈ Γ(s_t)} u_t(s_t, a) + β ∫ V_{t+1}(s^{t+1}) P_{t+1}(s_t, a; ds_{t+1})`;
moreover `V_T(s^T) = u_T(s_T)` and `V_t` is Markovian: `V_t(sᵗ)` depends on `sᵗ` only through
`s_t`. -/
theorem theorem_6_3_1 [Nonempty A] {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 ≤ M.β) {T : ℕ}
    (hI : po_Assumption513 M T) {w : ℕ → S → ℝ} (hA : Assumption631 M T w)
    (hwT : w T = M.uT) :
    (∀ t < T, ∀ h : Fin (t + 1) → S,
      (∀ a ∈ M.Γ (h (Fin.last t)), Integrable (w (t + 1)) (M.P t (h (Fin.last t), a))) ∧
      po_VFrom M T t h = ⨆ a ∈ M.Γ (h (Fin.last t)),
        ((M.u t (h (Fin.last t), a) +
          M.β * ∫ s', w (t + 1) s' ∂M.P t (h (Fin.last t), a) : ℝ) : EReal)) ∧
    (∀ h : Fin (T + 1) → S, po_VFrom M T T h = M.uT (h (Fin.last T))) ∧
    (∀ t, ∀ h h' : Fin (t + 1) → S, h (Fin.last t) = h' (Fin.last t) →
      po_VFrom M T t h = po_VFrom M T t h') := by
  refine ⟨fun t ht h => ?_, fun h => po_VFrom_terminal M T h, fun t h h' hh => by
    rw [eq_6_14, eq_6_14, hh]⟩
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hIt := hI t ht.le
  rw [hn] at hIt
  have hdata : Measurable (w (t + 1)) ∧
      (∀ s, V0 (po_shift (po_shift M t) 1) n s = w (t + 1) s) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
        (∀ s, ρ s ∈ feasiblePlans (po_shift (po_shift M t) 1) (n : ℕ∞) s) ∧
        (∀ s, w (t + 1) s ≤ J0T (po_shift (po_shift M t) 1) n s (ρ s) + ε) ∧
        po_JointMeas ρ n := by
    rw [po_shift_shift]
    rcases Nat.lt_or_ge (t + 1) T with h1 | h1
    · obtain ⟨hm, hV, hρ⟩ := hA (t + 1) (by omega) h1
      rw [hn'] at hρ
      refine ⟨hm, fun s => ?_, hρ⟩
      have := hV fun _ => s
      rw [eq_6_14, hn'] at this
      exact this
    · have hT : t + 1 = T := by omega
      have hn0 : n = 0 := by omega
      subst hn0
      rw [hT, hwT]
      refine ⟨(hI T le_rfl).2.1, fun s => po_V0_zero _ s, fun ε hε => ?_⟩
      refine ⟨fun _ _ _ => Classical.arbitrary A, fun s => po_feasible_zero _ s _,
        fun s => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [po_J0T_zero]
      exact le_add_of_nonneg_right hε.le
  obtain ⟨hm, hV, hρ⟩ := hdata
  have := po_bellman_step (po_shift_isMarkov hP t) hβ hIt hm hV hρ (h (Fin.last t))
  rw [po_shift_u0, po_shift_P0] at this
  refine ⟨this.1, ?_⟩
  rw [eq_6_14, hn]
  exact this.2

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The verification theorem: plans generated by the Bellman policy are optimal

Miao, §6.3, pp. 167–169: the policy correspondence `G_t` of the Bellman equation (6.19),
Markovian plans generated by measurable selections of `(G_t)`, and **Theorem 6.3.2**.

* `po_bellmanVal M w t s a = u_t(s, a) + β ∫ w_{t+1} dP_{t+1}(s, a; ·)`, the right-hand side of
  (6.19) at the action `a`; `po_G M w t s`, the set of maximisers `G_t(s)`.
* `po_genPlan g s`, the plan `π_t(sᵗ) = g_t(s_t)` generated from `s` by decision rules
  `g = (g_t)`, and its continuation (`po_cont_genPlan`); it is Markovian
  (`po_genPlan_markov`) and feasible when each `g_t` is a measurable selection of `Γ`
  (`po_genPlan_feasible`). `po_genFrom g t s` is the plan from a history ending in `s` at date
  `t` (the book's `π^{*sᵗ}`), equal to the restriction of the plan generated from `s₀`.
* `po_verification_core`: the induction behind Theorem 6.3.2, for date `0` of any process; it
  only needs the rewards to be integrable along the plan considered, so it also applies to
  problems where Assumption 5.1.3 fails (`po_verification_intPlans`).
* **Theorem 6.3.2** (`theorem_6_3_2`).

**Departure from the book.** The book asks `V*_t` to be "finite and measurable"; for the
integrals in (6.19) to exist (and for the proof's inequalities between them) one also needs
`V*_{t+1}` integrable against `P_{t+1}(s, a; ·)` for `a ∈ Γ(s)`; this is a hypothesis here.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The right-hand side of the Bellman equation (6.19) at the action `a`:
`u_t(s, a) + β ∫ w_{t+1}(s′) P_{t+1}(s, a; ds′)`. -/
noncomputable def po_bellmanVal (M : MDP S A) (w : ℕ → S → ℝ) (t : ℕ) (s : S) (a : A) : ℝ :=
  M.u t (s, a) + M.β * ∫ s', w (t + 1) s' ∂M.P t (s, a)

/-- The optimal policy correspondence `G_t(s)` of the Bellman equation (6.19) (Miao, p. 167): the
feasible actions attaining the supremum `w_t(s)`. -/
def po_G (M : MDP S A) (w : ℕ → S → ℝ) (t : ℕ) (s : S) : Set A :=
  {a | a ∈ M.Γ s ∧ po_bellmanVal M w t s a = w t s}

/-- `w` solves the Bellman equation (6.19) at `(t, s)`:
`w_t(s) = sup_{a ∈ Γ(s)} u_t(s, a) + β ∫ w_{t+1} dP_{t+1}(s, a; ·)`. -/
def po_SolvesAt (M : MDP S A) (w : ℕ → S → ℝ) (t : ℕ) (s : S) : Prop :=
  (w t s : EReal) = ⨆ a ∈ M.Γ s, (po_bellmanVal M w t s a : EReal)

theorem po_bellmanVal_le {M : MDP S A} {w : ℕ → S → ℝ} {t : ℕ} {s : S}
    (h : po_SolvesAt M w t s) {a : A} (ha : a ∈ M.Γ s) : po_bellmanVal M w t s a ≤ w t s := by
  have := le_iSup₂_of_le (f := fun a (_ : a ∈ M.Γ s) => (po_bellmanVal M w t s a : EReal)) a ha
    le_rfl
  rw [← h] at this
  exact EReal.coe_le_coe_iff.1 this

/-- If every feasible action gives at most `w_t(s)` and some feasible action gives exactly
`w_t(s)`, then `w` solves the Bellman equation at `(t, s)` and that action lies in `G_t(s)`. -/
theorem po_solvesAt_of_max {M : MDP S A} {w : ℕ → S → ℝ} {t : ℕ} {s : S}
    (hle : ∀ a ∈ M.Γ s, po_bellmanVal M w t s a ≤ w t s) {a₀ : A} (ha₀ : a₀ ∈ M.Γ s)
    (heq : po_bellmanVal M w t s a₀ = w t s) : po_SolvesAt M w t s ∧ a₀ ∈ po_G M w t s := by
  refine ⟨le_antisymm ?_ (iSup₂_le fun a ha => EReal.coe_le_coe_iff.2 (hle a ha)), ha₀, heq⟩
  rw [← heq]
  exact le_iSup₂_of_le (f := fun a (_ : a ∈ M.Γ s) => (po_bellmanVal M w t s a : EReal)) a₀ ha₀
    le_rfl

/-- The plan generated from `s` by the decision rules `g = (g_t)` (Miao, p. 168):
`π₀ = g₀(s)`, `π_t(sᵗ) = g_t(s_t)`. -/
def po_genPlan (g : ℕ → S → A) (s : S) : Plan S A := fun j h => g j (lastState s h)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_cont_genPlan (g : ℕ → S → A) (s s' : S) :
    po_cont (po_genPlan g s) s' = po_genPlan (fun j => g (j + 1)) s' := by
  funext j h
  simp only [po_cont, po_genPlan, lastState_cons]

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- Miao, p. 168: "By this construction, the plan `π` is Markovian." -/
theorem po_genPlan_markov (g : ℕ → S → A) (s : S) (T : ℕ∞) :
    IsMarkovian T (po_genPlan g s) :=
  ⟨g, fun _ _ _ => rfl⟩

theorem po_genPlan_feasible {M : MDP S A} {n : ℕ} {g : ℕ → S → A}
    (hg : ∀ j < n, Measurable (g j)) (hgΓ : ∀ j < n, ∀ s, g j s ∈ M.Γ s) (s : S) :
    po_genPlan g s ∈ feasiblePlans M (n : ℕ∞) s :=
  ⟨fun j hj => (hg j (po_cast_lt.1 hj)).comp (measurable_lastState s j),
    fun j hj _ => hgΓ j (po_cast_lt.1 hj) _⟩

/-- The plan `π^{*sᵗ}` from a history ending in `s` at date `t` (Miao, p. 168):
`π_t = g_t(s)`, `π_{t+j}(s^{t+j}_{t+1}) = g_{t+j}(s_{t+j})`. -/
def po_genFrom (g : ℕ → S → A) (t : ℕ) (s : S) : Plan S A := po_genPlan (fun j => g (j + t)) s

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The plan from a history of the plan generated from `s₀` is the plan generated from the
current state: at date `j + t`, on any history `H` whose current state is that of the history
`h'` after `sᵗ`, `π^*_{t+j}(H) = π^{*sᵗ}_{t+j}(h')`. -/
theorem po_genPlan_restrict (g : ℕ → S → A) (s₀ s : S) (t j : ℕ) (H : Fin (j + t) → S)
    (h' : Fin j → S) (hH : lastState s₀ H = lastState s h') :
    po_genPlan g s₀ (j + t) H = po_genFrom g t s j h' := by
  simp only [po_genPlan, po_genFrom, hH]

/-- **The induction behind Theorem 6.3.2**, at date `0` of a process `M` with horizon `n`. Let
`w` satisfy, at dates `j < n`, `u_j(s, a) + β ∫ w_{j+1} dP_{j+1}(s, a; ·) ≤ w_j(s)` for `a ∈ Γ(s)`
(with the integrals existing), with equality at `a = g_j(s) ∈ Γ(s)`, `g_j` measurable, and
`w_n = u_T`. Then every feasible plan with integrable rewards has `J ≤ w₀(s)`, and the plan
generated by `g` has `J = w₀(s)` when its rewards are integrable. -/
theorem po_verification_core :
    ∀ (n : ℕ) (M : MDP S A) (w : ℕ → S → ℝ) (g : ℕ → S → A), M.IsMarkov → 0 ≤ M.β →
      (∀ j < n, Measurable (g j)) →
      (∀ j < n, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (j + 1)) (M.P j (s, a)) ∧
        M.u j (s, a) + M.β * ∫ s', w (j + 1) s' ∂M.P j (s, a) ≤ w j s) →
      (∀ j < n, ∀ s, g j s ∈ M.Γ s ∧
        w j s = M.u j (s, g j s) + M.β * ∫ s', w (j + 1) s' ∂M.P j (s, g j s)) →
      (∀ s, w n s = M.uT s) → ∀ s,
      (∀ π ∈ feasiblePlans M (n : ℕ∞) s, po_IntPlan M n s π → J0T M n s π ≤ w 0 s) ∧
      (po_IntPlan M n s (po_genPlan g s) → J0T M n s (po_genPlan g s) = w 0 s) := by
  intro n
  induction n with
  | zero =>
    intro M w g _ _ _ _ _ hwT s
    refine ⟨fun π _ _ => by rw [po_J0T_zero, hwT], fun _ => by rw [po_J0T_zero, hwT]⟩
  | succ n ih =>
    intro M w g hP hβ hg hB1 hB2 hwT s
    have IH := ih (po_shift M 1) (fun j => w (j + 1)) (fun j => g (j + 1))
      (po_shift_isMarkov hP 1) hβ (fun j hj => hg (j + 1) (by omega))
      (fun j hj s a ha => hB1 (j + 1) (by omega) s a ha)
      (fun j hj s => hB2 (j + 1) (by omega) s) (fun s => hwT s)
    refine ⟨fun π hπ hIπ => ?_, fun hIg => ?_⟩
    · have hπm := po_plan_meas hπ
      have ha : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 (po_cast_lt.2 (Nat.succ_pos n)) Fin.elim0
      obtain ⟨hint, hle⟩ := hB1 0 (Nat.succ_pos n) s _ ha
      rw [po_J0T_succ hP hπm hIπ]
      refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ)) hle
      refine integral_mono_ae (po_integrable_J0T_cont hP hπm hIπ) hint ?_
      filter_upwards [po_ae_IntPlan_cont hP hπm hIπ] with s' hs'
      exact (IH s').1 _ (po_cont_feasible hπ s') hs'
    · have hgm : ∀ j ≤ n, Measurable (po_genPlan g s j) := fun j hj =>
        (hg j (by omega)).comp (measurable_lastState s j)
      obtain ⟨-, heq⟩ := hB2 0 (Nat.succ_pos n) s
      rw [po_J0T_succ hP hgm hIg, heq]
      congr 2
      refine integral_congr_ae ?_
      filter_upwards [po_ae_IntPlan_cont hP hgm hIg] with s' hs'
      rw [po_cont_genPlan] at hs' ⊢
      exact (IH s').2 hs'

/-- **Policy evaluation** (used for the secretary problem): if `w` satisfies the recursion of a
Markovian plan generated by `g`, `w_j(s) = u_j(s, g_j(s)) + β ∫ w_{j+1} dP_{j+1}(s, g_j(s); ·)`,
`w_n = u_T`, then the plan generated by `g` (with integrable rewards) has `J = w₀(s)`. No
optimality is assumed. -/
theorem po_policy_value :
    ∀ (n : ℕ) (M : MDP S A) (w : ℕ → S → ℝ) (g : ℕ → S → A), M.IsMarkov →
      (∀ j < n, Measurable (g j)) →
      (∀ j < n, ∀ s, w j s = M.u j (s, g j s) + M.β * ∫ s', w (j + 1) s' ∂M.P j (s, g j s)) →
      (∀ s, w n s = M.uT s) → ∀ s,
      po_IntPlan M n s (po_genPlan g s) → J0T M n s (po_genPlan g s) = w 0 s := by
  intro n
  induction n with
  | zero => intro M w g _ _ _ hwT s _; rw [po_J0T_zero, hwT]
  | succ n ih =>
    intro M w g hP hg hB2 hwT s hIg
    have IH := ih (po_shift M 1) (fun j => w (j + 1)) (fun j => g (j + 1))
      (po_shift_isMarkov hP 1) (fun j hj => hg (j + 1) (by omega))
      (fun j hj s => hB2 (j + 1) (by omega) s) (fun s => hwT s)
    have hgm : ∀ j ≤ n, Measurable (po_genPlan g s j) := fun j hj =>
      (hg j (by omega)).comp (measurable_lastState s j)
    rw [po_J0T_succ hP hgm hIg, hB2 0 (Nat.succ_pos n) s]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [po_ae_IntPlan_cont hP hgm hIg] with s' hs'
    rw [po_cont_genPlan] at hs' ⊢
    exact IH s' hs'

/-- Theorem 6.3.2 for the problems in which only the plans with integrable rewards are admitted
(no Assumption 5.1.3): under the hypotheses of `po_verification_core`, the plan generated by `g`,
if its rewards are integrable, attains `sup {J₀ⁿ(s, π) : π ∈ Π(s), rewards integrable}`. -/
theorem po_verification_intPlans {n : ℕ} {M : MDP S A} {w : ℕ → S → ℝ} {g : ℕ → S → A}
    (hP : M.IsMarkov) (hβ : 0 ≤ M.β) (hg : ∀ j < n, Measurable (g j))
    (hB1 : ∀ j < n, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (j + 1)) (M.P j (s, a)) ∧
      M.u j (s, a) + M.β * ∫ s', w (j + 1) s' ∂M.P j (s, a) ≤ w j s)
    (hB2 : ∀ j < n, ∀ s, g j s ∈ M.Γ s ∧
      w j s = M.u j (s, g j s) + M.β * ∫ s', w (j + 1) s' ∂M.P j (s, g j s))
    (hwT : ∀ s, w n s = M.uT s) (s : S) (hIg : po_IntPlan M n s (po_genPlan g s)) :
    po_genPlan g s ∈ feasiblePlans M (n : ℕ∞) s ∧ J0T M n s (po_genPlan g s) = w 0 s ∧
      ∀ π ∈ feasiblePlans M (n : ℕ∞) s, po_IntPlan M n s π →
        J0T M n s π ≤ J0T M n s (po_genPlan g s) := by
  have hc := po_verification_core n M w g hP hβ hg hB1 hB2 hwT s
  refine ⟨po_genPlan_feasible hg (fun j hj s => (hB2 j hj s).1) s, hc.2 hIg, fun π hπ hIπ => ?_⟩
  rw [hc.2 hIg]
  exact hc.1 π hπ hIπ

/-- **Theorem 6.3.2** (Miao, p. 168), the verification theorem. Let `w_t` (`t ≤ T`) be finite
measurable functions solving the Bellman equation (6.19) with `w_T = u_T`, the integrals of
`w_{t+1}` against `P_{t+1}(s, a; ·)`, `a ∈ Γ(s)`, existing, and let `g_t` be measurable
selections of the policy correspondences `G_t` (`t < T`). Under Assumption 5.1.3 at every date
and `β ≥ 0`, for every `t ≤ T` and history `sᵗ`, the plan `π^{*sᵗ}` generated by `(g_t)` from
`sᵗ` is feasible and `w_t(s_t) = J_t^T(sᵗ, π^{*sᵗ}) = V_t(sᵗ)`. In particular the Markovian plan
generated by `(G_t)` from `s₀` is optimal for (5.5). -/
theorem theorem_6_3_2 {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 ≤ M.β) {T : ℕ}
    (hI : po_Assumption513 M T) {w : ℕ → S → ℝ} {g : ℕ → S → A}
    (hint : ∀ t < T, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (t + 1)) (M.P t (s, a)))
    (hsol : ∀ t < T, ∀ s, po_SolvesAt M w t s)
    (hg : ∀ t < T, Measurable (g t)) (hgG : ∀ t < T, ∀ s, g t s ∈ po_G M w t s)
    (hwT : ∀ s, w T s = M.uT s) (t : ℕ) (ht : t ≤ T) (h : Fin (t + 1) → S) :
    po_genFrom g t (h (Fin.last t)) ∈ po_plansFrom M T t h ∧
      po_JFrom M T t h (po_genFrom g t (h (Fin.last t))) = w t (h (Fin.last t)) ∧
      po_VFrom M T t h = w t (h (Fin.last t)) := by
  set s := h (Fin.last t)
  have e : ∀ j, j + 1 + t = j + t + 1 := fun j => by omega
  have hc := po_verification_core (T - t) (po_shift M t) (fun j => w (j + t))
    (fun j => g (j + t)) (po_shift_isMarkov hP t) hβ (fun j hj => hg (j + t) (by omega))
    (fun j hj s a ha => by
      have h1 := hint (j + t) (by omega) s a ha
      have h2 := po_bellmanVal_le (hsol (j + t) (by omega) s) ha
      simp only [po_bellmanVal] at h2
      refine ⟨?_, ?_⟩
      · simp only [e]
        exact h1
      · simp only [e]
        exact h2)
    (fun j hj s => by
      obtain ⟨hΓ, heq⟩ := hgG (j + t) (by omega) s
      simp only [po_bellmanVal] at heq
      refine ⟨hΓ, ?_⟩
      simp only [e]
      exact heq.symm)
    (fun s => by simp only [Nat.sub_add_cancel ht]; exact hwT s) s
  have hF : po_genFrom g t s ∈ po_plansFrom M T t h :=
    po_genPlan_feasible (fun j hj => hg (j + t) (by have := hj; omega))
      (fun j hj s => (hgG (j + t) (by omega) s).1) s
  have hIg := po_intPlan_of_assumption513 (hI t ht) hF
  have hJ : po_JFrom M T t h (po_genFrom g t s) = w t s := by
    have := hc.2 hIg
    simp only [zero_add] at this
    exact this
  refine ⟨hF, hJ, le_antisymm (iSup₂_le fun π hπ => ?_) ?_⟩
  · have := hc.1 π hπ (po_intPlan_of_assumption513 (hI t ht) hπ)
    simp only [zero_add] at this
    exact EReal.coe_le_coe_iff.2 this
  · rw [← hJ]
    exact po_J_le_V0 hF

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal plans follow the Bellman policy: Theorem 6.3.3, corrected

Miao, §6.3, pp. 169–172. **Theorem 6.3.3** claims that every optimal plan `π*` of (5.5)
satisfies `π*_0 ∈ G_0(s_0)` and `π*_t(sᵗ) ∈ G_t(s_t)` for **all** `t` and `sᵗ`.

**Correction.** This holds only for almost every history: changing an optimal plan on a set of
histories of probability zero leaves its value unchanged and keeps it optimal.
* `theorem_6_3_3` proves `π*_0 ∈ G_0(s_0)` and, for `t < T`, `π*_t(sᵗ) ∈ G_t(s_t)` for
  `μᵗ(s₀, ·; π*)`-almost every history `sᵗ` (the histories that `π*` reaches), when `β > 0`.
  The core induction is `po_converse_core`.
* `theorem_6_3_3_counterexample`: a process on `S = A = Bool` with `T = 2` (the next state is
  always `true`; the reward is `1` for the action `true`) and an optimal plan with
  `π*_1(false) = false ∉ G_1(false) = {true}`; the history `s₁ = false` has probability zero.

The book's hypotheses that `G_t` be nonempty with a measurable selection are not needed: the
proof below only uses that `V_t = w_t` solves the Bellman equation. The book's argument via
Theorem 6.3.2 is replaced by the definition of `V_1` as a supremum. Also needed, and assumed:
`β > 0` (with `β = 0` the decisions after date `0` are unrestricted), and the integrability of
`V_{t+1}` against `P_{t+1}(s, a; ·)` for `a ∈ Γ(s)`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

theorem po_measurableSet_G {M : MDP S A} {w : ℕ → S → ℝ} {j : ℕ} (hu : Measurable (M.u j))
    (hw : Measurable (w (j + 1))) (hw' : Measurable (w j)) (hP : M.IsMarkov) {s : S}
    {π : Plan S A} (hπm : Measurable (π j)) (hπΓ : ∀ h, π j h ∈ M.Γ (lastState s h)) :
    MeasurableSet {h : Fin j → S | π j h ∈ po_G M w j (lastState s h)} := by
  have hk := isSFiniteKernel_stepKernel M hP s π j
  have hI : Measurable fun h : Fin j → S =>
      ∫ s', w (j + 1) s' ∂M.P j (lastState s h, π j h) := by
    have := (hw.stronglyMeasurable.integral_kernel (κ := stepKernel M s π j)).measurable
    have heq : (fun h : Fin j → S => ∫ s', w (j + 1) s' ∂M.P j (lastState s h, π j h)) =
        fun h => ∫ s', w (j + 1) s' ∂stepKernel M s π j h := by
      funext h
      rw [stepKernel_apply M s hπm]
    rw [heq]
    exact this
  have hF : Measurable fun h : Fin j → S => po_bellmanVal M w j (lastState s h) (π j h) :=
    (hu.comp ((measurable_lastState s j).prodMk hπm)).add (measurable_const.mul hI)
  have : {h : Fin j → S | π j h ∈ po_G M w j (lastState s h)} =
      {h | po_bellmanVal M w j (lastState s h) (π j h) = w j (lastState s h)} := by
    ext h
    exact ⟨fun hh => hh.2, fun hh => ⟨hπΓ h, hh⟩⟩
  rw [this]
  exact measurableSet_eq_fun hF (hw'.comp (measurable_lastState s j))

/-- **The induction behind Theorem 6.3.3**, at date `0` of a process `M` with horizon `n`: if
`w_j` is the value from date `j` (`j ≤ n`), measurable, and satisfies the Bellman inequalities
(`w` solves the Bellman equation), `β > 0`, and `π` is a feasible plan from `s` with integrable
rewards and `J₀ⁿ(s, π) = w₀(s)`, then `π_j(sʲ) ∈ G_j(s_j)` for `μʲ(s, ·; π)`-a.e. `sʲ`. -/
theorem po_converse_core :
    ∀ (n : ℕ) (M : MDP S A) (w : ℕ → S → ℝ), M.IsMarkov → 0 < M.β →
      (∀ j < n, Measurable (M.u j)) → (∀ j ≤ n, Measurable (w j)) →
      (∀ j ≤ n, ∀ s, V0 (po_shift M j) (n - j) s = w j s) →
      (∀ j < n, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (j + 1)) (M.P j (s, a)) ∧
        po_bellmanVal M w j s a ≤ w j s) →
      ∀ (s : S) (π : Plan S A), π ∈ feasiblePlans M (n : ℕ∞) s → po_IntPlan M n s π →
      J0T M n s π = w 0 s →
      ∀ j < n, ∀ᵐ h ∂mu M s π j, π j h ∈ po_G M w j (lastState s h) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro M w hP hβ hu hwm hV hB s π hπ hIπ hopt
    have hπm := po_plan_meas hπ
    have ha : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 (po_cast_lt.2 (Nat.succ_pos n)) Fin.elim0
    obtain ⟨hint, hle⟩ := hB 0 (Nat.succ_pos n) s _ ha
    have hJi := po_integrable_J0T_cont hP hπm hIπ
    have hJle : ∀ s', J0T (po_shift M 1) n s' (po_cont π s') ≤ w 1 s' := fun s' => by
      have h1 := po_J_le_V0 (po_cont_feasible hπ s')
      have h2 := hV 1 (by omega) s'
      simp only [Nat.add_sub_cancel] at h2
      rw [h2] at h1
      exact EReal.coe_le_coe_iff.1 h1
    have hrec := po_J0T_succ hP hπm hIπ
    rw [hopt] at hrec
    have hmono : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) ≤
        ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := integral_mono hJi hint hJle
    simp only [po_bellmanVal] at hle
    have hEq : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) =
        ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := by
      refine le_antisymm hmono ?_
      have := mul_le_mul_of_nonneg_left hmono hβ.le
      by_contra hne
      have hlt : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) <
          ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := lt_of_not_ge hne
      have := mul_lt_mul_of_pos_left hlt hβ
      linarith
    have hG0 : po_bellmanVal M w 0 s (π 0 Fin.elim0) = w 0 s := by
      simp only [po_bellmanVal]
      rw [← hEq]
      linarith
    have hae : ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
        J0T (po_shift M 1) n s' (po_cont π s') = w 1 s' := by
      have hnn : 0 ≤ᵐ[M.P 0 (s, π 0 Fin.elim0)]
          fun s' => w 1 s' - J0T (po_shift M 1) n s' (po_cont π s') :=
        Filter.Eventually.of_forall fun s' => sub_nonneg.2 (hJle s')
      have h0 : ∫ s', (w 1 s' - J0T (po_shift M 1) n s' (po_cont π s'))
          ∂M.P 0 (s, π 0 Fin.elim0) = 0 := by
        rw [integral_sub hint hJi, hEq, sub_self]
      have := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub hJi)).1 h0
      filter_upwards [this] with s' hs'
      have : w 1 s' - J0T (po_shift M 1) n s' (po_cont π s') = 0 := hs'
      linarith
    intro j hj
    cases j with
    | zero =>
      refine Filter.Eventually.of_forall fun h => ?_
      have : h = Fin.elim0 := Subsingleton.elim _ _
      subst this
      exact ⟨ha, hG0⟩
    | succ j =>
      have hIH := ih (po_shift M 1) (fun j => w (j + 1)) (po_shift_isMarkov hP 1) hβ
        (fun k hk => hu (k + 1) (by omega)) (fun k hk => hwm (k + 1) (by omega))
        (fun k hk s => by
          rw [po_shift_shift, Nat.add_comm 1 k]
          have := hV (k + 1) (by omega) s
          rwa [show n + 1 - (k + 1) = n - k by omega] at this)
        (fun k hk s a ha => hB (k + 1) (by omega) s a ha)
      refine po_ae_mu_succ hP s (fun k hk => hπm k (by omega))
        (po_measurableSet_G (hu (j + 1) (by omega)) (hwm (j + 2) (by omega))
          (hwm (j + 1) (by omega)) hP (hπm (j + 1) (by omega))
          fun h => hπ.2 (j + 1) (po_cast_lt.2 hj) h) ?_
      filter_upwards [hae, po_ae_IntPlan_cont hP hπm hIπ] with s' h1 h2
      have := hIH s' (po_cont π s') (po_cont_feasible hπ s') h2 h1 j (by omega)
      filter_upwards [this] with h hh
      rw [lastState_cons]
      exact hh

/-- **Theorem 6.3.3** (Miao, p. 170), corrected. Let the value functions `V_t = w_t` (`t ≤ T`)
be measurable, real-valued and solve the Bellman equation (6.17)/(6.19), with the integrals of
`w_{t+1}` against `P_{t+1}(s, a; ·)`, `a ∈ Γ(s)`, existing; let Assumption 5.1.3 hold and
`β > 0`. Then any optimal plan `π*` for (5.5) from `s₀` satisfies `π*_0 ∈ G_0(s₀)` and, for every
`t < T`, `π*_t(sᵗ) ∈ G_t(s_t)` for `μᵗ(s₀, ·; π*)`-almost every history `sᵗ`. (The book's "for
all `sᵗ`" is false: `theorem_6_3_3_counterexample`.) -/
theorem theorem_6_3_3 {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 < M.β) {T : ℕ}
    (hI : Assumption513 M T) {w : ℕ → S → ℝ} (hwm : ∀ t ≤ T, Measurable (w t))
    (hV : ∀ t ≤ T, ∀ s, V0 (po_shift M t) (T - t) s = w t s)
    (hint : ∀ t < T, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (t + 1)) (M.P t (s, a)))
    (hsol : ∀ t < T, ∀ s, po_SolvesAt M w t s) {s₀ : S} {π : Plan S A}
    (hopt : IsOptimalPlan0 M T s₀ π) :
    (0 < T → π 0 Fin.elim0 ∈ po_G M w 0 s₀) ∧
      ∀ t < T, ∀ᵐ h ∂mu M s₀ π t, π t h ∈ po_G M w t (lastState s₀ h) := by
  have hJ : J0T M T s₀ π = w 0 s₀ := by
    have h1 := hopt.2
    have h2 := hV 0 (Nat.zero_le T) s₀
    rw [po_shift_zero, Nat.sub_zero] at h2
    rw [h2] at h1
    exact (EReal.coe_eq_coe_iff.1 h1).symm
  have hc := po_converse_core T M w hP hβ (fun j hj => hI.1 j hj) hwm hV
    (fun j hj s a ha => ⟨hint j hj s a ha, po_bellmanVal_le (hsol j hj s) ha⟩) s₀ π hopt.1
    (po_intPlan_of_assumption513 hI hopt.1) hJ
  refine ⟨fun hT => ?_, hc⟩
  have := hc 0 hT
  rw [mu_zero, ae_dirac_iff (Subsingleton.measurableSet)] at this
  exact this

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.3.3 fails off the reachable histories

Miao, Theorem 6.3.3, p. 170, claims `π*_t(sᵗ) ∈ G_t(s_t)` for **all** histories `sᵗ`. Here is a
process satisfying every hypothesis of the theorem with an optimal plan that violates the claim
on a history of probability zero (`theorem_6_3_3_counterexample`).

`S = A = Bool`, `Γ(s) = A`, the next state is always `true` (`P_{t+1}(s, a; ·) = δ_true`), the
reward is `u_t(s, a) = 1` if `a = true` and `0` otherwise, `u_T = 0`, `β = 1`, `T = 2`. The value
functions are `V₀ = 2`, `V₁ = 1`, `V₂ = 0` and `G_t(s) = {true}`. The plan `π₀ = true`,
`π₁(s₁) = s₁` is optimal (the history `s₁ = true` has probability one), but
`π₁(false) = false ∉ G₁(false)`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

/-- The process of the counterexample. -/
noncomputable def po_cexModel : MDP Bool Bool where
  Γ := fun _ => Set.univ
  P := fun _ => Kernel.const _ (Measure.dirac true)
  u := fun _ x => if x.2 then 1 else 0
  uT := fun _ => 0
  β := 1

/-- Its value functions. -/
def po_cexW : ℕ → Bool → ℝ := fun t _ => if t = 0 then 2 else if t = 1 then 1 else 0

/-- The optimal plan `π₀ = true`, `π₁(s₁) = s₁` (and `π_t(sᵗ) = s₁` later). -/
def po_cexPlan : Plan Bool Bool := fun j h => if hj : 0 < j then h ⟨0, hj⟩ else true

theorem po_cex_markov : po_cexModel.IsMarkov := fun _ => by
  change IsMarkovKernel (Kernel.const _ (Measure.dirac true))
  infer_instance

theorem po_cex_bellmanVal (t : ℕ) (s a : Bool) :
    po_bellmanVal po_cexModel po_cexW t s a = (if a then 1 else 0) + po_cexW (t + 1) true := by
  simp only [po_bellmanVal, po_cexModel, Kernel.const_apply, integral_dirac, one_mul]

theorem po_cex_solves (t : ℕ) (ht : t < 2) (s : Bool) :
    po_SolvesAt po_cexModel po_cexW t s ∧ true ∈ po_G po_cexModel po_cexW t s := by
  refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_
  · rw [po_cex_bellmanVal]
    interval_cases t <;> cases a <;> norm_num [po_cexW]
  · rw [po_cex_bellmanVal]
    interval_cases t <;> norm_num [po_cexW]

theorem po_cex_assumption (T : ℕ) : po_Assumption513 po_cexModel T :=
  po_assumption513_of_bounded po_cex_markov (B := 1)
    ⟨fun t x => by simp only [po_cexModel]; split_ifs <;> norm_num,
      fun s => by simp [po_cexModel]⟩
    (fun _ => measurable_of_countable _) (measurable_of_countable _) T

theorem po_cex_values (t : ℕ) (ht : t ≤ 2) (s : Bool) :
    V0 (po_shift po_cexModel t) (2 - t) s = po_cexW t s := by
  have := (theorem_6_3_2 po_cex_markov zero_le_one (po_cex_assumption 2) (g := fun _ _ => true)
    (fun t _ s a _ => by
      change Integrable _ (Measure.dirac true)
      exact Integrable.of_finite) (fun t ht s => (po_cex_solves t ht s).1)
    (fun _ _ => measurable_const) (fun t ht s => (po_cex_solves t ht s).2)
    (fun s => by simp [po_cexW, po_cexModel]) t ht (fun _ => s)).2.2
  rw [eq_6_14] at this
  exact this

/-- **Theorem 6.3.3 as printed is false** (Miao, p. 170): the counterexample process satisfies
the hypotheses of `theorem_6_3_3` (Markov kernels, `β > 0`, Assumption 5.1.3, measurable value
functions solving the Bellman equation with integrable continuation values) and `po_cexPlan` is
optimal from `s₀ = true`, yet `π₁(sᵗ) ∈ G₁(s₁)` fails at the history `s₁ = false`. -/
theorem theorem_6_3_3_counterexample :
    po_cexModel.IsMarkov ∧ 0 < po_cexModel.β ∧ Assumption513 po_cexModel 2 ∧
      (∀ t ≤ 2, Measurable (po_cexW t)) ∧
      (∀ t ≤ 2, ∀ s, V0 (po_shift po_cexModel t) (2 - t) s = po_cexW t s) ∧
      (∀ t < 2, ∀ s, ∀ a ∈ po_cexModel.Γ s,
        Integrable (po_cexW (t + 1)) (po_cexModel.P t (s, a))) ∧
      (∀ t < 2, ∀ s, po_SolvesAt po_cexModel po_cexW t s) ∧
      IsOptimalPlan0 po_cexModel 2 true po_cexPlan ∧
      ¬ ∀ t < 2, ∀ h : Fin t → Bool,
        po_cexPlan t h ∈ po_G po_cexModel po_cexW t (lastState true h) := by
  have hI := po_cex_assumption 2
  have hF : po_cexPlan ∈ feasiblePlans po_cexModel ((2 : ℕ) : ℕ∞) true :=
    ⟨fun _ _ => measurable_of_countable _, fun _ _ _ => Set.mem_univ _⟩
  refine ⟨po_cex_markov, one_pos, hI 0 (Nat.zero_le 2), fun _ _ => measurable_of_countable _,
    po_cex_values, fun _ _ _ _ _ => by
      change Integrable _ (Measure.dirac true)
      exact Integrable.of_finite,
    fun t ht s => (po_cex_solves t ht s).1, ⟨hF, ?_⟩, ?_⟩
  · have hV := po_cex_values 0 (Nat.zero_le 2) true
    rw [po_shift_zero, Nat.sub_zero] at hV
    rw [hV]
    have hF1 := po_cont_feasible hF true
    have hI1 : Assumption513 (po_shift po_cexModel 1) 1 := hI 1 (by norm_num)
    have h1 : J0T po_cexModel 2 true po_cexPlan =
        po_cexModel.u 0 (true, po_cexPlan 0 Fin.elim0) + po_cexModel.β *
          ∫ s', J0T (po_shift po_cexModel 1) 1 s' (po_cont po_cexPlan s') ∂Measure.dirac true :=
      po_J0T_succ (n := 1) po_cex_markov (po_plan_meas hF)
        (po_intPlan_of_assumption513 (hI 0 (Nat.zero_le 2)) hF)
    have h2 : J0T (po_shift po_cexModel 1) 1 true (po_cont po_cexPlan true) =
        (po_shift po_cexModel 1).u 0 (true, po_cont po_cexPlan true 0 Fin.elim0) +
          (po_shift po_cexModel 1).β * ∫ s', J0T (po_shift (po_shift po_cexModel 1) 1) 0 s'
            (po_cont (po_cont po_cexPlan true) s') ∂Measure.dirac true :=
      po_J0T_succ (n := 0) (po_shift_isMarkov po_cex_markov 1) (po_plan_meas hF1)
        (po_intPlan_of_assumption513 hI1 hF1)
    rw [integral_dirac] at h1 h2
    rw [po_J0T_zero] at h2
    rw [h1, h2]
    norm_num [po_cexW, po_cexModel, po_shift, po_cexPlan, po_cont]
  · intro h
    have := (h 1 (by norm_num) fun _ => false).2
    rw [po_cex_bellmanVal] at this
    simp [po_cexPlan, po_cexW] at this

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The principle of optimality for deterministic problems

**Exercise 6.1** (Miao, p. 189): Theorems 6.3.1–6.3.3 for the deterministic case. A deterministic
problem has states `S`, actions `A` (arbitrary types: no σ-algebras), a constraint
correspondence `Γ`, laws of motion `s_{t+1} = f_t(s_t, a_t)`, rewards `u_t`, a terminal reward
`u_T` and a discount factor `β`. With no uncertainty a plan is a sequence of actions `(a_t)`
(`po_traj` is the state path it generates), and the history after the first state is
determined, so

* there is **no measurability requirement** anywhere: no measurable plans (Definition 5.1.1),
  no measurable value functions or ε-optimal plans (Assumption 6.3.1), no measurable
  selections of `G_t`, no integrability (Assumption 5.1.3);
* in Theorem 6.3.1 the ε-optimal continuation is needed only from the single successor state
  `f_t(s_t, a_t)`, so it exists by the definition of the supremum
  (`ex_6_1_theorem_6_3_1`, only finiteness of `V_{t+1}` is assumed);
* Theorem 6.3.2 holds for any selection `g_t` of `G_t` (`ex_6_1_theorem_6_3_2`);
* Theorem 6.3.3 holds **everywhere along the optimal path**, `a*_t ∈ G_t(s*_t)` for all `t`,
  since the only histories are those the plan reaches; the continuation of an optimal plan from
  `s*_t` is optimal at date `t` (time consistency, `ex_6_1_theorem_6_3_3`).

The date-`t` problem is date `0` of the shifted problem `po_detShift D t`.
-/

namespace Miao.FiniteHorizonDP

/-- A deterministic finite-horizon problem (Miao, Exercise 6.1). -/
structure po_Det (S A : Type*) where
  Γ : S → Set A
  f : ℕ → S × A → S
  u : ℕ → S × A → ℝ
  uT : S → ℝ
  β : ℝ

variable {S A : Type*}

/-- The problem from date `t` on. -/
def po_detShift (D : po_Det S A) (t : ℕ) : po_Det S A :=
  ⟨D.Γ, fun j => D.f (j + t), fun j => D.u (j + t), D.uT, D.β⟩

theorem po_detShift_shift (D : po_Det S A) (a b : ℕ) :
    po_detShift (po_detShift D a) b = po_detShift D (a + b) := by
  have h : ∀ j, j + b + a = j + (a + b) := fun j => by omega
  simp only [po_detShift, h]

/-- The state path `s_0 = s`, `s_{j+1} = f_j(s_j, a_j)` generated by a sequence of actions. -/
def po_traj (D : po_Det S A) (s : S) (a : ℕ → A) : ℕ → S
  | 0 => s
  | j + 1 => D.f j (po_traj D s a j, a j)

/-- The feasible action sequences from `s` over the horizon `n`. -/
def po_detFeasible (D : po_Det S A) (n : ℕ) (s : S) : Set (ℕ → A) :=
  {a | ∀ j < n, a j ∈ D.Γ (po_traj D s a j)}

/-- The objective `∑_{j<n} βʲ u_j(s_j, a_j) + βⁿ u_T(s_n)`. -/
def po_detJ (D : po_Det S A) (n : ℕ) (s : S) (a : ℕ → A) : ℝ :=
  ∑ j ∈ Finset.range n, D.β ^ j * D.u j (po_traj D s a j, a j) +
    D.β ^ n * D.uT (po_traj D s a n)

/-- The value `sup_{a feasible} J(s, a)` in `[−∞, +∞]`. -/
noncomputable def po_detV (D : po_Det S A) (n : ℕ) (s : S) : EReal :=
  ⨆ a ∈ po_detFeasible D n s, (po_detJ D n s a : EReal)

/-- The value at date `t` of the problem with horizon `T`. -/
noncomputable def po_detVt (D : po_Det S A) (T t : ℕ) (s : S) : EReal :=
  po_detV (po_detShift D t) (T - t) s

/-- Prepend an action. -/
def po_seqCons (a₀ : A) (σ : ℕ → A) : ℕ → A
  | 0 => a₀
  | j + 1 => σ j

theorem po_traj_succ (D : po_Det S A) (s : S) (a : ℕ → A) (j : ℕ) :
    po_traj D s a (j + 1) =
      po_traj (po_detShift D 1) (D.f 0 (s, a 0)) (fun i => a (i + 1)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change D.f (j + 1) (po_traj D s a (j + 1), a (j + 1)) = _
    rw [ih]
    rfl

theorem po_traj_shift (D : po_Det S A) (s : S) (a : ℕ → A) (j i : ℕ) :
    po_traj D s a (i + j) =
      po_traj (po_detShift D j) (po_traj D s a j) (fun k => a (k + j)) i := by
  induction i with
  | zero => simp only [Nat.zero_add]; rfl
  | succ i ih =>
    rw [show i + 1 + j = (i + j) + 1 by omega]
    change D.f (i + j) (po_traj D s a (i + j), a (i + j)) = _
    rw [ih]
    rfl

theorem po_detFeasible_succ (D : po_Det S A) (n : ℕ) (s : S) (a : ℕ → A) :
    a ∈ po_detFeasible D (n + 1) s ↔
      a 0 ∈ D.Γ s ∧ (fun i => a (i + 1)) ∈ po_detFeasible (po_detShift D 1) n (D.f 0 (s, a 0)) := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.succ_pos n), fun j hj => ?_⟩
    have := h (j + 1) (by omega)
    rw [po_traj_succ] at this
    exact this
  · rintro ⟨h0, h1⟩ j hj
    cases j with
    | zero => exact h0
    | succ j =>
      rw [po_traj_succ]
      exact h1 j (by omega)

/-- The recursive form of the objective (Lemma 6.3.1, deterministic):
`J(s, a) = u_0(s, a_0) + β J₁(f_0(s, a_0), (a_{t+1}))`. -/
theorem po_detJ_succ (D : po_Det S A) (n : ℕ) (s : S) (a : ℕ → A) :
    po_detJ D (n + 1) s a = D.u 0 (s, a 0) +
      D.β * po_detJ (po_detShift D 1) n (D.f 0 (s, a 0)) (fun i => a (i + 1)) := by
  unfold po_detJ
  rw [Finset.sum_range_succ', po_traj_succ, mul_add, Finset.mul_sum]
  simp only [po_traj_succ]
  have : (po_detShift D 1).β = D.β := rfl
  simp only [this, pow_succ, pow_zero, one_mul]
  have hu : ∀ i, (po_detShift D 1).u i = D.u (i + 1) := fun i => rfl
  have huT : (po_detShift D 1).uT = D.uT := rfl
  simp only [hu, huT]
  rw [show po_traj D s a 0 = s from rfl]
  ring_nf

theorem po_detJ_le_V {D : po_Det S A} {n : ℕ} {s : S} {a : ℕ → A}
    (ha : a ∈ po_detFeasible D n s) : (po_detJ D n s a : EReal) ≤ po_detV D n s :=
  le_iSup₂ (f := fun a (_ : a ∈ po_detFeasible D n s) => (po_detJ D n s a : EReal)) a ha

theorem po_detJ_zero (D : po_Det S A) (s : S) (a : ℕ → A) : po_detJ D 0 s a = D.uT s := by
  simp [po_detJ, po_traj]

theorem po_detV_zero [Nonempty A] (D : po_Det S A) (s : S) : po_detV D 0 s = D.uT s := by
  refine le_antisymm (iSup₂_le fun a _ => by rw [po_detJ_zero]) ?_
  have : (fun _ => Classical.arbitrary A) ∈ po_detFeasible D 0 s := fun j hj =>
    absurd hj (Nat.not_lt_zero j)
  have h := po_detJ_le_V this
  rwa [po_detJ_zero] at h

/-- The Bellman step at date `0` of a deterministic problem with horizon `n + 1`, when the
value from date `1` is a real function `w'` (the deterministic Theorem 6.3.1). -/
theorem po_det_bellman_step {D : po_Det S A} (hβ : 0 ≤ D.β) {n : ℕ} {w' : S → ℝ}
    (hw : ∀ s, po_detV (po_detShift D 1) n s = w' s) (s : S) :
    po_detV D (n + 1) s = ⨆ a ∈ D.Γ s, ((D.u 0 (s, a) + D.β * w' (D.f 0 (s, a)) : ℝ) : EReal) := by
  refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup₂_le fun a₀ ha₀ => ?_)
  · obtain ⟨h0, h1⟩ := (po_detFeasible_succ D n s a).1 ha
    have hJ := po_detJ_le_V h1
    rw [hw] at hJ
    rw [po_detJ_succ]
    refine le_trans ?_ (le_iSup₂_of_le (a 0) h0 le_rfl)
    exact EReal.coe_le_coe_iff.2 (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.1 hJ) hβ))
  · refine po_coe_le_of_forall_sub fun δ hδ => ?_
    have hβ1 : 0 < D.β + 1 := by linarith
    set x := D.f 0 (s, a₀)
    have hlt : ((w' x - δ / (D.β + 1) : ℝ) : EReal) < po_detV (po_detShift D 1) n x := by
      rw [hw]
      exact EReal.coe_lt_coe_iff.2 (by linarith [div_pos hδ hβ1])
    obtain ⟨σ, hσ, hσJ⟩ := lt_biSup_iff.1 hlt
    have hσJ' := EReal.coe_lt_coe_iff.1 hσJ
    have hfeas : po_seqCons a₀ σ ∈ po_detFeasible D (n + 1) s :=
      (po_detFeasible_succ D n s _).2 ⟨ha₀, hσ⟩
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (po_detJ_le_V hfeas)
    rw [po_detJ_succ]
    change D.u 0 (s, a₀) + D.β * w' x - δ ≤ D.u 0 (s, a₀) +
      D.β * po_detJ (po_detShift D 1) n x σ
    have h2 := mul_le_mul_of_nonneg_left hσJ'.le hβ
    have h3 : D.β * (δ / (D.β + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hβ1]
      nlinarith
    nlinarith

/-- **Exercise 6.1: Theorem 6.3.1, deterministic** (Miao, p. 189). With `β ≥ 0`, if `V_{t+1}` is
finite (`V_{t+1} = w_{t+1}`), then
`V_t(s) = sup_{a ∈ Γ(s)} u_t(s, a) + β V_{t+1}(f_t(s, a))` for `t < T`; `V_T = u_T`. No
measurability or ε-selection assumption is needed. -/
theorem ex_6_1_theorem_6_3_1 [Nonempty A] {D : po_Det S A} (hβ : 0 ≤ D.β) {T : ℕ}
    {w : ℕ → S → ℝ} (hw : ∀ t < T, ∀ s, po_detVt D T (t + 1) s = w (t + 1) s) :
    (∀ t < T, ∀ s, po_detVt D T t s =
      ⨆ a ∈ D.Γ s, ((D.u t (s, a) + D.β * w (t + 1) (D.f t (s, a)) : ℝ) : EReal)) ∧
    ∀ s, po_detVt D T T s = D.uT s := by
  refine ⟨fun t ht s => ?_, fun s => by rw [po_detVt, Nat.sub_self, po_detV_zero]; rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  rw [po_detVt, hn]
  have := po_det_bellman_step (D := po_detShift D t) hβ (n := n) (w' := w (t + 1))
    (fun s => by rw [po_detShift_shift, ← hn', ← hw t ht s]; rfl) s
  rw [this]
  have hu : (po_detShift D t).u 0 = D.u t := by simp only [po_detShift, zero_add]
  have hf : (po_detShift D t).f 0 = D.f t := by simp only [po_detShift, zero_add]
  rw [hu, hf]
  rfl

/-- The state path of the plan generated by decision rules `g = (g_t)`. -/
def po_genTraj (D : po_Det S A) (g : ℕ → S → A) (s : S) : ℕ → S
  | 0 => s
  | j + 1 => D.f j (po_genTraj D g s j, g j (po_genTraj D g s j))

/-- The action sequence `a_t = g_t(s_t)` generated by decision rules `g` from `s`. -/
def po_genSeq (D : po_Det S A) (g : ℕ → S → A) (s : S) : ℕ → A :=
  fun j => g j (po_genTraj D g s j)

theorem po_traj_genSeq (D : po_Det S A) (g : ℕ → S → A) (s : S) (j : ℕ) :
    po_traj D s (po_genSeq D g s) j = po_genTraj D g s j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change D.f j (po_traj D s (po_genSeq D g s) j, po_genSeq D g s j) = _
    rw [ih]
    rfl

theorem po_genTraj_succ (D : po_Det S A) (g : ℕ → S → A) (s : S) (j : ℕ) :
    po_genTraj D g s (j + 1) =
      po_genTraj (po_detShift D 1) (fun i => g (i + 1)) (D.f 0 (s, g 0 s)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change D.f (j + 1) (po_genTraj D g s (j + 1), g (j + 1) (po_genTraj D g s (j + 1))) = _
    rw [ih]
    rfl

theorem po_genSeq_tail (D : po_Det S A) (g : ℕ → S → A) (s : S) :
    (fun i => po_genSeq D g s (i + 1)) =
      po_genSeq (po_detShift D 1) (fun i => g (i + 1)) (D.f 0 (s, g 0 s)) := by
  funext i
  simp only [po_genSeq, po_genTraj_succ]

/-- The induction behind the deterministic Theorem 6.3.2, at date `0` with horizon `n`. -/
theorem po_det_verification_core :
    ∀ (n : ℕ) (D : po_Det S A) (w : ℕ → S → ℝ) (g : ℕ → S → A), 0 ≤ D.β →
      (∀ j < n, ∀ s, ∀ a ∈ D.Γ s, D.u j (s, a) + D.β * w (j + 1) (D.f j (s, a)) ≤ w j s) →
      (∀ j < n, ∀ s, g j s ∈ D.Γ s ∧
        w j s = D.u j (s, g j s) + D.β * w (j + 1) (D.f j (s, g j s))) →
      (∀ s, w n s = D.uT s) → ∀ s,
      (∀ a ∈ po_detFeasible D n s, po_detJ D n s a ≤ w 0 s) ∧
      po_genSeq D g s ∈ po_detFeasible D n s ∧ po_detJ D n s (po_genSeq D g s) = w 0 s := by
  intro n
  induction n with
  | zero =>
    intro D w g _ _ _ hwT s
    exact ⟨fun a _ => by rw [po_detJ_zero, hwT], fun j hj => absurd hj (Nat.not_lt_zero j),
      by rw [po_detJ_zero, hwT]⟩
  | succ n ih =>
    intro D w g hβ hB1 hB2 hwT s
    have IH := ih (po_detShift D 1) (fun j => w (j + 1)) (fun j => g (j + 1)) hβ
      (fun j hj s a ha => hB1 (j + 1) (by omega) s a ha)
      (fun j hj s => hB2 (j + 1) (by omega) s) (fun s => hwT s)
    obtain ⟨hg0, heq⟩ := hB2 0 (Nat.succ_pos n) s
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · obtain ⟨h0, h1⟩ := (po_detFeasible_succ D n s a).1 ha
      rw [po_detJ_succ]
      exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ((IH _).1 _ h1) hβ))
        (hB1 0 (Nat.succ_pos n) s _ h0)
    · refine (po_detFeasible_succ D n s _).2 ⟨hg0, ?_⟩
      rw [po_genSeq_tail]
      exact (IH _).2.1
    · rw [po_detJ_succ, po_genSeq_tail]
      change D.u 0 (s, g 0 s) + D.β * po_detJ (po_detShift D 1) n (D.f 0 (s, g 0 s)) _ = w 0 s
      rw [(IH _).2.2]
      exact heq.symm

/-- **Exercise 6.1: Theorem 6.3.2, deterministic** (Miao, p. 189). If `w` solves the Bellman
equation with `w_T = u_T` and `g_t(s)` is any maximiser (`g_t(s) ∈ G_t(s)`), then for every
`t ≤ T` and `s` the action sequence generated by `g` from `s` at date `t` is feasible, attains
`w_t(s)`, and `w_t(s) = V_t(s)`. No measurability of `g_t` is needed. -/
theorem ex_6_1_theorem_6_3_2 {D : po_Det S A} (hβ : 0 ≤ D.β) {T : ℕ} {w : ℕ → S → ℝ}
    {g : ℕ → S → A}
    (hB1 : ∀ t < T, ∀ s, ∀ a ∈ D.Γ s, D.u t (s, a) + D.β * w (t + 1) (D.f t (s, a)) ≤ w t s)
    (hB2 : ∀ t < T, ∀ s, g t s ∈ D.Γ s ∧
      w t s = D.u t (s, g t s) + D.β * w (t + 1) (D.f t (s, g t s)))
    (hwT : ∀ s, w T s = D.uT s) (t : ℕ) (ht : t ≤ T) (s : S) :
    po_genSeq (po_detShift D t) (fun j => g (j + t)) s ∈
        po_detFeasible (po_detShift D t) (T - t) s ∧
      po_detJ (po_detShift D t) (T - t) s (po_genSeq (po_detShift D t) (fun j => g (j + t)) s) =
        w t s ∧
      po_detVt D T t s = w t s := by
  have e : ∀ j, j + 1 + t = j + t + 1 := fun j => by omega
  have hc := po_det_verification_core (T - t) (po_detShift D t) (fun j => w (j + t))
    (fun j => g (j + t)) hβ
    (fun j hj s a ha => by
      have := hB1 (j + t) (by omega) s a ha
      simp only [e]
      exact this)
    (fun j hj s => by
      have := hB2 (j + t) (by omega) s
      simp only [e]
      exact this)
    (fun s => by simp only [Nat.sub_add_cancel ht]; exact hwT s) s
  simp only [zero_add] at hc
  refine ⟨hc.2.1, hc.2.2, le_antisymm (iSup₂_le fun a ha => EReal.coe_le_coe_iff.2
    (hc.1 a ha)) ?_⟩
  rw [← hc.2.2]
  exact po_detJ_le_V hc.2.1

/-- The policy correspondence `G_t(s)` of a deterministic Bellman equation. -/
def po_detG (D : po_Det S A) (w : ℕ → S → ℝ) (t : ℕ) (s : S) : Set A :=
  {a | a ∈ D.Γ s ∧ D.u t (s, a) + D.β * w (t + 1) (D.f t (s, a)) = w t s}

/-- The induction behind the deterministic Theorem 6.3.3, at date `0` with horizon `n`: an
optimal sequence takes actions in `G_j` at every date along its path, and its continuation from
`s_j` is optimal at date `j`. -/
theorem po_det_converse_core :
    ∀ (n : ℕ) (D : po_Det S A) (w : ℕ → S → ℝ), 0 < D.β →
      (∀ j ≤ n, ∀ s, po_detV (po_detShift D j) (n - j) s = w j s) →
      (∀ j < n, ∀ s, ∀ a ∈ D.Γ s, D.u j (s, a) + D.β * w (j + 1) (D.f j (s, a)) ≤ w j s) →
      ∀ (s : S) (a : ℕ → A), a ∈ po_detFeasible D n s → po_detJ D n s a = w 0 s →
      (∀ j < n, a j ∈ po_detG D w j (po_traj D s a j)) ∧
      ∀ j ≤ n, po_detJ (po_detShift D j) (n - j) (po_traj D s a j) (fun i => a (i + j)) =
        w j (po_traj D s a j) := by
  intro n
  induction n with
  | zero =>
    intro D w _ _ _ s a _ hopt
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    exact hopt
  | succ n ih =>
    intro D w hβ hV hB s a ha hopt
    obtain ⟨h0, h1⟩ := (po_detFeasible_succ D n s a).1 ha
    set x := D.f 0 (s, a 0)
    have hJ' : po_detJ (po_detShift D 1) n x (fun i => a (i + 1)) ≤ w 1 x := by
      have h2 := po_detJ_le_V h1
      have h3 := hV 1 (by omega) x
      simp only [Nat.add_sub_cancel] at h3
      rw [h3] at h2
      exact EReal.coe_le_coe_iff.1 h2
    have hrec := po_detJ_succ D n s a
    rw [hopt] at hrec
    have hle := hB 0 (Nat.succ_pos n) s _ h0
    have hEq : po_detJ (po_detShift D 1) n x (fun i => a (i + 1)) = w 1 x := by
      by_contra hne
      have hlt := lt_of_le_of_ne hJ' hne
      have := mul_lt_mul_of_pos_left hlt hβ
      linarith
    have IH := ih (po_detShift D 1) (fun j => w (j + 1)) hβ
      (fun k hk s => by
        rw [po_detShift_shift, Nat.add_comm 1 k]
        have := hV (k + 1) (by omega) s
        rwa [show n + 1 - (k + 1) = n - k by omega] at this)
      (fun k hk s a ha => hB (k + 1) (by omega) s a ha) x _ h1 hEq
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero =>
        refine ⟨h0, ?_⟩
        change D.u 0 (s, a 0) + D.β * w 1 x = w 0 s
        rw [← hEq]
        linarith
      | succ j =>
        have := IH.1 j (by omega)
        rw [po_traj_succ]
        exact this
    · cases j with
      | zero =>
        simp only [Nat.sub_zero, Nat.add_zero]
        exact hopt
      | succ j =>
        have := IH.2 j (by omega)
        rw [po_detShift_shift, Nat.add_comm 1 j, show n - j = n + 1 - (j + 1) by omega,
          ← po_traj_succ] at this
        have ha' : (fun i => a (i + j + 1)) = fun i => a (i + (j + 1)) := by
          funext i
          rw [show i + j + 1 = i + (j + 1) by omega]
        simp only [ha'] at this
        exact this

/-- **Exercise 6.1: Theorem 6.3.3, deterministic** (Miao, p. 189). If the value functions
`V_t = w_t` are finite and satisfy the Bellman equation, and `β > 0`, then any optimal action
sequence `a*` from `s₀` satisfies `a*_t ∈ G_t(s*_t)` at **every** date `t < T` along its path
`s*_t` (no "almost every"), and its continuation from `s*_t` is optimal for the problem from
date `t` (time consistency). -/
theorem ex_6_1_theorem_6_3_3 {D : po_Det S A} (hβ : 0 < D.β) {T : ℕ} {w : ℕ → S → ℝ}
    (hV : ∀ t ≤ T, ∀ s, po_detVt D T t s = w t s)
    (hB : ∀ t < T, ∀ s, (w t s : EReal) =
      ⨆ a ∈ D.Γ s, ((D.u t (s, a) + D.β * w (t + 1) (D.f t (s, a)) : ℝ) : EReal))
    {s₀ : S} {a : ℕ → A} (ha : a ∈ po_detFeasible D T s₀)
    (hopt : po_detJ D T s₀ a = po_detVt D T 0 s₀) :
    (∀ t < T, a t ∈ po_detG D w t (po_traj D s₀ a t)) ∧
      ∀ t ≤ T, (po_detJ (po_detShift D t) (T - t) (po_traj D s₀ a t) (fun i => a (i + t)) :
        EReal) = po_detVt D T t (po_traj D s₀ a t) := by
  have hB1 : ∀ t < T, ∀ s, ∀ b ∈ D.Γ s, D.u t (s, b) + D.β * w (t + 1) (D.f t (s, b)) ≤
      w t s := fun t ht s b hb => by
    have := le_iSup₂_of_le (f := fun b (_ : b ∈ D.Γ s) =>
      ((D.u t (s, b) + D.β * w (t + 1) (D.f t (s, b)) : ℝ) : EReal)) b hb le_rfl
    rw [← hB t ht s] at this
    exact EReal.coe_le_coe_iff.1 this
  have hopt' : po_detJ D T s₀ a = w 0 s₀ := by
    have := hV 0 (Nat.zero_le T) s₀
    rw [← hopt] at this
    exact EReal.coe_eq_coe_iff.1 this
  have hc := po_det_converse_core T D w hβ (fun j hj s => hV j hj s) hB1 s₀ a ha hopt'
  refine ⟨hc.1, fun t ht => ?_⟩
  rw [hc.2 t ht, hV t ht]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A motivating example: the finite-horizon log/Cobb–Douglas planner

Miao, §6.1, pp. 157–160: `max ∑_{t=0}^T βᵗ ln C_t` subject to `C_t + K_{t+1} = K_t^α`, `K₀`
given, with `α, β ∈ (0, 1)`. Write `n = T − t` for the number of periods to go and `p = αβ`.

* The savings rate `θ_n = αβ(1 − pⁿ)/(1 − p^{n+1})` of (6.3)–(6.4) (`po61_theta`), the
  coefficient `α(1 − p^{n+1})/(1 − p)` of (6.5) (`po61_coef`), `b_t` of (6.6) (`po61_b`) and
  `A_t` (`po61_A`), with `A_t = βA_{t+1} + b_t`, `A_T = 0` (`po61_A_succ`, `po61_A_terminal`).
* **The Euler equation and (6.3)**: the path `K_{t+1} = θ_{T−t} K_t^α` (`po61_path`) is positive,
  feasible, satisfies the second-order Euler equation and `K_{T+1} = 0` (`eq_6_3`); and it is the
  only positive feasible path satisfying them (`eq_6_3_unique`), which is the book's "using these
  two conditions we obtain".
* **The problem as a deterministic dynamic program** (`po61_model`, states and actions in
  `(0, ∞)`): the value functions (6.5) with `b_t` from (6.6) satisfy the Bellman equation
  `V_t(K) = max_{0 < K' < K^α} ln(K^α − K') + βV_{t+1}(K')` as a proved maximisation, with the
  unique maximiser `K' = θ_{T−t}K^α` (`po61_bellman`); by Exercise 6.1 (the deterministic
  Theorem 6.3.2) they **are** the values of the sequence problems, and the plan generated by the
  policy functions is optimal (`eq_6_5_6_6`, `eq_6_4`).
* The last two periods: (6.7) (`eq_6_7`) and (6.8) (`eq_6_8`).
* The remarks of p. 160 (`time_consistency_6_1`): (i) the value functions satisfy the Bellman
  equation; (ii) every optimal plan is the one generated by the policy functions, and the plan
  made at date `0` remains optimal at every later date from the capital it leads to.

**Corrections.**
1. The printed `C_{T−1} = K_T^{α−1}/(1 + αβ)` is wrong; it is `C_{T−1} = K_{T−1}^α/(1 + αβ)`
   (`eq_6_8`; `eq_6_8_misprint` shows the printed formula fails for every `α, β`).
2. The Euler equation holds for `t = 0, …, T − 1`, not `t = 0, …, T` as printed (at `t = T` it
   would involve `K_{T+1}^{α−1}` with `K_{T+1} = 0`).
3. (6.3)–(6.6), `b_t` and `A_T = 0` are correct as printed (with `n = T − t ≥ 1` in (6.6); `b_t`
   is used only for `t < T`).
-/

namespace Miao.FiniteHorizonDP


/-- The savings rate `θ_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)^{n+1})` with `n = T − t` periods to go
(Miao (6.3)–(6.4)): `K_{t+1} = θ_{T−t} K_t^α`. -/
noncomputable def po61_theta (α β : ℝ) (n : ℕ) : ℝ :=
  α * β * (1 - (α * β) ^ n) / (1 - (α * β) ^ (n + 1))

/-- The coefficient of `ln K_t` in (6.5): `α(1 − (αβ)^{n+1})/(1 − αβ)`, `n = T − t`. -/
noncomputable def po61_coef (α β : ℝ) (n : ℕ) : ℝ := α * (1 - (α * β) ^ (n + 1)) / (1 - α * β)

/-- `b_t` of (6.6), as a function of `n = T − t`. -/
noncomputable def po61_b (α β : ℝ) (n : ℕ) : ℝ :=
  Real.log ((1 - α * β) / (1 - (α * β) ^ (n + 1))) +
    α * β * (1 - (α * β) ^ n) / (1 - α * β) *
      (Real.log (α * β) + Real.log ((1 - (α * β) ^ n) / (1 - (α * β) ^ (n + 1))))

/-- `A_t = ∑_{j=t}^{T−1} β^{j−t} b_j`, the solution of `A_t = βA_{t+1} + b_t`, `A_T = 0`. -/
noncomputable def po61_A (α β : ℝ) (T t : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico t T, β ^ (j - t) * po61_b α β (T - j)

/-- The value function (6.5): `V_t(K) = α(1 − (αβ)^{T−t+1})/(1 − αβ) · ln K + A_t`. -/
noncomputable def po61_V (α β : ℝ) (T t : ℕ) (K : ℝ) : ℝ :=
  po61_coef α β (T - t) * Real.log K + po61_A α β T t

/-- Miao, p. 158: `A_T = 0`. -/
theorem po61_A_terminal (α β : ℝ) (T : ℕ) : po61_A α β T T = 0 := by
  simp [po61_A]

/-- Miao, p. 158: `A_t = βA_{t+1} + b_t` for `t < T`. -/
theorem po61_A_succ (α β : ℝ) {T t : ℕ} (ht : t < T) :
    po61_A α β T t = β * po61_A α β T (t + 1) + po61_b α β (T - t) := by
  unfold po61_A
  rw [Finset.sum_eq_sum_Ico_succ_bot ht, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum,
    add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_Ico.1 hj
  rw [show j - t = (j - (t + 1)) + 1 by omega, pow_succ]
  ring

/-- The standing hypotheses `α, β ∈ (0, 1)`. -/
structure po61_Params (α β : ℝ) : Prop where
  α_pos : 0 < α
  α_lt : α < 1
  β_pos : 0 < β
  β_lt : β < 1

theorem po61_Params.p_pos {α β : ℝ} (h : po61_Params α β) : 0 < α * β :=
  mul_pos h.α_pos h.β_pos

theorem po61_Params.p_lt {α β : ℝ} (h : po61_Params α β) : α * β < 1 := by
  have := mul_lt_mul'' h.α_lt h.β_lt h.α_pos.le h.β_pos.le
  simpa using this

theorem po61_pow_lt {α β : ℝ} (h : po61_Params α β) (n : ℕ) : (α * β) ^ (n + 1) < 1 :=
  pow_lt_one₀ h.p_pos.le h.p_lt (Nat.succ_ne_zero n)

theorem po61_den_pos {α β : ℝ} (h : po61_Params α β) (n : ℕ) : 0 < 1 - (α * β) ^ (n + 1) := by
  linarith [po61_pow_lt h n]

theorem po61_coef_pos {α β : ℝ} (h : po61_Params α β) (n : ℕ) : 0 < po61_coef α β n :=
  div_pos (mul_pos h.α_pos (po61_den_pos h n)) (by linarith [h.p_lt])

theorem po61_theta_zero (α β : ℝ) : po61_theta α β 0 = 0 := by simp [po61_theta]

theorem po61_one_sub_frac (p r : ℝ) (h : 1 - r * p ≠ 0) :
    1 - p * (1 - r) / (1 - r * p) = (1 - p) / (1 - r * p) := by
  rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

theorem po61_one_add_frac (p q : ℝ) (h : 1 - p ≠ 0) :
    1 + p * (1 - q) / (1 - p) = (1 - q * p) / (1 - p) := by
  rw [eq_div_iff h, add_mul, div_mul_cancel₀ _ h]
  ring

/-- `1 − θ_m = (1 − αβ)/(1 − (αβ)^{m+1})`. -/
theorem po61_one_sub_theta {α β : ℝ} (h : po61_Params α β) (m : ℕ) :
    1 - po61_theta α β m = (1 - α * β) / (1 - (α * β) ^ (m + 1)) := by
  have hd := (po61_den_pos h m).ne'
  unfold po61_theta
  rw [pow_succ] at hd ⊢
  exact po61_one_sub_frac (α * β) ((α * β) ^ m) hd

theorem po61_beta_coef (α β : ℝ) (n : ℕ) :
    β * po61_coef α β n = α * β * (1 - (α * β) ^ (n + 1)) / (1 - α * β) := by
  unfold po61_coef
  ring

theorem po61_one_add_c {α β : ℝ} (h : po61_Params α β) (n : ℕ) :
    1 + β * po61_coef α β n = (1 - (α * β) ^ (n + 1 + 1)) / (1 - α * β) := by
  have hp1 : 1 - α * β ≠ 0 := by linarith [h.p_lt]
  rw [po61_beta_coef, po61_one_add_frac _ _ hp1, pow_succ (α * β) (n + 1)]

/-- `θ_{n+1} = c/(1 + c)` and `1 − θ_{n+1} = 1/(1 + c)`, where `c = β · coef_n`. -/
theorem po61_theta_succ {α β : ℝ} (h : po61_Params α β) (n : ℕ) :
    po61_theta α β (n + 1) = β * po61_coef α β n / (1 + β * po61_coef α β n) ∧
      1 - po61_theta α β (n + 1) = 1 / (1 + β * po61_coef α β n) := by
  have hp1 : 1 - α * β ≠ 0 := by linarith [h.p_lt]
  refine ⟨?_, ?_⟩
  · rw [po61_one_add_c h n, po61_beta_coef, div_div_div_cancel_right₀ hp1]
    rfl
  · rw [po61_one_sub_theta h, po61_one_add_c h n, one_div_div]

theorem po61_theta_pos {α β : ℝ} (h : po61_Params α β) (n : ℕ) : 0 < po61_theta α β (n + 1) := by
  rw [(po61_theta_succ h n).1]
  have hc := po61_coef_pos h n
  exact div_pos (mul_pos h.β_pos hc) (by nlinarith [h.β_pos])

theorem po61_theta_lt_one {α β : ℝ} (h : po61_Params α β) (n : ℕ) : po61_theta α β n < 1 := by
  have := po61_one_sub_theta h n
  have h1 : 0 < (1 - α * β) / (1 - (α * β) ^ (n + 1)) :=
    div_pos (by linarith [h.p_lt]) (po61_den_pos h n)
  linarith

/-- `coef_{n+1} = α(1 + β coef_n)`. -/
theorem po61_coef_succ {α β : ℝ} (h : po61_Params α β) (n : ℕ) :
    po61_coef α β (n + 1) = α * (1 + β * po61_coef α β n) := by
  rw [po61_one_add_c h n]
  unfold po61_coef
  ring

/-- `b_{n+1} = −(1 + c) ln(1 + c) + c ln c` with `c = β coef_n`: (6.6) is
`ln(1 − θ_{n+1}) + c ln θ_{n+1}`. -/
theorem po61_b_succ {α β : ℝ} (h : po61_Params α β) (n : ℕ) :
    po61_b α β (n + 1) = -((1 + β * po61_coef α β n) * Real.log (1 + β * po61_coef α β n)) +
      β * po61_coef α β n * Real.log (β * po61_coef α β n) := by
  have hp0 := h.p_pos
  have hp1 : 1 - α * β ≠ 0 := by linarith [h.p_lt]
  have hd1 := po61_den_pos h n
  have hd2 := po61_den_pos h (n + 1)
  have hc := po61_coef_pos h n
  have hcpos : 0 < β * po61_coef α β n := mul_pos h.β_pos hc
  have hc1 : 0 < 1 + β * po61_coef α β n := by linarith
  have e1 : (1 - α * β) / (1 - (α * β) ^ (n + 1 + 1)) = 1 / (1 + β * po61_coef α β n) := by
    rw [po61_one_add_c h n, one_div_div]
  have e2 : α * β * (1 - (α * β) ^ (n + 1)) / (1 - α * β) = β * po61_coef α β n :=
    (po61_beta_coef α β n).symm
  have e3 : Real.log (α * β) + Real.log ((1 - (α * β) ^ (n + 1)) / (1 - (α * β) ^ (n + 1 + 1))) =
      Real.log (β * po61_coef α β n) - Real.log (1 + β * po61_coef α β n) := by
    rw [← Real.log_mul hp0.ne' (div_pos hd1 hd2).ne', ← Real.log_div hcpos.ne' hc1.ne',
      ← (po61_theta_succ h n).1]
    unfold po61_theta
    rw [mul_div_assoc]
  unfold po61_b
  rw [e1, e2, e3, one_div, Real.log_inv]
  ring

/-- The two-period maximisation behind the Bellman equation of §6.1: for `y > 0`, `c > 0`,
`0 < x < y`, `ln(y − x) + c ln x ≤ (1 + c) ln y − (1 + c) ln(1 + c) + c ln c`, with equality at
`x = c y/(1 + c)` and strict inequality elsewhere. -/
theorem po61_max {y c x : ℝ} (hy : 0 < y) (hc : 0 < c) (hx0 : 0 < x) (hxy : x < y) :
    Real.log (y - x) + c * Real.log x ≤
      (1 + c) * Real.log y - (1 + c) * Real.log (1 + c) + c * Real.log c ∧
    (x ≠ c * y / (1 + c) → Real.log (y - x) + c * Real.log x <
      (1 + c) * Real.log y - (1 + c) * Real.log (1 + c) + c * Real.log c) := by
  have hc1 : 0 < 1 + c := by linarith
  set xs := c * y / (1 + c) with hxs
  have hxs0 : 0 < xs := by positivity
  have hyx : 0 < y - xs := by
    rw [hxs]
    have : y - c * y / (1 + c) = y / (1 + c) := by field_simp; ring
    rw [this]
    positivity
  have hval : Real.log (y - xs) + c * Real.log xs =
      (1 + c) * Real.log y - (1 + c) * Real.log (1 + c) + c * Real.log c := by
    have h1 : y - xs = y / (1 + c) := by rw [hxs]; field_simp; ring
    have h2 : xs = c * (y / (1 + c)) := by rw [hxs]; ring
    rw [h1, h2, Real.log_mul hc.ne' (by positivity), Real.log_div hy.ne' hc1.ne']
    ring
  have hr1 : 0 < (y - x) / (y - xs) := div_pos (by linarith) hyx
  have hr2 : 0 < x / xs := div_pos hx0 hxs0
  have hsum : ((y - x) / (y - xs) - 1) + c * (x / xs - 1) = 0 := by
    have h1 : y - xs = y / (1 + c) := by rw [hxs]; field_simp; ring
    rw [h1, hxs]
    field_simp
    ring
  have hdecomp : Real.log (y - x) + c * Real.log x = Real.log (y - xs) + c * Real.log xs +
      (Real.log ((y - x) / (y - xs)) + c * Real.log (x / xs)) := by
    rw [Real.log_div (by linarith) hyx.ne', Real.log_div hx0.ne' hxs0.ne']
    ring
  have hle1 := Real.log_le_sub_one_of_pos hr1
  have hle2 := Real.log_le_sub_one_of_pos hr2
  refine ⟨?_, fun hne => ?_⟩
  · rw [hdecomp, ← hval]
    nlinarith
  · have hne' : x / xs ≠ 1 := by
      intro h1
      exact hne ((div_eq_one_iff_eq hxs0.ne').1 h1)
    have hlt2 := Real.log_lt_sub_one_of_pos hr2 hne'
    rw [hdecomp, ← hval]
    nlinarith

/-- The positive reals, the state and action space of §6.1. -/
abbrev po61_Pos := {x : ℝ // 0 < x}

/-- §6.1 as a deterministic problem (Exercise 6.1's model): the state is `K_t > 0`, the action is
`K_{t+1} ∈ (0, K_t^α)`, the reward is `ln C_t = ln(K_t^α − K_{t+1})` and the terminal reward is
`V_T(K_T) = α ln K_T`, the value of the last-period problem (6.7) (`eq_6_7`). -/
noncomputable def po61_model (α β : ℝ) : po_Det po61_Pos po61_Pos where
  Γ := fun K => {K' | K'.1 < K.1 ^ α}
  f := fun _ x => x.2
  u := fun _ x => Real.log (x.1.1 ^ α - x.2.1)
  uT := fun K => α * Real.log K.1
  β := β

theorem po61_policy_pos {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t < T) (K : ℝ)
    (hK : 0 < K) :
    0 < po61_theta α β (T - t) * K ^ α := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  rw [hn]
  exact mul_pos (po61_theta_pos h n) (Real.rpow_pos_of_pos hK α)

/-- The policy functions `g_t(K) = θ_{T−t} K^α` (for `t < T`; any value at `t ≥ T`). -/
noncomputable def po61_g {α β : ℝ} (h : po61_Params α β) (T t : ℕ) (K : po61_Pos) : po61_Pos :=
  if ht : t < T then ⟨po61_theta α β (T - t) * K.1 ^ α, po61_policy_pos h ht K.1 K.2⟩ else K

/-- **The Bellman equation of §6.1** (Miao, p. 160), as a proved maximisation: for `t < T` and
`K > 0`, `ln(K^α − K') + βV_{t+1}(K') ≤ V_t(K)` for every feasible `K' ∈ (0, K^α)`, with
equality at `K' = g_t(K) = θ_{T−t}K^α` and strict inequality at every other `K'`. -/
theorem po61_bellman {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t < T) {K : ℝ}
    (hK : 0 < K) :
    (∀ K' : ℝ, 0 < K' → K' < K ^ α →
      Real.log (K ^ α - K') + β * po61_V α β T (t + 1) K' ≤ po61_V α β T t K) ∧
    (0 < po61_theta α β (T - t) * K ^ α ∧ po61_theta α β (T - t) * K ^ α < K ^ α ∧
      Real.log (K ^ α - po61_theta α β (T - t) * K ^ α) +
        β * po61_V α β T (t + 1) (po61_theta α β (T - t) * K ^ α) = po61_V α β T t K) ∧
    (∀ K' : ℝ, 0 < K' → K' < K ^ α → K' ≠ po61_theta α β (T - t) * K ^ α →
      Real.log (K ^ α - K') + β * po61_V α β T (t + 1) K' < po61_V α β T t K) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hy : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hc := mul_pos h.β_pos (po61_coef_pos h n)
  set c := β * po61_coef α β n with hcdef
  have hlogy : Real.log (K ^ α) = α * Real.log K := Real.log_rpow hK α
  have hVt : po61_V α β T t K = (1 + c) * Real.log (K ^ α) - (1 + c) * Real.log (1 + c) +
      c * Real.log c + β * po61_A α β T (t + 1) := by
    unfold po61_V
    rw [po61_A_succ α β ht, hn, po61_coef_succ h n, po61_b_succ h n, hlogy, ← hcdef]
    ring
  have hrhs : ∀ K', β * po61_V α β T (t + 1) K' = c * Real.log K' + β * po61_A α β T (t + 1) :=
    fun K' => by unfold po61_V; rw [hn', hcdef]; ring
  have hθ : po61_theta α β (T - t) * K ^ α = c * K ^ α / (1 + c) := by
    rw [hn, (po61_theta_succ h n).1, ← hcdef]
    ring
  have hθlt : po61_theta α β (T - t) * K ^ α < K ^ α := by
    rw [hθ, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨fun K' hK' hK'y => ?_, ⟨po61_policy_pos h ht K hK, hθlt, ?_⟩,
    fun K' hK' hK'y hne => ?_⟩
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).1
    linarith
  · rw [hrhs, hVt, hθ]
    have hxs0 : 0 < c * K ^ α / (1 + c) := by positivity
    have h1 : K ^ α - c * K ^ α / (1 + c) = K ^ α / (1 + c) := by field_simp; ring
    have h2 : c * K ^ α / (1 + c) = c * (K ^ α / (1 + c)) := by ring
    rw [h1, h2, Real.log_mul hc.ne' (by positivity), Real.log_div hy.ne' (by linarith)]
    ring
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).2 (by rw [← hθ]; exact hne)
    linarith

/-- The Bellman equation of `po61_model` in the form of Exercise 6.1: inequality for every
feasible action and equality at the policy `g_t`. -/
theorem po61_model_bellman {α β : ℝ} (h : po61_Params α β) (T : ℕ) :
    (∀ t < T, ∀ K, ∀ K' ∈ (po61_model α β).Γ K,
      (po61_model α β).u t (K, K') +
        (po61_model α β).β * po61_V α β T (t + 1) ((po61_model α β).f t (K, K')).1 ≤
          po61_V α β T t K.1) ∧
    (∀ t < T, ∀ K, po61_g h T t K ∈ (po61_model α β).Γ K ∧
      po61_V α β T t K.1 = (po61_model α β).u t (K, po61_g h T t K) +
        (po61_model α β).β * po61_V α β T (t + 1)
          ((po61_model α β).f t (K, po61_g h T t K)).1) ∧
    (∀ K, po61_V α β T T K.1 = (po61_model α β).uT K) := by
  refine ⟨fun t ht K K' hK' => ?_, fun t ht K => ?_, fun K => ?_⟩
  · exact (po61_bellman h ht K.2).1 K'.1 K'.2 hK'
  · obtain ⟨-, ⟨-, hlt, heq⟩, -⟩ := po61_bellman h ht K.2
    simp only [po61_g, ht, ↓reduceDIte]
    exact ⟨hlt, heq.symm⟩
  · have hp1 : (1 - α * β) ≠ 0 := by linarith [h.p_lt]
    simp only [po61_V, Nat.sub_self, po61_A_terminal, po61_coef, zero_add, pow_one,
      po61_model, add_zero]
    field_simp

/-- **(6.5)–(6.6)** (Miao, p. 158). For `t ≤ T` and `K > 0`, the value of the sequence problem
from date `t` is `V_t(K) = α(1 − (αβ)^{T−t+1})/(1 − αβ) · ln K + A_t`, with `A_t = βA_{t+1} + b_t`,
`A_T = 0` and `b_t` as in (6.6); the plan generated by `g` is optimal. Proved via Exercise 6.1
(the deterministic Theorem 6.3.2). -/
theorem eq_6_5_6_6 {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t ≤ T) (K : po61_Pos) :
    po_detVt (po61_model α β) T t K = po61_V α β T t K.1 := by
  obtain ⟨hB1, hB2, hT⟩ := po61_model_bellman h T
  exact (ex_6_1_theorem_6_3_2 (D := po61_model α β) (w := fun t K => po61_V α β T t K.1)
    h.β_pos.le hB1 hB2 hT t ht K).2.2

/-- **(6.4)** (Miao, p. 158): the plan generated by the policy functions from `K_t` at date `t` is
optimal for the date-`t` problem, and its capital path is
`K_{t+1+j} = θ_{T−t−j} K_{t+j}^α` for `t + j < T`. -/
theorem eq_6_4 {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t ≤ T) (K : po61_Pos) :
    let D := po_detShift (po61_model α β) t
    let a := po_genSeq D (fun j => po61_g h T (j + t)) K
    a ∈ po_detFeasible D (T - t) K ∧
      (po_detJ D (T - t) K a : EReal) = po_detVt (po61_model α β) T t K ∧
      ∀ j, j + t < T → (po_traj D K a (j + 1)).1 =
        po61_theta α β (T - (j + t)) * (po_traj D K a j).1 ^ α := by
  intro D a
  obtain ⟨hB1, hB2, hT⟩ := po61_model_bellman h T
  have hv := ex_6_1_theorem_6_3_2 (D := po61_model α β) (w := fun t K => po61_V α β T t K.1)
    (g := po61_g h T) h.β_pos.le hB1 hB2 hT t ht K
  refine ⟨hv.1, by rw [hv.2.1, hv.2.2], fun j hj => ?_⟩
  rw [po_traj_genSeq, po_traj_genSeq]
  change (po61_g h T (j + t) (po_genTraj D (fun j => po61_g h T (j + t)) K j)).1 = _
  simp only [po61_g, hj, ↓reduceDIte]

/-- The path of (6.3): `K₀` given, `K_{t+1} = θ_{T−t} K_t^α` (so `K_{T+1} = 0`). -/
noncomputable def po61_path (α β : ℝ) (T : ℕ) (K₀ : ℝ) : ℕ → ℝ
  | 0 => K₀
  | t + 1 => po61_theta α β (T - t) * po61_path α β T K₀ t ^ α

/-- `αβ(1 − θ_{m+1}) = θ_{m+1}(1 − θ_m)`, the identity behind the Euler equation. -/
theorem po61_theta_euler {α β : ℝ} (h : po61_Params α β) (m : ℕ) :
    α * β * (1 - po61_theta α β (m + 1)) = po61_theta α β (m + 1) * (1 - po61_theta α β m) := by
  have hd1 := (po61_den_pos h m).ne'
  have hd2 := (po61_den_pos h (m + 1)).ne'
  rw [po61_one_sub_theta h, po61_one_sub_theta h]
  unfold po61_theta
  rw [mul_div_assoc', div_mul_div_comm, div_eq_div_iff hd2 (mul_ne_zero hd2 hd1)]
  ring

/-- `αβ/(1 + αβ − θ_m) = θ_{m+1}`, which solves the Euler equation backward. -/
theorem po61_theta_back {α β : ℝ} (h : po61_Params α β) (m : ℕ) :
    0 < 1 + α * β - po61_theta α β m ∧
      α * β / (1 + α * β - po61_theta α β m) = po61_theta α β (m + 1) := by
  have hlt := po61_theta_lt_one h m
  have hp := h.p_pos
  refine ⟨by linarith, ?_⟩
  have hd1 := (po61_den_pos h m).ne'
  have e : 1 + α * β - po61_theta α β m =
      (1 - (α * β) ^ (m + 1) * (α * β)) / (1 - (α * β) ^ (m + 1)) := by
    rw [show 1 + α * β - po61_theta α β m = α * β + (1 - po61_theta α β m) by ring,
      po61_one_sub_theta h, eq_div_iff hd1, add_mul, div_mul_cancel₀ _ hd1]
    ring
  rw [e, div_div_eq_mul_div]
  unfold po61_theta
  rw [pow_succ (α * β) (m + 1)]

/-- **(6.3) and the Euler equation** (Miao, p. 158). For `K₀ > 0`, the path
`K_{t+1} = αβ(1 − (αβ)^{T−t})/(1 − (αβ)^{T−t+1}) K_t^α` has `K_t > 0` and
`0 < K_{t+1} < K_t^α` for `t < T` and `K_{T+1} = 0`, and satisfies the second-order Euler
equation `1/(K_t^α − K_{t+1}) = βαK_{t+1}^{α−1}/(K_{t+1}^α − K_{t+2})` for `t = 0, …, T − 1`. -/
theorem eq_6_3 {α β : ℝ} (h : po61_Params α β) (T : ℕ) {K₀ : ℝ} (hK₀ : 0 < K₀) :
    (∀ t ≤ T, 0 < po61_path α β T K₀ t) ∧
    (∀ t < T, po61_path α β T K₀ (t + 1) < po61_path α β T K₀ t ^ α) ∧
    po61_path α β T K₀ (T + 1) = 0 ∧
    ∀ t < T, 1 / (po61_path α β T K₀ t ^ α - po61_path α β T K₀ (t + 1)) =
      β * α * po61_path α β T K₀ (t + 1) ^ (α - 1) /
        (po61_path α β T K₀ (t + 1) ^ α - po61_path α β T K₀ (t + 2)) := by
  have hpos : ∀ t ≤ T, 0 < po61_path α β T K₀ t := by
    intro t
    induction t with
    | zero => intro _; exact hK₀
    | succ t ih =>
      intro ht
      exact po61_policy_pos h (by omega) _ (ih (by omega))
  have hlt : ∀ t < T, po61_path α β T K₀ (t + 1) < po61_path α β T K₀ t ^ α := fun t ht => by
    change po61_theta α β (T - t) * _ < _
    have hy := Real.rpow_pos_of_pos (hpos t ht.le) α
    nlinarith [po61_theta_lt_one h (T - t)]
  refine ⟨hpos, hlt, ?_, fun t ht => ?_⟩
  · change po61_theta α β (T - T) * _ = 0
    rw [Nat.sub_self, po61_theta_zero, zero_mul]
  · obtain ⟨m, hm⟩ : ∃ m, T - t = m + 1 := ⟨T - t - 1, by omega⟩
    have hm' : T - (t + 1) = m := by omega
    set y := po61_path α β T K₀ t ^ α with hydef
    have hy : 0 < y := Real.rpow_pos_of_pos (hpos t ht.le) α
    have hx : po61_path α β T K₀ (t + 1) = po61_theta α β (m + 1) * y := by
      change po61_theta α β (T - t) * _ = _
      rw [hm]
    have hx2 : po61_path α β T K₀ (t + 2) =
        po61_theta α β m * po61_path α β T K₀ (t + 1) ^ α := by
      change po61_theta α β (T - (t + 1)) * _ = _
      rw [hm']
    set x := po61_path α β T K₀ (t + 1) with hxdef
    have hxpos : 0 < x := hpos (t + 1) ht
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    have hθ := po61_theta_euler h m
    have hθ1 := po61_theta_lt_one h m
    have hθ2 := po61_theta_lt_one h (m + 1)
    have hθp := po61_theta_pos h m
    have hrp : x ^ (α - 1) = x ^ α / x := by
      rw [Real.rpow_sub hxpos, Real.rpow_one]
    rw [hx2, hrp, hx]
    rw [hx] at hxa hxpos
    have h1 : 0 < 1 - po61_theta α β (m + 1) := by linarith
    have h2 : 0 < 1 - po61_theta α β m := by linarith
    have e1 : y - po61_theta α β (m + 1) * y = (1 - po61_theta α β (m + 1)) * y := by ring
    have e2 : (po61_theta α β (m + 1) * y) ^ α - po61_theta α β m *
        (po61_theta α β (m + 1) * y) ^ α =
        (1 - po61_theta α β m) * (po61_theta α β (m + 1) * y) ^ α := by ring
    rw [e1, e2]
    field_simp
    nlinarith [hθ]

/-- **(6.3) is the only solution** (Miao, p. 158: "Using these two conditions, we obtain the
following solution"). Any path with `K_t > 0` (`t ≤ T`), `K_{t+1} < K_t^α` (`t < T`),
`K_{T+1} = 0` and the Euler equation for `t < T` is `K_{t+1} = θ_{T−t} K_t^α`, `t ≤ T`. -/
theorem eq_6_3_unique {α β : ℝ} (h : po61_Params α β) (T : ℕ) {K : ℕ → ℝ}
    (hpos : ∀ t ≤ T, 0 < K t) (hlt : ∀ t < T, K (t + 1) < K t ^ α) (hT : K (T + 1) = 0)
    (heuler : ∀ t < T, 1 / (K t ^ α - K (t + 1)) =
      β * α * K (t + 1) ^ (α - 1) / (K (t + 1) ^ α - K (t + 2))) :
    ∀ t ≤ T, K (t + 1) = po61_theta α β (T - t) * K t ^ α := by
  have key : ∀ n, ∀ t, T - t = n → t ≤ T → K (t + 1) = po61_theta α β (T - t) * K t ^ α := by
    intro n
    induction n with
    | zero =>
      intro t hn ht
      have : t = T := by omega
      subst this
      rw [hT, Nat.sub_self, po61_theta_zero, zero_mul]
    | succ m ih =>
      intro t hn ht
      have htT : t < T := by omega
      have hnext := ih (t + 1) (by omega) (by omega)
      rw [show T - (t + 1) = m by omega] at hnext
      rw [hn]
      have hx := hpos (t + 1) (by omega)
      have hy : 0 < K t ^ α := Real.rpow_pos_of_pos (hpos t ht) α
      have hxa : 0 < K (t + 1) ^ α := Real.rpow_pos_of_pos hx α
      have he := heuler t htT
      have hd : 0 < K t ^ α - K (t + 1) := by linarith [hlt t htT]
      have hθ1 := po61_theta_lt_one h m
      have h2 : 0 < 1 - po61_theta α β m := by linarith
      rw [hnext] at he
      have hrp : K (t + 1) ^ (α - 1) = K (t + 1) ^ α / K (t + 1) := by
        rw [Real.rpow_sub hx, Real.rpow_one]
      rw [hrp, show K (t + 1) ^ α - po61_theta α β m * K (t + 1) ^ α =
        (1 - po61_theta α β m) * K (t + 1) ^ α by ring] at he
      field_simp at he
      obtain ⟨hb0, hb⟩ := po61_theta_back h m
      rw [← hb]
      rw [div_mul_eq_mul_div, eq_div_iff hb0.ne']
      linarith
  exact fun t ht => key (T - t) t rfl ht

/-- **(6.7)** (Miao, p. 159): the last-period problem `max ln C_T` subject to
`C_T + K_{T+1} = K_T^α`, `K_{T+1} ≥ 0`, is solved by `C_T = K_T^α`, `K_{T+1} = 0`, with value
`α ln K_T = V_T(K_T)`. -/
theorem eq_6_7 {α : ℝ} {K : ℝ} (hK : 0 < K) :
    (∀ K', 0 ≤ K' → K' < K ^ α → Real.log (K ^ α - K') ≤ α * Real.log K) ∧
      Real.log (K ^ α - 0) = α * Real.log K := by
  have hy := Real.rpow_pos_of_pos hK α
  refine ⟨fun K' hK' hK'y => ?_, by rw [sub_zero, Real.log_rpow hK]⟩
  rw [← Real.log_rpow hK]
  exact Real.log_le_log (by linarith) (by linarith)

/-- **(6.8)** (Miao, p. 159), corrected: the two-period problem `max ln(C_{T−1}) + βV_T(K_T)`
subject to `C_{T−1} + K_T = K_{T−1}^α` is solved by `K_T = αβ/(1 + αβ) K_{T−1}^α` and
`C_{T−1} = K_{T−1}^α/(1 + αβ)` (the book prints `K_T^{α−1}/(1 + αβ)`), and its value is
`V_{T−1}(K_{T−1})`. -/
theorem eq_6_8 {α β : ℝ} (h : po61_Params α β) (T : ℕ) {K : ℝ} (hK : 0 < K) :
    po61_theta α β 1 = α * β / (1 + α * β) ∧
      K ^ α - α * β / (1 + α * β) * K ^ α = K ^ α / (1 + α * β) ∧
      (∀ K' : ℝ, 0 < K' → K' < K ^ α →
        Real.log (K ^ α - K') + β * (α * Real.log K') ≤ po61_V α β (T + 1) T K) ∧
      Real.log (K ^ α / (1 + α * β)) + β * (α * Real.log (α * β / (1 + α * β) * K ^ α)) =
        po61_V α β (T + 1) T K := by
  have hp := h.p_pos
  have hp1 : 1 - α * β ≠ 0 := by linarith [h.p_lt]
  have hθ1 : po61_theta α β 1 = α * β / (1 + α * β) := by
    unfold po61_theta
    have h1 : (1 : ℝ) + α * β ≠ 0 := by linarith
    have h2 : (1 : ℝ) - (α * β) ^ (1 + 1) ≠ 0 := (po61_den_pos h 1).ne'
    rw [div_eq_div_iff h2 h1]
    ring
  have hVT : ∀ K', po61_V α β (T + 1) (T + 1) K' = α * Real.log K' := fun K' => by
    simp only [po61_V, Nat.sub_self, po61_A_terminal, po61_coef, zero_add, pow_one, add_zero]
    field_simp
  obtain ⟨hle, ⟨-, -, heq⟩, -⟩ := po61_bellman h (Nat.lt_succ_self T) hK
  rw [show T + 1 - T = 1 by omega, hθ1] at heq
  refine ⟨hθ1, by field_simp; ring, fun K' hK' hK'y => ?_, ?_⟩
  · have := hle K' hK' hK'y
    rwa [hVT] at this
  · rw [hVT] at heq
    rw [← heq]
    congr 2
    field_simp
    ring

/-- **The printed `C_{T−1}` of (6.8) is wrong** (Miao, p. 159): for all `α, β ∈ (0, 1)` there is a
capital stock `K_{T−1} > 0` at which the optimal `C_{T−1} = K_{T−1}^α − K_T`
(`K_T = αβ/(1 + αβ)K_{T−1}^α`) differs from the printed `K_T^{α−1}/(1 + αβ)`. -/
theorem eq_6_8_misprint {α β : ℝ} (h : po61_Params α β) :
    ∃ K : ℝ, 0 < K ∧
      K ^ α - α * β / (1 + α * β) * K ^ α ≠
        (α * β / (1 + α * β) * K ^ α) ^ (α - 1) / (1 + α * β) := by
  have hp := h.p_pos
  have hp1 : 0 < 1 + α * β := by linarith
  refine ⟨((1 + α * β) / (α * β)) ^ α⁻¹, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have hK : (((1 + α * β) / (α * β)) ^ α⁻¹) ^ α = (1 + α * β) / (α * β) :=
    Real.rpow_inv_rpow (by positivity) h.α_pos.ne'
  rw [hK]
  have hpne : α * β ≠ 0 := hp.ne'
  have h1 : α * β / (1 + α * β) * ((1 + α * β) / (α * β)) = 1 := by
    rw [div_mul_div_comm, mul_comm (α * β), div_self (mul_ne_zero hp1.ne' hpne)]
  rw [h1, Real.one_rpow]
  intro heq
  rw [div_sub_one hpne, show 1 + α * β - α * β = 1 by ring,
    div_eq_div_iff hpne hp1.ne'] at heq
  linarith

/-- **Time consistency** (Miao, p. 160, properties (i)–(ii)). For `K₀ > 0`: (i) the value
functions of the planning problems satisfy the Bellman equation (`po61_bellman`, and
`eq_6_5_6_6` identifies them with the sequence values); (ii) every optimal plan of the date-`0`
problem is the plan generated by the policy functions `g_t(K) = θ_{T−t}K^α` (its capital path is
(6.3)), and its continuation from the capital `K_t` it reaches is optimal for the date-`t`
problem. -/
theorem time_consistency_6_1 {α β : ℝ} (h : po61_Params α β) (T : ℕ) (K₀ : po61_Pos)
    {a : ℕ → po61_Pos} (ha : a ∈ po_detFeasible (po61_model α β) T K₀)
    (hopt : (po_detJ (po61_model α β) T K₀ a : EReal) = po_detVt (po61_model α β) T 0 K₀) :
    (∀ t < T, a t = po61_g h T t (po_traj (po61_model α β) K₀ a t)) ∧
      (∀ t ≤ T, (po_traj (po61_model α β) K₀ a t).1 = po61_path α β T K₀.1 t) ∧
      ∀ t ≤ T, (po_detJ (po_detShift (po61_model α β) t) (T - t)
        (po_traj (po61_model α β) K₀ a t) (fun i => a (i + t)) : EReal) =
          po_detVt (po61_model α β) T t (po_traj (po61_model α β) K₀ a t) := by
  obtain ⟨hB1, hB2, hT⟩ := po61_model_bellman h T
  have hV : ∀ t ≤ T, ∀ K, po_detVt (po61_model α β) T t K = po61_V α β T t K.1 :=
    fun t ht K => eq_6_5_6_6 h ht K
  have hB : ∀ t < T, ∀ K, ((po61_V α β T t K.1 : ℝ) : EReal) =
      ⨆ K' ∈ (po61_model α β).Γ K, (((po61_model α β).u t (K, K') + (po61_model α β).β *
        po61_V α β T (t + 1) ((po61_model α β).f t (K, K')).1 : ℝ) : EReal) := by
    intro t ht K
    refine le_antisymm ?_ (iSup₂_le fun K' hK' => EReal.coe_le_coe_iff.2 (hB1 t ht K K' hK'))
    obtain ⟨hg, heq⟩ := hB2 t ht K
    rw [heq]
    exact le_iSup₂_of_le (f := fun K' (_ : K' ∈ (po61_model α β).Γ K) =>
      (((po61_model α β).u t (K, K') + (po61_model α β).β *
        po61_V α β T (t + 1) ((po61_model α β).f t (K, K')).1 : ℝ) : EReal)) _ hg le_rfl
  have hc := ex_6_1_theorem_6_3_3 (D := po61_model α β) (w := fun t K => po61_V α β T t K.1)
    h.β_pos hV hB ha hopt
  have hpol : ∀ t < T, a t = po61_g h T t (po_traj (po61_model α β) K₀ a t) := by
    intro t ht
    obtain ⟨hΓ, heq⟩ := hc.1 t ht
    set K := po_traj (po61_model α β) K₀ a t
    by_contra hne
    have hne' : (a t).1 ≠ po61_theta α β (T - t) * K.1 ^ α := by
      intro h'
      apply hne
      apply Subtype.ext
      simp only [po61_g, ht, ↓reduceDIte]
      exact h'
    have := (po61_bellman h ht K.2).2.2 (a t).1 (a t).2 hΓ hne'
    change Real.log (K.1 ^ α - (a t).1) + β * po61_V α β T (t + 1) (a t).1 =
      po61_V α β T t K.1 at heq
    linarith
  refine ⟨hpol, fun t => ?_, hc.2⟩
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    change (a t).1 = po61_theta α β (T - t) * po61_path α β T K₀.1 t ^ α
    rw [hpol t (by omega), ← ih (by omega)]
    simp only [po61_g, show t < T by omega, ↓reduceDIte]

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The measurability problem

Miao, §6.2, pp. 161–162 (after Bertsekas and Shreve 1978). A two-period problem: choose
`a₀ ∈ A` and a measurable `π₁ : S → A` to maximise `∫ u(s₁, π₁(s₁)) P(s₀, a₀; ds₁)`
(`po_V0`). Backward induction gives `V₁*(s₁) = sup_a u(s₁, a)` (`po_V1star`) and
`V₀*(s₀) = sup_{a₀} ∫ V₁* dP(s₀, a₀; ·)` (`po_V0star`).

* `two_step_6_2`: the book's two-step argument as a theorem. With `u` measurable and bounded,
  `A` nonempty, `V₁*` **measurable** (needed for the integral in (6.11)) and, for every `ε > 0`, a
  **measurable** ε-maximiser `a₁*` (6.9) (needed for (6.10)), `V₀ = V₀*`. Step 1 (`V₀ ≤ V₀*`) is
  `two_step_6_2_step1` and needs only the measurability of `V₁*`.
* The projection identity, p. 162. **Correction:** the book prints
  `{s₁ : V₁(s₁) < c} = proj_{s₁} {(s₁, a₁) : u(s₁, a₁) < c}`, which is false for a supremum
  (`proj_identity_6_2_misprint`); the correct identity is
  `{V₁* > c} = proj {u > c}` (`proj_identity_6_2`), and so `{V₁* ≤ c}` is the complement of a
  projection.
* Blackwell's point (`blackwell_6_2`): for `u = 1_E` with `E ⊆ S × A` measurable,
  `V₁* = 1_{proj E}`, so `V₁*` is measurable if and only if the projection of `E` is.

**Not formalised:** an actual Borel set `E ⊆ ℝ²` with non-Borel projection (Souslin). Mathlib
v4.34.0 has analytic sets (`MeasureTheory.AnalyticSet`) and Lusin's separation theorem, but no
non-Borel analytic set and no Borel set with a non-Borel projection, so Blackwell's example is
stated for any measurable `E` whose projection is not measurable.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `V₁*(s₁) = sup_{a₁ ∈ A} u(s₁, a₁)` (Miao, p. 161). -/
noncomputable def po_V1star (u : S × A → ℝ) (s : S) : ℝ := ⨆ a, u (s, a)

/-- `V₀*(s₀) = sup_{a₀ ∈ A} ∫ V₁*(s₁) P(s₀, a₀; ds₁)` (Miao, p. 161). -/
noncomputable def po_V0star (P : Kernel (S × A) S) (u : S × A → ℝ) (s₀ : S) : ℝ :=
  ⨆ a₀, ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀)

/-- `V₀(s₀) = sup_{π = (π₀, π₁)} ∫ u(s₁, π₁(s₁)) P(s₀, π₀; ds₁)` over `π₀ ∈ A` and measurable
`π₁ : S → A` (Miao, p. 161). -/
noncomputable def po_V0 (P : Kernel (S × A) S) (u : S × A → ℝ) (s₀ : S) : ℝ :=
  ⨆ π : A × {f : S → A // Measurable f}, ∫ s₁, u (s₁, π.2.1 s₁) ∂P (s₀, π.1)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_V1star_le [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) :
    po_V1star u s ≤ B :=
  ciSup_le fun _ => (le_abs_self _).trans (hB _)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_le_V1star {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) (a : A) :
    u (s, a) ≤ po_V1star u s :=
  le_ciSup (f := fun a => u (s, a)) ⟨B, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hB _)⟩ a

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_abs_V1star_le [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) :
    |po_V1star u s| ≤ B := by
  obtain ⟨a⟩ := ‹Nonempty A›
  refine abs_le.2 ⟨?_, po_V1star_le hB s⟩
  linarith [po_le_V1star hB s a, neg_abs_le (u (s, a)), hB (s, a)]

theorem po_integrable_bdd {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, |f s| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hB s)

theorem po_abs_integral_le {μ : Measure S} [IsProbabilityMeasure μ] {f : S → ℝ} {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) : |∫ s, f s ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hB s)
  simpa [Real.norm_eq_abs] using this

/-- **Step 1** of Miao, p. 161: if `V₁*` is measurable, then for every plan
`∫ u(s₁, π₁) dP ≤ ∫ V₁* dP ≤ V₀*(s₀)`, so `V₀ ≤ V₀*`. -/
theorem two_step_6_2_step1 [Nonempty A] {P : Kernel (S × A) S} [IsMarkovKernel P]
    {u : S × A → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hV1 : Measurable (po_V1star u)) (s₀ : S) : po_V0 P u s₀ ≤ po_V0star P u s₀ := by
  have : Nonempty {f : S → A // Measurable f} :=
    ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩
  have hbdd : BddAbove (Set.range fun a₀ => ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀)) :=
    ⟨B, by
      rintro _ ⟨a₀, rfl⟩
      exact (le_abs_self _).trans (po_abs_integral_le (po_abs_V1star_le hB))⟩
  refine ciSup_le fun π => ?_
  have hπm : Measurable fun s₁ => u (s₁, π.2.1 s₁) := hu.comp (measurable_id.prodMk π.2.2)
  refine le_trans (integral_mono (po_integrable_bdd hπm fun s => hB _)
    (po_integrable_bdd hV1 (po_abs_V1star_le hB)) fun s₁ => po_le_V1star hB s₁ _) ?_
  exact le_ciSup hbdd π.1

/-- **The two-step argument of §6.2** (Miao, pp. 161–162) as a theorem: with `A` nonempty, a
Markov kernel `P`, `u` measurable and bounded, `V₁*` measurable, and measurable ε-maximisers
`a₁*` (`u(s₁, a₁*(s₁)) + ε ≥ V₁*(s₁)`, (6.9)) for every `ε > 0`, the Principle of Optimality
`V₀ = V₀*` holds. -/
theorem two_step_6_2 [Nonempty A] {P : Kernel (S × A) S} [IsMarkovKernel P]
    {u : S × A → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hV1 : Measurable (po_V1star u))
    (hsel : ∀ ε : ℝ, 0 < ε → ∃ g : S → A, Measurable g ∧ ∀ s, po_V1star u s ≤ u (s, g s) + ε)
    (s₀ : S) : po_V0 P u s₀ = po_V0star P u s₀ := by
  refine le_antisymm (two_step_6_2_step1 hu hB hV1 s₀) ?_
  have : Nonempty {f : S → A // Measurable f} :=
    ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩
  have hbdd : BddAbove (Set.range fun π : A × {f : S → A // Measurable f} =>
      ∫ s₁, u (s₁, π.2.1 s₁) ∂P (s₀, π.1)) :=
    ⟨B, by
      rintro _ ⟨π, rfl⟩
      exact (le_abs_self _).trans (po_abs_integral_le fun s => hB _)⟩
  refine ciSup_le fun a₀ => le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, hg, hgε⟩ := hsel ε hε
  have hgm : Measurable fun s₁ => u (s₁, g s₁) := hu.comp (measurable_id.prodMk hg)
  have h1 : ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀) ≤ ∫ s₁, (u (s₁, g s₁) + ε) ∂P (s₀, a₀) :=
    integral_mono (po_integrable_bdd hV1 (po_abs_V1star_le hB))
      ((po_integrable_bdd hgm fun s => hB _).add (integrable_const ε)) hgε
  rw [integral_add (po_integrable_bdd hgm fun s => hB _) (integrable_const ε)] at h1
  have hc : ∫ _, ε ∂P (s₀, a₀) = ε := by simp
  rw [hc] at h1
  have h2 : ∫ s₁, u (s₁, g s₁) ∂P (s₀, a₀) ≤ po_V0 P u s₀ :=
    le_ciSup hbdd (a₀, ⟨g, hg⟩)
  linarith

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- **The projection identity**, Miao p. 162, corrected: for `u` bounded above,
`{s₁ : V₁*(s₁) > c} = proj_{s₁} {(s₁, a₁) : u(s₁, a₁) > c}`. -/
theorem proj_identity_6_2 [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (c : ℝ) :
    {s | c < po_V1star u s} = Prod.fst '' {x | c < u x} := by
  ext s
  simp only [Set.mem_image]
  constructor
  · intro h
    have hbdd : BddAbove (Set.range fun a => u (s, a)) :=
      ⟨B, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hB _)⟩
    obtain ⟨a, ha⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨(s, a), ha, rfl⟩
  · rintro ⟨⟨s', a⟩, ha, rfl⟩
    exact lt_of_lt_of_le ha (po_le_V1star hB s' a)

/-- **The printed projection identity is false** (Miao, p. 162): with `S` a point, `A = Bool`,
`u(s, a) = 1` if `a` and `0` otherwise, and `c = 1/2`, `{V₁* < c} = ∅` but
`proj {u < c} = S`. -/
theorem proj_identity_6_2_misprint :
    let u : Unit × Bool → ℝ := fun x => if x.2 then 1 else 0
    {s | po_V1star u s < 1 / 2} ≠ Prod.fst '' {x | u x < 1 / 2} := by
  intro u
  have hB : ∀ x, |u x| ≤ 1 := fun x => by
    simp only [u]
    split_ifs <;> norm_num
  have h1 : ∀ s, 1 ≤ po_V1star u s := fun s => by
    have := po_le_V1star hB s true
    simpa [u] using this
  intro h
  have hmem : (((), false) : Unit × Bool).1 ∈ Prod.fst '' {x | u x < 1 / 2} :=
    Set.mem_image_of_mem _ (by simp [u])
  rw [← h] at hmem
  have := h1 ()
  have h2 : po_V1star u () < 1 / 2 := hmem
  linarith

omit [MeasurableSpace A] in
/-- **Blackwell's point** (Miao, p. 162): for `u = 1_E` with `E ⊆ S × A` measurable (and `A`
nonempty), `V₁* = 1_{proj E}`; hence `V₁*` is measurable if and only if the projection
`proj_{s₁} E` is a measurable set. -/
theorem blackwell_6_2 [Nonempty A] (E : Set (S × A)) :
    po_V1star (E.indicator 1) = (Prod.fst '' E).indicator 1 ∧
      (Measurable (po_V1star (E.indicator (1 : S × A → ℝ))) ↔ MeasurableSet (Prod.fst '' E)) := by
  have hB : ∀ x, |E.indicator (1 : S × A → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ E <;> simp [hx]
  have heq : po_V1star (E.indicator (1 : S × A → ℝ)) = (Prod.fst '' E).indicator 1 := by
    funext s
    by_cases hs : s ∈ Prod.fst '' E
    · obtain ⟨⟨s', a⟩, ha, rfl⟩ := hs
      rw [Set.indicator_of_mem (Set.mem_image_of_mem Prod.fst ha)]
      refine le_antisymm ((po_V1star_le hB s').trans le_rfl) ?_
      have := po_le_V1star hB s' a
      rwa [Set.indicator_of_mem ha] at this
    · rw [Set.indicator_of_notMem hs]
      refine le_antisymm (ciSup_le fun a => ?_) ?_
      · rw [Set.indicator_of_notMem fun h => hs ⟨(s, a), h, rfl⟩]
      · obtain ⟨a⟩ := ‹Nonempty A›
        have := po_le_V1star hB s a
        rwa [Set.indicator_of_notMem fun h => hs ⟨(s, a), h, rfl⟩] at this
  refine ⟨heq, ?_⟩
  rw [heq]
  exact measurable_indicator_const_iff 1

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.2: the §6.1 planner with a Markov productivity shock

**Exercise 6.2** (Miao, p. 189): `max E ∑_{t=0}^T βᵗ ln C_t` subject to
`C_t + K_{t+1} = z_t K_t^α`, where the productivity `z_t = ζ(x_t) > 0` is a function of a Markov
process `(x_t)` on a measurable space `X` with transition function `Q`. Integrability: `ln ζ` is
measurable and **bounded** (so every expectation below exists); `Q` is a Markov kernel.

With `n = T − t` periods to go, `θ_n` and the coefficient `coef_n` of §6.1 (`po61_theta`,
`po61_coef`) and `b_n` of (6.6) (`po61_b`):

* the value function is `V_t(K, x) = coef_{T−t} ln K + E_{T−t}(x)`, where
  `E_0(x) = ln ζ(x)` and
  `E_{n+1}(x) = (1 + β coef_n) ln ζ(x) + b_{n+1} + β ∫ E_n(x′) Q(x, dx′)` (`po62_E`, `po62_V`);
* the policies are `K_{t+1} = θ_{T−t} z_t K_t^α` (investment) and
  `C_t = (1 − θ_{T−t}) z_t K_t^α = z_t K_t^α/(1 + β coef_{T−t−1})` (consumption): the saving rate
  is the deterministic one of (6.3) and does not depend on the shock (`ex_6_2_policies`).

`ex_6_2` proves the stochastic Bellman equation
`V_t(K, x) = max_{0 < K′ < ζ(x)K^α} ln(ζ(x)K^α − K′) + β ∫ V_{t+1}(K′, x′) Q(x, dx′)` as a
maximisation, with the unique maximiser `K′ = θ_{T−t}ζ(x)K^α`, and `V_T(K, x) = ln(ζ(x)K^α)`.
`po62_E_bounded` gives the integrability used.

That the policy plan is optimal for the sequence problem (among the plans with integrable
rewards; Assumption 5.1.3 fails for this model) is `ex_6_2_optimal` in `POStochasticGrowthMDP`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The shock part of the value function, by periods to go. -/
noncomputable def po62_E (Q : Kernel X X) (ζ : X → ℝ) (α β : ℝ) : ℕ → X → ℝ
  | 0 => fun x => Real.log (ζ x)
  | n + 1 => fun x => (1 + β * po61_coef α β n) * Real.log (ζ x) + po61_b α β (n + 1) +
      β * ∫ x', po62_E Q ζ α β n x' ∂Q x

/-- The value function `V_t(K, x) = coef_{T−t} ln K + E_{T−t}(x)`. -/
noncomputable def po62_V (Q : Kernel X X) (ζ : X → ℝ) (α β : ℝ) (T t : ℕ) (K : ℝ) (x : X) : ℝ :=
  po61_coef α β (T - t) * Real.log K + po62_E Q ζ α β (T - t) x

/-- `E_n` is measurable and bounded when `ln ζ` is. -/
theorem po62_E_bounded {Q : Kernel X X} [IsMarkovKernel Q] {ζ : X → ℝ}
    (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ} (hB : ∀ x, |Real.log (ζ x)| ≤ B)
    (α β : ℝ) : ∀ n, Measurable (po62_E Q ζ α β n) ∧ ∃ D, ∀ x, |po62_E Q ζ α β n x| ≤ D := by
  intro n
  induction n with
  | zero => exact ⟨hζm, B, hB⟩
  | succ n ih =>
    obtain ⟨hm, D, hD⟩ := ih
    refine ⟨?_, ?_⟩
    · exact ((measurable_const.mul hζm).add measurable_const).add (measurable_const.mul
        (hm.stronglyMeasurable.integral_kernel (κ := Q)).measurable)
    · refine ⟨|1 + β * po61_coef α β n| * B + |po61_b α β (n + 1)| + |β| * D, fun x => ?_⟩
      have h1 : |∫ x', po62_E Q ζ α β n x' ∂Q x| ≤ D := by
        have := norm_integral_le_of_norm_le_const (μ := Q x) (f := po62_E Q ζ α β n) (C := D)
          (Filter.Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hD x')
        simpa [Real.norm_eq_abs] using this
      simp only [po62_E]
      calc |(1 + β * po61_coef α β n) * Real.log (ζ x) + po61_b α β (n + 1) +
            β * ∫ x', po62_E Q ζ α β n x' ∂Q x|
          ≤ |(1 + β * po61_coef α β n) * Real.log (ζ x)| + |po61_b α β (n + 1)| +
              |β * ∫ x', po62_E Q ζ α β n x' ∂Q x| := abs_add_three _ _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hB x

theorem po62_integrable_E {Q : Kernel X X} [IsMarkovKernel Q] {ζ : X → ℝ}
    (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ} (hB : ∀ x, |Real.log (ζ x)| ≤ B)
    (α β : ℝ) (n : ℕ) (x : X) : Integrable (po62_E Q ζ α β n) (Q x) := by
  obtain ⟨hm, D, hD⟩ := po62_E_bounded (Q := Q) hζm hB α β n
  exact Integrable.of_bound hm.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hD x')

/-- **Exercise 6.2** (Miao, p. 189): the Bellman equation of the stochastic growth model, solved.
For `t < T`, `K > 0` and every state `x` of the shock (with `z = ζ(x) > 0`):
`ln(zK^α − K′) + β ∫ V_{t+1}(K′, x′) Q(x, dx′) ≤ V_t(K, x)` for every `K′ ∈ (0, zK^α)`, with
equality at `K′ = θ_{T−t} zK^α` and strict inequality elsewhere; and `V_T(K, x) = ln(zK^α)`. -/
theorem ex_6_2 {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} [IsMarkovKernel Q]
    {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x) (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ}
    (hB : ∀ x, |Real.log (ζ x)| ≤ B) {T t : ℕ} (ht : t < T) {K : ℝ} (hK : 0 < K) (x : X) :
    (∀ K' : ℝ, 0 < K' → K' < ζ x * K ^ α →
      Real.log (ζ x * K ^ α - K') + β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x ≤
        po62_V Q ζ α β T t K x) ∧
    (0 < po61_theta α β (T - t) * (ζ x * K ^ α) ∧
      po61_theta α β (T - t) * (ζ x * K ^ α) < ζ x * K ^ α ∧
      Real.log (ζ x * K ^ α - po61_theta α β (T - t) * (ζ x * K ^ α)) +
        β * ∫ x', po62_V Q ζ α β T (t + 1) (po61_theta α β (T - t) * (ζ x * K ^ α)) x' ∂Q x =
          po62_V Q ζ α β T t K x) ∧
    (∀ K' : ℝ, 0 < K' → K' < ζ x * K ^ α → K' ≠ po61_theta α β (T - t) * (ζ x * K ^ α) →
      Real.log (ζ x * K ^ α - K') + β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x <
        po62_V Q ζ α β T t K x) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hy : 0 < ζ x * K ^ α := mul_pos (hζ x) (Real.rpow_pos_of_pos hK α)
  have hc := mul_pos h.β_pos (po61_coef_pos h n)
  set c := β * po61_coef α β n with hcdef
  have hint := po62_integrable_E (Q := Q) hζm hB α β n x
  have hlogy : Real.log (ζ x * K ^ α) = Real.log (ζ x) + α * Real.log K := by
    rw [Real.log_mul (hζ x).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK α]
  have hVt : po62_V Q ζ α β T t K x = (1 + c) * Real.log (ζ x * K ^ α) -
      (1 + c) * Real.log (1 + c) + c * Real.log c + β * ∫ x', po62_E Q ζ α β n x' ∂Q x := by
    unfold po62_V
    rw [hn, po61_coef_succ h n, ← hcdef]
    simp only [po62_E]
    rw [po61_b_succ h n, ← hcdef, hlogy]
    ring
  have hrhs : ∀ K', β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x =
      c * Real.log K' + β * ∫ x', po62_E Q ζ α β n x' ∂Q x := by
    intro K'
    unfold po62_V
    rw [hn', integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
      hcdef]
    ring
  have hθ : po61_theta α β (T - t) * (ζ x * K ^ α) = c * (ζ x * K ^ α) / (1 + c) := by
    rw [hn, (po61_theta_succ h n).1, ← hcdef]
    ring
  have hθlt : po61_theta α β (T - t) * (ζ x * K ^ α) < ζ x * K ^ α := by
    rw [hθ, div_lt_iff₀ (by linarith)]
    nlinarith
  have hθpos : 0 < po61_theta α β (T - t) * (ζ x * K ^ α) := by
    rw [hθ]
    positivity
  refine ⟨fun K' hK' hK'y => ?_, ⟨hθpos, hθlt, ?_⟩, fun K' hK' hK'y hne => ?_⟩
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).1
    linarith
  · rw [hrhs, hVt, hθ]
    have h1 : ζ x * K ^ α - c * (ζ x * K ^ α) / (1 + c) = ζ x * K ^ α / (1 + c) := by
      field_simp
      ring
    have h2 : c * (ζ x * K ^ α) / (1 + c) = c * (ζ x * K ^ α / (1 + c)) := by ring
    rw [h1, h2, Real.log_mul hc.ne' (by positivity), Real.log_div hy.ne' (by linarith)]
    ring
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).2 (by rw [← hθ]; exact hne)
    linarith

/-- Exercise 6.2, the terminal date: `V_T(K, x) = ln(ζ(x)K^α)`. -/
theorem ex_6_2_terminal {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} {ζ : X → ℝ}
    (hζ : ∀ x, 0 < ζ x) (T : ℕ) {K : ℝ} (hK : 0 < K) (x : X) :
    po62_V Q ζ α β T T K x = Real.log (ζ x * K ^ α) := by
  have hp1 : (1 : ℝ) - α * β ≠ 0 := by linarith [h.p_lt]
  rw [Real.log_mul (hζ x).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK α]
  simp only [po62_V, Nat.sub_self, po62_E, po61_coef, zero_add, pow_one]
  field_simp
  ring

/-- **Exercise 6.2: the optimal policies** (Miao, p. 189). For `t < T`: investment
`K_{t+1} = θ_{T−t} z_t K_t^α` and consumption `C_t = z_t K_t^α − K_{t+1} = (1 − θ_{T−t}) z_t K_t^α
= z_t K_t^α/(1 + β coef_{T−t−1})`, with the deterministic saving rate `θ_{T−t}` of (6.3). -/
theorem ex_6_2_policies {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t < T) (y : ℝ) :
    y - po61_theta α β (T - t) * y = (1 - po61_theta α β (T - t)) * y ∧
      (1 - po61_theta α β (T - t)) * y = y / (1 + β * po61_coef α β (T - t - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  refine ⟨by ring, ?_⟩
  rw [hn, (po61_theta_succ h n).2, show n + 1 - 1 = n by omega]
  ring

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.2 as a Markov decision process: the policies are optimal

The stochastic growth model of Exercise 6.2 (Miao, p. 189) as a Markov decision process of
Chapter 5 (`po62_model`): the state is `(K, x)` with `K > 0`, the action is `K′ ∈ (0, ζ(x)K^α)`,
the next state is `(K′, x′)` with `x′ ~ Q(x, ·)` (`po62_kernel`), the reward is
`ln(ζ(x)K^α − K′)` and the terminal reward `ln(ζ(x)K^α)`.

**Integrability.** Assumption 5.1.3 fails for this model: along an arbitrary measurable feasible
plan, `ln C_t` (unbounded below as `C_t → 0`) need not be integrable, so the sequence problem is
posed over the feasible plans **with integrable rewards** (`po_IntPlan`), the plans for which the
objective (6.13) is defined. The policy plan has integrable rewards: under its history measures
`|ln K_t|` is almost surely bounded (`po62_ae_bound`), because `ln K_{t+1} = ln θ + ln ζ(x_t) +
α ln K_t` almost surely and `ln ζ` is bounded (`po62_intPlan`).

**`ex_6_2_optimal`**: the plan generated by the policy `K_{t+1} = θ_{T−t} ζ(x_t) K_t^α` is
feasible, has integrable rewards, attains `V₀(K₀, x₀)` of `POStochasticGrowth`, and does at least
as well as every feasible plan with integrable rewards (Theorem 6.3.2 in the form
`po_verification_intPlans`).
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The transition of Exercise 6.2: from `((K, x), K′)` to `(K′, x′)` with `x′ ~ Q(x, ·)`. -/
noncomputable def po62_kernel (Q : Kernel X X) :
    Kernel ((po61_Pos × X) × po61_Pos) (po61_Pos × X) :=
  pushKernel (Q.comap (fun p : (po61_Pos × X) × po61_Pos => p.1.2) measurable_fst.snd)
    fun q => (q.1.2, q.2)

theorem po62_kernel_apply (Q : Kernel X X) [IsMarkovKernel Q]
    (p : (po61_Pos × X) × po61_Pos) : po62_kernel Q p = (Q p.1.2).map fun x' => (p.2, x') := by
  rw [po62_kernel, pushKernel_apply _ (measurable_fst.snd.prodMk measurable_snd)]
  rfl

theorem po62_kernel_markov (Q : Kernel X X) [IsMarkovKernel Q] :
    IsMarkovKernel (po62_kernel Q) :=
  isMarkovKernel_pushKernel _ (measurable_fst.snd.prodMk measurable_snd)

/-- Exercise 6.2 as a Markov decision process (5.1). -/
noncomputable def po62_model (Q : Kernel X X) (ζ : X → ℝ) (α β : ℝ) :
    MDP (po61_Pos × X) po61_Pos where
  Γ := fun s => {a | a.1 < ζ s.2 * s.1.1 ^ α}
  P := fun _ => po62_kernel Q
  u := fun _ x => Real.log (ζ x.1.2 * x.1.1.1 ^ α - x.2.1)
  uT := fun s => Real.log (ζ s.2 * s.1.1 ^ α)
  β := β

omit [MeasurableSpace X] in
theorem po62_policy_pos {α β : ℝ} (h : po61_Params α β) {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x)
    {T j : ℕ} (hj : j < T) (s : po61_Pos × X) :
    0 < po61_theta α β (T - j) * (ζ s.2 * s.1.1 ^ α) := by
  obtain ⟨n, hn⟩ : ∃ n, T - j = n + 1 := ⟨T - j - 1, by omega⟩
  rw [hn]
  exact mul_pos (po61_theta_pos h n) (mul_pos (hζ _) (Real.rpow_pos_of_pos s.1.2 α))

/-- The policy `K′ = θ_{T−j} ζ(x) K^α` (any value at dates `j ≥ T`). -/
noncomputable def po62_g {α β : ℝ} (h : po61_Params α β) {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x)
    (T j : ℕ) (s : po61_Pos × X) : po61_Pos :=
  if hj : j < T then ⟨po61_theta α β (T - j) * (ζ s.2 * s.1.1 ^ α), po62_policy_pos h hζ hj s⟩
  else s.1

/-- The bounds `D_j` on `|ln K_j|` along the policy plan. -/
noncomputable def po62_D (α β B : ℝ) (T : ℕ) (K₀ : ℝ) : ℕ → ℝ
  | 0 => |Real.log K₀|
  | j + 1 => |Real.log (po61_theta α β (T - j))| + B + |α| * po62_D α β B T K₀ j

theorem po62_measurable_ζ {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x)
    (hζm : Measurable fun x => Real.log (ζ x)) : Measurable ζ := by
  have : (fun x => Real.exp (Real.log (ζ x))) = ζ := funext fun x => Real.exp_log (hζ x)
  rw [← this]
  exact Real.measurable_exp.comp hζm

theorem po62_measurable_g {α β : ℝ} (h : po61_Params α β) {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x)
    (hζm : Measurable fun x => Real.log (ζ x)) (T j : ℕ) : Measurable (po62_g h hζ T j) := by
  have hζ' := po62_measurable_ζ hζ hζm
  by_cases hj : j < T
  · have e : po62_g h hζ T j = fun s =>
        (⟨po61_theta α β (T - j) * (ζ s.2 * s.1.1 ^ α), po62_policy_pos h hζ hj s⟩ : po61_Pos) :=
      funext fun s => by simp only [po62_g, hj, ↓reduceDIte]
    rw [e]
    refine Measurable.subtype_mk ?_
    exact measurable_const.mul ((hζ'.comp measurable_snd).mul
      ((measurable_subtype_coe.comp measurable_fst).pow_const α))
  · have e : po62_g h hζ T j = fun s => s.1 := funext fun s => by
      simp only [po62_g, hj, ↓reduceDIte]
    rw [e]
    exact measurable_fst

/-- **The capital stock along the policy plan is almost surely bounded in logs**: for `j ≤ T`,
`|ln K_j| ≤ D_j` for `μʲ`-almost every history. -/
theorem po62_ae_bound {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} [IsMarkovKernel Q]
    {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x) (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ}
    (hB : ∀ x, |Real.log (ζ x)| ≤ B) (T : ℕ) (s₀ : po61_Pos × X) :
    ∀ j ≤ T, ∀ᵐ hh ∂mu (po62_model Q ζ α β) s₀ (po_genPlan (po62_g h hζ T) s₀) j,
      |Real.log (lastState s₀ hh).1.1| ≤ po62_D α β B T s₀.1.1 j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine Filter.Eventually.of_forall fun hh => ?_
    have : hh = Fin.elim0 := Subsingleton.elim _ _
    subst this
    exact le_rfl
  | succ j ih =>
    intro hj
    have hIH := ih (by omega)
    have hmeas : ∀ n, MeasurableSet {hh : Fin n → po61_Pos × X |
        |Real.log (lastState s₀ hh).1.1| ≤ po62_D α β B T s₀.1.1 (j + 1)} := fun n =>
      measurableSet_le (continuous_abs.measurable.comp (Real.measurable_log.comp
        (measurable_subtype_coe.comp (measurable_fst.comp (measurable_lastState s₀ n)))))
        measurable_const
    have hπm : Measurable (po_genPlan (po62_g h hζ T) s₀ j) :=
      (po62_measurable_g h hζ hζm T j).comp (measurable_lastState s₀ j)
    change ∀ᵐ hh ∂((mu (po62_model Q ζ α β) s₀ (po_genPlan (po62_g h hζ T) s₀) j) ⊗ₘ
      stepKernel (po62_model Q ζ α β) s₀ (po_genPlan (po62_g h hζ T) s₀) j).map
        (fun p => (Fin.snoc p.1 p.2 : Fin (j + 1) → po61_Pos × X)), _
    rw [ae_map_iff (measurable_snoc j).aemeasurable (hmeas (j + 1))]
    refine Measure.ae_compProd_of_ae_ae ((measurable_snoc j) (hmeas (j + 1))) ?_
    filter_upwards [hIH] with hh hhb
    rw [stepKernel_apply _ s₀ hπm]
    change ∀ᵐ s' ∂po62_kernel Q _, _
    rw [po62_kernel_apply]
    have hset : MeasurableSet {s' : po61_Pos × X |
        |Real.log s'.1.1| ≤ po62_D α β B T s₀.1.1 (j + 1)} :=
      measurableSet_le (continuous_abs.measurable.comp (Real.measurable_log.comp
        (measurable_subtype_coe.comp measurable_fst))) measurable_const
    have hset' : {s' : po61_Pos × X | |Real.log (lastState s₀
        (Fin.snoc hh s' : Fin (j + 1) → po61_Pos × X)).1.1| ≤ po62_D α β B T s₀.1.1 (j + 1)} =
        {s' | |Real.log s'.1.1| ≤ po62_D α β B T s₀.1.1 (j + 1)} := by
      ext s'
      simp only [lastState_snoc]
    change ∀ᵐ s' ∂_, s' ∈ {s' : po61_Pos × X | |Real.log (lastState s₀
        (Fin.snoc hh s' : Fin (j + 1) → po61_Pos × X)).1.1| ≤ po62_D α β B T s₀.1.1 (j + 1)}
    rw [hset']
    refine (ae_map_iff measurable_prodMk_left.aemeasurable hset).2
      (Filter.Eventually.of_forall fun x' => ?_)
    have hjT : j < T := by omega
    set s := lastState s₀ hh
    change |Real.log (po62_g h hζ T j s).1| ≤ po62_D α β B T s₀.1.1 (j + 1)
    simp only [po62_g, hjT, ↓reduceDIte, po62_D]
    obtain ⟨n, hn⟩ : ∃ n, T - j = n + 1 := ⟨T - j - 1, by omega⟩
    have hθ := po61_theta_pos h n
    rw [← hn] at hθ
    rw [Real.log_mul hθ.ne' (mul_pos (hζ _) (Real.rpow_pos_of_pos s.1.2 α)).ne',
      Real.log_mul (hζ _).ne' (Real.rpow_pos_of_pos s.1.2 α).ne', Real.log_rpow s.1.2]
    calc |Real.log (po61_theta α β (T - j)) + (Real.log (ζ s.2) + α * Real.log s.1.1)|
        ≤ |Real.log (po61_theta α β (T - j))| + (|Real.log (ζ s.2)| + |α * Real.log s.1.1|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ _ := by
        rw [abs_mul]
        have := hB s.2
        have := mul_le_mul_of_nonneg_left hhb (abs_nonneg α)
        linarith

/-- **The policy plan has integrable rewards.** -/
theorem po62_intPlan {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} [IsMarkovKernel Q]
    {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x) (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ}
    (hB : ∀ x, |Real.log (ζ x)| ≤ B) (T : ℕ) (s₀ : po61_Pos × X) :
    po_IntPlan (po62_model Q ζ α β) T s₀ (po_genPlan (po62_g h hζ T) s₀) := by
  have hζ' := po62_measurable_ζ hζ hζm
  have hP : (po62_model Q ζ α β).IsMarkov := fun _ => po62_kernel_markov Q
  have hπm : ∀ j, Measurable (po_genPlan (po62_g h hζ T) s₀ j) := fun j =>
    (po62_measurable_g h hζ hζm T j).comp (measurable_lastState s₀ j)
  have hu : ∀ j, Measurable ((po62_model Q ζ α β).u j) := fun j =>
    Real.measurable_log.comp (((hζ'.comp measurable_fst.snd).mul
      ((measurable_subtype_coe.comp measurable_fst.fst).pow_const α)).sub
        (measurable_subtype_coe.comp measurable_snd))
  refine ⟨fun j hj => ?_, ?_⟩
  · have := isProbabilityMeasure_mu (po62_model Q ζ α β) hP s₀ (t := j) fun i _ => hπm i
    refine Integrable.of_bound (measurable_rew _ s₀ (hu j) (hπm j)).aestronglyMeasurable
      (|Real.log (1 - po61_theta α β (T - j))| + B + |α| * po62_D α β B T s₀.1.1 j) ?_
    filter_upwards [po62_ae_bound h hζ hζm hB T s₀ j hj.le] with hh hhb
    rw [Real.norm_eq_abs]
    set s := lastState s₀ hh
    change |Real.log (ζ s.2 * s.1.1 ^ α - (po62_g h hζ T j s).1)| ≤ _
    simp only [po62_g, hj, ↓reduceDIte]
    have hy : 0 < ζ s.2 * s.1.1 ^ α := mul_pos (hζ _) (Real.rpow_pos_of_pos s.1.2 α)
    have h1θ : 0 < 1 - po61_theta α β (T - j) := by linarith [po61_theta_lt_one h (T - j)]
    rw [show ζ s.2 * s.1.1 ^ α - po61_theta α β (T - j) * (ζ s.2 * s.1.1 ^ α) =
      (1 - po61_theta α β (T - j)) * (ζ s.2 * s.1.1 ^ α) by ring,
      Real.log_mul h1θ.ne' hy.ne', Real.log_mul (hζ _).ne' (Real.rpow_pos_of_pos s.1.2 α).ne',
      Real.log_rpow s.1.2]
    calc |Real.log (1 - po61_theta α β (T - j)) + (Real.log (ζ s.2) + α * Real.log s.1.1)|
        ≤ |Real.log (1 - po61_theta α β (T - j))| + (|Real.log (ζ s.2)| + |α * Real.log s.1.1|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ _ := by
        rw [abs_mul]
        have := hB s.2
        have := mul_le_mul_of_nonneg_left hhb (abs_nonneg α)
        linarith
  · have := isProbabilityMeasure_mu (po62_model Q ζ α β) hP s₀ (t := T) fun i _ => hπm i
    have huT : Measurable (po62_model Q ζ α β).uT :=
      Real.measurable_log.comp ((hζ'.comp measurable_snd).mul
        ((measurable_subtype_coe.comp measurable_fst).pow_const α))
    refine Integrable.of_bound (huT.comp (measurable_lastState s₀ T)).aestronglyMeasurable
      (B + |α| * po62_D α β B T s₀.1.1 T) ?_
    filter_upwards [po62_ae_bound h hζ hζm hB T s₀ T le_rfl] with hh hhb
    rw [Real.norm_eq_abs]
    set s := lastState s₀ hh
    change |Real.log (ζ s.2 * s.1.1 ^ α)| ≤ _
    rw [Real.log_mul (hζ _).ne' (Real.rpow_pos_of_pos s.1.2 α).ne', Real.log_rpow s.1.2]
    calc |Real.log (ζ s.2) + α * Real.log s.1.1| ≤ |Real.log (ζ s.2)| + |α * Real.log s.1.1| :=
          abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        have := hB s.2
        have := mul_le_mul_of_nonneg_left hhb (abs_nonneg α)
        linarith

/-- **Exercise 6.2: the policies are optimal** (Miao, p. 189). For `α, β ∈ (0, 1)`, a Markov
kernel `Q` and a productivity `ζ > 0` with `ln ζ` measurable and bounded, and any initial state
`s₀ = (K₀, x₀)`: the plan generated by the investment policy `K_{t+1} = θ_{T−t} ζ(x_t) K_t^α` is
feasible, has integrable rewards, attains `V₀(K₀, x₀) = coef_T ln K₀ + E_T(x₀)`, and
`J(s₀, π) ≤ J(s₀, π*)` for every feasible plan `π` with integrable rewards. -/
theorem ex_6_2_optimal {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} [IsMarkovKernel Q]
    {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x) (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ}
    (hB : ∀ x, |Real.log (ζ x)| ≤ B) (T : ℕ) (s₀ : po61_Pos × X) :
    po_genPlan (po62_g h hζ T) s₀ ∈ feasiblePlans (po62_model Q ζ α β) (T : ℕ∞) s₀ ∧
      po_IntPlan (po62_model Q ζ α β) T s₀ (po_genPlan (po62_g h hζ T) s₀) ∧
      J0T (po62_model Q ζ α β) T s₀ (po_genPlan (po62_g h hζ T) s₀) =
        po62_V Q ζ α β T 0 s₀.1.1 s₀.2 ∧
      ∀ π ∈ feasiblePlans (po62_model Q ζ α β) (T : ℕ∞) s₀,
        po_IntPlan (po62_model Q ζ α β) T s₀ π →
          J0T (po62_model Q ζ α β) T s₀ π ≤
            J0T (po62_model Q ζ α β) T s₀ (po_genPlan (po62_g h hζ T) s₀) := by
  have hP : (po62_model Q ζ α β).IsMarkov := fun _ => po62_kernel_markov Q
  have hEint := po62_integrable_E (Q := Q) hζm hB α β
  have hint : ∀ j s (a : po61_Pos), Integrable (fun s' : po61_Pos × X =>
      po62_V Q ζ α β T (j + 1) s'.1.1 s'.2) ((po62_model Q ζ α β).P j (s, a)) := by
    intro j s a
    change Integrable _ (po62_kernel Q (s, a))
    rw [po62_kernel_apply]
    have hm : Measurable fun s' : po61_Pos × X => po62_V Q ζ α β T (j + 1) s'.1.1 s'.2 :=
      (measurable_const.mul (Real.measurable_log.comp (measurable_subtype_coe.comp
        measurable_fst))).add (((po62_E_bounded (Q := Q) hζm hB α β _).1).comp measurable_snd)
    refine (integrable_map_measure hm.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 ?_
    change Integrable (fun x' => po61_coef α β (T - (j + 1)) * Real.log a.1 +
      po62_E Q ζ α β (T - (j + 1)) x') (Q s.2)
    exact (integrable_const _).add (hEint _ s.2)
  have hval : ∀ j s (a : po61_Pos), ∫ s', po62_V Q ζ α β T (j + 1) s'.1.1 s'.2
      ∂(po62_model Q ζ α β).P j (s, a) = ∫ x', po62_V Q ζ α β T (j + 1) a.1 x' ∂Q s.2 := by
    intro j s a
    change ∫ s', _ ∂po62_kernel Q (s, a) = _
    rw [po62_kernel_apply]
    have hm : Measurable fun s' : po61_Pos × X => po62_V Q ζ α β T (j + 1) s'.1.1 s'.2 :=
      (measurable_const.mul (Real.measurable_log.comp (measurable_subtype_coe.comp
        measurable_fst))).add (((po62_E_bounded (Q := Q) hζm hB α β _).1).comp measurable_snd)
    rw [integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
  have hc := po_verification_intPlans (n := T) (M := po62_model Q ζ α β)
    (w := fun j s => po62_V Q ζ α β T j s.1.1 s.2) (g := po62_g h hζ T) hP h.β_pos.le
    (fun j _ => po62_measurable_g h hζ hζm T j)
    (fun j hj s a ha => ⟨hint j s a, by
      rw [hval]
      exact (ex_6_2 h hζ hζm hB hj s.1.2 s.2).1 a.1 a.2 ha⟩)
    (fun j hj s => by
      obtain ⟨-, ⟨-, hlt, heq⟩, -⟩ := ex_6_2 h (Q := Q) hζ hζm hB hj s.1.2 s.2
      have hg : po62_g h hζ T j s =
          ⟨po61_theta α β (T - j) * (ζ s.2 * s.1.1 ^ α), po62_policy_pos h hζ hj s⟩ := by
        simp only [po62_g, hj, ↓reduceDIte]
      refine ⟨by rw [hg]; exact hlt, ?_⟩
      change _ = Real.log (ζ s.2 * s.1.1 ^ α - (po62_g h hζ T j s).1) +
        β * ∫ s', po62_V Q ζ α β T (j + 1) s'.1.1 s'.2 ∂(po62_model Q ζ α β).P j
          (s, po62_g h hζ T j s)
      rw [hval, hg]
      exact heq.symm)
    (fun s => (ex_6_2_terminal h hζ T s.1.2 s.2)) s₀ (po62_intPlan h hζ hζm hB T s₀)
  exact ⟨hc.1, po62_intPlan h hζ hζm hB T s₀, hc.2.1, hc.2.2⟩

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The secretary problem: the Bellman equations and the optimal threshold

Miao, §6.6.1, pp. 185–186. Candidates `t = 1, …, N` arrive in random order; the state is `1` if
the current candidate is the best so far and `0` otherwise; stopping at a best-so-far candidate
at date `t` wins with probability `t/N`; the next candidate is the best so far with probability
`1/(t + 1)`. (That these are the probabilities of the problem is `secretary_prob` in
`MDPSecretary`; that the recursion below gives the values of the Markov decision problem of
Chapter 5 is `SecretaryMDP`.)

* `sec_V N t z`: the solution of the book's Bellman equation, `V_N(1) = 1`, `V_N(0) = 0`,
  `V_t(1) = max{t/N, V_{t+1}(1)/(t+1) + tV_{t+1}(0)/(t+1)}`,
  `V_t(0) = max{0, V_{t+1}(1)/(t+1) + tV_{t+1}(0)/(t+1)}` (`sec_bellman`, `sec_V_terminal`).
* (6.41)–(6.42) (`eq_6_41_6_42`); `V_t ≥ 0`, `V_t(1) ≥ V_t(0)`, `V_t(0)` nonincreasing.
* `sec_H N t = 1/t + ⋯ + 1/(N − 1)`, `sec_tau N` = τ of (6.43).
* The closed form `V_t(0) = (t/N)(1/t + ⋯ + 1/(N − 1))` for `τ ≤ t ≤ N` (`sec_V0_closed`), and the
  threshold structure: `V_t(0) ≤ t/N` for `τ ≤ t ≤ N` (stop at a best-so-far candidate) and
  `V_t(0) ≥ t/N` for `1 ≤ t < τ` (continue) (`sec_threshold`).
* **Corrections.** (6.43) gives `τ(4) = 2`, not the printed `τ(4) = 1` (`sec_tau_four`). With τ as
  in (6.43), τ is the first date at which a best-so-far candidate is accepted: it is optimal to
  reject the first `τ − 1` candidates (one candidate for `N = 4`, as the book's prose says), not
  `τ` as Proposition 6.6.1 states (`prop_6_6_1_misprint` in `SecretaryMDP`). The proof's claim
  "`t/N ≤ V_t(0)` for all `t ≤ τ`" fails at `t = τ` (`sec_threshold_misprint`); it holds for
  `t < τ`.
-/

namespace Miao.FiniteHorizonDP

/-- The book's Bellman equation for the secretary problem, by time to go `n = N − t`:
`sec_val N n z = V_{N−n}(z)`. -/
noncomputable def sec_val (N : ℕ) : ℕ → Fin 2 → ℝ
  | 0 => fun z => if z = 1 then 1 else 0
  | n + 1 => fun z =>
    if z = 1 then
      max (((N - (n + 1) : ℕ) : ℝ) / N)
        (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 1 +
          ((N - (n + 1) : ℕ) : ℝ) / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 0)
    else
      max 0 (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 1 +
        ((N - (n + 1) : ℕ) : ℝ) / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 0)

/-- `V_t(z)`, the value at date `t` in state `z` (Miao, p. 185). -/
noncomputable def sec_V (N t : ℕ) (z : Fin 2) : ℝ := sec_val N (N - t) z

/-- The continuation value `V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)`. -/
noncomputable def sec_C (N t : ℕ) : ℝ :=
  1 / ((t : ℝ) + 1) * sec_V N (t + 1) 1 + (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0

/-- Miao, p. 185: `V_N(1) = h(1) = 1`, `V_N(0) = h(0) = 0`. -/
theorem sec_V_terminal (N : ℕ) : sec_V N N 1 = 1 ∧ sec_V N N 0 = 0 := by
  simp [sec_V, sec_val]

/-- **The Bellman equation of the secretary problem** (Miao, p. 185): for `t < N`,
`V_t(1) = max{t/N, V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)}` and
`V_t(0) = max{0, V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)}`. -/
theorem sec_bellman (N : ℕ) {t : ℕ} (ht : t < N) :
    sec_V N t 1 = max ((t : ℝ) / N) (sec_C N t) ∧ sec_V N t 0 = max 0 (sec_C N t) := by
  have e1 : N - t = (N - (t + 1)) + 1 := by omega
  have e2 : N - (N - (t + 1) + 1) = t := by omega
  unfold sec_V sec_C
  rw [e1]
  simp only [sec_val, e2, ite_true]
  exact ⟨rfl, by simp [sec_V]⟩

theorem sec_V_nonneg (N : ℕ) : ∀ t z, 0 ≤ sec_V N t z := by
  have : ∀ n z, 0 ≤ sec_val N n z := by
    intro n
    induction n with
    | zero => intro z; simp only [sec_val]; split_ifs <;> norm_num
    | succ n ih =>
      intro z
      simp only [sec_val]
      split_ifs
      · exact le_max_of_le_left (by positivity)
      · exact le_max_left _ _
  exact fun t z => this _ z

theorem sec_C_nonneg (N t : ℕ) : 0 ≤ sec_C N t := by
  have := sec_V_nonneg N
  unfold sec_C
  have h1 := this (t + 1) 1
  have h0 := this (t + 1) 0
  positivity

/-- **(6.41)–(6.42)** (Miao, p. 185): for `t < N`, since `V_t ≥ 0`,
`V_t(0) = V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)` and `V_t(1) = max{t/N, V_t(0)}`. -/
theorem eq_6_41_6_42 (N : ℕ) {t : ℕ} (ht : t < N) :
    sec_V N t 0 = 1 / ((t : ℝ) + 1) * sec_V N (t + 1) 1 +
        (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0 ∧
      sec_V N t 1 = max ((t : ℝ) / N) (sec_V N t 0) := by
  obtain ⟨h1, h0⟩ := sec_bellman N ht
  rw [h0, max_eq_right (sec_C_nonneg N t)] at *
  exact ⟨rfl, h1⟩

/-- (6.42) at the terminal date too: `V_N(1) = max{N/N, V_N(0)}` (for `N ≥ 1`). -/
theorem eq_6_42_terminal {N : ℕ} (hN : 1 ≤ N) :
    sec_V N N 1 = max ((N : ℝ) / N) (sec_V N N 0) := by
  obtain ⟨h1, h0⟩ := sec_V_terminal N
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [h1, h0, div_self this]
  simp

/-- Miao, p. 186: `V_t(1) ≥ V_t(0)` (for `t ≤ N`). -/
theorem sec_V1_ge_V0 (N : ℕ) {t : ℕ} (ht : t ≤ N) : sec_V N t 0 ≤ sec_V N t 1 := by
  rcases Nat.lt_or_ge t N with h | h
  · obtain ⟨h1, h0⟩ := sec_bellman N h
    rw [h1, h0]
    exact max_le_max (by positivity) le_rfl
  · have : t = N := le_antisymm ht h
    subst this
    obtain ⟨h1, h0⟩ := sec_V_terminal t
    rw [h1, h0]
    norm_num

/-- Miao, p. 186: `V_t(0) ≥ V_{t+1}(0)` (from (6.41) and `V_{t+1}(1) ≥ V_{t+1}(0)`). -/
theorem sec_V0_succ_le (N : ℕ) {t : ℕ} (ht : t < N) : sec_V N (t + 1) 0 ≤ sec_V N t 0 := by
  rw [(eq_6_41_6_42 N ht).1]
  have h := sec_V1_ge_V0 N (show t + 1 ≤ N by omega)
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have key : 1 / ((t : ℝ) + 1) * sec_V N (t + 1) 0 +
      (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0 = sec_V N (t + 1) 0 := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1))
  linarith

theorem sec_V0_antitone (N : ℕ) {t t' : ℕ} (htt : t ≤ t') (ht' : t' ≤ N) :
    sec_V N t' 0 ≤ sec_V N t 0 := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact le_rfl
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with h | h
    · rw [h]
    · exact (sec_V0_succ_le N (by omega)).trans (ih (by omega) (by omega))

/-- `1/t + 1/(t + 1) + ⋯ + 1/(N − 1)` (Miao (6.43)). -/
noncomputable def sec_H (N t : ℕ) : ℝ := ∑ k ∈ Finset.Ico t N, (1 : ℝ) / k

/-- `τ = min{t ≥ 1 : 1/t + ⋯ + 1/(N − 1) < 1}` (Miao (6.43)). -/
noncomputable def sec_tau (N : ℕ) : ℕ := sInf {t : ℕ | 1 ≤ t ∧ sec_H N t < 1}

theorem sec_H_self (N : ℕ) : sec_H N N = 0 := by simp [sec_H]

theorem sec_H_succ {N t : ℕ} (ht : t < N) : sec_H N t = 1 / t + sec_H N (t + 1) := by
  unfold sec_H
  rw [Finset.sum_eq_sum_Ico_succ_bot ht]

theorem sec_H_nonneg (N t : ℕ) : 0 ≤ sec_H N t :=
  Finset.sum_nonneg fun k _ => by positivity

theorem sec_H_anti (N : ℕ) {t t' : ℕ} (h : t ≤ t') : sec_H N t' ≤ sec_H N t :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left h)
    fun k _ _ => by positivity

theorem sec_tau_spec {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ sec_tau N ∧ sec_H N (sec_tau N) < 1 ∧ sec_tau N ≤ N := by
  have hne : ({t : ℕ | 1 ≤ t ∧ sec_H N t < 1} : Set ℕ).Nonempty :=
    ⟨N, hN, by rw [sec_H_self]; norm_num⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hmem.1, hmem.2, Nat.sInf_le ⟨hN, by rw [sec_H_self]; norm_num⟩⟩

theorem sec_tau_min {N t : ℕ} (h1 : 1 ≤ t) (ht : t < sec_tau N) : 1 ≤ sec_H N t := by
  by_contra h
  exact Nat.notMem_of_lt_sInf ht ⟨h1, lt_of_not_ge h⟩

theorem sec_H_lt_one {N t : ℕ} (hN : 1 ≤ N) (ht : sec_tau N ≤ t) : sec_H N t < 1 :=
  lt_of_le_of_lt (sec_H_anti N ht) (sec_tau_spec hN).2.1

/-- **The closed form** (Miao, p. 186): for `τ ≤ t ≤ N`,
`V_t(0) = (t/N)(1/t + 1/(t + 1) + ⋯ + 1/(N − 1))`. -/
theorem sec_V0_closed {N : ℕ} (hN : 1 ≤ N) :
    ∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 = (t : ℝ) / N * sec_H N t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ n t, N - t = n → sec_tau N ≤ t → t ≤ N →
      sec_V N t 0 = (t : ℝ) / N * sec_H N t := by
    intro n
    induction n with
    | zero =>
      intro t hn _ ht
      have : t = N := by omega
      subst this
      rw [(sec_V_terminal t).2, sec_H_self, mul_zero]
    | succ n ih =>
      intro t hn hτ ht
      have htN : t < N := by omega
      have ht1 : 1 ≤ t := le_trans (sec_tau_spec hN).1 hτ
      have hIH := ih (t + 1) (by omega) (by omega) (by omega)
      have hH1 := sec_H_lt_one hN (show sec_tau N ≤ t + 1 by omega)
      have hV1 : sec_V N (t + 1) 1 = ((t : ℝ) + 1) / N := by
        rcases Nat.lt_or_ge (t + 1) N with h | h
        · rw [(eq_6_41_6_42 N h).2, hIH]
          push_cast
          refine max_eq_left ?_
          have : 0 ≤ ((t : ℝ) + 1) / N := by positivity
          nlinarith [sec_H_nonneg N (t + 1)]
        · have : t + 1 = N := by omega
          rw [this, (sec_V_terminal N).1]
          rw [← this]
          push_cast
          field_simp
      rw [(eq_6_41_6_42 N htN).1, hV1, hIH, sec_H_succ htN]
      have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      push_cast
      field_simp
  exact fun t hτ ht => key (N - t) t rfl hτ ht

/-- **The threshold structure** (Miao, p. 186), with τ as in (6.43): for `τ ≤ t ≤ N`,
`V_t(0) ≤ t/N`, so `V_t(1) = t/N` and accepting a best-so-far candidate is optimal; for
`1 ≤ t < τ`, `V_t(0) ≥ t/N`, so `V_t(1) = V_t(0)` and continuing is optimal. -/
theorem sec_threshold {N : ℕ} (hN : 1 ≤ N) :
    (∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 ≤ (t : ℝ) / N) ∧
      (∀ t, 1 ≤ t → t < sec_tau N → (t : ℝ) / N ≤ sec_V N t 0) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstop : ∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 ≤ (t : ℝ) / N := by
    intro t hτ ht
    rw [sec_V0_closed hN t hτ ht]
    have := sec_H_lt_one hN hτ
    have : 0 ≤ (t : ℝ) / N := by positivity
    nlinarith
  refine ⟨hstop, fun t ht1 htτ => ?_⟩
  obtain ⟨hτ1, -, hτN⟩ := sec_tau_spec hN
  set m := sec_tau N - 1 with hm
  have hm1 : t ≤ m := by omega
  have hmN : m < N := by omega
  have hmτ : m + 1 = sec_tau N := by omega
  have hVm : sec_V N m 0 = (m : ℝ) / N * sec_H N m := by
    have hcl := sec_V0_closed hN (m + 1) (by omega) (by omega)
    have hV1 : sec_V N (m + 1) 1 = ((m : ℝ) + 1) / N := by
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [(eq_6_41_6_42 N h).2, hcl]
        push_cast
        refine max_eq_left ?_
        have := sec_H_lt_one hN (show sec_tau N ≤ m + 1 by omega)
        have : 0 ≤ ((m : ℝ) + 1) / N := by positivity
        nlinarith [sec_H_nonneg N (m + 1)]
      · have : m + 1 = N := by omega
        rw [this, (sec_V_terminal N).1, ← this]
        push_cast
        field_simp
    rw [(eq_6_41_6_42 N hmN).1, hV1, hcl, sec_H_succ hmN]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast
    field_simp
  have hHm : 1 ≤ sec_H N m := sec_tau_min (by omega) (by omega)
  have h1 : (m : ℝ) / N ≤ sec_V N m 0 := by
    rw [hVm]
    have : 0 ≤ (m : ℝ) / N := by positivity
    nlinarith
  have h2 : (t : ℝ) / N ≤ (m : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm1) hNpos.le
  exact h2.trans (h1.trans (sec_V0_antitone N hm1 hmN.le))

/-- **τ(4) = 2, not 1** (Miao, p. 186): by (6.43), `1 + 1/2 + 1/3 ≥ 1` and `1/2 + 1/3 < 1`, so
`τ(4) = 2`. The book's `τ(4) = 1` is the number of candidates rejected, `τ − 1`. -/
theorem sec_tau_four : sec_tau 4 = 2 ∧ sec_tau 4 ≠ 1 ∧ sec_tau 4 - 1 = 1 := by
  have h3 : sec_H 4 3 = 1 / 3 := by
    rw [sec_H_succ (by norm_num), sec_H_self]
    norm_num
  have h2 : sec_H 4 2 = 5 / 6 := by
    rw [sec_H_succ (by norm_num), h3]
    norm_num
  have h1 : sec_H 4 1 = 11 / 6 := by
    rw [sec_H_succ (by norm_num), h2]
    norm_num
  have hτ : sec_tau 4 = 2 := by
    refine le_antisymm (Nat.sInf_le ⟨by norm_num, by rw [h2]; norm_num⟩) ?_
    refine le_csInf ⟨2, by norm_num, by rw [h2]; norm_num⟩ fun t ht => ?_
    obtain ⟨ht1, htH⟩ := ht
    by_contra hlt
    have : t = 1 := by omega
    subst this
    rw [h1] at htH
    norm_num at htH
  exact ⟨hτ, by rw [hτ]; norm_num, by rw [hτ]⟩

/-- **The book's "`t/N ≤ V_t(0)` for all `t ≤ τ`" fails at `t = τ`** (Miao, p. 186): for `N = 4`,
`τ = 2` and `V_2(0) = (2/4)(1/2 + 1/3) = 5/12 < 2/4`. -/
theorem sec_threshold_misprint : sec_V 4 2 0 = 5 / 12 ∧ sec_V 4 2 0 < (2 : ℝ) / 4 := by
  have hτ := sec_tau_four.1
  have h2 : sec_H 4 2 = 5 / 6 := by
    rw [sec_H_succ (by norm_num), sec_H_succ (by norm_num), sec_H_self]
    norm_num
  have := sec_V0_closed (N := 4) (by norm_num) 2 (by rw [hτ]) (by norm_num)
  rw [this, h2]
  norm_num

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The secretary problem as a Markov decision process: Proposition 6.6.1

Miao, §6.6.1, pp. 185–186, in Chapter 5's formulation `secretary N` (`MDPStoppingExamples`): the
optimal stopping problem recast as the Markov decision process `(secretary N).toMDP` on
`{0, 1} ∪ {ŝ}` (`Sum.inl z`, `Sum.inr ()`) with actions `1` = continue, `0` = stop, `β = 1`,
**dates shifted by one** (MDP date `t` is the book's date `t + 1`), and horizon `T = N − 1`.

* `sec_integral_cont`, `sec_integral_stop`, `sec_integral_hat`: the integrals against the
  kernels; `sec_bellmanVal_*`: the right-hand side of (6.19).
* `sec_mdp_values`: by Theorem 6.3.2, the recursion of `SecretaryBellman` gives the value
  functions of the Markov decision problem, `V_{t+1}^{MDP}(z) = sec_V N (t + 1) z`; so the Bellman
  equations (6.41)–(6.42) are those of the problem's values.
* **Proposition 6.6.1** (`prop_6_6_1`), corrected: the plan "accept the first best-so-far candidate
  at a date `≥ τ`" (`sec_rule N τ`), i.e. reject the first `τ − 1` candidates, is optimal, with
  value `V_1(1)`; it is optimal from every history (`prop_6_6_1_from`).
* `prop_6_6_1_misprint`: the printed rule "interview `τ` candidates and subsequently choose the
  first candidate better than those" (`sec_rule N (τ + 1)`) is not optimal: for `N = 4` it wins
  with probability `5/12 < 11/24 = V_1(1)`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

theorem po_fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Every function on `{0, 1} ∪ {ŝ}` is measurable (the space has no `MeasurableSingletonClass`
instance in Mathlib, so this is proved from the two summands). -/
theorem sec_measurable {β : Type*} [MeasurableSpace β] (f : Fin 2 ⊕ Unit → β) : Measurable f := by
  rw [← Sum.elim_comp_inl_inr f]
  exact (measurable_of_countable _).sumElim (measurable_of_countable _)

theorem sec_integrable (μ : Measure (Fin 2 ⊕ Unit)) [IsFiniteMeasure μ]
    (w : Fin 2 ⊕ Unit → ℝ) : Integrable w μ :=
  Integrable.of_bound (sec_measurable w).aestronglyMeasurable (∑ x, |w x|)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun x _ => abs_nonneg (w x)) (Finset.mem_univ s))

theorem sec_isMarkov (N : ℕ) : (secretary N).toMDP.IsMarkov := (secretary_assumptions N).1

theorem sec_P_cont (N t : ℕ) (z : Fin 2) :
    (secretary N).toMDP.P t (Sum.inl z, 1) = (bern (1 / ((t : ℝ) + 2))).map Sum.inl := by
  change stopKernel ((secretary N).Q t) (Sum.inl z, 1) = _
  rw [stopKernel, famKernel_apply]
  simp only [ite_true]
  rw [contKernel_inl]
  rfl

theorem sec_P_stop (N t : ℕ) (s : Fin 2 ⊕ Unit) :
    (secretary N).toMDP.P t (s, 0) = Measure.dirac sHat := by
  change stopKernel ((secretary N).Q t) (s, 0) = _
  rw [stopKernel, famKernel_apply]
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, Kernel.const_apply]

theorem sec_P_hat (N t : ℕ) (u : Unit) (a : Fin 2) :
    (secretary N).toMDP.P t (Sum.inr u, a) = Measure.dirac sHat := by
  change stopKernel ((secretary N).Q t) (Sum.inr u, a) = _
  rw [stopKernel, famKernel_apply]
  split_ifs
  · exact contKernel_inr _ u
  · rfl

/-- The integral after continuing at a candidate:
`∫ w dP = w(1)/(t + 2) + (t + 1)w(0)/(t + 2)` (MDP date `t`, book date `t + 1`). -/
theorem sec_integral_cont (N t : ℕ) (z : Fin 2) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s, w s ∂(secretary N).toMDP.P t (Sum.inl z, 1) =
      1 / ((t : ℝ) + 2) * w (Sum.inl 1) + ((t : ℝ) + 1) / ((t : ℝ) + 2) * w (Sum.inl 0) := by
  have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 2) := by positivity
  have h1 : 1 / ((t : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have := isProbabilityMeasure_bern h0 h1
  rw [sec_P_cont, integral_map measurable_inl.aemeasurable
    (sec_measurable _).aestronglyMeasurable, integral_fintype Integrable.of_finite,
    Fin.sum_univ_two]
  obtain ⟨e1, e0⟩ := bern_one (1 / ((t : ℝ) + 2))
  simp only [measureReal_def, e1, e0, smul_eq_mul]
  rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  have : 1 - 1 / ((t : ℝ) + 2) = ((t : ℝ) + 1) / ((t : ℝ) + 2) := by field_simp; ring
  rw [this]
  ring

theorem sec_integral_stop (N t : ℕ) (s : Fin 2 ⊕ Unit) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s', w s' ∂(secretary N).toMDP.P t (s, 0) = w sHat := by
  rw [sec_P_stop, integral_dirac' _ _ (sec_measurable w).stronglyMeasurable]

theorem sec_integral_hat (N t : ℕ) (u : Unit) (a : Fin 2) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s', w s' ∂(secretary N).toMDP.P t (Sum.inr u, a) = w sHat := by
  rw [sec_P_hat, integral_dirac' _ _ (sec_measurable w).stronglyMeasurable]

theorem sec_u_inl (N t : ℕ) (z a : Fin 2) :
    (secretary N).toMDP.u t (Sum.inl z, a) =
      if a = 1 then 0 else if z = 1 then ((min (t + 1) N : ℕ) : ℝ) / N else 0 := by
  simp [StoppingProblem.toMDP, secretary]

theorem sec_u_inr (N t : ℕ) (u : Unit) (a : Fin 2) :
    (secretary N).toMDP.u t (Sum.inr u, a) = 0 := rfl

/-- The value functions of the Markov decision problem, in MDP dates: `w_t(z) = V_{t+1}(z)` and
`w_t(ŝ) = 0`. -/
noncomputable def sec_w (N t : ℕ) : Fin 2 ⊕ Unit → ℝ :=
  Sum.elim (fun z => sec_V N (t + 1) z) fun _ => 0

/-- The threshold rule: at MDP date `t` (the `(t + 1)`-th candidate), stop at a best-so-far
candidate if `t + 1 ≥ r`, otherwise continue. -/
def sec_rule (r : ℕ) (t : ℕ) : Fin 2 ⊕ Unit → Fin 2 :=
  Sum.elim (fun z => if z = 1 ∧ r ≤ t + 1 then 0 else 1) fun _ => 1

theorem sec_bv_cont {N t : ℕ} (z : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) 1 = sec_C N (t + 1) := by
  unfold po_bellmanVal
  rw [sec_integral_cont, sec_u_inl]
  simp only [ite_true, zero_add, sec_w, Sum.elim_inl, sec_C]
  have : (secretary N).toMDP.β = 1 := rfl
  rw [this, one_mul]
  push_cast
  ring_nf

theorem sec_bv_stop {N t : ℕ} (ht : t + 1 ≤ N) (z : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) 0 =
      if z = 1 then ((t : ℝ) + 1) / N else 0 := by
  unfold po_bellmanVal
  rw [sec_integral_stop, sec_u_inl, min_eq_left ht]
  have : (secretary N).toMDP.β = 1 := rfl
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, sec_w, sHat, Sum.elim_inr, this,
    mul_zero, add_zero]
  push_cast
  rfl

theorem sec_bv_hat {N t : ℕ} (u : Unit) (a : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inr u) a = 0 := by
  unfold po_bellmanVal
  rw [sec_integral_hat, sec_u_inr]
  simp [sec_w, sHat]

theorem sec_bounded (N : ℕ) : BoundedRewards (secretary N).toMDP 1 := by
  refine ⟨fun t x => ?_, fun s => ?_⟩
  · obtain ⟨s, a⟩ := x
    cases s with
    | inl z =>
      rw [sec_u_inl]
      split_ifs
      · simp
      · rcases Nat.eq_zero_or_pos N with hN | hN
        · simp [hN]
        · rw [abs_of_nonneg (by positivity), div_le_one (by exact_mod_cast hN)]
          exact_mod_cast min_le_right _ _
      · simp
    | inr u => rw [sec_u_inr]; simp
  · cases s with
    | inl z => simp only [StoppingProblem.toMDP, Sum.elim_inl, secretary]; split_ifs <;> simp
    | inr u => simp [StoppingProblem.toMDP]

theorem sec_assumption (N T : ℕ) : po_Assumption513 (secretary N).toMDP T :=
  po_assumption513_of_bounded (sec_isMarkov N) (sec_bounded N)
    (fun _ => measurable_toMDP_u _ measurable_const (measurable_of_countable _))
    (measurable_toMDP_uT _ (measurable_of_countable _)) T

/-- The Bellman equation of the Markov decision problem is solved by `sec_w`, and the threshold
rule with `r = τ` selects maximisers, at every MDP date `t < N − 1`. -/
theorem sec_solves {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t < N - 1) (s : Fin 2 ⊕ Unit) :
    po_SolvesAt (secretary N).toMDP (sec_w N) t s ∧
      sec_rule (sec_tau N) t s ∈ po_G (secretary N).toMDP (sec_w N) t s := by
  have hk : t + 1 < N := by omega
  obtain ⟨hV1, hV0⟩ := sec_bellman N hk
  have hC := sec_C_nonneg N (t + 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hstop, hcont⟩ := sec_threshold (show 1 ≤ N by omega)
  push_cast at hV1
  cases s with
  | inr u =>
    refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_ <;>
      simp only [sec_bv_hat, sec_w, Sum.elim_inr, le_refl]
  | inl z =>
    have hle : ∀ a ∈ (secretary N).toMDP.Γ (Sum.inl z),
        po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) a ≤ sec_w N t (Sum.inl z) := by
      intro a _
      simp only [sec_w, Sum.elim_inl]
      rcases po_fin2_cases a with rfl | rfl
      · rw [sec_bv_stop hk.le]
        rcases po_fin2_cases z with rfl | rfl
        · simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false]
          rw [hV0]
          exact le_max_left _ _
        · simp only [ite_true]
          rw [hV1]
          exact le_max_left _ _
      · rw [sec_bv_cont]
        rcases po_fin2_cases z with rfl | rfl
        · rw [hV0]
          exact le_max_right _ _
        · rw [hV1]
          exact le_max_right _ _
    refine po_solvesAt_of_max hle (Set.mem_univ _) ?_
    simp only [sec_w, Sum.elim_inl, sec_rule]
    rcases po_fin2_cases z with rfl | rfl
    · simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, ite_false]
      rw [sec_bv_cont, hV0, max_eq_right hC]
    · simp only [true_and]
      split_ifs with hτ
      · rw [sec_bv_stop hk.le]
        simp only [ite_true]
        have h1 := hstop (t + 1) hτ hk.le
        rw [hV0] at h1
        push_cast at h1
        rw [hV1, max_eq_left (le_trans (le_max_right _ _) h1)]
      · rw [sec_bv_cont]
        have h1 := hcont (t + 1) (by omega) (by omega)
        rw [hV0, max_eq_right hC] at h1
        push_cast at h1
        rw [hV1, max_eq_right h1]

theorem sec_wT {N : ℕ} (hN : 1 ≤ N) (s : Fin 2 ⊕ Unit) :
    sec_w N (N - 1) s = (secretary N).toMDP.uT s := by
  cases s with
  | inl z =>
    simp only [sec_w, Sum.elim_inl, Nat.sub_add_cancel hN, StoppingProblem.toMDP, secretary]
    rcases po_fin2_cases z with rfl | rfl
    · simp [(sec_V_terminal N).2]
    · simp [(sec_V_terminal N).1]
  | inr u => rfl

/-- **The secretary problem's value functions** (Miao, pp. 185–186). By Theorem 6.3.2, for every
MDP date `t ≤ N − 1` and history `sᵗ`, the value of the sequence problem (6.14) is `sec_w N t`
(the book's `V_{t+1}`), and the threshold plan with `r = τ` attains it. -/
theorem sec_mdp_values {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 2 ⊕ Unit) :
    po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t)) ∈
        po_plansFrom (secretary N).toMDP (N - 1) t h ∧
      po_JFrom (secretary N).toMDP (N - 1) t h
        (po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t))) = sec_w N t (h (Fin.last t)) ∧
      po_VFrom (secretary N).toMDP (N - 1) t h = sec_w N t (h (Fin.last t)) :=
  theorem_6_3_2 (sec_isMarkov N) zero_le_one (sec_assumption N (N - 1))
    (fun t _ s a _ => by
      have := sec_isMarkov N t
      exact sec_integrable _ _)
    (fun t ht s => (sec_solves hN ht s).1) (fun _ _ => sec_measurable _)
    (fun t ht s => (sec_solves hN ht s).2) (sec_wT (by omega)) t ht h

/-- **Proposition 6.6.1** (Miao, p. 185), corrected. For `N ≥ 2`, with τ as in (6.43), the plan
"reject the first `τ − 1` candidates, then accept the first candidate who is the best so far"
(stop at a best-so-far candidate at a date `≥ τ`) is optimal from the first candidate
(`s₀ = 1`: the first candidate is the best so far), and its probability of choosing the best is
`V_1(1)`. -/
theorem prop_6_6_1 {N : ℕ} (hN : 2 ≤ N) :
    po_genPlan (sec_rule (sec_tau N)) (Sum.inl 1) ∈
        feasiblePlans (secretary N).toMDP ((N - 1 : ℕ) : ℕ∞) (Sum.inl 1) ∧
      J0T (secretary N).toMDP (N - 1) (Sum.inl 1) (po_genPlan (sec_rule (sec_tau N))
        (Sum.inl 1)) = sec_V N 1 1 ∧
      V0 (secretary N).toMDP (N - 1) (Sum.inl 1) = sec_V N 1 1 := by
  have := sec_mdp_values hN (Nat.zero_le _) fun _ => Sum.inl 1
  exact this

/-- Proposition 6.6.1 from every history: the threshold plan is optimal at every date `t` from
every history (Theorem 6.3.2), in particular after any history reached by following it. -/
theorem prop_6_6_1_from {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 2 ⊕ Unit) :
    (po_JFrom (secretary N).toMDP (N - 1) t h
      (po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t))) : EReal) =
      po_VFrom (secretary N).toMDP (N - 1) t h := by
  obtain ⟨-, h1, h2⟩ := sec_mdp_values hN ht h
  rw [h1, h2]

/-- The probabilities of winning under the rule `sec_rule 3` for `N = 4`, by date. -/
noncomputable def sec4_w : ℕ → Fin 2 ⊕ Unit → ℝ := fun t =>
  Sum.elim (fun z => if t = 3 then (if z = 1 then 1 else 0)
    else if t = 2 then (if z = 1 then 3 / 4 else 1 / 4) else 5 / 12) fun _ => 0

/-- **The printed Proposition 6.6.1 is off by one** (Miao, p. 185): for `N = 4`, `τ = 2` by
(6.43), and the rule "interview `τ` candidates and subsequently choose the first candidate that is
better than those `τ`" (`sec_rule (τ + 1)`) wins with probability `5/12`, less than the optimal
`V_1(1) = 11/24`. -/
theorem prop_6_6_1_misprint :
    J0T (secretary 4).toMDP 3 (Sum.inl 1) (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) =
        5 / 12 ∧ sec_V 4 1 1 = 11 / 24 ∧
      J0T (secretary 4).toMDP 3 (Sum.inl 1) (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) <
        V0 (secretary 4).toMDP 3 (Sum.inl 1) := by
  have hτ := sec_tau_four.1
  have hV : sec_V 4 1 1 = 11 / 24 := by
    obtain ⟨h0, h1⟩ := eq_6_41_6_42 4 (t := 1) (by norm_num)
    have h20 := sec_threshold_misprint.1
    have h21 := (eq_6_41_6_42 4 (t := 2) (by norm_num)).2
    rw [h20] at h21
    norm_num at h21
    rw [h1, h0, h21, h20]
    norm_num
  have hF : po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1) ∈
      feasiblePlans (secretary 4).toMDP ((3 : ℕ) : ℕ∞) (Sum.inl 1) :=
    po_genPlan_feasible (fun _ _ => sec_measurable _) (fun _ _ _ => Set.mem_univ _) _
  have hJ : J0T (secretary 4).toMDP 3 (Sum.inl 1)
      (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) = 5 / 12 := by
    have := po_policy_value 3 (secretary 4).toMDP sec4_w (sec_rule (sec_tau 4 + 1))
      (sec_isMarkov 4) (fun _ _ => sec_measurable _) (fun j hj s => ?_) (fun s => ?_)
      (Sum.inl 1) (po_intPlan_of_assumption513 (sec_assumption 4 3 0 (Nat.zero_le 3)) hF)
    · rw [this]
      simp [sec4_w]
    · have hβ : (secretary 4).toMDP.β = 1 := rfl
      rw [hτ, hβ, one_mul]
      cases s with
      | inr u =>
        rw [sec_u_inr, sec_rule, Sum.elim_inr, sec_integral_hat]
        simp [sec4_w, sHat]
      | inl z =>
        interval_cases j <;> rcases po_fin2_cases z with rfl | rfl <;>
          simp [sec_rule, sec_u_inl, sec_integral_cont, sec_integral_stop, sec4_w, sHat] <;>
          norm_num
    · cases s with
      | inr u => rfl
      | inl z =>
        rcases po_fin2_cases z with rfl | rfl <;> simp [sec4_w, StoppingProblem.toMDP, secretary]
  refine ⟨hJ, hV, ?_⟩
  rw [hJ, (prop_6_6_1 (N := 4) (by norm_num)).2.2, hV]
  norm_num

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The secretary problem for many candidates: `τ(N)/N → 1/e`

Miao, p. 186: "for `N` sufficiently large, `1 ≃ 1/τ(N) + ⋯ + 1/(N − 1) ≃ ∫_{τ(N)}^N dx/x`, thus
`τ(N)/N ≃ 1/e ≃ 0.368`." Made precise:

* `sec_log_le_H`, `sec_H_le_log`: `ln(N/t) ≤ 1/t + ⋯ + 1/(N − 1) ≤ ln((N − 1)/(t − 1))`
  (the integral comparison, via `ln(1 + x) ≤ x`).
* `sec_tau_bounds`: `1/e < τ(N)/N ≤ 1/e + 2/N` for every `N ≥ 1`, with τ as in (6.43).
* `sec_tau_limit`: **`τ(N)/N → 1/e`** as `N → ∞`; and `0.3678 < 1/e < 0.3679`
  (`sec_inv_e_approx`), the book's 36.8%.
-/

namespace Miao.FiniteHorizonDP

open Filter Topology

theorem sec_H_succ_top {N t : ℕ} (h : t ≤ N) : sec_H (N + 1) t = sec_H N t + 1 / (N : ℝ) := by
  unfold sec_H
  rw [Finset.sum_Ico_succ_top h]

/-- `ln(N/t) ≤ 1/t + ⋯ + 1/(N − 1)` for `1 ≤ t ≤ N`. -/
theorem sec_log_le_H {t : ℕ} (ht : 1 ≤ t) : ∀ N, t ≤ N → Real.log ((N : ℝ) / t) ≤ sec_H N t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le hN with h | h
    · rw [← h, sec_H_self, div_self ht0.ne', Real.log_one]
    · have hN' : t ≤ N := by omega
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [sec_H_succ_top hN']
      have hsplit : Real.log (((N + 1 : ℕ) : ℝ) / t) =
          Real.log ((N : ℝ) / t) + Real.log (((N : ℝ) + 1) / N) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp
      have hstep : Real.log (((N : ℝ) + 1) / N) ≤ 1 / N := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
        have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
        linarith
      rw [hsplit]
      linarith [ih hN']

/-- `1/t + ⋯ + 1/(N − 1) ≤ ln((N − 1)/(t − 1))` for `2 ≤ t ≤ N`. -/
theorem sec_H_le_log {t : ℕ} (ht : 2 ≤ t) :
    ∀ N, t ≤ N → sec_H N t ≤ Real.log (((N : ℝ) - 1) / ((t : ℝ) - 1)) := by
  have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le hN with h | h
    · rw [← h, sec_H_self, div_self ht1.ne', Real.log_one]
    · have hN' : t ≤ N := by omega
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
        linarith
      have hNpos : (0 : ℝ) < N := by linarith
      rw [sec_H_succ_top hN']
      have hsplit : Real.log ((((N + 1 : ℕ) : ℝ) - 1) / ((t : ℝ) - 1)) =
          Real.log (((N : ℝ) - 1) / ((t : ℝ) - 1)) + Real.log ((N : ℝ) / ((N : ℝ) - 1)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp
        ring
      have hstep : 1 / (N : ℝ) ≤ Real.log ((N : ℝ) / ((N : ℝ) - 1)) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) - 1) / N by positivity)
        have e : ((N : ℝ) - 1) / N - 1 = -(1 / N) := by field_simp; ring
        have e2 : Real.log ((N : ℝ) / ((N : ℝ) - 1)) = -Real.log (((N : ℝ) - 1) / N) := by
          rw [← Real.log_inv, inv_div]
        rw [e2]
        linarith
      rw [hsplit]
      linarith [ih hN']

/-- **Bounds on τ(N)/N**: `1/e < τ(N)/N ≤ 1/e + 2/N` for `N ≥ 1`, with τ as in (6.43). -/
theorem sec_tau_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-1) < (sec_tau N : ℝ) / N ∧ (sec_tau N : ℝ) / N ≤ Real.exp (-1) + 2 / N := by
  obtain ⟨hτ1, hτH, hτN⟩ := sec_tau_spec hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hτpos : (0 : ℝ) < sec_tau N := by exact_mod_cast hτ1
  refine ⟨?_, ?_⟩
  · have h1 := sec_log_le_H hτ1 N hτN
    have h2 : Real.log ((N : ℝ) / sec_tau N) < 1 := lt_of_le_of_lt h1 hτH
    have h3 : (N : ℝ) / sec_tau N < Real.exp 1 :=
      (Real.log_lt_iff_lt_exp (by positivity)).1 h2
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by positivity), inv_div]
    exact h3
  · have he := Real.exp_pos (-1)
    rcases Nat.lt_or_ge (sec_tau N) 3 with h | h
    · have : (sec_tau N : ℝ) ≤ 2 := by exact_mod_cast (show sec_tau N ≤ 2 by omega)
      have : (sec_tau N : ℝ) / N ≤ 2 / N := div_le_div_of_nonneg_right this hNpos.le
      linarith
    · set m := sec_tau N - 1 with hm
      have hm2 : 2 ≤ m := by omega
      have hHm : 1 ≤ sec_H N m := sec_tau_min (by omega) (by omega)
      have hlog := sec_H_le_log hm2 N (by omega)
      have hmr : (m : ℝ) - 1 = (sec_tau N : ℝ) - 2 := by
        rw [hm]
        push_cast [show 1 ≤ sec_tau N by omega]
        ring
      rw [hmr] at hlog
      have hτ2 : (0 : ℝ) < (sec_tau N : ℝ) - 2 := by
        have : (3 : ℝ) ≤ sec_tau N := by exact_mod_cast h
        linarith
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (sec_tau N : ℝ) ≤ N := by exact_mod_cast hτN
        linarith
      have h1 : 1 ≤ Real.log (((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2)) := le_trans hHm hlog
      have h2 : Real.exp 1 ≤ ((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2))]
        exact Real.exp_le_exp.2 h1
      have h3 : (sec_tau N : ℝ) - 2 ≤ ((N : ℝ) - 1) * Real.exp (-1) := by
        rw [le_div_iff₀ hτ2] at h2
        have he1 : Real.exp 1 * Real.exp (-1) = 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
      nlinarith

/-- **`τ(N)/N → 1/e`** (Miao, p. 186), with τ as in (6.43): with many candidates the employer
should interview about `N/e` of them before accepting the best so far. -/
theorem sec_tau_limit :
    Tendsto (fun N : ℕ => (sec_tau N : ℝ) / N) atTop (𝓝 (Real.exp (-1))) := by
  have hup : Tendsto (fun N : ℕ => Real.exp (-1) + 2 / (N : ℝ)) atTop (𝓝 (Real.exp (-1))) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (sec_tau_bounds hN).1.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (sec_tau_bounds hN).2

/-- Miao, p. 186: `1/e ≃ 0.368`; precisely `0.3678 < 1/e < 0.3679`. -/
theorem sec_inv_e_approx : 0.3678 < Real.exp (-1) ∧ Real.exp (-1) < 0.3679 := by
  rw [Real.exp_neg]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  constructor
  · rw [lt_inv_comm₀ (by norm_num) hpos]
    linarith
  · rw [inv_lt_comm₀ hpos (by norm_num)]
    linarith

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 6.3–6.4: two variants of the secretary problem

Miao, p. 189. Dates are the book's: the `k`-th candidate is seen at date `k = 1, …, N`.

**Exercise 6.3** (choose one of the two best). The state is the relative rank of the current
candidate among the first `k`: `1` (best so far), `2` (second best so far) or `0` (other); the
model is Chapter 5's `secretaryTwo` (Exercise 5.3), whose payoffs are the probabilities that a
candidate of relative rank `1` or `2` among the first `k` is among the two best of all,
`g_k(1) = k(2N − k − 1)/(N(N − 1))`, `g_k(2) = k(k − 1)/(N(N − 1))` (their counting derivation is
not formalised), and the next candidate has relative rank `1` or `2` with probability
`1/(k + 1)` each.
* The Bellman equation `V_k(r) = max{g_k(r), W_k}`,
  `W_k = (V_{k+1}(1) + V_{k+1}(2))/(k + 1) + (k − 1)V_{k+1}(0)/(k + 1)`, `V_N(1) = V_N(2) = 1`,
  `V_N(0) = 0` (`two_V`, `ex_6_3_bellman`).
* The threshold form (`ex_6_3_threshold`): `W_k` is nonincreasing and `g_k(r)` nondecreasing in
  `k`, so for each relative rank the dates at which stopping is optimal form a final segment
  `{τ_r, …, N}`; and stopping at relative rank `2` implies stopping at relative rank `1`, so
  `τ_1 ≤ τ_2`.
* The explicit part (`ex_6_3_rank2`): stopping at a second-best-so-far candidate at date
  `k ≤ N − 1` is optimal if and only if `3k ≥ 2N + 1`, i.e. `τ_2 = ⌈(2N + 1)/3⌉`; on those dates
  `W_k = 2k(N − k)/(N(N − 1))` and `V_k(r) = g_k(r)` for `r = 1, 2`. In general
  `W_k ≥ 2k(N − k)/(N(N − 1))` (`ex_6_3_lower`). The first threshold `τ_1` has no closed form; its
  asymptotics (`τ_1/N → 0.347`) are not formalised.
* `ex_6_3_mdp` (in `SecretaryTwoMDP`): by Theorem 6.3.2 the recursion gives the value functions of
  Chapter 5's Markov decision problem `(secretaryTwo N).toMDP`, and the threshold rule is optimal.

**Exercise 6.4** (minimise the expected rank; the book's "maximize the expected rank" means the
rank number is to be minimised, rank `1` being the best). The state is the relative rank
`r ∈ {1, …, k}`; stopping at relative rank `r` at date `k` gives the expected absolute rank
`r(N + 1)/(k + 1)` (taken as the model's data; its derivation is not formalised); the next
relative rank is uniform on `{1, …, k + 1}`.
* The Bellman equation `V_k(r) = min{r(N + 1)/(k + 1), W_k}`,
  `W_k = (1/(k + 1)) ∑_{r'=1}^{k+1} V_{k+1}(r')`, `V_N(r) = r` (`rank_V`, `ex_6_4_bellman`).
* The threshold form (`ex_6_4_threshold`): stopping at date `k` is optimal exactly for the
  relative ranks `r ≤ s_k = (k + 1)W_k/(N + 1)`, and `s_k` is nondecreasing in `k` (since `W_k` is
  nondecreasing).
* Explicit values: `W_{N−1} = (N + 1)/2` (`ex_6_4_last`) and, for `N = 3`, the minimal expected
  rank is `5/3` (`ex_6_4_three`). The Chow–Moriguti–Robbins–Samuels limit `≈ 3.8695` as
  `N → ∞` is out of scope and not formalised.
-/

namespace Miao.FiniteHorizonDP

/-! ### Exercise 6.3 -/

/-- The payoff of stopping at relative rank `r` at date `k` (Exercise 6.3). -/
noncomputable def two_g (N k : ℕ) (r : Fin 3) : ℝ :=
  if r = 1 then (k : ℝ) * (2 * N - k - 1) / (N * (N - 1))
  else if r = 2 then (k : ℝ) * (k - 1) / (N * (N - 1)) else 0

/-- The Bellman equation of Exercise 6.3, by time to go `n = N − k`. -/
noncomputable def two_val (N : ℕ) : ℕ → Fin 3 → ℝ
  | 0 => fun r => if r = 0 then 0 else 1
  | n + 1 => fun r =>
    max (two_g N (N - (n + 1)) r)
      ((two_val N n 1 + two_val N n 2) / (((N - (n + 1) : ℕ) : ℝ) + 1) +
        (((N - (n + 1) : ℕ) : ℝ) - 1) / (((N - (n + 1) : ℕ) : ℝ) + 1) * two_val N n 0)

/-- `V_k(r)` of Exercise 6.3. -/
noncomputable def two_V (N k : ℕ) (r : Fin 3) : ℝ := two_val N (N - k) r

/-- The continuation value `W_k` of Exercise 6.3. -/
noncomputable def two_W (N k : ℕ) : ℝ :=
  (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) +
    ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_V N (k + 1) 0

/-- **Exercise 6.3: the Bellman equation** (Miao, p. 189): `V_N(0) = 0`, `V_N(1) = V_N(2) = 1`,
and `V_k(r) = max{g_k(r), W_k}` for `k < N`. -/
theorem ex_6_3_bellman (N : ℕ) :
    (two_V N N 0 = 0 ∧ two_V N N 1 = 1 ∧ two_V N N 2 = 1) ∧
      ∀ k < N, ∀ r, two_V N k r = max (two_g N k r) (two_W N k) := by
  refine ⟨by simp [two_V, two_val], fun k hk r => ?_⟩
  have e1 : N - k = (N - (k + 1)) + 1 := by omega
  have e2 : N - (N - (k + 1) + 1) = k := by omega
  unfold two_V two_W
  rw [e1]
  simp only [two_val, e2]
  rfl

theorem two_g_nonneg {N k : ℕ} (hk : k ≤ N) (r : Fin 3) : 0 ≤ two_g N k r := by
  unfold two_g
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hden : 0 ≤ (N : ℝ) * (N - 1) := by nlinarith
  split_ifs
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h0
      exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden
  · exact le_rfl

theorem two_V_nonneg {N k : ℕ} (hk : k ≤ N) (r : Fin 3) : 0 ≤ two_V N k r := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [(ex_6_3_bellman N).2 k h r]
    exact le_max_of_le_left (two_g_nonneg hk r)
  · have : k = N := le_antisymm hk h
    subst this
    obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman k).1
    fin_cases r
    · simp [h0]
    · simp [h1]
    · simp [h2]

theorem two_W_nonneg {N k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) : 0 ≤ two_W N k := by
  unfold two_W
  have h1 := two_V_nonneg (N := N) (k := k + 1) (by omega) 1
  have h2 := two_V_nonneg (N := N) (k := k + 1) (by omega) 2
  have h0 := two_V_nonneg (N := N) (k := k + 1) (by omega) 0
  have : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  positivity

theorem two_V0 {N k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) : two_V N k 0 = two_W N k := by
  rw [(ex_6_3_bellman N).2 k hk 0]
  simp only [two_g, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, ite_false]
  exact max_eq_right (two_W_nonneg hk1 hk)

theorem two_V_ge_V0 {N k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N) (r : Fin 3) :
    two_V N k 0 ≤ two_V N k r := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [two_V0 hk1 h, (ex_6_3_bellman N).2 k h r]
    exact le_max_right _ _
  · have : k = N := le_antisymm hk h
    subst this
    obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman k).1
    rw [h0]
    exact two_V_nonneg le_rfl r

/-- `W_k` is nonincreasing. -/
theorem two_W_anti {N k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 < N) : two_W N (k + 1) ≤ two_W N k := by
  rw [← two_V0 (by omega) hk]
  have h1 := two_V_ge_V0 (N := N) (k := k + 1) (by omega) hk.le 1
  have h2 := two_V_ge_V0 (N := N) (k := k + 1) (by omega) hk.le 2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  unfold two_W
  have e : (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) +
      ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_V N (k + 1) 0 - two_V N (k + 1) 0 =
      ((two_V N (k + 1) 1 - two_V N (k + 1) 0) + (two_V N (k + 1) 2 - two_V N (k + 1) 0)) /
        ((k : ℝ) + 1) := by
    field_simp
    ring
  have : 0 ≤ ((two_V N (k + 1) 1 - two_V N (k + 1) 0) +
      (two_V N (k + 1) 2 - two_V N (k + 1) 0)) / ((k : ℝ) + 1) :=
    div_nonneg (by linarith) hpos.le
  linarith

theorem two_W_anti' {N k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k') (hk' : k' < N) :
    two_W N k' ≤ two_W N k := by
  induction k' with
  | zero => omega
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with h | h
    · rw [h]
    · exact (two_W_anti (by omega) hk').trans (ih (by omega) (by omega))

/-- The payoffs are nondecreasing in the date, and `g_k(2) ≤ g_k(1)`. -/
theorem two_g_mono {N k : ℕ} (hk : k + 1 ≤ N) :
    two_g N k 1 ≤ two_g N (k + 1) 1 ∧ two_g N k 2 ≤ two_g N (k + 1) 2 ∧
      two_g N k 2 ≤ two_g N k 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hden : 0 ≤ (N : ℝ) * (N - 1) := by nlinarith
  simp only [two_g, ite_true, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  push_cast
  refine ⟨div_le_div_of_nonneg_right (by nlinarith) hden,
    div_le_div_of_nonneg_right (by nlinarith) hden,
    div_le_div_of_nonneg_right (by nlinarith) hden⟩

theorem two_g_mono' {N k k' : ℕ} (hkk : k ≤ k') (hk' : k' ≤ N) (r : Fin 3) (hr : r ≠ 0) :
    two_g N k r ≤ two_g N k' r := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    rw [this]
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with h | h
    · rw [h]
    · have hm := two_g_mono (N := N) (k := k') hk'
      refine (ih (by omega) (by omega)).trans ?_
      fin_cases r
      · exact absurd rfl hr
      · exact hm.1
      · exact hm.2.1

/-- **Exercise 6.3: the threshold form** (Miao, p. 189). For a relative rank `r ∈ {1, 2}` and
`1 ≤ k ≤ k' ≤ N − 1`, if stopping is optimal at `(k, r)` (`g_k(r) ≥ W_k`) it is optimal at
`(k', r)`; and if stopping at relative rank `2` is optimal at `k`, so is stopping at relative
rank `1`. -/
theorem ex_6_3_threshold {N : ℕ} {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k') (hk' : k' < N)
    (r : Fin 3) (hr : r ≠ 0) :
    (two_W N k ≤ two_g N k r → two_W N k' ≤ two_g N k' r) ∧
      (two_W N k ≤ two_g N k 2 → two_W N k ≤ two_g N k 1) := by
  refine ⟨fun h => (two_W_anti' hk1 hkk hk').trans (h.trans
    (two_g_mono' hkk hk'.le r hr)), fun h => h.trans ?_⟩
  rcases Nat.lt_or_ge k N with hlt | hge
  · exact (two_g_mono (N := N) (k := k) hlt).2.2
  · omega

/-- The value of "stop at the first candidate of relative rank `1` or `2` after date `k`":
`2k(N − k)/(N(N − 1))`. -/
noncomputable def two_L (N k : ℕ) : ℝ := 2 * k * (N - k) / (N * (N - 1))

theorem two_L_step {N k : ℕ} (hN : 2 ≤ N) (hk1 : 1 ≤ k) :
    (two_g N (k + 1) 1 + two_g N (k + 1) 2) / ((k : ℝ) + 1) +
      ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_L N (k + 1) = two_L N k := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (N : ℝ) * (N - 1) ≠ 0 := by nlinarith
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  simp only [two_g, two_L, ite_true, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  push_cast
  field_simp
  ring

theorem two_W_last {N : ℕ} (hN : 2 ≤ N) : two_W N (N - 1) = two_L N (N - 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman N).1
  unfold two_W two_L
  rw [Nat.sub_add_cancel (by omega), h0, h1, h2]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [show 1 ≤ N by omega]; ring
  rw [hc, show (N : ℝ) - 1 + 1 = N by ring]
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Exercise 6.3: a lower bound** — `W_k ≥ 2k(N − k)/(N(N − 1))` for `1 ≤ k ≤ N − 1`, the value
of stopping at the first candidate of relative rank `1` or `2` after `k`. -/
theorem ex_6_3_lower {N : ℕ} (hN : 2 ≤ N) :
    ∀ k, 1 ≤ k → k ≤ N - 1 → two_L N k ≤ two_W N k := by
  have key : ∀ n k, N - 1 - k = n → 1 ≤ k → k ≤ N - 1 → two_L N k ≤ two_W N k := by
    intro n
    induction n with
    | zero =>
      intro k hn _ hk
      have : k = N - 1 := by omega
      subst this
      rw [two_W_last hN]
    | succ n ih =>
      intro k hn hk1 hk
      have hIH := ih (k + 1) (by omega) (by omega) (by omega)
      have hlt : k + 1 < N := by omega
      have hV1 := (ex_6_3_bellman N).2 (k + 1) hlt 1
      have hV2 := (ex_6_3_bellman N).2 (k + 1) hlt 2
      have hV0 := two_V0 (N := N) (k := k + 1) (by omega) hlt
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      rw [← two_L_step hN hk1]
      unfold two_W
      rw [hV0]
      have e1 : two_g N (k + 1) 1 ≤ two_V N (k + 1) 1 := by rw [hV1]; exact le_max_left _ _
      have e2 : two_g N (k + 1) 2 ≤ two_V N (k + 1) 2 := by rw [hV2]; exact le_max_left _ _
      have e3 : 0 ≤ ((k : ℝ) - 1) / ((k : ℝ) + 1) := div_nonneg (by linarith) hpos.le
      have := mul_le_mul_of_nonneg_left hIH e3
      have : (two_g N (k + 1) 1 + two_g N (k + 1) 2) / ((k : ℝ) + 1) ≤
          (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      linarith
  exact fun k hk1 hk => key (N - 1 - k) k rfl hk1 hk

theorem two_g2_sub_L {N k : ℕ} (hN : 2 ≤ N) :
    two_g N k 2 - two_L N k = (k : ℝ) * (3 * k - 2 * N - 1) / (N * (N - 1)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  simp only [two_g, two_L, show (2 : Fin 3) ≠ 1 by decide, ite_false, ite_true]
  field_simp
  ring

/-- **Exercise 6.3: the second threshold, explicitly** (Miao, p. 189). For `N ≥ 2` and
`1 ≤ k ≤ N − 1`: stopping at a candidate who is second best so far is optimal at date `k` if and
only if `3k ≥ 2N + 1`; on those dates `W_k = 2k(N − k)/(N(N − 1))` and `V_k(r) = g_k(r)` for
`r = 1, 2`. -/
theorem ex_6_3_rank2 {N : ℕ} (hN : 2 ≤ N) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    (two_W N k ≤ two_g N k 2 ↔ 2 * N + 1 ≤ 3 * k) ∧
      (2 * N + 1 ≤ 3 * k → two_W N k = two_L N k ∧
        two_V N k 1 = two_g N k 1 ∧ two_V N k 2 = two_g N k 2) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (0 : ℝ) < N * (N - 1) := by nlinarith
  -- exactness on the final segment
  have exact : ∀ n k, N - 1 - k = n → 1 ≤ k → k ≤ N - 1 → 2 * N + 1 ≤ 3 * k →
      two_W N k = two_L N k := by
    intro n
    induction n with
    | zero =>
      intro k hn _ hk _
      have : k = N - 1 := by omega
      subst this
      exact two_W_last hN
    | succ n ih =>
      intro k hn hk1 hk h3
      have hIH := ih (k + 1) (by omega) (by omega) (by omega) (by omega)
      have hlt : k + 1 < N := by omega
      have hge2 : two_W N (k + 1) ≤ two_g N (k + 1) 2 := by
        rw [hIH, ← sub_nonneg, two_g2_sub_L hN]
        have : (2 * N + 1 : ℝ) ≤ 3 * ((k : ℝ) + 1) := by exact_mod_cast (by omega : _)
        push_cast
        exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden.le
      have hge1 : two_W N (k + 1) ≤ two_g N (k + 1) 1 :=
        hge2.trans (two_g_mono (N := N) (k := k + 1) hlt).2.2
      have hV1 : two_V N (k + 1) 1 = two_g N (k + 1) 1 := by
        rw [(ex_6_3_bellman N).2 (k + 1) hlt 1, max_eq_left hge1]
      have hV2 : two_V N (k + 1) 2 = two_g N (k + 1) 2 := by
        rw [(ex_6_3_bellman N).2 (k + 1) hlt 2, max_eq_left hge2]
      have hV0 := two_V0 (N := N) (k := k + 1) (by omega) hlt
      unfold two_W
      rw [hV1, hV2, hV0, hIH, two_L_step hN hk1]
  have hL := ex_6_3_lower hN k hk1 hk
  have hdiff := two_g2_sub_L (N := N) (k := k) hN
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hfin : 2 * N + 1 ≤ 3 * k → two_W N k = two_L N k ∧
      two_V N k 1 = two_g N k 1 ∧ two_V N k 2 = two_g N k 2 := by
    intro h3
    have hW := exact (N - 1 - k) k rfl hk1 hk h3
    have hle2 : two_W N k ≤ two_g N k 2 := by
      rw [hW, ← sub_nonneg, hdiff]
      have : (2 * N + 1 : ℝ) ≤ 3 * k := by exact_mod_cast h3
      exact div_nonneg (mul_nonneg hkpos.le (by linarith)) hden.le
    have hlt : k < N := by omega
    refine ⟨hW, ?_, ?_⟩
    · rw [(ex_6_3_bellman N).2 k hlt 1,
        max_eq_left (hle2.trans (two_g_mono (N := N) (k := k) hlt).2.2)]
    · rw [(ex_6_3_bellman N).2 k hlt 2, max_eq_left hle2]
  refine ⟨⟨fun h => ?_, fun h3 => ?_⟩, hfin⟩
  · by_contra h3
    have h3' : (3 * k : ℝ) < 2 * N + 1 := by exact_mod_cast (lt_of_not_ge h3)
    have hneg : two_g N k 2 - two_L N k < 0 := by
      rw [hdiff]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hkpos (by linarith)) hden
    linarith
  · have := (hfin h3).1
    rw [this, ← sub_nonneg, hdiff]
    have : (2 * N + 1 : ℝ) ≤ 3 * k := by exact_mod_cast h3
    exact div_nonneg (mul_nonneg hkpos.le (by linarith)) hden.le

/-! ### Exercise 6.4 -/

/-- The Bellman equation of Exercise 6.4, by time to go `n = N − k`; the state is the relative
rank `r`. -/
noncomputable def rank_val (N : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun r => r
  | n + 1 => fun r =>
    min ((r : ℝ) * (N + 1) / (((N - (n + 1) : ℕ) : ℝ) + 1))
      (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) *
        ∑ i ∈ Finset.range (N - (n + 1) + 1), rank_val N n (i + 1))

/-- `V_k(r)` of Exercise 6.4: the minimal expected rank at date `k` with relative rank `r`. -/
noncomputable def rank_V (N k r : ℕ) : ℝ := rank_val N (N - k) r

/-- The continuation value `W_k = (1/(k + 1)) ∑_{r=1}^{k+1} V_{k+1}(r)`. -/
noncomputable def rank_W (N k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1) * ∑ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1)

/-- **Exercise 6.4: the Bellman equation** (Miao, p. 189): `V_N(r) = r` and
`V_k(r) = min{r(N + 1)/(k + 1), W_k}` for `k < N`. -/
theorem ex_6_4_bellman (N : ℕ) :
    (∀ r, rank_V N N r = r) ∧
      ∀ k < N, ∀ r, rank_V N k r = min ((r : ℝ) * (N + 1) / ((k : ℝ) + 1)) (rank_W N k) := by
  refine ⟨fun r => by simp [rank_V, rank_val], fun k hk r => ?_⟩
  have e1 : N - k = (N - (k + 1)) + 1 := by omega
  have e2 : N - (N - (k + 1) + 1) = k := by omega
  unfold rank_V rank_W
  rw [e1]
  simp only [rank_val, e2]
  rfl

theorem rank_V_nonneg (N : ℕ) : ∀ k r, 0 ≤ rank_V N k r := by
  have : ∀ n r, 0 ≤ rank_val N n r := by
    intro n
    induction n with
    | zero => intro r; simp only [rank_val]; positivity
    | succ n ih =>
      intro r
      simp only [rank_val]
      exact le_min (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => ih _))
  exact fun k r => this _ r

theorem rank_W_nonneg (N k : ℕ) : 0 ≤ rank_W N k :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => rank_V_nonneg N _ _)

/-- `W_k ≤ W_{k+1}`: an earlier date offers more options. -/
theorem rank_W_mono {N k : ℕ} (hk : k + 1 < N) : rank_W N k ≤ rank_W N (k + 1) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold rank_W
  have : ∀ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1) ≤ rank_W N (k + 1) := by
    intro i _
    rw [(ex_6_4_bellman N).2 (k + 1) hk]
    exact min_le_right _ _
  have hs := Finset.sum_le_sum this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  push_cast at hs
  calc 1 / ((k : ℝ) + 1) * ∑ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1)
      ≤ 1 / ((k : ℝ) + 1) * (((k : ℝ) + 1) * rank_W N (k + 1)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = rank_W N (k + 1) := by field_simp
    _ = _ := rfl

/-- **Exercise 6.4: the threshold form** (Miao, p. 189). At a date `k < N`, stopping is optimal
(`r(N + 1)/(k + 1) ≤ W_k`) exactly for the relative ranks `r ≤ s_k = (k + 1)W_k/(N + 1)`, and the
threshold `s_k` is nondecreasing in `k` (for `k + 1 < N`). -/
theorem ex_6_4_threshold {N k : ℕ} (r : ℕ) :
    ((r : ℝ) * (N + 1) / ((k : ℝ) + 1) ≤ rank_W N k ↔
      (r : ℝ) ≤ ((k : ℝ) + 1) * rank_W N k / (N + 1)) ∧
    (k + 1 < N → ((k : ℝ) + 1) * rank_W N k / (N + 1) ≤
      ((k : ℝ) + 1 + 1) * rank_W N (k + 1) / (N + 1)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨?_, fun hk' => ?_⟩
  · rw [div_le_iff₀ hk, le_div_iff₀ hN]
    constructor <;> intro h <;> linarith
  · refine div_le_div_of_nonneg_right ?_ hN.le
    have h1 := rank_W_mono hk'
    have h2 := rank_W_nonneg N (k + 1)
    nlinarith

theorem rank_sum_range (n : ℕ) : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Exercise 6.4 at the last decision date: `W_{N−1} = (N + 1)/2`, the mean rank of the last
candidate. -/
theorem ex_6_4_last {N : ℕ} (hN : 1 ≤ N) : rank_W N (N - 1) = ((N : ℝ) + 1) / 2 := by
  unfold rank_W
  rw [Nat.sub_add_cancel hN]
  simp only [(ex_6_4_bellman N).1]
  push_cast
  rw [rank_sum_range]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [hN]; ring
  rw [hc, show (N : ℝ) - 1 + 1 = N by ring]
  have hNne : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp

/-- **Exercise 6.4 for `N = 3`**: the minimal expected rank is `V_1(1) = 5/3` (reject the first
candidate; accept the second if it is better than the first; otherwise take the third). -/
theorem ex_6_4_three : rank_V 3 1 1 = 5 / 3 := by
  simp only [rank_V, rank_val, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.3 as a Markov decision process

The best-two secretary problem in Chapter 5's formulation `secretaryTwo N` (Exercise 5.3,
`MDPStoppingExamples`), recast as the Markov decision process `(secretaryTwo N).toMDP` with
dates shifted by one (MDP date `t` is the book's date `t + 1`) and horizon `T = N − 1`.

* `two_integral_cont`: after continuing, `∫ w dP = (w(1) + w(2))/(t + 2) + t w(0)/(t + 2)`.
* `ex_6_3_mdp` (with Theorem 6.3.2): the recursion `two_V` of `SecretaryExercises` gives the value
  functions of the Markov decision problem, and the rule "stop at relative rank `r` at date `k`
  iff `g_k(r) ≥ W_k`" (`two_rule`) is optimal from every history. With `ex_6_3_threshold` and
  `ex_6_3_rank2` this is the solution of Exercise 6.3: two thresholds `τ_1 ≤ τ_2`, with
  `τ_2 = ⌈(2N + 1)/3⌉`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z]

theorem po_stopP_cont (sp : StoppingProblem Z) (t : ℕ) (z : Z) :
    sp.toMDP.P t (Sum.inl z, 1) = (sp.Q t z).map Sum.inl := by
  change stopKernel (sp.Q t) (Sum.inl z, 1) = _
  rw [stopKernel, famKernel_apply]
  simp only [ite_true]
  rw [contKernel_inl]

theorem po_stopP_stop (sp : StoppingProblem Z) (t : ℕ) (s : Z ⊕ Unit) :
    sp.toMDP.P t (s, 0) = Measure.dirac sHat := by
  change stopKernel (sp.Q t) (s, 0) = _
  rw [stopKernel, famKernel_apply]
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, Kernel.const_apply]

theorem po_stopP_hat (sp : StoppingProblem Z) (t : ℕ) (u : Unit) (a : Fin 2) :
    sp.toMDP.P t (Sum.inr u, a) = Measure.dirac sHat := by
  change stopKernel (sp.Q t) (Sum.inr u, a) = _
  rw [stopKernel, famKernel_apply]
  split_ifs
  · exact contKernel_inr _ u
  · rfl

/-- Bounded payoffs give bounded rewards of the stopping MDP. -/
theorem po_toMDP_bounded (sp : StoppingProblem Z) {B : ℝ} (hB : sp.Bounded B) :
    BoundedRewards sp.toMDP B := by
  refine ⟨fun t x => ?_, fun s => ?_⟩
  · obtain ⟨s, a⟩ := x
    cases s with
    | inl z =>
      simp only [StoppingProblem.toMDP, Sum.elim_inl]
      split_ifs
      · exact hB.2.1 t z
      · exact hB.2.2.1 t z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1
  · cases s with
    | inl z => exact hB.2.2.2 z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1

theorem two_measurable {β : Type*} [MeasurableSpace β] (f : Fin 3 ⊕ Unit → β) : Measurable f := by
  rw [← Sum.elim_comp_inl_inr f]
  exact (measurable_of_countable _).sumElim (measurable_of_countable _)

theorem two_integrable (μ : Measure (Fin 3 ⊕ Unit)) [IsFiniteMeasure μ]
    (w : Fin 3 ⊕ Unit → ℝ) : Integrable w μ :=
  Integrable.of_bound (two_measurable w).aestronglyMeasurable (∑ x, |w x|)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun x _ => abs_nonneg (w x)) (Finset.mem_univ s))

theorem po_fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

theorem two_isMarkov {N : ℕ} (hN : 2 ≤ N) : (secretaryTwo N).toMDP.IsMarkov := (ex_5_3 hN).1

theorem two_bounded {N : ℕ} (hN : 2 ≤ N) : (secretaryTwo N).Bounded 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * (N - 1) := by nlinarith
  refine ⟨zero_le_one, fun t z => by simp [secretaryTwo], fun t z => ?_, fun z => ?_⟩
  · set k : ℕ := min (t + 1) N with hk
    have hk1 : 1 ≤ k := le_min (by omega) (by omega)
    have hkN : k ≤ N := min_le_right _ _
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hcase : (k : ℝ) = N ∨ (k : ℝ) + 1 ≤ N := by
      rcases Nat.lt_or_ge k N with h | h
      · exact Or.inr (by exact_mod_cast h)
      · exact Or.inl (by exact_mod_cast le_antisymm hkN h)
    simp only [secretaryTwo, ← hk]
    split_ifs
    · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
      rcases hcase with h | h
      · rw [h]
        linarith
      · nlinarith
    · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
      nlinarith
    · simp
  · simp only [secretaryTwo]
    split_ifs <;> simp

theorem two_assumption {N : ℕ} (hN : 2 ≤ N) (T : ℕ) :
    po_Assumption513 (secretaryTwo N).toMDP T :=
  po_assumption513_of_bounded (two_isMarkov hN) (po_toMDP_bounded _ (two_bounded hN))
    (fun _ => measurable_toMDP_u _ measurable_const (measurable_of_countable _))
    (measurable_toMDP_uT _ (measurable_of_countable _)) T

/-- The integral after continuing (MDP date `t`, book date `t + 1`):
`∫ w dP = w(1)/(t + 2) + w(2)/(t + 2) + t w(0)/(t + 2)`. -/
theorem two_integral_cont (N t : ℕ) (z : Fin 3) (w : Fin 3 ⊕ Unit → ℝ) :
    ∫ s, w s ∂(secretaryTwo N).toMDP.P t (Sum.inl z, 1) =
      1 / ((t : ℝ) + 2) * w (Sum.inl 1) + 1 / ((t : ℝ) + 2) * w (Sum.inl 2) +
        (t : ℝ) / ((t : ℝ) + 2) * w (Sum.inl 0) := by
  have := isProbabilityMeasure_rank3 t
  rw [po_stopP_cont]
  change ∫ s, w s ∂(rank3 t).map Sum.inl = _
  rw [integral_map measurable_inl.aemeasurable (two_measurable _).aestronglyMeasurable,
    integral_fintype Integrable.of_finite, Fin.sum_univ_three]
  have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 2) := by positivity
  have h1 : (0 : ℝ) ≤ (t : ℝ) / ((t : ℝ) + 2) := by positivity
  have r0 : (rank3 t).real {0} = (t : ℝ) / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ENNReal.toReal_ofReal h1]
  have ht2 : (0 : ℝ) ≤ (t : ℝ) + 2 := by positivity
  have r1 : (rank3 t).real {1} = 1 / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ht2]
  have r2 : (rank3 t).real {2} = 1 / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ht2]
  simp only [r0, r1, r2, smul_eq_mul]
  ring

theorem two_u_inl (N t : ℕ) (z : Fin 3) (b : Fin 2) :
    (secretaryTwo N).toMDP.u t (Sum.inl z, b) =
      if b = 1 then 0 else (secretaryTwo N).g t z := by
  simp [StoppingProblem.toMDP, secretaryTwo]

/-- The value functions in MDP dates: `w_t(r) = V_{t+1}(r)`, `w_t(ŝ) = 0`. -/
noncomputable def two_w (N t : ℕ) : Fin 3 ⊕ Unit → ℝ :=
  Sum.elim (fun z => two_V N (t + 1) z) fun _ => 0

open Classical in
/-- The optimal rule: at MDP date `t` (book date `k = t + 1`), stop at relative rank `r` iff
`g_k(r) ≥ W_k`. -/
noncomputable def two_rule (N t : ℕ) : Fin 3 ⊕ Unit → Fin 2 :=
  Sum.elim (fun z => if two_W N (t + 1) ≤ two_g N (t + 1) z then 0 else 1) fun _ => 1

theorem two_g_eq {N t : ℕ} (ht : t + 1 ≤ N) (z : Fin 3) :
    (secretaryTwo N).g t z = two_g N (t + 1) z := by
  simp only [secretaryTwo, two_g, min_eq_left ht]

theorem two_bv {N t : ℕ} (ht : t + 1 < N) (z : Fin 3) (b : Fin 2) :
    po_bellmanVal (secretaryTwo N).toMDP (two_w N) t (Sum.inl z) b =
      if b = 1 then two_W N (t + 1) else two_g N (t + 1) z := by
  have hβ : (secretaryTwo N).toMDP.β = 1 := rfl
  unfold po_bellmanVal
  rw [two_u_inl N t z b, hβ, one_mul]
  rcases po_fin2_cases b with rfl | rfl
  · rw [po_stopP_stop, integral_dirac' _ _ (two_measurable _).stronglyMeasurable]
    simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, two_w, sHat, Sum.elim_inr, add_zero,
      two_g_eq ht.le]
  · rw [two_integral_cont]
    simp only [ite_true, zero_add, two_w, Sum.elim_inl, two_W]
    push_cast
    ring_nf

theorem two_bv_hat {N t : ℕ} (u : Unit) (b : Fin 2) :
    po_bellmanVal (secretaryTwo N).toMDP (two_w N) t (Sum.inr u) b = 0 := by
  unfold po_bellmanVal
  rw [po_stopP_hat, integral_dirac' _ _ (two_measurable _).stronglyMeasurable]
  simp [two_w, sHat, StoppingProblem.toMDP]

theorem two_solves {N : ℕ} {t : ℕ} (ht : t < N - 1) (s : Fin 3 ⊕ Unit) :
    po_SolvesAt (secretaryTwo N).toMDP (two_w N) t s ∧
      two_rule N t s ∈ po_G (secretaryTwo N).toMDP (two_w N) t s := by
  have hk : t + 1 < N := by omega
  cases s with
  | inr u =>
    refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_ <;>
      simp only [two_bv_hat, two_w, Sum.elim_inr, le_refl]
  | inl z =>
    have hV := (ex_6_3_bellman N).2 (t + 1) hk z
    refine po_solvesAt_of_max (fun b _ => ?_) (Set.mem_univ _) ?_
    · simp only [two_w, Sum.elim_inl]
      rw [two_bv hk, hV]
      split_ifs
      · exact le_max_right _ _
      · exact le_max_left _ _
    · simp only [two_w, Sum.elim_inl, two_rule]
      rw [hV]
      split_ifs with h
      · rw [two_bv hk]
        simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false]
        exact (max_eq_left h).symm
      · rw [two_bv hk]
        simp only [ite_true]
        exact (max_eq_right (le_of_lt (lt_of_not_ge h))).symm

theorem two_wT {N : ℕ} (hN : 1 ≤ N) (s : Fin 3 ⊕ Unit) :
    two_w N (N - 1) s = (secretaryTwo N).toMDP.uT s := by
  obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman N).1
  cases s with
  | inl z =>
    simp only [two_w, Sum.elim_inl, Nat.sub_add_cancel hN, StoppingProblem.toMDP, secretaryTwo]
    rcases po_fin3_cases z with rfl | rfl | rfl
    · simp [h0]
    · simp [h1]
    · simp [h2, show (2 : Fin 3) ≠ 0 by decide]
  | inr u => rfl

/-- **Exercise 6.3, solved as a Markov decision problem** (Miao, p. 189). For `N ≥ 2`, every MDP
date `t ≤ N − 1` and every history `sᵗ`: the value of the sequence problem (6.14) of
`(secretaryTwo N).toMDP` is `two_w N t` (the book's `V_{t+1}` of `ex_6_3_bellman`), and the rule
"stop at relative rank `r` iff `g_k(r) ≥ W_k`" attains it. -/
theorem ex_6_3_mdp {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 3 ⊕ Unit) :
    po_genFrom (two_rule N) t (h (Fin.last t)) ∈
        po_plansFrom (secretaryTwo N).toMDP (N - 1) t h ∧
      po_JFrom (secretaryTwo N).toMDP (N - 1) t h
        (po_genFrom (two_rule N) t (h (Fin.last t))) = two_w N t (h (Fin.last t)) ∧
      po_VFrom (secretaryTwo N).toMDP (N - 1) t h = two_w N t (h (Fin.last t)) :=
  theorem_6_3_2 (two_isMarkov hN) zero_le_one (two_assumption hN (N - 1))
    (fun t _ s a _ => by
      have := two_isMarkov hN t
      exact two_integrable _ _)
    (fun t ht s => (two_solves ht s).1) (fun _ _ => two_measurable _)
    (fun t ht s => (two_solves ht s).2) (two_wT (by omega)) t ht h

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences

Copied from `RecursiveMethods/StochasticDP` (`Correspondences.lean`), namespace renamed.

SLP §3.3, pp. 56–61, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`): lower and upper hemi-continuity on metric spaces (`IsLHC`, `IsUHC`),
the graph, Exercise 3.11a (`continuousAt_of_isUHC_singleton`) and Exercise 3.15
(`isCompact_graph`).
-/


namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Theorem of the Maximum

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


namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Measurable Selection Theorem

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability of a concave function from below: Benveniste and Scheinkman

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


namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 9.5: integration preserves continuity, monotonicity and concavity

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The optimal control model of §6.4: Bellman equation and assumptions

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 6.4.1: the expected continuation value is continuous

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.1: existence

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.2: monotonicity

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.3: concavity and the policy function

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.3: the policy correspondence need not be single-valued

Miao, §6.4, p. 177. The book concludes from strict concavity of `V_t(·, z)` that `G_t` is
single-valued. Assumption 6.4.10 is strict only in `x`, so the objective
`u_t(x, z, a) + β E V_{t+1}(φ(x, a, z, z′), z′)` need not be strictly concave in `a`.

`theorem_6_4_3_counterexample`: `X = (−∞, 0]`, `A = Γ(x, z) = [0, 1]`, `Z` a single point,
`φ(x, a, z, z′) = x`, `u_t(x, z, a) = u_T(x, z) = −x²`, `β = 1/2`, `T = 1`. Assumptions
6.4.1–6.4.12 and 5.1.2 all hold, but `G_0(0, z) = [0, 1]`. Hence `theorem_6_4_3` adds that
`φ(x, ·, z, z′)` is one-to-one on `A`.

`isLHC_const`, `isUHC_const`: a constant nonempty compact correspondence is continuous.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-- A constant nonempty correspondence is lower hemicontinuous. -/
theorem isLHC_const {S Y : Type*} [MetricSpace S] [MetricSpace Y] {K : Set Y} (hK : K.Nonempty)
    (s : S) : IsLHC (fun _ : S => K) s :=
  ⟨hK, fun y hy _ _ => ⟨0, fun _ => y, fun _ _ => hy, tendsto_const_nhds⟩⟩

/-- A constant nonempty compact correspondence is upper hemicontinuous. -/
theorem isUHC_const {S Y : Type*} [MetricSpace S] [MetricSpace Y] {K : Set Y} (hK : K.Nonempty)
    (hc : IsCompact K) (s : S) : IsUHC (fun _ : S => K) s :=
  ⟨hK, fun _ _ _ hys => hc.tendsto_subseq hys⟩

/-- The model of the counterexample to single-valuedness of `G_t`. -/
noncomputable def oc_flatModel : OCModel ℝ ℝ Unit :=
  ⟨Set.Iic 0, Set.Icc 0 1, Kernel.const Unit (Measure.dirac ()), fun _ _ => Set.Icc 0 1,
    fun x _ _ _ => x, fun _ x _ _ => -x ^ 2, fun x _ => -x ^ 2, 1 / 2, 1⟩

theorem oc_negSq_comb {x y θ η : ℝ} (hs : θ + η = 1) :
    -(θ * x + η * y) ^ 2 - (θ * -x ^ 2 + η * -y ^ 2) = θ * η * (x - y) ^ 2 := by
  have : η = 1 - θ := by linarith
  subst this
  ring

theorem oc_negSq_strict : StrictConcaveOn ℝ (Set.Iic (0 : ℝ)) fun x => -x ^ 2 := by
  refine ⟨convex_Iic 0, fun x _ y _ hne θ η hθ hη hs => ?_⟩
  simp only [smul_eq_mul]
  have h := oc_negSq_comb (x := x) (y := y) hs
  have : 0 < θ * η * (x - y) ^ 2 := by
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
    positivity
  linarith

/-- **Counterexample to Theorem 6.4.3 as printed** (Miao, p. 177): Assumptions 6.4.1–6.4.12 and
5.1.2 hold, but the policy correspondence `G_0(0, z) = [0, 1]` is not single-valued. -/
theorem theorem_6_4_3_counterexample :
    ∃ M : OCModel ℝ ℝ Unit, IsMarkovKernel M.Q ∧ M.Assumption641 ∧ M.Assumption642 ∧
      M.Assumption643ii ∧ M.Assumption644 ∧ M.Assumption645 ∧ M.Assumption646 ∧
      M.Assumption647 ∧ M.Assumption648 ∧ M.Assumption649 ∧ M.Assumption6410 ∧
      M.Assumption6411 ∧ M.Assumption6412 ∧ 0 < M.β ∧ M.β < 1 ∧ 0 < M.T ∧
      ¬ (M.G 0 0 ()).Subsingleton := by
  have hX : oc_flatModel.X = Set.Iic 0 := rfl
  have hA : oc_flatModel.A = Set.Icc 0 1 := rfl
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  have h644 : oc_flatModel.Assumption644 :=
    ⟨fun _ _ _ => subset_rfl, fun s => ⟨isCompact_Icc, isLHC_const hne s,
      isUHC_const hne isCompact_Icc s⟩⟩
  have h6410 : oc_flatModel.Assumption6410 := by
    refine ⟨fun _ => oc_negSq_strict, fun t _ z x _ x' _ a _ a' _ θ η hθ hη hs => ?_⟩
    change θ * -x ^ 2 + η * -x' ^ 2 ≤ -(θ • x + η • x') ^ 2 ∧
      (x ≠ x' → θ * -x ^ 2 + η * -x' ^ 2 < -(θ • x + η • x') ^ 2)
    simp only [smul_eq_mul]
    have h := oc_negSq_comb (x := x) (y := x') hs
    refine ⟨by nlinarith [sq_nonneg (x - x'), mul_pos hθ hη], fun hxx => ?_⟩
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hxx)
    nlinarith [mul_pos (mul_pos hθ hη) this]
  have hMk : IsMarkovKernel oc_flatModel.Q := by
    change IsMarkovKernel (Kernel.const Unit (Measure.dirac ()))
    infer_instance
  refine ⟨oc_flatModel, hMk, ⟨convex_Iic 0, measurableSet_Iic⟩, ⟨convex_Icc 0 1,
    measurableSet_Icc⟩, ⟨inferInstance, inferInstance, fun f _ _ => continuous_of_discreteTopology⟩,
    h644, ⟨fun x hx _ _ _ _ => hx, continuous_fst.continuousOn⟩,
    ⟨fun _ _ => (continuous_fst.pow 2).neg.continuousOn, (continuous_fst.pow 2).neg.continuousOn⟩,
    ⟨fun _ => ?_, fun _ _ _ _ _ => ?_⟩, fun _ _ _ _ _ _ => subset_rfl,
    fun _ _ _ _ _ _ _ _ h => h, h6410, fun _ _ _ _ _ a ha a' ha' θ η hθ hη hs =>
      (convex_Icc 0 1) ha ha' hθ.le hη.le hs, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => le_rfl,
    by norm_num [oc_flatModel], by norm_num [oc_flatModel], by norm_num [oc_flatModel], ?_⟩
  · intro x hx y hy hxy
    change -x ^ 2 < -y ^ 2
    have hy' : y ≤ 0 := hy
    nlinarith
  · intro x hx y hy hxy
    change -x ^ 2 < -y ^ 2
    have hy' : y ≤ 0 := hy
    nlinarith
  · -- every action is optimal at `t = 0`
    have hconst : ∀ a, oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () a =
        oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 := fun _ => rfl
    have hV : oc_flatModel.V 0 0 () = oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 := by
      rw [oc_flatModel.V_succ_apply (by norm_num [oc_flatModel])]
      have : oc_flatModel.obj 0 (oc_flatModel.V (0 + 1)) 0 () '' oc_flatModel.Γ 0 () =
          {oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0} := by
        rw [show oc_flatModel.obj 0 (oc_flatModel.V (0 + 1)) 0 () =
          fun _ => oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 from funext hconst]
        exact hne.image_const _
      rw [this, csSup_singleton]
    have hmem : ∀ a ∈ Set.Icc (0 : ℝ) 1, a ∈ oc_flatModel.G 0 0 () := fun a ha =>
      ⟨ha, by rw [hV]; exact hconst a⟩
    intro hsub
    have := hsub (hmem 0 ⟨le_rfl, zero_le_one⟩) (hmem 1 ⟨zero_le_one, le_rfl⟩)
    norm_num at this

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two facts about concave functions of one variable

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 6.4.4: differentiability, the envelope condition and the Euler equations

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.5: the Maximum Principle

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.5: concave Hamiltonians, dynamic programming, deterministic transitions

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The optimal control model

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `OptimalControl`),
with the namespace renamed.

Miao, §5.2.4, pp. 153–154. The state is `s = (x, z)`: an exogenous Markov shock `z` with
transition function `Q` and an endogenous state moving by the state transition equation (5.11),
`x_{t+1} = φ_t(x_t, a_t, z_t, z_{t+1})`; actions satisfy `a_t ∈ Γ(x_t, z_t)` and pay
`u_t(x_t, z_t, a_t)`; the objective is the Bolza form (5.12).

* `ControlProblem.toMDP`: the Markov decision process of p. 154, with the kernels
  `P_{t+1}(x, z, a; ·)` = the law of `(φ_t(x, a, z, z′), z′)`, `z′ ~ Q(z, ·)`.
* **Correction.** The book's formula
  `P_{t+1}(x_t, z_t, a_t; B₁ × B₂) = 1_{B₂}(z_{t+1}) 1_{B₁}(φ_t(x_t, a_t, z_t, z_{t+1})) Q(z_t, B₂)`
  contains the free variable `z_{t+1}`; the kernel is
  `P_{t+1}(x, z, a; B₁ × B₂) = ∫_{B₂} 1_{B₁}(φ_t(x, a, z, z′)) Q(z, dz′)`
  (`controlKernel_rect`). When `φ_t` does not depend on `z′` this is
  `1_{B₁}(φ_t(x, a, z)) Q(z, B₂)` (`controlKernel_rect_of_indep`), the book's formula without the
  stray factor.
* `ctrlX`, `controlObj`: the control problem in its own terms — a policy `a_t = σ_t(z₁, …, z_t)`,
  the states it generates by (5.11), and the objective (5.12) as an expectation over the shocks.
* `J0T_control`: the MDP objective of any plan is the control objective of the policy it
  induces; `controlObj_toPlan`: every feasible control policy is induced by a feasible plan.
  Hence `V0_control`: the MDP and the control problem have the same value. The infinite-horizon
  objective (5.13) is the limit of the same partial sums (`J_control`).
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter

variable {X Z A : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]

/-- The data of an optimal control problem (Miao, p. 153). -/
structure ControlProblem (X Z A : Type*) [MeasurableSpace Z] where
  Q : Kernel Z Z
  φ : ℕ → X × A × Z × Z → X
  Γ : X × Z → Set A
  u : ℕ → X × Z × A → ℝ
  uT : X × Z → ℝ
  β : ℝ

/-- The kernel of the control problem: the law of `(φ_t(x, a, z, z′), z′)`, `z′ ~ Q(z, ·)`. -/
noncomputable def controlKernel (cp : ControlProblem X Z A) (t : ℕ) :
    Kernel ((X × Z) × A) (X × Z) :=
  pushKernel (cp.Q.comap (fun y : (X × Z) × A => y.1.2) (measurable_fst.snd))
    fun p => (cp.φ t (p.1.1.1, p.1.2, p.1.1.2, p.2), p.2)

/-- The optimal control problem as a Markov decision process (Miao, p. 154). -/
noncomputable def ControlProblem.toMDP (cp : ControlProblem X Z A) : MDP (X × Z) A where
  Γ := cp.Γ
  P := controlKernel cp
  u := fun t y => cp.u t (y.1.1, y.1.2, y.2)
  uT := cp.uT
  β := cp.β

theorem measurable_controlNext (cp : ControlProblem X Z A) {t : ℕ} (hφ : Measurable (cp.φ t)) :
    Measurable fun p : ((X × Z) × A) × Z => (cp.φ t (p.1.1.1, p.1.2, p.1.1.2, p.2), p.2) :=
  (hφ.comp (measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk
    (measurable_fst.fst.snd.prodMk measurable_snd)))).prodMk measurable_snd

theorem controlKernel_apply (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q] {t : ℕ}
    (hφ : Measurable (cp.φ t)) (x : X) (z : Z) (a : A) :
    controlKernel cp t ((x, z), a) = (cp.Q z).map fun z' => (cp.φ t (x, a, z, z'), z') :=
  pushKernel_apply _ (measurable_controlNext cp hφ) _

theorem isMarkovKernel_controlKernel (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q] {t : ℕ}
    (hφ : Measurable (cp.φ t)) : IsMarkovKernel (controlKernel cp t) :=
  isMarkovKernel_pushKernel _ (measurable_controlNext cp hφ)

/-- **Correction to Miao, p. 154.** `P_{t+1}(x, z, a; B₁ × B₂) = Q(z, {z′ ∈ B₂ :
φ_t(x, a, z, z′) ∈ B₁}) = ∫_{B₂} 1_{B₁}(φ_t(x, a, z, z′)) Q(z, dz′)`. -/
theorem controlKernel_rect (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q] {t : ℕ}
    (hφ : Measurable (cp.φ t)) (x : X) (z : Z) (a : A) {B₁ : Set X} {B₂ : Set Z}
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    controlKernel cp t ((x, z), a) (B₁ ×ˢ B₂) = cp.Q z (B₂ ∩ {z' | cp.φ t (x, a, z, z') ∈ B₁}) ∧
      controlKernel cp t ((x, z), a) (B₁ ×ˢ B₂) =
        ∫⁻ z' in B₂, B₁.indicator 1 (cp.φ t (x, a, z, z')) ∂cp.Q z := by
  have hm : Measurable fun z' => (cp.φ t (x, a, z, z'), z') :=
    (hφ.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
      measurable_id)))).prodMk measurable_id
  have hpre : (fun z' => (cp.φ t (x, a, z, z'), z')) ⁻¹' (B₁ ×ˢ B₂) =
      B₂ ∩ {z' | cp.φ t (x, a, z, z') ∈ B₁} := by
    ext z'
    simp [and_comm]
  have hφz : Measurable fun z' => cp.φ t (x, a, z, z') := measurable_fst.comp hm
  rw [controlKernel_apply cp hφ, Measure.map_apply hm (h₁.prod h₂), hpre]
  refine ⟨rfl, ?_⟩
  have hset : MeasurableSet (B₂ ∩ {z' | cp.φ t (x, a, z, z') ∈ B₁}) := h₂.inter (hφz h₁)
  rw [← lintegral_indicator_one (s := B₂ ∩ {z' | cp.φ t (x, a, z, z') ∈ B₁}) hset,
    ← lintegral_indicator h₂]
  refine lintegral_congr fun z' => ?_
  by_cases hz : z' ∈ B₂ <;> by_cases hb : cp.φ t (x, a, z, z') ∈ B₁ <;>
    simp [hz, hb, Set.indicator]

/-- Miao, p. 154: when the law of motion does not depend on `z′`, the kernel is the book's
product `1_{B₁}(φ_t(x, a, z)) Q(z, B₂)`. -/
theorem controlKernel_rect_of_indep (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q] {t : ℕ}
    (hφ : Measurable (cp.φ t)) {φ' : X × A × Z → X}
    (hφ' : ∀ x a z z', cp.φ t (x, a, z, z') = φ' (x, a, z)) (x : X) (z : Z) (a : A)
    {B₁ : Set X} {B₂ : Set Z} (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    controlKernel cp t ((x, z), a) (B₁ ×ˢ B₂) = B₁.indicator 1 (φ' (x, a, z)) * cp.Q z B₂ := by
  rw [(controlKernel_rect cp hφ x z a h₁ h₂).1]
  simp only [hφ']
  by_cases hb : φ' (x, a, z) ∈ B₁
  · simp [hb]
  · simp [hb]

/-- The endogenous states generated by a control policy `σ_t(z₁, …, z_t)` through (5.11). -/
def ctrlX (cp : ControlProblem X Z A) (x₀ : X) (z₀ : Z) (σ : Plan Z A) :
    (t : ℕ) → (Fin t → Z) → X
  | 0, _ => x₀
  | t + 1, h => cp.φ t (ctrlX cp x₀ z₀ σ t (Fin.init h), σ t (Fin.init h),
      lastState z₀ (Fin.init h), h (Fin.last t))

/-- The objective (5.12) of a control policy, as an expectation over the shocks. -/
noncomputable def controlObj (cp : ControlProblem X Z A) (T : ℕ) (x₀ : X) (z₀ : Z)
    (σ : Plan Z A) : ℝ :=
  ∑ t ∈ Finset.range T, cp.β ^ t * ∫ h, cp.u t (ctrlX cp x₀ z₀ σ t h, lastState z₀ h, σ t h)
      ∂chainHist (fun _ => cp.Q) z₀ t +
    cp.β ^ T * ∫ h, cp.uT (ctrlX cp x₀ z₀ σ T h, lastState z₀ h) ∂chainHist (fun _ => cp.Q) z₀ T

/-- A feasible control policy: measurable, and `σ_t(zᵗ) ∈ Γ(x_t, z_t)` for every `zᵗ`. -/
def IsFeasibleControl (cp : ControlProblem X Z A) (T : ℕ∞) (x₀ : X) (z₀ : Z) (σ : Plan Z A) :
    Prop :=
  IsPlan T σ ∧ ∀ t : ℕ, (t : ℕ∞) < T → ∀ h, σ t h ∈ cp.Γ (ctrlX cp x₀ z₀ σ t h, lastState z₀ h)

/-- The value of the `T`-horizon control problem (5.12). -/
noncomputable def controlV (cp : ControlProblem X Z A) (T : ℕ) (x₀ : X) (z₀ : Z) : EReal :=
  ⨆ σ ∈ {σ | IsFeasibleControl cp T x₀ z₀ σ}, (controlObj cp T x₀ z₀ σ : EReal)

/-- The step map: from the MDP history `g` and the next shock `z′`, the next state
`(φ_t(x_t, π_t(g), z_t, z′), z′)`. -/
def ctrlStep (cp : ControlProblem X Z A) (s₀ : X × Z) (π : Plan (X × Z) A) (t : ℕ)
    (g : Fin t → X × Z) (z : Z) : X × Z :=
  (cp.φ t ((lastState s₀ g).1, π t g, (lastState s₀ g).2, z), z)

/-- The MDP history `Φ_t(z₁, …, z_t)` generated by the plan `π`. -/
def ctrlLift (cp : ControlProblem X Z A) (s₀ : X × Z) (π : Plan (X × Z) A) :
    (t : ℕ) → (Fin t → Z) → Fin t → X × Z :=
  liftHist (ctrlStep cp s₀ π)

/-- The control policy induced by an MDP plan: `σ_t = π_t ∘ Φ_t`. -/
def inducedPolicy (cp : ControlProblem X Z A) (s₀ : X × Z) (π : Plan (X × Z) A) : Plan Z A :=
  fun t h => π t (ctrlLift cp s₀ π t h)

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- Along `Φ`, the MDP state is `(x_t, z_t)` of the induced policy. -/
theorem lastState_ctrlLift (cp : ControlProblem X Z A) (x₀ : X) (z₀ : Z) (π : Plan (X × Z) A)
    (t : ℕ) (h : Fin t → Z) :
    lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π t h) =
      (ctrlX cp x₀ z₀ (inducedPolicy cp (x₀, z₀) π) t h, lastState z₀ h) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e : lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π (t + 1) h) =
        ctrlStep cp (x₀, z₀) π t (ctrlLift cp (x₀, z₀) π t (Fin.init h)) (h (Fin.last t)) := by
      simp only [ctrlLift, liftHist, lastState_snoc]
    rw [e, ctrlStep, ih]
    rfl

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- The shock coordinates of `Φ_t(zᵗ)` are `zᵗ`. -/
theorem snd_ctrlLift (cp : ControlProblem X Z A) (s₀ : X × Z) (π : Plan (X × Z) A) (t : ℕ)
    (h : Fin t → Z) : (fun i => (ctrlLift cp s₀ π t h i).2) = h := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [ctrlLift, liftHist, ctrlStep]
    · have := congrFun (ih (Fin.init h)) j
      simp only [ctrlLift, liftHist, Fin.snoc_castSucc] at this ⊢
      exact this

theorem measurable_ctrlStep (cp : ControlProblem X Z A) (s₀ : X × Z) {π : Plan (X × Z) A}
    {t : ℕ} (hφ : Measurable (cp.φ t)) (hπ : Measurable (π t)) :
    Measurable fun p : (Fin t → X × Z) × Z => ctrlStep cp s₀ π t p.1 p.2 := by
  have hl : Measurable fun p : (Fin t → X × Z) × Z => lastState s₀ p.1 :=
    (measurable_lastState s₀ t).comp measurable_fst
  exact (hφ.comp (hl.fst.prodMk ((hπ.comp measurable_fst).prodMk (hl.snd.prodMk
    measurable_snd)))).prodMk measurable_snd

theorem ctrl_hstep (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) (x₀ : X) (z₀ : Z) (π : Plan (X × Z) A) (j : ℕ)
    (h : Fin j → Z) :
    cp.toMDP.P j (lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π j h),
        π j (ctrlLift cp (x₀, z₀) π j h)) =
      ((chainMDP fun _ => cp.Q).P j (lastState z₀ h, ())).map
        (ctrlStep cp (x₀, z₀) π j (ctrlLift cp (x₀, z₀) π j h)) := by
  have e := lastState_ctrlLift cp x₀ z₀ π j h
  change controlKernel cp j (lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π j h),
    π j (ctrlLift cp (x₀, z₀) π j h)) = (cp.Q (lastState z₀ h)).map _
  rw [e, controlKernel_apply cp (hφ j)]
  congr 1
  funext z'
  simp only [ctrlStep, e]

theorem controlMDP_isMarkov (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) : cp.toMDP.IsMarkov :=
  fun t => isMarkovKernel_controlKernel cp (hφ t)

theorem expRew_control (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) (hu : ∀ t, Measurable (cp.u t)) (x₀ : X) (z₀ : Z)
    {π : Plan (X × Z) A} {t : ℕ} (hπ : ∀ j ≤ t, Measurable (π j)) :
    expRew cp.toMDP (x₀, z₀) π t = ∫ h, cp.u t (ctrlX cp x₀ z₀ (inducedPolicy cp (x₀, z₀) π) t h,
      lastState z₀ h, inducedPolicy cp (x₀, z₀) π t h) ∂chainHist (fun _ => cp.Q) z₀ t := by
  have hmu : Measurable (cp.toMDP.u t) :=
    (hu t).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  rw [expRew, expRew_simulation (chainMDP fun _ => cp.Q) cp.toMDP
    (chainMDP_isMarkov fun _ => inferInstance) (controlMDP_isMarkov cp hφ) z₀ (x₀, z₀)
    (π₁ := fun _ _ => ()) (fun j hj => measurable_ctrlStep cp _ (hφ j) (hπ j hj.le))
    (fun _ _ => measurable_const) (fun j hj => hπ j hj.le)
    (fun j _ h => ctrl_hstep cp hφ x₀ z₀ π j h) (measurable_rew _ _ hmu (hπ t le_rfl))]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  simp only [rew, ControlProblem.toMDP]
  change cp.u t ((lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π t h)).1,
    (lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π t h)).2, π t (ctrlLift cp (x₀, z₀) π t h)) = _
  rw [lastState_ctrlLift]
  rfl

/-- Miao, p. 154: the MDP objective (5.3) of a plan is the control objective (5.12) of the
policy it induces. -/
theorem J0T_control (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) (hu : ∀ t, Measurable (cp.u t)) (huT : Measurable cp.uT)
    (x₀ : X) (z₀ : Z) {T : ℕ} {π : Plan (X × Z) A} (hπ : ∀ j < T, Measurable (π j)) :
    J0T cp.toMDP T (x₀, z₀) π = controlObj cp T x₀ z₀ (inducedPolicy cp (x₀, z₀) π) := by
  rw [J0T, controlObj]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [expRew_control cp hφ hu x₀ z₀ fun j hj =>
      hπ j (by have := Finset.mem_range.1 ht; omega)]
    rfl
  · rw [expRew_simulation (chainMDP fun _ => cp.Q) cp.toMDP
      (chainMDP_isMarkov fun _ => inferInstance) (controlMDP_isMarkov cp hφ) z₀ (x₀, z₀)
      (π₁ := fun _ _ => ()) (fun j hj => measurable_ctrlStep cp _ (hφ j) (hπ j hj))
      (fun _ _ => measurable_const) hπ (fun j _ h => ctrl_hstep cp hφ x₀ z₀ π j h)
      (f := fun g => cp.toMDP.uT (lastState (x₀, z₀) g))
      (huT.comp (measurable_lastState _ T))]
    refine congrArg _ (integral_congr_ae (Eventually.of_forall fun h => ?_))
    change cp.uT (lastState (x₀, z₀) (ctrlLift cp (x₀, z₀) π T h)) = _
    rw [lastState_ctrlLift]

/-- Miao (5.13)–(5.14): the infinite-horizon MDP objective is the limit of the partial sums of
the control objective of the induced policy. -/
theorem J_control (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) (hu : ∀ t, Measurable (cp.u t)) (x₀ : X) (z₀ : Z)
    {π : Plan (X × Z) A} (hπ : ∀ j, Measurable (π j)) :
    J cp.toMDP (x₀, z₀) π = limUnder atTop fun n => ((∑ t ∈ Finset.range (n + 1), cp.β ^ t *
      ∫ h, cp.u t (ctrlX cp x₀ z₀ (inducedPolicy cp (x₀, z₀) π) t h, lastState z₀ h,
        inducedPolicy cp (x₀, z₀) π t h) ∂chainHist (fun _ => cp.Q) z₀ t : ℝ) : EReal) := by
  rw [J]
  congr 1
  funext n
  simp only [partialSum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [expRew_control cp hφ hu x₀ z₀ fun j _ => hπ j]
  rfl

theorem measurable_inducedPolicy (cp : ControlProblem X Z A) (hφ : ∀ t, Measurable (cp.φ t))
    (s₀ : X × Z) {π : Plan (X × Z) A} {t : ℕ} (hπ : ∀ j ≤ t, Measurable (π j)) :
    Measurable (inducedPolicy cp s₀ π t) :=
  (hπ t le_rfl).comp (measurable_liftHist fun j hj => measurable_ctrlStep cp s₀ (hφ j)
    (hπ j hj.le))

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem ctrlX_congr (cp : ControlProblem X Z A) (x₀ : X) (z₀ : Z) {σ σ' : Plan Z A} {t : ℕ}
    (h : ∀ j < t, σ j = σ' j) : ctrlX cp x₀ z₀ σ t = ctrlX cp x₀ z₀ σ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext g
    simp only [ctrlX, ih fun j hj => h j (by omega), h t (by omega)]

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem controlObj_congr (cp : ControlProblem X Z A) (T : ℕ) (x₀ : X) (z₀ : Z)
    {σ σ' : Plan Z A} (h : ∀ j < T, σ j = σ' j) :
    controlObj cp T x₀ z₀ σ = controlObj cp T x₀ z₀ σ' := by
  unfold controlObj
  rw [ctrlX_congr cp x₀ z₀ h]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [ctrlX_congr cp x₀ z₀ fun j hj => h j (by omega), h t ht']

/-- The plan that applies a control policy `σ` to the shock part of the history, falling back on
a selection `sel` of `Γ` off the histories the policy generates. -/
noncomputable def controlPlan (cp : ControlProblem X Z A) (s₀ : X × Z) (sel : X × Z → A)
    (σ : Plan Z A) : Plan (X × Z) A :=
  open Classical in fun t g =>
    if σ t (fun i => (g i).2) ∈ cp.Γ (lastState s₀ g) then σ t (fun i => (g i).2)
    else sel (lastState s₀ g)

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem controlPlan_apply (cp : ControlProblem X Z A) (s₀ : X × Z) (sel : X × Z → A)
    (σ : Plan Z A) (t : ℕ) (g : Fin t → X × Z) :
    controlPlan cp s₀ sel σ t g =
      open Classical in
      if σ t (fun i => (g i).2) ∈ cp.Γ (lastState s₀ g) then σ t (fun i => (g i).2)
      else sel (lastState s₀ g) := rfl

theorem controlPlan_feasible (cp : ControlProblem X Z A) {T : ℕ∞} (s₀ : X × Z)
    {sel : X × Z → A} (hsel : Measurable sel) (hselΓ : ∀ s, sel s ∈ cp.Γ s)
    (hΓ : MeasurableSet {p : (X × Z) × A | p.2 ∈ cp.Γ p.1}) {σ : Plan Z A} (hσ : IsPlan T σ) :
    controlPlan cp s₀ sel σ ∈ feasiblePlans cp.toMDP T s₀ := by
  classical
  refine ⟨fun t ht => ?_, fun t _ g => ?_⟩
  · have hz : Measurable fun g : Fin t → X × Z => fun i => (g i).2 :=
      measurable_pi_iff.2 fun i => (measurable_pi_apply i).snd
    have hσt := (hσ t ht).comp hz
    have hset : MeasurableSet {g : Fin t → X × Z |
        σ t (fun i => (g i).2) ∈ cp.Γ (lastState s₀ g)} :=
      ((measurable_lastState s₀ t).prodMk hσt) hΓ
    exact Measurable.ite hset hσt (hsel.comp (measurable_lastState s₀ t))
  · change controlPlan cp s₀ sel σ t g ∈ cp.Γ (lastState s₀ g)
    unfold controlPlan
    split_ifs with h
    · exact h
    · exact hselΓ _

omit [MeasurableSpace X] in
/-- A feasible control policy is the policy induced by `controlPlan`. -/
theorem inducedPolicy_controlPlan (cp : ControlProblem X Z A) {T : ℕ∞} (x₀ : X) (z₀ : Z)
    (sel : X × Z → A) {σ : Plan Z A} (hσ : IsFeasibleControl cp T x₀ z₀ σ) :
    ∀ t : ℕ, (t : ℕ∞) < T → inducedPolicy cp (x₀, z₀) (controlPlan cp (x₀, z₀) sel σ) t = σ t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    funext h
    have hX : ctrlX cp x₀ z₀ (inducedPolicy cp (x₀, z₀) (controlPlan cp (x₀, z₀) sel σ)) t =
        ctrlX cp x₀ z₀ σ t :=
      ctrlX_congr cp x₀ z₀ fun j hj => ih j hj (lt_of_le_of_lt (by exact_mod_cast hj.le) ht)
    have hmem := hσ.2 t ht h
    have e1 := lastState_ctrlLift cp x₀ z₀ (controlPlan cp (x₀, z₀) sel σ) t h
    have e2 := snd_ctrlLift cp (x₀, z₀) (controlPlan cp (x₀, z₀) sel σ) t h
    rw [hX] at e1
    change controlPlan cp (x₀, z₀) sel σ t
      (ctrlLift cp (x₀, z₀) (controlPlan cp (x₀, z₀) sel σ) t h) = σ t h
    rw [controlPlan_apply, e1, e2]
    simp only [hmem, ↓reduceIte]

/-- **The control problem is the MDP** (Miao, p. 154): with measurable data, a measurable graph
of `Γ` and a measurable selection, the value of the `T`-horizon MDP from `(x₀, z₀)` equals the
value (5.12) of the control problem. -/
theorem V0_control (cp : ControlProblem X Z A) [IsMarkovKernel cp.Q]
    (hφ : ∀ t, Measurable (cp.φ t)) (hu : ∀ t, Measurable (cp.u t)) (huT : Measurable cp.uT)
    (hΓ : MeasurableSet {p : (X × Z) × A | p.2 ∈ cp.Γ p.1}) {sel : X × Z → A}
    (hsel : Measurable sel) (hselΓ : ∀ s, sel s ∈ cp.Γ s) (T : ℕ) (x₀ : X) (z₀ : Z) :
    V0 cp.toMDP T (x₀, z₀) = controlV cp T x₀ z₀ := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun σ hσ => ?_)
  · have hπm : ∀ j < T, Measurable (π j) := fun j hj => hπ.1 j (by exact_mod_cast hj)
    rw [J0T_control cp hφ hu huT x₀ z₀ hπm]
    refine le_iSup₂ (f := fun σ (_ : σ ∈ {σ | IsFeasibleControl cp T x₀ z₀ σ}) =>
      (controlObj cp T x₀ z₀ σ : EReal)) _ ⟨fun t ht => ?_, fun t ht h => ?_⟩
    · exact measurable_inducedPolicy cp hφ _ fun j hj =>
        hπ.1 j (lt_of_le_of_lt (by exact_mod_cast hj) ht)
    · have := hπ.2 t ht (ctrlLift cp (x₀, z₀) π t h)
      rwa [lastState_ctrlLift] at this
  · have hπ := controlPlan_feasible cp (x₀, z₀) hsel hselΓ hΓ hσ.1
    have := le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans cp.toMDP T (x₀, z₀)) =>
      (J0T cp.toMDP T (x₀, z₀) π : EReal)) _ hπ
    rw [J0T_control cp hφ hu huT x₀ z₀ fun j hj => hπ.1 j (by exact_mod_cast hj),
      controlObj_congr cp T x₀ z₀ fun j hj =>
        inducedPolicy_controlPlan cp x₀ z₀ sel hσ j (by exact_mod_cast hj)] at this
    exact this

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Bellman solution of §6.4 is the value of the Markov decision problem

Miao, §6.4, p. 175: "By this theorem [6.4.1] and the Measurable Selection Theorem, each `G_t`
permits a measurable selection. We can then apply Theorem 6.3.2 to deduce that the function
`V_0` delivered by the Bellman equation is equal to the value function for the Markov decision
problem at date zero and that any plan generated by `(G_t)` gives the optimal plan for this
problem."

The state space is `X ⊆ ℝⁿ` (with `Z`) and the action space `A ⊆ ℝᵐ`, the spaces of the
Measurable Selection Theorem (SLP Theorem 7.6, `theorem_7_6`).

* `OCModel.toCP`: the control model of §6.4 as the control problem of §5.2.4
  (`ControlProblem`, copied in `MDPOptimalControl`), with state space `↥X × Z` and action space
  `↥A`; `OCModel.toMDP` is its Markov decision process (Miao, p. 154), whose kernel is the law
  of `(φ(x, a, z, z′), z′)`, `z′ ~ Q(z, ·)` (`controlKernel`). Assumption 6.4.5 makes `φ` map
  `X × A × Z × Z` into `X`, which is what lets the state space be `X` rather than `ℝⁿ`.
* `bellmanVal_toMDP`: `∫ V_{t+1} dP_{t+1}((x, z), a; ·) = ∫ V_{t+1}(φ(x, a, z, z′), z′) Q(z, dz′)`
  (`integral_map` through the control kernel), so the Bellman equation (6.29) is the Bellman
  equation (6.19) of the MDP, with `w_t(x, z) = V_t(x, z)`.
* `exists_selection_G`: each `G_t` has a measurable selection with values in `A`.
* `p175`: Theorem 6.3.2 applied to the MDP; `p175_date_zero`: `V_0` is the MDP value at date
  zero and every plan generated by measurable selections of `(G_t)` is optimal;
  `p175_control`: the same plan solves the control problem (5.12) = (6.28) (Chapter 5's
  `J0T_control`, `V0_control`).
* `p175_compact`, `p175_countable`: the two cases of Assumption 6.4.3.

**Added hypothesis.** Theorem 6.3.2 needs Assumption 5.1.3 (the rewards along every feasible
plan are integrable). Continuous rewards on a non-compact `X` need not be integrable, so we
assume the rewards bounded on `X × Z × A`: `|u_t(x, z, a)| ≤ B` (`t < T`) and `|u_T(x, z)| ≤ B`.
This is the hypothesis `theorem_6_4_1_countable` already needs; in case (ii) it holds when `X`
and `A` are compact (`bounded_of_compact`, used in `p175_compact_XA`). Also `β ≥ 0` (from
Assumption 5.1.2) and `Z` second countable (to make the product σ-algebra on `X × Z × A`
Borel; it holds in both cases of Assumption 6.4.3). The rewards of the MDP after the horizon,
`u_t` for `t ≥ T`, which the book leaves out, are set to `0`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {n m : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- The control model of §6.4 as the control problem of §5.2.4 (Miao, p. 172: "the model in
§5.2.4"), on the state space `X × Z` and the action space `A`. `hX` is the first half of
Assumption 6.4.5 (`φ` maps `X × A × Z × Z` into `X`). Rewards after the horizon are `0`. -/
noncomputable def toCP (M : OCModel (Fin n → ℝ) (Fin m → ℝ) Z)
    (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) : ControlProblem ↥M.X Z ↥M.A where
  Q := M.Q
  φ := fun _ p => ⟨M.φ p.1 p.2.1 p.2.2.1 p.2.2.2, hX _ p.1.2 _ p.2.1.2 _ _⟩
  Γ := fun s => {a | (a : Fin m → ℝ) ∈ M.Γ s.1 s.2}
  u := fun t p => if t < M.T then M.u t p.1 p.2.1 p.2.2 else 0
  uT := fun s => M.uT s.1 s.2
  β := M.β

/-- The Markov decision process of the control model (Miao, pp. 154 and 175). -/
noncomputable def toMDP (M : OCModel (Fin n → ℝ) (Fin m → ℝ) Z)
    (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) : MDP (↥M.X × Z) ↥M.A :=
  (M.toCP hX).toMDP

/-- The candidate value `w_t(x, z) = V_t(x, z)` on the state space `X × Z`. -/
noncomputable def wV (M : OCModel (Fin n → ℝ) (Fin m → ℝ) Z) (t : ℕ) (s : ↥M.X × Z) : ℝ :=
  M.V t s.1 s.2

/-- The embedding of `X × Z` (a product of a subtype) into the subtype `↥(X ×ˢ univ)`. -/
def toXZ (M : OCModel (Fin n → ℝ) (Fin m → ℝ) Z) (s : ↥M.X × Z) :
    ↥(M.X ×ˢ (Set.univ : Set Z)) :=
  ⟨(s.1, s.2), s.1.2, Set.mem_univ _⟩

variable [MetricSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (M : OCModel (Fin n → ℝ) (Fin m → ℝ) Z) (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X)
  {P : ((Fin n → ℝ) → Z → ℝ) → Prop}

omit [BorelSpace Z] [SecondCountableTopology Z] in
theorem continuous_toXZ : Continuous M.toXZ :=
  ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

theorem measurable_toXZ : Measurable M.toXZ := (M.continuous_toXZ).measurable

/-- A function continuous on `X × Z` is measurable on the state space `↥X × Z`. -/
theorem measurable_of_continuousOn {f : (Fin n → ℝ) → Z → ℝ}
    (hf : ContinuousOn (fun p : (Fin n → ℝ) × Z => f p.1 p.2) (M.X ×ˢ Set.univ)) :
    Measurable fun s : ↥M.X × Z => f s.1 s.2 :=
  (hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    fun s => ⟨s.1.2, Set.mem_univ _⟩).measurable

include hX in
/-- Assumption 6.4.5 makes the law of motion `φ` of the control problem measurable. -/
theorem measurable_toCP_φ (h645 : M.Assumption645) (t : ℕ) : Measurable ((M.toCP hX).φ t) := by
  refine Continuous.measurable (Continuous.subtype_mk ?_ _)
  refine h645.2.comp_continuous (Continuous.prodMk
    (continuous_subtype_val.comp continuous_fst) (Continuous.prodMk
      (continuous_subtype_val.comp continuous_snd.fst) continuous_snd.snd)) fun p => ?_
  exact ⟨p.1.2, p.2.1.2, Set.mem_univ _⟩

/-- Assumption 6.4.6 makes the rewards of the control problem measurable. -/
theorem measurable_toCP_u (h646 : M.Assumption646) (t : ℕ) : Measurable ((M.toCP hX).u t) := by
  by_cases ht : t < M.T
  · have hc : Continuous fun p : ↥M.X × Z × ↥M.A => M.u t p.1 p.2.1 p.2.2 := by
      refine (h646.1 t ht).comp_continuous (Continuous.prodMk
        (continuous_subtype_val.comp continuous_fst) (Continuous.prodMk continuous_snd.fst
          (continuous_subtype_val.comp continuous_snd.snd))) fun p => ?_
      exact ⟨p.1.2, Set.mem_univ _, p.2.2.2⟩
    have e : (M.toCP hX).u t = fun p => M.u t p.1 p.2.1 p.2.2 := by
      funext p
      simp only [toCP, ht, ↓reduceIte]
    rw [e]
    exact hc.measurable
  · have e : (M.toCP hX).u t = fun _ => 0 := by
      funext p
      simp only [toCP, ht, ↓reduceIte]
    rw [e]
    exact measurable_const

theorem measurable_toCP_uT (h646 : M.Assumption646) : Measurable (M.toCP hX).uT :=
  M.measurable_of_continuousOn h646.2

/-- The kernel of the MDP: `P_{t+1}((x, z), a; ·)` is the law of `(φ(x, a, z, z′), z′)`,
`z′ ~ Q(z, ·)`. -/
theorem toMDP_P [IsMarkovKernel M.Q] (h645 : M.Assumption645) (t : ℕ) (x : ↥M.X) (z : Z)
    (a : ↥M.A) : (M.toMDP hX).P t ((x, z), a) =
      (M.Q z).map fun z' => ((M.toCP hX).φ t (x, a, z, z'), z') := by
  have : IsMarkovKernel (M.toCP hX).Q := ‹IsMarkovKernel M.Q›
  exact controlKernel_apply (M.toCP hX) (M.measurable_toCP_φ hX h645 t) x z a

theorem measurable_next (h645 : M.Assumption645) (t : ℕ) (x : ↥M.X) (z : Z) (a : ↥M.A) :
    Measurable fun z' : Z => ((M.toCP hX).φ t (x, a, z, z'), z') :=
  ((M.measurable_toCP_φ hX h645 t).comp (measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk measurable_id)))).prodMk measurable_id

/-- **The rewrite of p. 175.** For `t < T`, the right-hand side of the MDP Bellman equation
(6.19) at `w = V` is the objective of (6.29):
`u_t(x, z, a) + β ∫ V_{t+1} dP_{t+1}((x, z), a; ·) =
u_t(x, z, a) + β ∫ V_{t+1}(φ(x, a, z, z′), z′) Q(z, dz′)`, by `integral_map`. -/
theorem bellmanVal_toMDP [IsMarkovKernel M.Q] (hS : M.Standing P) {t : ℕ} (ht : t < M.T)
    (x : ↥M.X) (z : Z) (a : ↥M.A) :
    po_bellmanVal (M.toMDP hX) M.wV t (x, z) a = M.obj t (M.V (t + 1)) x z a := by
  have hw : Measurable (M.wV (t + 1)) := M.measurable_of_continuousOn (hS.contV ht)
  simp only [po_bellmanVal]
  rw [M.toMDP_P hX hS.a645 t x z a, integral_map (M.measurable_next hX hS.a645 t x z a).aemeasurable
    hw.aestronglyMeasurable]
  simp only [obj, toMDP, ControlProblem.toMDP, toCP, ht, ↓reduceIte, wV, cont]

/-- The integrals in (6.19) exist: `V_{t+1}` is integrable against `P_{t+1}((x, z), a; ·)`. -/
theorem integrable_toMDP [IsMarkovKernel M.Q] (hS : M.Standing P) {t : ℕ} (ht : t < M.T)
    (x : ↥M.X) (z : Z) (a : ↥M.A) : Integrable (M.wV (t + 1)) ((M.toMDP hX).P t ((x, z), a)) := by
  have hw : Measurable (M.wV (t + 1)) := M.measurable_of_continuousOn (hS.contV ht)
  rw [M.toMDP_P hX hS.a645 t x z a, integrable_map_measure hw.aestronglyMeasurable
    (M.measurable_next hX hS.a645 t x z a).aemeasurable]
  exact hS.integrable ht x.2 a.2 z

/-- **Measurable selections of `G_t`** (Miao, p. 175: "By this theorem and the Measurable
Selection Theorem, each `G_t` permits a measurable selection"): there are measurable
`g_t : X × Z → A` with `g_t(x, z) ∈ G_t(x, z)` for `t < T`. -/
theorem exists_selection_G (hS : M.Standing P) :
    ∃ g : ℕ → ↥M.X × Z → ↥M.A, ∀ t < M.T, Measurable (g t) ∧
      ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2 := by
  have hsel : ∀ t < M.T, ∃ g : ↥(M.X ×ˢ (Set.univ : Set Z)) → ↥M.A,
      Measurable g ∧ ∀ s, (g s : Fin m → ℝ) ∈ M.Gs t s := by
    intro t ht
    have h := (M.theorem_6_4_1 P hS.expCont hS.memP hS.a644 hS.a646).2 t ht
    exact theorem_7_6_subtype (fun s => (h s).2.2) (fun s => (h s).2.1) fun s _ ha =>
      hS.a644.1 _ s.2.1 _ ha.1
  choose sel hsm hsG using hsel
  have hne : ∀ s : ↥M.X × Z, (M.Γ s.1 s.2).Nonempty := fun s =>
    (hS.a644.2 (M.toXZ s)).2.1.1
  classical
  refine ⟨fun t s => if ht : t < M.T then sel t ht (M.toXZ s) else
    ⟨(hne s).some, hS.a644.1 _ s.1.2 _ (hne s).some_mem⟩, fun t ht => ⟨?_, fun s => ?_⟩⟩
  · simp only [ht, ↓reduceDIte]
    exact (hsm t ht).comp M.measurable_toXZ
  · simp only [ht, ↓reduceDIte]
    exact hsG t ht (M.toXZ s)

/-- Miao, p. 175: **the Bellman solution is the value of the Markov decision problem**, at
every date. Let Lemma 6.4.1 hold on a class `P` containing every `V_t` and Assumptions 6.4.4–6.4.6
hold (`Standing`; cases (i) and (ii) of Assumption 6.4.3 give it), with `X ⊆ ℝⁿ`, `A ⊆ ℝᵐ`,
`Q` a stochastic kernel on a second-countable metric space `Z`, `β ≥ 0`, and — the added
hypothesis that makes Assumption 5.1.3 hold — rewards bounded by `B` on `X × Z × A`. Let
`g_t : X × Z → A` (`t < T`) be measurable selections of `G_t` (they exist:
`exists_selection_G`). Then, by Theorem 6.3.2 applied to the MDP `toMDP` with
`w_t = V_t`, for every `t ≤ T` and history `sᵗ` ending in `(x, z)`, the plan generated by
`(g_t)` from `sᵗ` is feasible, attains `V_t(x, z)`, and `V_t(x, z)` is the value `V_t(sᵗ)` of
the MDP from `sᵗ`. -/
theorem p175 [IsMarkovKernel M.Q] (hS : M.Standing P) (hβ : 0 ≤ M.β) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) {g : ℕ → ↥M.X × Z → ↥M.A}
    (hg : ∀ t < M.T, Measurable (g t))
    (hgG : ∀ t < M.T, ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) (t : ℕ)
    (ht : t ≤ M.T) (h : Fin (t + 1) → ↥M.X × Z) :
    po_genFrom g t (h (Fin.last t)) ∈ po_plansFrom (M.toMDP hS.a645.1) M.T t h ∧
      po_JFrom (M.toMDP hS.a645.1) M.T t h (po_genFrom g t (h (Fin.last t))) =
        M.V t (h (Fin.last t)).1 (h (Fin.last t)).2 ∧
      po_VFrom (M.toMDP hS.a645.1) M.T t h = M.V t (h (Fin.last t)).1 (h (Fin.last t)).2 := by
  have hX := hS.a645.1
  have : IsMarkovKernel (M.toCP hX).Q := ‹IsMarkovKernel M.Q›
  have hP : (M.toMDP hX).IsMarkov :=
    controlMDP_isMarkov (M.toCP hX) (M.measurable_toCP_φ hX hS.a645)
  have hI : po_Assumption513 (M.toMDP hX) M.T := by
    refine po_assumption513_of_bounded hP (B := max B 0) ⟨fun t p => ?_, fun s => ?_⟩
      (fun t => (M.measurable_toCP_u hX hS.a646 t).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
      (M.measurable_toCP_uT hX hS.a646) M.T
    · change |(M.toCP hX).u t (p.1.1, p.1.2, p.2)| ≤ max B 0
      by_cases ht : t < M.T
      · simp only [toCP, ht, ↓reduceIte]
        exact (hu t ht _ p.1.1.2 _ _ p.2.2).trans (le_max_left _ _)
      · simp only [toCP, ht, ↓reduceIte, abs_zero]
        exact le_max_right _ _
    · exact (huT _ s.1.2 _).trans (le_max_left _ _)
  have hmax : ∀ t < M.T, ∀ s : ↥M.X × Z, po_SolvesAt (M.toMDP hX) M.wV t s ∧
      g t s ∈ po_G (M.toMDP hX) M.wV t s := by
    intro t ht s
    obtain ⟨x, z⟩ := s
    refine po_solvesAt_of_max (fun a ha => ?_) (hgG t ht (x, z)).1 ?_
    · rw [M.bellmanVal_toMDP hX hS ht]
      exact hS.obj_le_V ht x.2 ha
    · rw [M.bellmanVal_toMDP hX hS ht]
      exact (hgG t ht (x, z)).2
  exact theorem_6_3_2 hP hβ hI (fun t ht s a _ => M.integrable_toMDP hX hS ht s.1 s.2 a)
    (fun t ht s => (hmax t ht s).1) hg (fun t ht s => (hmax t ht s).2)
    (fun s => by simp only [wV, M.V_T_eq]; rfl) t ht h

/-- Miao, p. 175: at date zero, "the function `V_0` delivered by the Bellman equation is equal
to the value function for the Markov decision problem at date zero and any plan generated by
`(G_t)` gives the optimal plan for this problem." Under the hypotheses of `p175`, the plan
`π_t(sᵗ) = g_t(s_t)` generated from `s₀ = (x₀, z₀)` is feasible and
`J₀ᵀ(s₀, π) = V_0(x₀, z₀) = V₀ᵀ(s₀)`, the value (5.5) of the MDP. -/
theorem p175_date_zero [IsMarkovKernel M.Q] (hS : M.Standing P) (hβ : 0 ≤ M.β) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) {g : ℕ → ↥M.X × Z → ↥M.A}
    (hg : ∀ t < M.T, Measurable (g t))
    (hgG : ∀ t < M.T, ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) (x₀ : ↥M.X) (z₀ : Z) :
    po_genPlan g (x₀, z₀) ∈ feasiblePlans (M.toMDP hS.a645.1) M.T (x₀, z₀) ∧
      J0T (M.toMDP hS.a645.1) M.T (x₀, z₀) (po_genPlan g (x₀, z₀)) = M.V 0 x₀ z₀ ∧
      V0 (M.toMDP hS.a645.1) M.T (x₀, z₀) = M.V 0 x₀ z₀ := by
  have h := M.p175 hS hβ hu huT hg hgG 0 (Nat.zero_le _) fun _ => (x₀, z₀)
  have e : po_genFrom g 0 (x₀, z₀) = po_genPlan g (x₀, z₀) := rfl
  rw [e] at h
  rw [← po_VFrom_zero]
  exact h

include hX in
/-- The graph `{((x, z), a) : a ∈ Γ(x, z)}` is closed in `(X × Z) × A`, hence measurable, when
`Γ` is u.h.c. (Assumption 6.4.4). -/
theorem measurableSet_graph_toCP (h644 : M.Assumption644) :
    MeasurableSet {p : (↥M.X × Z) × ↥M.A | p.2 ∈ (M.toCP hX).Γ p.1} := by
  refine IsClosed.measurableSet (IsSeqClosed.isClosed fun ps p hps hlim => ?_)
  have h1 : Tendsto (fun k => M.toXZ (ps k).1) atTop (𝓝 (M.toXZ p.1)) :=
    (M.continuous_toXZ.tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
  obtain ⟨y, hy, φ, hφm, hφ⟩ := (h644.2 (M.toXZ p.1)).2.2.2 _ h1
    (fun k => ((ps k).2 : Fin m → ℝ)) fun k => hps k
  have h2 : Tendsto (fun k => ((ps k).2 : Fin m → ℝ)) atTop (𝓝 (p.2 : Fin m → ℝ)) :=
    (continuous_subtype_val.tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have e := tendsto_nhds_unique hφ (h2.comp hφm.tendsto_atTop)
  change (p.2 : Fin m → ℝ) ∈ M.Γ p.1.1 p.1.2
  rw [← e]
  exact hy

/-- `Γ` has a measurable selection with values in `A` (SLP Theorem 7.6, Assumption 6.4.4). -/
theorem exists_selection_Γ (h644 : M.Assumption644) :
    ∃ sel : ↥M.X × Z → ↥M.A, Measurable sel ∧ ∀ s, sel s ∈ (M.toCP hX).Γ s := by
  obtain ⟨h, hm, hmem⟩ := theorem_7_6_subtype (T := M.A) (fun s => (h644.2 s).2.2)
    (fun s => (h644.2 s).1) fun s _ ha => h644.1 _ s.2.1 _ ha
  exact ⟨fun s => h (M.toXZ s), hm.comp M.measurable_toXZ, fun s => hmem (M.toXZ s)⟩

/-- Miao, p. 175: **the control problem (6.28).** Under the hypotheses of `p175`, the plan
generated by measurable selections `(g_t)` of `(G_t)` from `(x₀, z₀)` is optimal for the control
problem. By Chapter 5's equivalence of the control problem and the MDP (Miao, p. 154:
`J0T_control`, `V0_control`), the control policy `σ_t(z₁, …, z_t)` it induces is feasible, its
Bolza objective (5.12) = (6.28) (an expectation over the shock histories) is `V_0(x₀, z₀)`, and
`V_0(x₀, z₀)` is the value of the control problem. -/
theorem p175_control [IsMarkovKernel M.Q] (hS : M.Standing P) (hβ : 0 ≤ M.β) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) {g : ℕ → ↥M.X × Z → ↥M.A}
    (hg : ∀ t < M.T, Measurable (g t))
    (hgG : ∀ t < M.T, ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) (x₀ : ↥M.X) (z₀ : Z) :
    IsFeasibleControl (M.toCP hS.a645.1) M.T x₀ z₀
        (inducedPolicy (M.toCP hS.a645.1) (x₀, z₀) (po_genPlan g (x₀, z₀))) ∧
      controlObj (M.toCP hS.a645.1) M.T x₀ z₀
        (inducedPolicy (M.toCP hS.a645.1) (x₀, z₀) (po_genPlan g (x₀, z₀))) = M.V 0 x₀ z₀ ∧
      controlV (M.toCP hS.a645.1) M.T x₀ z₀ = M.V 0 x₀ z₀ := by
  obtain ⟨hF, hJ, hV⟩ := M.p175_date_zero hS hβ hu huT hg hgG x₀ z₀
  set cp := M.toCP hS.a645.1
  have : IsMarkovKernel cp.Q := ‹IsMarkovKernel M.Q›
  have e : M.toMDP hS.a645.1 = cp.toMDP := rfl
  rw [e] at hF hJ hV
  have hφ := M.measurable_toCP_φ hS.a645.1 hS.a645
  have hu' := M.measurable_toCP_u hS.a645.1 hS.a646
  have huT' := M.measurable_toCP_uT hS.a645.1 hS.a646
  have hπm : ∀ j < M.T, Measurable (po_genPlan g (x₀, z₀) j) := fun j hj =>
    hF.1 j (by exact_mod_cast hj)
  obtain ⟨sel, hsel, hselΓ⟩ := M.exists_selection_Γ hS.a645.1 hS.a644
  refine ⟨⟨fun t ht => ?_, fun t ht h => ?_⟩, ?_, ?_⟩
  · exact measurable_inducedPolicy cp hφ _ fun j hj =>
      hF.1 j (lt_of_le_of_lt (by exact_mod_cast hj) ht)
  · have := hF.2 t ht (ctrlLift cp (x₀, z₀) (po_genPlan g (x₀, z₀)) t h)
    rwa [lastState_ctrlLift] at this
  · rw [← J0T_control cp hφ hu' huT' x₀ z₀ hπm]
    exact hJ
  · rw [← V0_control cp hφ hu' huT' (M.measurableSet_graph_toCP hS.a645.1 hS.a644) hsel hselΓ]
    exact hV

omit [BorelSpace Z] [SecondCountableTopology Z] in
/-- Miao, p. 175: **case (ii) of Assumption 6.4.3** (`Z` compact, `Q` Feller), with rewards
bounded on `X × Z × A`: under Assumptions 6.4.4–6.4.6 and `β ≥ 0`, the plan generated from
`(x₀, z₀)` by measurable selections of `(G_t)` is feasible and optimal for the MDP, and
`V_0(x₀, z₀)` is the MDP value at date zero. -/
theorem p175_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii) (h644 : M.Assumption644)
    (h645 : M.Assumption645) (h646 : M.Assumption646) (hβ : 0 ≤ M.β) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) {g : ℕ → ↥M.X × Z → ↥M.A}
    (hg : ∀ t < M.T, Measurable (g t))
    (hgG : ∀ t < M.T, ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) (x₀ : ↥M.X) (z₀ : Z) :
    po_genPlan g (x₀, z₀) ∈ feasiblePlans (M.toMDP h645.1) M.T (x₀, z₀) ∧
      J0T (M.toMDP h645.1) M.T (x₀, z₀) (po_genPlan g (x₀, z₀)) = M.V 0 x₀ z₀ ∧
      V0 (M.toMDP h645.1) M.T (x₀, z₀) = M.V 0 x₀ z₀ := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  exact M.p175_date_zero (Standing.of_compact M h643 h644 h645 h646) hβ hu huT hg hgG x₀ z₀

omit [BorelSpace Z] [SecondCountableTopology Z] in
/-- In case (ii) of Assumption 6.4.3, compact `X` and `A` make the continuous rewards bounded on
`X × Z × A` (Assumption 6.4.6), as `p175_compact` needs. -/
theorem bounded_of_compact (h643 : M.Assumption643ii) (hXc : IsCompact M.X)
    (hAc : IsCompact M.A) (h646 : M.Assumption646) : ∃ B : ℝ,
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B) ∧
        ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B := by
  have : CompactSpace Z := h643.1
  have hK : IsCompact (M.X ×ˢ (Set.univ : Set Z) ×ˢ M.A) := hXc.prod (isCompact_univ.prod hAc)
  have hK' : IsCompact (M.X ×ˢ (Set.univ : Set Z)) := hXc.prod isCompact_univ
  have hC : ∀ t, ∃ C : ℝ, t < M.T → ∀ p ∈ M.X ×ˢ (Set.univ : Set Z) ×ˢ M.A,
      ‖M.u t p.1 p.2.1 p.2.2‖ ≤ C := by
    intro t
    by_cases ht : t < M.T
    · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (h646.1 t ht)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose C hC using hC
  obtain ⟨D, hD⟩ := hK'.exists_bound_of_continuousOn h646.2
  refine ⟨∑ t ∈ Finset.range M.T, |C t| + |D|, fun t ht x hx z a ha => ?_, fun x hx z => ?_⟩
  · have h1 := hC t ht (x, z, a) ⟨hx, Set.mem_univ _, ha⟩
    rw [Real.norm_eq_abs] at h1
    have h2 : |C t| ≤ ∑ t ∈ Finset.range M.T, |C t| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_range.2 ht)
    linarith [le_abs_self (C t), abs_nonneg D]
  · have h1 := hD (x, z) ⟨hx, Set.mem_univ _⟩
    rw [Real.norm_eq_abs] at h1
    have h2 : 0 ≤ ∑ t ∈ Finset.range M.T, |C t| :=
      Finset.sum_nonneg fun i _ => abs_nonneg (C i)
    linarith [le_abs_self D]

omit [BorelSpace Z] [SecondCountableTopology Z] in
/-- Miao, p. 175: **case (ii) of Assumption 6.4.3 with compact `X` and `A`**; no bound on the
rewards is assumed (it follows from `bounded_of_compact`). Under Assumptions 6.4.4–6.4.6 and
`β ≥ 0`, measurable selections of `(G_t)` exist, and the plan they generate from `(x₀, z₀)` is
feasible and optimal for the MDP, with value `V_0(x₀, z₀)`. -/
theorem p175_compact_XA [IsMarkovKernel M.Q] (h643 : M.Assumption643ii) (hXc : IsCompact M.X)
    (hAc : IsCompact M.A) (h644 : M.Assumption644) (h645 : M.Assumption645)
    (h646 : M.Assumption646) (hβ : 0 ≤ M.β) (x₀ : ↥M.X) (z₀ : Z) :
    ∃ g : ℕ → ↥M.X × Z → ↥M.A, (∀ t < M.T, Measurable (g t) ∧
      ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) ∧
      po_genPlan g (x₀, z₀) ∈ feasiblePlans (M.toMDP h645.1) M.T (x₀, z₀) ∧
      J0T (M.toMDP h645.1) M.T (x₀, z₀) (po_genPlan g (x₀, z₀)) = M.V 0 x₀ z₀ ∧
      V0 (M.toMDP h645.1) M.T (x₀, z₀) = M.V 0 x₀ z₀ := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  have hS := Standing.of_compact M h643 h644 h645 h646
  obtain ⟨B, hu, huT⟩ := M.bounded_of_compact h643 hXc hAc h646
  obtain ⟨g, hg⟩ := M.exists_selection_G hS
  exact ⟨g, hg, M.p175_date_zero hS hβ hu huT (fun t ht => (hg t ht).1)
    (fun t ht => (hg t ht).2) x₀ z₀⟩

omit [BorelSpace Z] [SecondCountableTopology Z] in
/-- Miao, p. 175: **case (i) of Assumption 6.4.3** (`Z` countable and discrete), with the bounded
rewards that Theorem 6.4.1 already needs in this case (`theorem_6_4_1_countable`): under
Assumptions 6.4.4–6.4.6 and `β ≥ 0`, the plan generated from `(x₀, z₀)` by measurable selections
of `(G_t)` is feasible and optimal for the MDP, and `V_0(x₀, z₀)` is the MDP value. -/
theorem p175_countable [IsMarkovKernel M.Q] (h643 : Assumption643i Z) (h644 : M.Assumption644)
    (h645 : M.Assumption645) (h646 : M.Assumption646) (hβ : 0 ≤ M.β) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) {g : ℕ → ↥M.X × Z → ↥M.A}
    (hg : ∀ t < M.T, Measurable (g t))
    (hgG : ∀ t < M.T, ∀ s : ↥M.X × Z, (g t s : Fin m → ℝ) ∈ M.G t s.1 s.2) (x₀ : ↥M.X) (z₀ : Z) :
    po_genPlan g (x₀, z₀) ∈ feasiblePlans (M.toMDP h645.1) M.T (x₀, z₀) ∧
      J0T (M.toMDP h645.1) M.T (x₀, z₀) (po_genPlan g (x₀, z₀)) = M.V 0 x₀ z₀ ∧
      V0 (M.toMDP h645.1) M.T (x₀, z₀) = M.V 0 x₀ z₀ := by
  have : Countable Z := h643.1
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  have : BorelSpace Z := DiscreteMeasurableSpace.toBorelSpace
  have : SecondCountableTopology Z := inferInstance
  exact M.p175_date_zero (Standing.of_countable M h643 h644 h645 h646 hu huT) hβ hu huT hg hgG
    x₀ z₀

end OCModel

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The consumption-saving problem of §6.6.2: the model and existence

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.6.2: monotonicity, concavity and the policy functions

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §6.6.2: the Inada condition, the envelope and first-order conditions, and comparisons

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 6.5–6.7: the consumption-saving problem with iid income, Markov income and
# random returns

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 6.8: the deterministic CRRA consumption-saving problem

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

namespace Miao.FiniteHorizonDP

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

end Miao.FiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 6.9–6.10: exponential (CARA) utility

Miao, Exercises 9–10, pp. 190–191.

**Exercise 6.9** (Schechtman–Escudero 1977). Utility `−e^{−γc}`, iid income `y` with
distribution `μ` concentrated on `[y_min, y_max]`, no constraint on `c` or `a`. Without a
terminal condition the problem is unbounded (utility is bounded above by `0`), so we impose
`a_{T+1} = 0`; then with cash on hand `x = Ra + y` the time-to-go problem is
`v_0(x) = −e^{−γx}`, `v_{n+1}(x) = sup_{s ∈ ℝ} −e^{−γ(x−s)} + β E v_n(Rs + y)` (`cs_cara_v`).
`ex_6_9`: `v_n(x) = −A_n e^{−α_n x}` with `α_n = γ / Σ_{k=0}^n R^{−k}`, `A_n > 0` given
recursively (`cs_caraA`), the unique optimal saving is
`s_{n+1}(x) = (γx + L_n)/(γ + α_n R)`, `L_n = log(β A_n M_n α_n R/γ)`, `M_n = E e^{−α_n y}`, and
consumption `c_{n+1}(x) = (α_n R x − L_n)/(γ + α_n R)` is linear in `x` with the certainty
marginal propensity `1/Σ_{k=0}^{n+1} R^{−k}`. The one-step problem is `cs_cara_step`.

**Exercise 6.10** (Levhari–Mirman–Zilcha 1980). Add `c ≥ 0`, `a_{t+1} ≥ 0`: this is §6.6.2 with
`u(c) = −e^{−γc}`, `b = 0` (`bookModel`). The Inada condition fails (`u′(0) = γ`), so only the
derivative-free results apply (`ex_6_10`): `v_n` strictly increasing and strictly concave, a
unique continuous saving policy, `s_n` and `g_n` increasing in `x`, and **threshold structure**:
`{x : s_n(x) = 0}` and `{x : g_n(x) = 0}` are initial segments of `[0, ∞)`. With one period to go
the policy is explicit (`ex_6_10_one`): **the Exercise 6.9 saving clamped to `[0, x]`**,
`s_1(x) = max(0, min(x, (γx + L_0)/(γ + γR)))`, `L_0 = log(βR E e^{−γy})`. For `n ≥ 2` the
continuation value `v_{n−1}` is no longer exponential, so the policy is not of the Exercise 6.9
form; we prove the structure only (not formalised: a closed form, which does not exist).
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory Real

/-- **The one-step CARA problem** (Exercises 9–10): with `γ, α, R, K > 0` and
`(γ + αR) s₀ = γx + L`, `L = log(KαR/γ)`, the function
`f(s) = −e^{−γ(x − s)} − K e^{−αRs}` has the strict global maximum `s₀`, and
`f(s₀) = −(1 + γ/(αR)) e^{γL/(γ + αR)} e^{−(γαR/(γ + αR)) x}`. -/
theorem cs_cara_step {γ α R K : ℝ} (hγ : 0 < γ) (hα : 0 < α) (hR : 0 < R) (hK : 0 < K)
    (x s₀ : ℝ) (hs₀ : (γ + α * R) * s₀ = γ * x + Real.log (K * α * R / γ)) :
    (∀ s, s ≠ s₀ → -Real.exp (-(γ * (x - s))) - K * Real.exp (-(α * R * s)) <
        -Real.exp (-(γ * (x - s₀))) - K * Real.exp (-(α * R * s₀))) ∧
      -Real.exp (-(γ * (x - s₀))) - K * Real.exp (-(α * R * s₀)) =
        -((1 + γ / (α * R)) * Real.exp (γ * Real.log (K * α * R / γ) / (γ + α * R))) *
          Real.exp (-(γ * α * R / (γ + α * R) * x)) := by
  set L := Real.log (K * α * R / γ)
  have hαR : 0 < α * R := mul_pos hα hR
  have hKL : Real.exp L = K * α * R / γ := Real.exp_log (by positivity)
  -- the first-order condition `γ E₁(s₀) = K α R E₂(s₀)`
  have hE1 : Real.exp (-(γ * (x - s₀))) = Real.exp L * Real.exp (-(α * R * s₀)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hfoc : K * Real.exp (-(α * R * s₀)) = γ / (α * R) * Real.exp (-(γ * (x - s₀))) := by
    rw [hE1, hKL]
    field_simp
  refine ⟨fun s hs => ?_, ?_⟩
  · have hd : s - s₀ ≠ 0 := sub_ne_zero.2 hs
    have h1 : Real.exp (-(γ * (x - s))) =
        Real.exp (-(γ * (x - s₀))) * Real.exp (γ * (s - s₀)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(α * R * s)) =
        Real.exp (-(α * R * s₀)) * Real.exp (-(α * R * (s - s₀))) := by
      rw [← Real.exp_add]; congr 1; ring
    have e1 := Real.add_one_lt_exp (mul_ne_zero hγ.ne' hd)
    have e2 := Real.add_one_lt_exp (neg_ne_zero.2 (mul_ne_zero hαR.ne' hd))
    have p1 := Real.exp_pos (-(γ * (x - s₀)))
    have p2 := Real.exp_pos (-(α * R * s₀))
    rw [h1, h2]
    have q1 := mul_lt_mul_of_pos_left e1 p1
    have q2 := mul_lt_mul_of_pos_left e2 (mul_pos hK p2)
    have hfoc' : K * Real.exp (-(α * R * s₀)) * (α * R) = γ * Real.exp (-(γ * (x - s₀))) := by
      rw [hfoc]; field_simp
    have hd' : K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀)) =
        Real.exp (-(γ * (x - s₀))) * (γ * (s - s₀)) := by
      rw [show K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀)) =
        K * Real.exp (-(α * R * s₀)) * (α * R) * (s - s₀) by ring, hfoc']
      ring
    have q1' : Real.exp (-(γ * (x - s₀))) * (γ * (s - s₀)) + Real.exp (-(γ * (x - s₀))) <
        Real.exp (-(γ * (x - s₀))) * Real.exp (γ * (s - s₀)) := by linarith [q1]
    have q2' : -(K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀))) +
        K * Real.exp (-(α * R * s₀)) <
        K * (Real.exp (-(α * R * s₀)) * Real.exp (-(α * R * (s - s₀)))) := by
      have : K * Real.exp (-(α * R * s₀)) * (-(α * R * (s - s₀)) + 1) =
          -(K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀))) + K * Real.exp (-(α * R * s₀)) := by
        ring
      rw [← this, ← mul_assoc]
      exact q2
    linarith
  · rw [hfoc]
    have h3 : Real.exp (-(γ * (x - s₀))) =
        Real.exp (γ * L / (γ + α * R)) * Real.exp (-(γ * α * R / (γ + α * R) * x)) := by
      rw [← Real.exp_add]
      congr 1
      have hden : 0 < γ + α * R := by positivity
      have hs : s₀ = (γ * x + L) / (γ + α * R) := by
        rw [eq_div_iff hden.ne']; linarith
      rw [hs]
      field_simp
      ring
    rw [h3]
    ring

/-- The value functions of Exercise 6.9: `v_0(x) = −e^{−γx}`,
`v_{n+1}(x) = sup_s −e^{−γ(x−s)} + β ∫ v_n(Rs + y) μ(dy)`. -/
noncomputable def cs_cara_v (γ β R : ℝ) (μ : Measure ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => -Real.exp (-(γ * x))
  | n + 1 => fun x => sSup (Set.range fun s =>
      -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ)

/-- The exponent `α_n`: `α_0 = γ`, `α_{n+1} = γ α_n R/(γ + α_n R)`. -/
noncomputable def cs_caraAlpha (γ R : ℝ) : ℕ → ℝ
  | 0 => γ
  | n + 1 => γ * cs_caraAlpha γ R n * R / (γ + cs_caraAlpha γ R n * R)

/-- `M_n = ∫ e^{−α_n y} μ(dy)`. -/
noncomputable def cs_caraM (γ R : ℝ) (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ y, Real.exp (-(cs_caraAlpha γ R n * y)) ∂μ

/-- The coefficient `A_n`: `A_0 = 1`,
`A_{n+1} = (1 + γ/(α_n R)) exp(γ L_n/(γ + α_n R))`, `L_n = log(β A_n M_n α_n R/γ)`. -/
noncomputable def cs_caraA (γ β R : ℝ) (μ : Measure ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 + γ / (cs_caraAlpha γ R n * R)) *
      Real.exp (γ * Real.log (β * cs_caraA γ β R μ n * cs_caraM γ R μ n * cs_caraAlpha γ R n *
        R / γ) / (γ + cs_caraAlpha γ R n * R))

/-- `L_n = log(β A_n M_n α_n R/γ)`. -/
noncomputable def cs_caraL (γ β R : ℝ) (μ : Measure ℝ) (n : ℕ) : ℝ :=
  Real.log (β * cs_caraA γ β R μ n * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ)

/-- The optimal saving with `n + 1` periods to go: `s_{n+1}(x) = (γx + L_n)/(γ + α_n R)`. -/
noncomputable def cs_caraS (γ β R : ℝ) (μ : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (γ * x + cs_caraL γ β R μ n) / (γ + cs_caraAlpha γ R n * R)

/-- `E e^{−αy} > 0` for `μ` concentrated on a bounded interval. -/
theorem cs_cara_M_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {ymin ymax α : ℝ} (hα : 0 < α)
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) : 0 < ∫ y, Real.exp (-(α * y)) ∂μ := by
  have hint : Integrable (fun y => Real.exp (-(α * y))) μ := by
    refine (integrable_const (Real.exp (-(α * ymin)))).mono'
      (by fun_prop : Continuous fun y => Real.exp (-(α * y))).aestronglyMeasurable ?_
    filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [hy.1])
  have hlow : ∫ _, Real.exp (-(α * ymax)) ∂μ ≤ ∫ y, Real.exp (-(α * y)) ∂μ := by
    refine integral_mono_ae (integrable_const _) hint ?_
    filter_upwards [hμ] with y hy
    exact Real.exp_le_exp.2 (by nlinarith [hy.2])
  rw [integral_const, probReal_univ, one_smul] at hlow
  exact lt_of_lt_of_le (Real.exp_pos _) hlow

/-- `∫ −A e^{−α(Rs + y)} μ(dy) = −A M e^{−αRs}` with `M = ∫ e^{−αy} μ(dy)`. -/
theorem cs_cara_integral (μ : Measure ℝ) (A α R s : ℝ) :
    ∫ y, -(A * Real.exp (-(α * (R * s + y)))) ∂μ =
      -(A * ∫ y, Real.exp (-(α * y)) ∂μ) * Real.exp (-(α * R * s)) := by
  have : ∀ y, -(A * Real.exp (-(α * (R * s + y)))) =
      -(A * Real.exp (-(α * R * s))) * Real.exp (-(α * y)) := fun y => by
    rw [show -(α * (R * s + y)) = -(α * R * s) + -(α * y) by ring, Real.exp_add]
    ring
  simp only [this, integral_const_mul]
  ring

/-- **Exercise 6.9** (Schechtman–Escudero 1977; Miao, p. 190). For `γ, β, R > 0` and iid income
concentrated on `[y_min, y_max]`, for every `n`:
* `v_n(x) = −A_n e^{−α_n x}` with `A_n > 0`, `α_n > 0` and `α_n = γ / Σ_{k=0}^n R^{−k}`;
* the objective of `v_{n+1}(x)` has the strict global maximum `s_{n+1}(x) =
  (γx + L_n)/(γ + α_n R)`, the **optimal saving**, and `v_{n+1}(x)` is its value;
* the **optimal consumption** `c_{n+1}(x) = x − s_{n+1}(x)` is
  `(α_n R x − L_n)/(γ + α_n R)`, linear with slope `1/Σ_{k=0}^{n+1} R^{−k}`. -/
theorem ex_6_9 {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 0 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (n : ℕ) :
    (0 < cs_caraAlpha γ R n ∧ 0 < cs_caraA γ β R μ n ∧
      cs_caraAlpha γ R n = γ / ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k ∧
      ∀ x, cs_cara_v γ β R μ n x = -(cs_caraA γ β R μ n * Real.exp (-(cs_caraAlpha γ R n * x)))) ∧
    ∀ x, (∀ s, s ≠ cs_caraS γ β R μ n x →
        -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ <
          -Real.exp (-(γ * (x - cs_caraS γ β R μ n x))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * cs_caraS γ β R μ n x + y) ∂μ) ∧
      cs_cara_v γ β R μ (n + 1) x = -Real.exp (-(γ * (x - cs_caraS γ β R μ n x))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * cs_caraS γ β R μ n x + y) ∂μ ∧
      x - cs_caraS γ β R μ n x =
        (cs_caraAlpha γ R n * R * x - cs_caraL γ β R μ n) / (γ + cs_caraAlpha γ R n * R) ∧
      cs_caraAlpha γ R n * R / (γ + cs_caraAlpha γ R n * R) =
        1 / ∑ k ∈ Finset.range (n + 2), R⁻¹ ^ k := by
  -- the closed form, by induction
  have key : ∀ n, 0 < cs_caraAlpha γ R n ∧ 0 < cs_caraA γ β R μ n ∧
      cs_caraAlpha γ R n = γ / ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k ∧
      ∀ x, cs_cara_v γ β R μ n x =
        -(cs_caraA γ β R μ n * Real.exp (-(cs_caraAlpha γ R n * x))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hγ, one_pos, by simp [cs_caraAlpha], fun x => ?_⟩
      simp only [cs_cara_v, cs_caraA, cs_caraAlpha, one_mul]
    | succ n ih =>
      obtain ⟨hα, hA, hαS, hv⟩ := ih
      set α := cs_caraAlpha γ R n
      set A := cs_caraA γ β R μ n
      have hM := cs_cara_M_pos hα hμ
      set Mn := cs_caraM γ R μ n
      have hK : 0 < β * A * Mn := by positivity
      have hαR : 0 < α * R := mul_pos hα hR
      refine ⟨by simp only [cs_caraAlpha]; positivity, by simp only [cs_caraA]; positivity,
        ?_, fun x => ?_⟩
      · have hS : 0 < ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k :=
          Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 hR) k) Finset.nonempty_range_add_one
        have hsum : ∑ k ∈ Finset.range (n + 1 + 1), R⁻¹ ^ k =
            R⁻¹ * ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k + 1 := by
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp only [pow_succ, pow_zero]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
        change γ * α * R / (γ + α * R) = _
        rw [hsum, hαS]
        field_simp
      · change sSup (Set.range fun s => -Real.exp (-(γ * (x - s))) +
          β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ) = _
        have hobj : ∀ s, -Real.exp (-(γ * (x - s))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ =
            -Real.exp (-(γ * (x - s))) - β * A * Mn * Real.exp (-(α * R * s)) := fun s => by
          have hMn : ∫ y, Real.exp (-(α * y)) ∂μ = Mn := rfl
          simp only [hv, cs_cara_integral, hMn]
          ring
        set s₀ := (γ * x + Real.log (β * A * Mn * α * R / γ)) / (γ + α * R)
        have hs₀ : (γ + α * R) * s₀ = γ * x + Real.log (β * A * Mn * α * R / γ) := by
          simp only [s₀]; field_simp
        obtain ⟨hmax, hval⟩ := cs_cara_step hγ hα hR hK x s₀ hs₀
        have hgreat : IsGreatest (Set.range fun s => -Real.exp (-(γ * (x - s))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ)
            (-Real.exp (-(γ * (x - s₀))) - β * A * Mn * Real.exp (-(α * R * s₀))) := by
          refine ⟨⟨s₀, hobj s₀⟩, ?_⟩
          rintro _ ⟨s, rfl⟩
          dsimp only
          rw [hobj s]
          rcases eq_or_ne s s₀ with h | h
          · rw [h]
          · exact (hmax s h).le
        rw [hgreat.csSup_eq, hval]
        simp only [cs_caraA, cs_caraAlpha]
        rw [neg_mul]
  refine ⟨key n, fun x => ?_⟩
  obtain ⟨hα, hA, hαS, hv⟩ := key n
  set α := cs_caraAlpha γ R n
  set A := cs_caraA γ β R μ n
  have hM := cs_cara_M_pos hα hμ
  set Mn := cs_caraM γ R μ n
  have hK : 0 < β * A * Mn := by positivity
  have hαR : 0 < α * R := mul_pos hα hR
  have hobj : ∀ s, -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ =
      -Real.exp (-(γ * (x - s))) - β * A * Mn * Real.exp (-(α * R * s)) := fun s => by
    have hMn : ∫ y, Real.exp (-(α * y)) ∂μ = Mn := rfl
    simp only [hv, cs_cara_integral, hMn]
    ring
  have hden : 0 < γ + α * R := by positivity
  have hs₀ : (γ + α * R) * cs_caraS γ β R μ n x =
      γ * x + Real.log (β * A * Mn * α * R / γ) := by
    have e1 : cs_caraAlpha γ R n = α := rfl
    have e2 : cs_caraA γ β R μ n = A := rfl
    have e3 : cs_caraM γ R μ n = Mn := rfl
    simp only [cs_caraS, cs_caraL, e1, e2, e3]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hden.ne'
  obtain ⟨hmax, -⟩ := cs_cara_step hγ hα hR hK x _ hs₀
  refine ⟨fun s hs => ?_, ?_, ?_, ?_⟩
  · rw [hobj, hobj]; exact hmax s hs
  · change sSup (Set.range fun s => -Real.exp (-(γ * (x - s))) +
      β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ) = _
    refine IsGreatest.csSup_eq ⟨⟨_, rfl⟩, ?_⟩
    rintro _ ⟨s, rfl⟩
    dsimp only
    rcases eq_or_ne s (cs_caraS γ β R μ n x) with h | h
    · rw [h]
    · rw [hobj, hobj]; exact (hmax s h).le
  · have e1 : cs_caraAlpha γ R n = α := rfl
    simp only [cs_caraS, e1]
    rw [eq_div_iff hden.ne', sub_mul, div_mul_cancel₀ _ hden.ne']
    ring
  · have hS : 0 < ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k :=
      Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 hR) k) Finset.nonempty_range_add_one
    have hsum : ∑ k ∈ Finset.range (n + 2), R⁻¹ ^ k =
        R⁻¹ * ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, pow_zero]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, hαS]
    field_simp

/-! ### Exercise 6.10: Levhari–Mirman–Zilcha (1980) -/

/-- The maximum of a concave function with global maximum `m` over `[a, b]` is attained at the
projection `max(a, min(b, m))` of `m` onto `[a, b]`. -/
theorem cs_clamp {f : ℝ → ℝ} (hf : ConcaveOn ℝ Set.univ f) {m a b : ℝ} (hab : a ≤ b)
    (hm : ∀ s, f s ≤ f m) : ∀ s ∈ Set.Icc a b, f s ≤ f (max a (min b m)) := by
  intro s hs
  rcases le_total m a with hma | hma
  · rw [max_eq_left ((min_le_right b m).trans hma)]
    have := hf.ge_on_segment (Set.mem_univ m) (Set.mem_univ s)
      (by rw [segment_eq_Icc (hma.trans hs.1)]; exact ⟨hma, hs.1⟩)
    rwa [min_eq_right (hm s)] at this
  · rcases le_total m b with hmb | hmb
    · rw [min_eq_right hmb, max_eq_right hma]
      exact hm s
    · rw [min_eq_left hmb, max_eq_right hab]
      have := hf.ge_on_segment (Set.mem_univ s) (Set.mem_univ m)
        (by rw [segment_eq_Icc (hs.2.trans hmb)]; exact ⟨hs.2, hmb⟩)
      rwa [min_eq_left (hm s)] at this

/-- **Exercise 6.10: the model** (Miao, p. 191): §6.6.2 with `u(c) = −e^{−γc}` and `b = 0`
satisfies the standing hypotheses when `γ, β, R > 0` and `y_min > 0`. -/
theorem cs_cara_basic {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}
    [IsProbabilityMeasure μ] (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin) :
    (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).Basic where
  β_pos := hβ
  u_cont := (by fun_prop : Continuous fun c : ℝ => -Real.exp (-(γ * c))).continuousOn
  u_mono := fun c _ c' _ h => by
    change -Real.exp (-(γ * c)) < -Real.exp (-(γ * c'))
    have := Real.exp_lt_exp.2 (by nlinarith : -(γ * c') < -(γ * c))
    linarith
  u_conc := by
    refine ⟨convex_Ici 0, fun c₁ _ c₂ _ hne θ η hθ hη hs => ?_⟩
    have hne' : -(γ * c₁) ≠ -(γ * c₂) := fun h => hne (by
      have := mul_left_cancel₀ hγ.ne' (neg_inj.1 h); exact this)
    have := strictConvexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hne' hθ hη hs
    change θ • -Real.exp (-(γ * c₁)) + η • -Real.exp (-(γ * c₂)) <
      -Real.exp (-(γ * (θ • c₁ + η • c₂)))
    simp only [smul_eq_mul] at this ⊢
    rw [show θ * -(γ * c₁) + η * -(γ * c₂) = -(γ * (θ * c₁ + η * c₂)) by ring] at this
    linarith
  ρ_cont := continuous_const
  ρ_pos := fun _ => hR
  w_cont := continuous_subtype_val.sub continuous_const
  w_pos := fun y => by
    change 0 < y.1 - (R - 1) * 0
    linarith [y.2.1]
  feller := CSModel.isFeller_const μ

/-- **Exercise 6.10** (Levhari–Mirman–Zilcha 1980; Miao, p. 191): with `c ≥ 0`, `a_{t+1} ≥ 0` and
CARA utility, for every `n` and current shock `z`: `v_n` is strictly increasing and strictly
concave on `[0, ∞)`; the optimal saving `s_{n+1}` is the unique maximizer and continuous; `s_n`
and `g_n` are increasing in `x`; and there are **thresholds**: the sets where the saving
constraint binds (`s_n(x) = 0`) and where consumption is zero (`g_n(x) = 0`) are initial
segments of `[0, ∞)`. -/
theorem ex_6_10 {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin) (n : ℕ) (z : Set.Icc ymin ymax) :
    StrictMonoOn (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v n x z)
        (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0)
        (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v n x z) ∧
      (∀ x, 0 ≤ x → ∀ s ∈ Set.Icc 0 x,
        ((bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).obj n x z s =
            (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v (n + 1) x z →
          s = (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav (n + 1) x z)) ∧
      ContinuousOn (fun p : ℝ × Set.Icc ymin ymax =>
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n p.1 p.2)
        (Set.Ici 0 ×ˢ Set.univ) ∧
      MonotoneOn (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x z)
        (Set.Ici 0) ∧
      MonotoneOn
        (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x z)
        (Set.Ici 0) ∧
      (∀ x x', 0 ≤ x' → x' ≤ x →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x z = 0 →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x' z = 0) ∧
      ∀ x x', 0 ≤ x' → x' ≤ x →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x z = 0 →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x' z = 0 := by
  have := bookModel_isMarkovKernel (u := fun c => -Real.exp (-(γ * c))) (β := β) (R := R) (b := 0)
    (μ := μ)
  have h := cs_cara_basic (μ := μ) hγ hβ hR hy
  set M := bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    fun x _ s hs hv => CSModel.sav_unique h n hs hv, CSModel.continuousOn_sav h n,
    CSModel.monotoneOn_sav h n z, CSModel.monotoneOn_cons h n z,
    fun x x' hx' hxx' h0 => ?_, fun x x' hx' hxx' h0 => ?_⟩
  · have h1 := CSModel.monotoneOn_sav h n z (Set.mem_Ici.2 hx') (Set.mem_Ici.2 (hx'.trans hxx'))
      hxx'
    have h2 := (CSModel.sav_mem' h n hx' z).1
    simp only at h1
    linarith
  · have h1 := CSModel.monotoneOn_cons h n z (Set.mem_Ici.2 hx') (Set.mem_Ici.2 (hx'.trans hxx'))
      hxx'
    have h2 := (CSModel.sav_mem' h n hx' z).2
    simp only [CSModel.cons] at h1 h0 ⊢
    linarith

/-- **Exercise 6.10 with one period to go** (Miao, p. 191): the optimal saving is the
Exercise 6.9 saving clamped to the feasible set,
`s_1(x) = max(0, min(x, (γx + L)/(γ + γR)))`, `L = log(β M γ R/γ)` with `M = E e^{−γy}`. The
saving constraint binds (`s_1 = 0`) where `γx + L ≤ 0`, and consumption is zero (`s_1 = x`)
where `(γx + L)/(γ + γR) ≥ x`. -/
theorem ex_6_10_one {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}
    [IsProbabilityMeasure μ] (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin)
    (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 ≤ x) :
    (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav 1 x z =
      max 0 (min x ((γ * x + Real.log (β * (∫ y, Real.exp (-(γ * y.1)) ∂μ) * γ * R / γ)) /
        (γ + γ * R))) := by
  have := bookModel_isMarkovKernel (u := fun c => -Real.exp (-(γ * c))) (β := β) (R := R) (b := 0)
    (μ := μ)
  have h := cs_cara_basic (μ := μ) hγ hβ hR hy
  set M := bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ
  set M₀ := ∫ y, Real.exp (-(γ * y.1)) ∂μ
  have hM₀ : 0 < M₀ := by
    have hc : Continuous fun y : Set.Icc ymin ymax => Real.exp (-(γ * y.1)) := by fun_prop
    have hint : Integrable (fun y : Set.Icc ymin ymax => Real.exp (-(γ * y.1))) μ :=
      integrable_of_abs_le hc.measurable fun y => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (by nlinarith [y.2.1] : -(γ * y.1) ≤ -(γ * ymin))
    have hlow : ∫ _, Real.exp (-(γ * ymax)) ∂μ ≤ M₀ :=
      integral_mono (integrable_const _) hint fun y =>
        Real.exp_le_exp.2 (by nlinarith [y.2.2] : -(γ * ymax) ≤ -(γ * y.1))
    rw [integral_const, probReal_univ, one_smul] at hlow
    exact lt_of_lt_of_le (Real.exp_pos _) hlow
  set K := β * M₀
  have hK : 0 < K := mul_pos hβ hM₀
  set g : ℝ → ℝ := fun s => -Real.exp (-(γ * (x - s))) - K * Real.exp (-(γ * R * s)) with hg
  set s₀ := (γ * x + Real.log (K * γ * R / γ)) / (γ + γ * R)
  have hden : 0 < γ + γ * R := by positivity
  have hs₀ : (γ + γ * R) * s₀ = γ * x + Real.log (K * γ * R / γ) := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  obtain ⟨hmax, -⟩ := cs_cara_step hγ hγ hR hK x s₀ hs₀
  have hgm : ∀ s, g s ≤ g s₀ := fun s => by
    rcases eq_or_ne s s₀ with e | e
    · rw [e]
    · exact (hmax s e).le
  -- `g` is concave
  have hconc : ConcaveOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun s₁ _ s₂ _ θ η hθ hη hs => ?_⟩
    have h1 := convexOn_exp.2 (Set.mem_univ (-(γ * (x - s₁)))) (Set.mem_univ (-(γ * (x - s₂))))
      hθ hη hs
    have h2 := convexOn_exp.2 (Set.mem_univ (-(γ * R * s₁))) (Set.mem_univ (-(γ * R * s₂)))
      hθ hη hs
    simp only [smul_eq_mul, hg] at h1 h2 ⊢
    rw [show θ * -(γ * (x - s₁)) + η * -(γ * (x - s₂)) = -(γ * (x - (θ * s₁ + η * s₂))) by
      linear_combination (-(γ * x)) * hs] at h1
    rw [show θ * -(γ * R * s₁) + η * -(γ * R * s₂) = -(γ * R * (θ * s₁ + η * s₂)) by ring] at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 hK.le]
  -- the objective on `[0, x]` is `g`
  have hobj : ∀ s ∈ Set.Icc 0 x, M.obj 0 x z s = g s := by
    intro s hs
    rw [M.obj_eq 0 z hs.2]
    change -Real.exp (-(γ * (x - s))) + β * ∫ y, -Real.exp (-(γ * (R * s + (y.1 - (R - 1) * 0))))
      ∂μ = _
    have : ∀ y : Set.Icc ymin ymax, -Real.exp (-(γ * (R * s + (y.1 - (R - 1) * 0)))) =
        -Real.exp (-(γ * R * s)) * Real.exp (-(γ * y.1)) := fun y => by
      rw [show -(γ * (R * s + (y.1 - (R - 1) * 0))) = -(γ * R * s) + -(γ * y.1) by ring,
        Real.exp_add]
      ring
    simp only [this, integral_const_mul, hg, K, M₀]
    ring
  set p := max 0 (min x s₀)
  have hp : p ∈ Set.Icc 0 x := ⟨le_max_left _ _, max_le hx (min_le_left _ _)⟩
  have hcl := cs_clamp hconc hx hgm
  obtain ⟨hm, hv⟩ := CSModel.sav_mem h 0 hx z
  have hpv : M.obj 0 x z p = M.v 1 x z := by
    refine le_antisymm (CSModel.obj_le h 0 hp) ?_
    rw [← hv, hobj _ hm, hobj _ hp]
    exact hcl _ hm
  rw [← CSModel.sav_unique h 0 hp hpv]

end Miao.FiniteHorizonDP

set_option linter.style.longLine false
#print axioms Miao.FiniteHorizonDP.measurable_cons
#print axioms Miao.FiniteHorizonDP.measurable_snoc
#print axioms Miao.FiniteHorizonDP.measurable_init
#print axioms Miao.FiniteHorizonDP.lastState
#print axioms Miao.FiniteHorizonDP.measurable_lastState
#print axioms Miao.FiniteHorizonDP.lastState_cons
#print axioms Miao.FiniteHorizonDP.lastState_snoc
#print axioms Miao.FiniteHorizonDP.MDP
#print axioms Miao.FiniteHorizonDP.MDP.mk
#print axioms Miao.FiniteHorizonDP.MDP.Γ
#print axioms Miao.FiniteHorizonDP.MDP.P
#print axioms Miao.FiniteHorizonDP.MDP.u
#print axioms Miao.FiniteHorizonDP.MDP.uT
#print axioms Miao.FiniteHorizonDP.MDP.β
#print axioms Miao.FiniteHorizonDP.MDP.NonemptyValued
#print axioms Miao.FiniteHorizonDP.MDP.IsMarkov
#print axioms Miao.FiniteHorizonDP.MDP.IsStationary
#print axioms Miao.FiniteHorizonDP.Plan
#print axioms Miao.FiniteHorizonDP.IsPlan
#print axioms Miao.FiniteHorizonDP.IsMarkovian
#print axioms Miao.FiniteHorizonDP.IsStationaryPlan
#print axioms Miao.FiniteHorizonDP.IsFeasible
#print axioms Miao.FiniteHorizonDP.feasiblePlans
#print axioms Miao.FiniteHorizonDP.HasMeasurableSelection
#print axioms Miao.FiniteHorizonDP.selectionPlan
#print axioms Miao.FiniteHorizonDP.selectionPlan_isPlan
#print axioms Miao.FiniteHorizonDP.selectionPlan_markov
#print axioms Miao.FiniteHorizonDP.IsStationaryPlan.isMarkovian
#print axioms Miao.FiniteHorizonDP.lemma_5_1_1
#print axioms Miao.FiniteHorizonDP.selection_of_feasible
#print axioms Miao.FiniteHorizonDP.lemma_5_1_1_iff
#print axioms Miao.FiniteHorizonDP.no_selection_example
#print axioms Miao.FiniteHorizonDP.detKernel
#print axioms Miao.FiniteHorizonDP.detKernel_apply
#print axioms Miao.FiniteHorizonDP.stepKernel
#print axioms Miao.FiniteHorizonDP.mu
#print axioms Miao.FiniteHorizonDP.stepKernel_apply
#print axioms Miao.FiniteHorizonDP.isMarkovKernel_stepKernel
#print axioms Miao.FiniteHorizonDP.isSFiniteKernel_stepKernel
#print axioms Miao.FiniteHorizonDP.sFinite_mu
#print axioms Miao.FiniteHorizonDP.isProbabilityMeasure_mu
#print axioms Miao.FiniteHorizonDP.mu_zero
#print axioms Miao.FiniteHorizonDP.integral_mu_zero
#print axioms Miao.FiniteHorizonDP.mu_succ_lintegral
#print axioms Miao.FiniteHorizonDP.eq_5_2
#print axioms Miao.FiniteHorizonDP.integral_mu_succ
#print axioms Miao.FiniteHorizonDP.mu_congr
#print axioms Miao.FiniteHorizonDP.mu_eq_of_stepKernel
#print axioms Miao.FiniteHorizonDP.rew
#print axioms Miao.FiniteHorizonDP.expRew
#print axioms Miao.FiniteHorizonDP.J0T
#print axioms Miao.FiniteHorizonDP.partialSum
#print axioms Miao.FiniteHorizonDP.J
#print axioms Miao.FiniteHorizonDP.Assumption512
#print axioms Miao.FiniteHorizonDP.Assumption513
#print axioms Miao.FiniteHorizonDP.Assumption514
#print axioms Miao.FiniteHorizonDP.measurable_rew
#print axioms Miao.FiniteHorizonDP.expRew_zero
#print axioms Miao.FiniteHorizonDP.eq_5_3
#print axioms Miao.FiniteHorizonDP.partialSum_eq
#print axioms Miao.FiniteHorizonDP.eq_5_4
#print axioms Miao.FiniteHorizonDP.J_spec
#print axioms Miao.FiniteHorizonDP.J_welldefined
#print axioms Miao.FiniteHorizonDP.BoundedRewards
#print axioms Miao.FiniteHorizonDP.integrable_of_bounded
#print axioms Miao.FiniteHorizonDP.plan_lt
#print axioms Miao.FiniteHorizonDP.assumption_5_1_3_of_bounded
#print axioms Miao.FiniteHorizonDP.abs_expRew_le
#print axioms Miao.FiniteHorizonDP.tendsto_partialSum_of_bounded
#print axioms Miao.FiniteHorizonDP.assumption_5_1_4_of_bounded
#print axioms Miao.FiniteHorizonDP.assumption_5_1_4_of_boundedOn
#print axioms Miao.FiniteHorizonDP.abs_J_le
#print axioms Miao.FiniteHorizonDP.geom_partial_tendsto
#print axioms Miao.FiniteHorizonDP.tendsto_partialSum_of_bddAbove
#print axioms Miao.FiniteHorizonDP.tendsto_partialSum_of_bddBelow
#print axioms Miao.FiniteHorizonDP.V0
#print axioms Miao.FiniteHorizonDP.V
#print axioms Miao.FiniteHorizonDP.IsValueOf
#print axioms Miao.FiniteHorizonDP.isValueOf_iff
#print axioms Miao.FiniteHorizonDP.V0_char
#print axioms Miao.FiniteHorizonDP.V_char
#print axioms Miao.FiniteHorizonDP.IsOptimalPlan0
#print axioms Miao.FiniteHorizonDP.IsOptimalPlan
#print axioms Miao.FiniteHorizonDP.IsOptimalPlan0.isGreatest
#print axioms Miao.FiniteHorizonDP.liftHist
#print axioms Miao.FiniteHorizonDP.liftHist_snoc
#print axioms Miao.FiniteHorizonDP.measurable_liftHist
#print axioms Miao.FiniteHorizonDP.mu_simulation
#print axioms Miao.FiniteHorizonDP.expRew_simulation
#print axioms Miao.FiniteHorizonDP.chainMDP
#print axioms Miao.FiniteHorizonDP.chainHist
#print axioms Miao.FiniteHorizonDP.chainMDP_isMarkov
#print axioms Miao.FiniteHorizonDP.isProbabilityMeasure_chainHist
#print axioms Miao.FiniteHorizonDP.chainHist_succ_lintegral
#print axioms Miao.FiniteHorizonDP.mu_markovian
#print axioms Miao.FiniteHorizonDP.famKernel
#print axioms Miao.FiniteHorizonDP.famKernel_apply
#print axioms Miao.FiniteHorizonDP.isMarkovKernel_famKernel
#print axioms Miao.FiniteHorizonDP.pushKernel
#print axioms Miao.FiniteHorizonDP.pushKernel_apply
#print axioms Miao.FiniteHorizonDP.isMarkovKernel_pushKernel
#print axioms Miao.FiniteHorizonDP.StoppingProblem
#print axioms Miao.FiniteHorizonDP.StoppingProblem.mk
#print axioms Miao.FiniteHorizonDP.StoppingProblem.Q
#print axioms Miao.FiniteHorizonDP.StoppingProblem.f
#print axioms Miao.FiniteHorizonDP.StoppingProblem.g
#print axioms Miao.FiniteHorizonDP.StoppingProblem.h
#print axioms Miao.FiniteHorizonDP.StoppingProblem.β
#print axioms Miao.FiniteHorizonDP.sHat
#print axioms Miao.FiniteHorizonDP.contKernel
#print axioms Miao.FiniteHorizonDP.contKernel_inl
#print axioms Miao.FiniteHorizonDP.contKernel_inr
#print axioms Miao.FiniteHorizonDP.stopKernel
#print axioms Miao.FiniteHorizonDP.StoppingProblem.toMDP
#print axioms Miao.FiniteHorizonDP.bookΓ
#print axioms Miao.FiniteHorizonDP.bookΓ_infeasible
#print axioms Miao.FiniteHorizonDP.stopRule
#print axioms Miao.FiniteHorizonDP.aliveSet
#print axioms Miao.FiniteHorizonDP.measurableSet_aliveSet
#print axioms Miao.FiniteHorizonDP.stopRew
#print axioms Miao.FiniteHorizonDP.stopTerm
#print axioms Miao.FiniteHorizonDP.stopValue
#print axioms Miao.FiniteHorizonDP.stopValueInf
#print axioms Miao.FiniteHorizonDP.stopV
#print axioms Miao.FiniteHorizonDP.stopVInf
#print axioms Miao.FiniteHorizonDP.stopStep
#print axioms Miao.FiniteHorizonDP.stopLift
#print axioms Miao.FiniteHorizonDP.inducedRule
#print axioms Miao.FiniteHorizonDP.measurable_stopStep
#print axioms Miao.FiniteHorizonDP.lastState_stopLift
#print axioms Miao.FiniteHorizonDP.isMarkovKernel_contKernel
#print axioms Miao.FiniteHorizonDP.toMDP_isMarkov
#print axioms Miao.FiniteHorizonDP.measurable_toMDP_u
#print axioms Miao.FiniteHorizonDP.measurable_toMDP_uT
#print axioms Miao.FiniteHorizonDP.stopStep_eq
#print axioms Miao.FiniteHorizonDP.stop_hstep
#print axioms Miao.FiniteHorizonDP.rew_stopLift
#print axioms Miao.FiniteHorizonDP.term_stopLift
#print axioms Miao.FiniteHorizonDP.expRew_toMDP
#print axioms Miao.FiniteHorizonDP.J0T_toMDP
#print axioms Miao.FiniteHorizonDP.J_toMDP
#print axioms Miao.FiniteHorizonDP.measurable_inducedRule
#print axioms Miao.FiniteHorizonDP.zOf
#print axioms Miao.FiniteHorizonDP.measurable_zOf
#print axioms Miao.FiniteHorizonDP.toPlan
#print axioms Miao.FiniteHorizonDP.lastState_comp_inl
#print axioms Miao.FiniteHorizonDP.stopLift_of_alive
#print axioms Miao.FiniteHorizonDP.aliveSet_toPlan
#print axioms Miao.FiniteHorizonDP.stopValue_toPlan
#print axioms Miao.FiniteHorizonDP.stopValueInf_toPlan
#print axioms Miao.FiniteHorizonDP.isPlan_toPlan
#print axioms Miao.FiniteHorizonDP.inducedRule_mem
#print axioms Miao.FiniteHorizonDP.V0_toMDP
#print axioms Miao.FiniteHorizonDP.V_toMDP
#print axioms Miao.FiniteHorizonDP.StoppingProblem.Bounded
#print axioms Miao.FiniteHorizonDP.StoppingProblem.IsStationary
#print axioms Miao.FiniteHorizonDP.toMDP_assumptions
#print axioms Miao.FiniteHorizonDP.optionExercise
#print axioms Miao.FiniteHorizonDP.eq_5_7_5_8
#print axioms Miao.FiniteHorizonDP.optionExercise_assumptions
#print axioms Miao.FiniteHorizonDP.americanCall_beta
#print axioms Miao.FiniteHorizonDP.exitProblem
#print axioms Miao.FiniteHorizonDP.eq_5_9_5_10
#print axioms Miao.FiniteHorizonDP.exitProblem_assumptions
#print axioms Miao.FiniteHorizonDP.bern
#print axioms Miao.FiniteHorizonDP.isProbabilityMeasure_bern
#print axioms Miao.FiniteHorizonDP.bern_one
#print axioms Miao.FiniteHorizonDP.secretary
#print axioms Miao.FiniteHorizonDP.secretary_Q
#print axioms Miao.FiniteHorizonDP.secretary_assumptions
#print axioms Miao.FiniteHorizonDP.jobSearch
#print axioms Miao.FiniteHorizonDP.ex_5_1_accept
#print axioms Miao.FiniteHorizonDP.ex_5_1
#print axioms Miao.FiniteHorizonDP.americanPut
#print axioms Miao.FiniteHorizonDP.ex_5_2
#print axioms Miao.FiniteHorizonDP.rank3
#print axioms Miao.FiniteHorizonDP.isProbabilityMeasure_rank3
#print axioms Miao.FiniteHorizonDP.secretaryTwo
#print axioms Miao.FiniteHorizonDP.ex_5_3
#print axioms Miao.FiniteHorizonDP.card_mul_of_equal_partition
#print axioms Miao.FiniteHorizonDP.bestOfFirst
#print axioms Miao.FiniteHorizonDP.bestOfAll
#print axioms Miao.FiniteHorizonDP.card_bestOfAll
#print axioms Miao.FiniteHorizonDP.swap_val_le
#print axioms Miao.FiniteHorizonDP.card_bestOfFirst
#print axioms Miao.FiniteHorizonDP.bestOfAll_subset
#print axioms Miao.FiniteHorizonDP.secretary_prob
#print axioms Miao.FiniteHorizonDP.po_shift
#print axioms Miao.FiniteHorizonDP.po_shift_zero
#print axioms Miao.FiniteHorizonDP.po_shift_shift
#print axioms Miao.FiniteHorizonDP.po_shift_isMarkov
#print axioms Miao.FiniteHorizonDP.po_cont
#print axioms Miao.FiniteHorizonDP.po_glue
#print axioms Miao.FiniteHorizonDP.po_cont_glue
#print axioms Miao.FiniteHorizonDP.po_JointMeas
#print axioms Miao.FiniteHorizonDP.po_measurable_tail
#print axioms Miao.FiniteHorizonDP.po_measurable_lastState_prod
#print axioms Miao.FiniteHorizonDP.po_cast_lt
#print axioms Miao.FiniteHorizonDP.po_cont_feasible
#print axioms Miao.FiniteHorizonDP.po_glue_feasible
#print axioms Miao.FiniteHorizonDP.po_measurable_lintegral_family
#print axioms Miao.FiniteHorizonDP.po_mu_succ_lintegral
#print axioms Miao.FiniteHorizonDP.po_contKernel
#print axioms Miao.FiniteHorizonDP.po_contKernel_apply
#print axioms Miao.FiniteHorizonDP.po_isMarkovKernel_contKernel
#print axioms Miao.FiniteHorizonDP.po_mu_succ_eq
#print axioms Miao.FiniteHorizonDP.po_integral_mu_succ
#print axioms Miao.FiniteHorizonDP.po_integrable_cont
#print axioms Miao.FiniteHorizonDP.po_ae_mu_succ
#print axioms Miao.FiniteHorizonDP.po_IntPlan
#print axioms Miao.FiniteHorizonDP.po_intPlan_of_assumption513
#print axioms Miao.FiniteHorizonDP.po_rew_cons
#print axioms Miao.FiniteHorizonDP.po_plan_meas
#print axioms Miao.FiniteHorizonDP.po_integrable_J0T_cont
#print axioms Miao.FiniteHorizonDP.po_ae_IntPlan_cont
#print axioms Miao.FiniteHorizonDP.po_J0T_succ
#print axioms Miao.FiniteHorizonDP.po_plansFrom
#print axioms Miao.FiniteHorizonDP.po_muFrom
#print axioms Miao.FiniteHorizonDP.eq_6_12
#print axioms Miao.FiniteHorizonDP.po_JFrom
#print axioms Miao.FiniteHorizonDP.eq_6_13
#print axioms Miao.FiniteHorizonDP.po_J0T_zero
#print axioms Miao.FiniteHorizonDP.eq_6_13_terminal
#print axioms Miao.FiniteHorizonDP.po_VFrom
#print axioms Miao.FiniteHorizonDP.eq_6_14
#print axioms Miao.FiniteHorizonDP.po_VFrom_zero
#print axioms Miao.FiniteHorizonDP.po_feasible_zero
#print axioms Miao.FiniteHorizonDP.po_V0_zero
#print axioms Miao.FiniteHorizonDP.po_VFrom_terminal
#print axioms Miao.FiniteHorizonDP.po_cont_mem_plansFrom
#print axioms Miao.FiniteHorizonDP.po_J_le_V0
#print axioms Miao.FiniteHorizonDP.po_coe_le_of_forall_sub
#print axioms Miao.FiniteHorizonDP.po_Assumption513
#print axioms Miao.FiniteHorizonDP.po_assumption513_of_bounded
#print axioms Miao.FiniteHorizonDP.po_shift_u0
#print axioms Miao.FiniteHorizonDP.po_shift_P0
#print axioms Miao.FiniteHorizonDP.lemma_6_3_1
#print axioms Miao.FiniteHorizonDP.Assumption631
#print axioms Miao.FiniteHorizonDP.po_bellman_step
#print axioms Miao.FiniteHorizonDP.theorem_6_3_1
#print axioms Miao.FiniteHorizonDP.po_bellmanVal
#print axioms Miao.FiniteHorizonDP.po_G
#print axioms Miao.FiniteHorizonDP.po_SolvesAt
#print axioms Miao.FiniteHorizonDP.po_bellmanVal_le
#print axioms Miao.FiniteHorizonDP.po_solvesAt_of_max
#print axioms Miao.FiniteHorizonDP.po_genPlan
#print axioms Miao.FiniteHorizonDP.po_cont_genPlan
#print axioms Miao.FiniteHorizonDP.po_genPlan_markov
#print axioms Miao.FiniteHorizonDP.po_genPlan_feasible
#print axioms Miao.FiniteHorizonDP.po_genFrom
#print axioms Miao.FiniteHorizonDP.po_genPlan_restrict
#print axioms Miao.FiniteHorizonDP.po_verification_core
#print axioms Miao.FiniteHorizonDP.po_policy_value
#print axioms Miao.FiniteHorizonDP.po_verification_intPlans
#print axioms Miao.FiniteHorizonDP.theorem_6_3_2
#print axioms Miao.FiniteHorizonDP.po_measurableSet_G
#print axioms Miao.FiniteHorizonDP.po_converse_core
#print axioms Miao.FiniteHorizonDP.theorem_6_3_3
#print axioms Miao.FiniteHorizonDP.po_cexModel
#print axioms Miao.FiniteHorizonDP.po_cexW
#print axioms Miao.FiniteHorizonDP.po_cexPlan
#print axioms Miao.FiniteHorizonDP.po_cex_markov
#print axioms Miao.FiniteHorizonDP.po_cex_bellmanVal
#print axioms Miao.FiniteHorizonDP.po_cex_solves
#print axioms Miao.FiniteHorizonDP.po_cex_assumption
#print axioms Miao.FiniteHorizonDP.po_cex_values
#print axioms Miao.FiniteHorizonDP.theorem_6_3_3_counterexample
#print axioms Miao.FiniteHorizonDP.po_Det
#print axioms Miao.FiniteHorizonDP.po_Det.mk
#print axioms Miao.FiniteHorizonDP.po_Det.Γ
#print axioms Miao.FiniteHorizonDP.po_Det.f
#print axioms Miao.FiniteHorizonDP.po_Det.u
#print axioms Miao.FiniteHorizonDP.po_Det.uT
#print axioms Miao.FiniteHorizonDP.po_Det.β
#print axioms Miao.FiniteHorizonDP.po_detShift
#print axioms Miao.FiniteHorizonDP.po_detShift_shift
#print axioms Miao.FiniteHorizonDP.po_traj
#print axioms Miao.FiniteHorizonDP.po_detFeasible
#print axioms Miao.FiniteHorizonDP.po_detJ
#print axioms Miao.FiniteHorizonDP.po_detV
#print axioms Miao.FiniteHorizonDP.po_detVt
#print axioms Miao.FiniteHorizonDP.po_seqCons
#print axioms Miao.FiniteHorizonDP.po_traj_succ
#print axioms Miao.FiniteHorizonDP.po_traj_shift
#print axioms Miao.FiniteHorizonDP.po_detFeasible_succ
#print axioms Miao.FiniteHorizonDP.po_detJ_succ
#print axioms Miao.FiniteHorizonDP.po_detJ_le_V
#print axioms Miao.FiniteHorizonDP.po_detJ_zero
#print axioms Miao.FiniteHorizonDP.po_detV_zero
#print axioms Miao.FiniteHorizonDP.po_det_bellman_step
#print axioms Miao.FiniteHorizonDP.ex_6_1_theorem_6_3_1
#print axioms Miao.FiniteHorizonDP.po_genTraj
#print axioms Miao.FiniteHorizonDP.po_genSeq
#print axioms Miao.FiniteHorizonDP.po_traj_genSeq
#print axioms Miao.FiniteHorizonDP.po_genTraj_succ
#print axioms Miao.FiniteHorizonDP.po_genSeq_tail
#print axioms Miao.FiniteHorizonDP.po_det_verification_core
#print axioms Miao.FiniteHorizonDP.ex_6_1_theorem_6_3_2
#print axioms Miao.FiniteHorizonDP.po_detG
#print axioms Miao.FiniteHorizonDP.po_det_converse_core
#print axioms Miao.FiniteHorizonDP.ex_6_1_theorem_6_3_3
#print axioms Miao.FiniteHorizonDP.po61_theta
#print axioms Miao.FiniteHorizonDP.po61_coef
#print axioms Miao.FiniteHorizonDP.po61_b
#print axioms Miao.FiniteHorizonDP.po61_A
#print axioms Miao.FiniteHorizonDP.po61_V
#print axioms Miao.FiniteHorizonDP.po61_A_terminal
#print axioms Miao.FiniteHorizonDP.po61_A_succ
#print axioms Miao.FiniteHorizonDP.po61_Params
#print axioms Miao.FiniteHorizonDP.po61_Params.mk
#print axioms Miao.FiniteHorizonDP.po61_Params.α_pos
#print axioms Miao.FiniteHorizonDP.po61_Params.α_lt
#print axioms Miao.FiniteHorizonDP.po61_Params.β_pos
#print axioms Miao.FiniteHorizonDP.po61_Params.β_lt
#print axioms Miao.FiniteHorizonDP.po61_Params.p_pos
#print axioms Miao.FiniteHorizonDP.po61_Params.p_lt
#print axioms Miao.FiniteHorizonDP.po61_pow_lt
#print axioms Miao.FiniteHorizonDP.po61_den_pos
#print axioms Miao.FiniteHorizonDP.po61_coef_pos
#print axioms Miao.FiniteHorizonDP.po61_theta_zero
#print axioms Miao.FiniteHorizonDP.po61_one_sub_frac
#print axioms Miao.FiniteHorizonDP.po61_one_add_frac
#print axioms Miao.FiniteHorizonDP.po61_one_sub_theta
#print axioms Miao.FiniteHorizonDP.po61_beta_coef
#print axioms Miao.FiniteHorizonDP.po61_one_add_c
#print axioms Miao.FiniteHorizonDP.po61_theta_succ
#print axioms Miao.FiniteHorizonDP.po61_theta_pos
#print axioms Miao.FiniteHorizonDP.po61_theta_lt_one
#print axioms Miao.FiniteHorizonDP.po61_coef_succ
#print axioms Miao.FiniteHorizonDP.po61_b_succ
#print axioms Miao.FiniteHorizonDP.po61_max
#print axioms Miao.FiniteHorizonDP.po61_Pos
#print axioms Miao.FiniteHorizonDP.po61_model
#print axioms Miao.FiniteHorizonDP.po61_policy_pos
#print axioms Miao.FiniteHorizonDP.po61_g
#print axioms Miao.FiniteHorizonDP.po61_bellman
#print axioms Miao.FiniteHorizonDP.po61_model_bellman
#print axioms Miao.FiniteHorizonDP.eq_6_5_6_6
#print axioms Miao.FiniteHorizonDP.eq_6_4
#print axioms Miao.FiniteHorizonDP.po61_path
#print axioms Miao.FiniteHorizonDP.po61_theta_euler
#print axioms Miao.FiniteHorizonDP.po61_theta_back
#print axioms Miao.FiniteHorizonDP.eq_6_3
#print axioms Miao.FiniteHorizonDP.eq_6_3_unique
#print axioms Miao.FiniteHorizonDP.eq_6_7
#print axioms Miao.FiniteHorizonDP.eq_6_8
#print axioms Miao.FiniteHorizonDP.eq_6_8_misprint
#print axioms Miao.FiniteHorizonDP.time_consistency_6_1
#print axioms Miao.FiniteHorizonDP.po_V1star
#print axioms Miao.FiniteHorizonDP.po_V0star
#print axioms Miao.FiniteHorizonDP.po_V0
#print axioms Miao.FiniteHorizonDP.po_V1star_le
#print axioms Miao.FiniteHorizonDP.po_le_V1star
#print axioms Miao.FiniteHorizonDP.po_abs_V1star_le
#print axioms Miao.FiniteHorizonDP.po_integrable_bdd
#print axioms Miao.FiniteHorizonDP.po_abs_integral_le
#print axioms Miao.FiniteHorizonDP.two_step_6_2_step1
#print axioms Miao.FiniteHorizonDP.two_step_6_2
#print axioms Miao.FiniteHorizonDP.proj_identity_6_2
#print axioms Miao.FiniteHorizonDP.proj_identity_6_2_misprint
#print axioms Miao.FiniteHorizonDP.blackwell_6_2
#print axioms Miao.FiniteHorizonDP.po62_E
#print axioms Miao.FiniteHorizonDP.po62_V
#print axioms Miao.FiniteHorizonDP.po62_E_bounded
#print axioms Miao.FiniteHorizonDP.po62_integrable_E
#print axioms Miao.FiniteHorizonDP.ex_6_2
#print axioms Miao.FiniteHorizonDP.ex_6_2_terminal
#print axioms Miao.FiniteHorizonDP.ex_6_2_policies
#print axioms Miao.FiniteHorizonDP.po62_kernel
#print axioms Miao.FiniteHorizonDP.po62_kernel_apply
#print axioms Miao.FiniteHorizonDP.po62_kernel_markov
#print axioms Miao.FiniteHorizonDP.po62_model
#print axioms Miao.FiniteHorizonDP.po62_policy_pos
#print axioms Miao.FiniteHorizonDP.po62_g
#print axioms Miao.FiniteHorizonDP.po62_D
#print axioms Miao.FiniteHorizonDP.po62_measurable_ζ
#print axioms Miao.FiniteHorizonDP.po62_measurable_g
#print axioms Miao.FiniteHorizonDP.po62_ae_bound
#print axioms Miao.FiniteHorizonDP.po62_intPlan
#print axioms Miao.FiniteHorizonDP.ex_6_2_optimal
#print axioms Miao.FiniteHorizonDP.sec_val
#print axioms Miao.FiniteHorizonDP.sec_V
#print axioms Miao.FiniteHorizonDP.sec_C
#print axioms Miao.FiniteHorizonDP.sec_V_terminal
#print axioms Miao.FiniteHorizonDP.sec_bellman
#print axioms Miao.FiniteHorizonDP.sec_V_nonneg
#print axioms Miao.FiniteHorizonDP.sec_C_nonneg
#print axioms Miao.FiniteHorizonDP.eq_6_41_6_42
#print axioms Miao.FiniteHorizonDP.eq_6_42_terminal
#print axioms Miao.FiniteHorizonDP.sec_V1_ge_V0
#print axioms Miao.FiniteHorizonDP.sec_V0_succ_le
#print axioms Miao.FiniteHorizonDP.sec_V0_antitone
#print axioms Miao.FiniteHorizonDP.sec_H
#print axioms Miao.FiniteHorizonDP.sec_tau
#print axioms Miao.FiniteHorizonDP.sec_H_self
#print axioms Miao.FiniteHorizonDP.sec_H_succ
#print axioms Miao.FiniteHorizonDP.sec_H_nonneg
#print axioms Miao.FiniteHorizonDP.sec_H_anti
#print axioms Miao.FiniteHorizonDP.sec_tau_spec
#print axioms Miao.FiniteHorizonDP.sec_tau_min
#print axioms Miao.FiniteHorizonDP.sec_H_lt_one
#print axioms Miao.FiniteHorizonDP.sec_V0_closed
#print axioms Miao.FiniteHorizonDP.sec_threshold
#print axioms Miao.FiniteHorizonDP.sec_tau_four
#print axioms Miao.FiniteHorizonDP.sec_threshold_misprint
#print axioms Miao.FiniteHorizonDP.po_fin2_cases
#print axioms Miao.FiniteHorizonDP.sec_measurable
#print axioms Miao.FiniteHorizonDP.sec_integrable
#print axioms Miao.FiniteHorizonDP.sec_isMarkov
#print axioms Miao.FiniteHorizonDP.sec_P_cont
#print axioms Miao.FiniteHorizonDP.sec_P_stop
#print axioms Miao.FiniteHorizonDP.sec_P_hat
#print axioms Miao.FiniteHorizonDP.sec_integral_cont
#print axioms Miao.FiniteHorizonDP.sec_integral_stop
#print axioms Miao.FiniteHorizonDP.sec_integral_hat
#print axioms Miao.FiniteHorizonDP.sec_u_inl
#print axioms Miao.FiniteHorizonDP.sec_u_inr
#print axioms Miao.FiniteHorizonDP.sec_w
#print axioms Miao.FiniteHorizonDP.sec_rule
#print axioms Miao.FiniteHorizonDP.sec_bv_cont
#print axioms Miao.FiniteHorizonDP.sec_bv_stop
#print axioms Miao.FiniteHorizonDP.sec_bv_hat
#print axioms Miao.FiniteHorizonDP.sec_bounded
#print axioms Miao.FiniteHorizonDP.sec_assumption
#print axioms Miao.FiniteHorizonDP.sec_solves
#print axioms Miao.FiniteHorizonDP.sec_wT
#print axioms Miao.FiniteHorizonDP.sec_mdp_values
#print axioms Miao.FiniteHorizonDP.prop_6_6_1
#print axioms Miao.FiniteHorizonDP.prop_6_6_1_from
#print axioms Miao.FiniteHorizonDP.sec4_w
#print axioms Miao.FiniteHorizonDP.prop_6_6_1_misprint
#print axioms Miao.FiniteHorizonDP.sec_H_succ_top
#print axioms Miao.FiniteHorizonDP.sec_log_le_H
#print axioms Miao.FiniteHorizonDP.sec_H_le_log
#print axioms Miao.FiniteHorizonDP.sec_tau_bounds
#print axioms Miao.FiniteHorizonDP.sec_tau_limit
#print axioms Miao.FiniteHorizonDP.sec_inv_e_approx
#print axioms Miao.FiniteHorizonDP.two_g
#print axioms Miao.FiniteHorizonDP.two_val
#print axioms Miao.FiniteHorizonDP.two_V
#print axioms Miao.FiniteHorizonDP.two_W
#print axioms Miao.FiniteHorizonDP.ex_6_3_bellman
#print axioms Miao.FiniteHorizonDP.two_g_nonneg
#print axioms Miao.FiniteHorizonDP.two_V_nonneg
#print axioms Miao.FiniteHorizonDP.two_W_nonneg
#print axioms Miao.FiniteHorizonDP.two_V0
#print axioms Miao.FiniteHorizonDP.two_V_ge_V0
#print axioms Miao.FiniteHorizonDP.two_W_anti
#print axioms Miao.FiniteHorizonDP.two_W_anti'
#print axioms Miao.FiniteHorizonDP.two_g_mono
#print axioms Miao.FiniteHorizonDP.two_g_mono'
#print axioms Miao.FiniteHorizonDP.ex_6_3_threshold
#print axioms Miao.FiniteHorizonDP.two_L
#print axioms Miao.FiniteHorizonDP.two_L_step
#print axioms Miao.FiniteHorizonDP.two_W_last
#print axioms Miao.FiniteHorizonDP.ex_6_3_lower
#print axioms Miao.FiniteHorizonDP.two_g2_sub_L
#print axioms Miao.FiniteHorizonDP.ex_6_3_rank2
#print axioms Miao.FiniteHorizonDP.rank_val
#print axioms Miao.FiniteHorizonDP.rank_V
#print axioms Miao.FiniteHorizonDP.rank_W
#print axioms Miao.FiniteHorizonDP.ex_6_4_bellman
#print axioms Miao.FiniteHorizonDP.rank_V_nonneg
#print axioms Miao.FiniteHorizonDP.rank_W_nonneg
#print axioms Miao.FiniteHorizonDP.rank_W_mono
#print axioms Miao.FiniteHorizonDP.ex_6_4_threshold
#print axioms Miao.FiniteHorizonDP.rank_sum_range
#print axioms Miao.FiniteHorizonDP.ex_6_4_last
#print axioms Miao.FiniteHorizonDP.ex_6_4_three
#print axioms Miao.FiniteHorizonDP.po_stopP_cont
#print axioms Miao.FiniteHorizonDP.po_stopP_stop
#print axioms Miao.FiniteHorizonDP.po_stopP_hat
#print axioms Miao.FiniteHorizonDP.po_toMDP_bounded
#print axioms Miao.FiniteHorizonDP.two_measurable
#print axioms Miao.FiniteHorizonDP.two_integrable
#print axioms Miao.FiniteHorizonDP.po_fin3_cases
#print axioms Miao.FiniteHorizonDP.two_isMarkov
#print axioms Miao.FiniteHorizonDP.two_bounded
#print axioms Miao.FiniteHorizonDP.two_assumption
#print axioms Miao.FiniteHorizonDP.two_integral_cont
#print axioms Miao.FiniteHorizonDP.two_u_inl
#print axioms Miao.FiniteHorizonDP.two_w
#print axioms Miao.FiniteHorizonDP.two_rule
#print axioms Miao.FiniteHorizonDP.two_g_eq
#print axioms Miao.FiniteHorizonDP.two_bv
#print axioms Miao.FiniteHorizonDP.two_bv_hat
#print axioms Miao.FiniteHorizonDP.two_solves
#print axioms Miao.FiniteHorizonDP.two_wT
#print axioms Miao.FiniteHorizonDP.ex_6_3_mdp
#print axioms Miao.FiniteHorizonDP.IsLHC
#print axioms Miao.FiniteHorizonDP.IsUHC
#print axioms Miao.FiniteHorizonDP.graph
#print axioms Miao.FiniteHorizonDP.continuousAt_of_isUHC_singleton
#print axioms Miao.FiniteHorizonDP.isCompact_graph
#print axioms Miao.FiniteHorizonDP.markovOpR
#print axioms Miao.FiniteHorizonDP.IsFeller
#print axioms Miao.FiniteHorizonDP.maxValue
#print axioms Miao.FiniteHorizonDP.argmax
#print axioms Miao.FiniteHorizonDP.continuousOn_section
#print axioms Miao.FiniteHorizonDP.exists_argmax
#print axioms Miao.FiniteHorizonDP.le_maxValue
#print axioms Miao.FiniteHorizonDP.tendsto_f_graph
#print axioms Miao.FiniteHorizonDP.theorem_3_6
#print axioms Miao.FiniteHorizonDP.UniqueArgmax
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.mk
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.nonempty
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.compact
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.lhc
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.uhc
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.cont
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.unique
#print axioms Miao.FiniteHorizonDP.argmaxFn
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.argmaxFn_mem
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.argmax_eq
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.lt_of_ne
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.continuous_argmaxFn
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.lemma_3_7
#print axioms Miao.FiniteHorizonDP.UniqueArgmax.lemma_3_7_uniform
#print axioms Miao.FiniteHorizonDP.shortfall_lt
#print axioms Miao.FiniteHorizonDP.theorem_3_8
#print axioms Miao.FiniteHorizonDP.theorem_3_8_uniform
#print axioms Miao.FiniteHorizonDP.IsMeasurableSelection
#print axioms Miao.FiniteHorizonDP.IsMeasCorr
#print axioms Miao.FiniteHorizonDP.minCoord
#print axioms Miao.FiniteHorizonDP.minCoord_mem
#print axioms Miao.FiniteHorizonDP.minCoord_le
#print axioms Miao.FiniteHorizonDP.measurable_minCoord
#print axioms Miao.FiniteHorizonDP.refineCorr
#print axioms Miao.FiniteHorizonDP.IsMeasCorr.refine
#print axioms Miao.FiniteHorizonDP.lexCorr
#print axioms Miao.FiniteHorizonDP.lexCorr_spec
#print axioms Miao.FiniteHorizonDP.isMeasCorr_of_uhc
#print axioms Miao.FiniteHorizonDP.theorem_7_6
#print axioms Miao.FiniteHorizonDP.theorem_7_6_subtype
#print axioms Miao.FiniteHorizonDP.theorem_4_10
#print axioms Miao.FiniteHorizonDP.ex_4_5
#print axioms Miao.FiniteHorizonDP.mop
#print axioms Miao.FiniteHorizonDP.PreservesBC
#print axioms Miao.FiniteHorizonDP.integrable_of_abs_le
#print axioms Miao.FiniteHorizonDP.integral_lt_integral_of_lt
#print axioms Miao.FiniteHorizonDP.abs_mop_le
#print axioms Miao.FiniteHorizonDP.integrable_section
#print axioms Miao.FiniteHorizonDP.lemma_9_5_discrete
#print axioms Miao.FiniteHorizonDP.lemma_9_5_compact
#print axioms Miao.FiniteHorizonDP.lemma_9_5_comb
#print axioms Miao.FiniteHorizonDP.lemma_9_5_comb_strict
#print axioms Miao.FiniteHorizonDP.lemma_9_5_mono
#print axioms Miao.FiniteHorizonDP.lemma_9_5_strictMono
#print axioms Miao.FiniteHorizonDP.lemma_9_5'
#print axioms Miao.FiniteHorizonDP.OCModel
#print axioms Miao.FiniteHorizonDP.OCModel.mk
#print axioms Miao.FiniteHorizonDP.OCModel.X
#print axioms Miao.FiniteHorizonDP.OCModel.A
#print axioms Miao.FiniteHorizonDP.OCModel.Q
#print axioms Miao.FiniteHorizonDP.OCModel.Γ
#print axioms Miao.FiniteHorizonDP.OCModel.φ
#print axioms Miao.FiniteHorizonDP.OCModel.u
#print axioms Miao.FiniteHorizonDP.OCModel.uT
#print axioms Miao.FiniteHorizonDP.OCModel.β
#print axioms Miao.FiniteHorizonDP.OCModel.T
#print axioms Miao.FiniteHorizonDP.OCModel.cont
#print axioms Miao.FiniteHorizonDP.OCModel.obj
#print axioms Miao.FiniteHorizonDP.OCModel.bellman
#print axioms Miao.FiniteHorizonDP.OCModel.W
#print axioms Miao.FiniteHorizonDP.OCModel.V
#print axioms Miao.FiniteHorizonDP.OCModel.V_T_eq
#print axioms Miao.FiniteHorizonDP.OCModel.V_succ
#print axioms Miao.FiniteHorizonDP.OCModel.V_succ_apply
#print axioms Miao.FiniteHorizonDP.OCModel.G
#print axioms Miao.FiniteHorizonDP.OCModel.g
#print axioms Miao.FiniteHorizonDP.OCModel.g_mem
#print axioms Miao.FiniteHorizonDP.OCModel.path
#print axioms Miao.FiniteHorizonDP.OCModel.IsPlan
#print axioms Miao.FiniteHorizonDP.OCModel.bolza
#print axioms Miao.FiniteHorizonDP.OCModel.policyPath
#print axioms Miao.FiniteHorizonDP.OCModel.policyPath_eq
#print axioms Miao.FiniteHorizonDP.OCModel.Γs
#print axioms Miao.FiniteHorizonDP.OCModel.Gs
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption641
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption642
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption643i
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption643ii
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption644
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption645
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption646
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption647
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption648
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption649
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption6410
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption6411
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption6412
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption6413
#print axioms Miao.FiniteHorizonDP.OCModel.Assumption6414
#print axioms Miao.FiniteHorizonDP.continuous_mop_of_compact
#print axioms Miao.FiniteHorizonDP.OCModel.ExpCont
#print axioms Miao.FiniteHorizonDP.OCModel.lemma_6_4_1_compact
#print axioms Miao.FiniteHorizonDP.OCModel.expCont_compact
#print axioms Miao.FiniteHorizonDP.OCModel.lemma_6_4_1_countable
#print axioms Miao.FiniteHorizonDP.OCModel.expCont_countable
#print axioms Miao.FiniteHorizonDP.oc_tent
#print axioms Miao.FiniteHorizonDP.oc_spike
#print axioms Miao.FiniteHorizonDP.oc_tent_eq_zero
#print axioms Miao.FiniteHorizonDP.oc_tent_nonneg
#print axioms Miao.FiniteHorizonDP.oc_tent_le_one
#print axioms Miao.FiniteHorizonDP.oc_spike_bound
#print axioms Miao.FiniteHorizonDP.oc_half
#print axioms Miao.FiniteHorizonDP.oc_spikeModel
#print axioms Miao.FiniteHorizonDP.lemma_6_4_1_countable_counterexample
#print axioms Miao.FiniteHorizonDP.OCModel.objS
#print axioms Miao.FiniteHorizonDP.OCModel.maxValue_objS
#print axioms Miao.FiniteHorizonDP.OCModel.V_eq_maxValue
#print axioms Miao.FiniteHorizonDP.OCModel.Gs_eq_argmax
#print axioms Miao.FiniteHorizonDP.OCModel.oc_abs_integral_le
#print axioms Miao.FiniteHorizonDP.OCModel.continuousOn_objS
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_1
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_1_compact
#print axioms Miao.FiniteHorizonDP.OCModel.V_bounded
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_1_countable
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_1_selection
#print axioms Miao.FiniteHorizonDP.OCModel.Standing
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.mk
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.expCont
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.memP
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.a644
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.a645
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.a646
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.of_compact
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.of_countable
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.contV
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.integrable
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.continuousOn_objS
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.obj_le_V
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.G_nonempty
#print axioms Miao.FiniteHorizonDP.OCModel.Standing.g_mem
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_2
#print axioms Miao.FiniteHorizonDP.OCModel.CompConcave
#print axioms Miao.FiniteHorizonDP.OCModel.CompStrictA
#print axioms Miao.FiniteHorizonDP.OCModel.PhiAffine
#print axioms Miao.FiniteHorizonDP.OCModel.PhiInjA
#print axioms Miao.FiniteHorizonDP.OCModel.compConcave_of_mono
#print axioms Miao.FiniteHorizonDP.OCModel.compStrictA_of_mono
#print axioms Miao.FiniteHorizonDP.OCModel.compConcave_of_affine
#print axioms Miao.FiniteHorizonDP.OCModel.compStrictA_of_affine
#print axioms Miao.FiniteHorizonDP.OCModel.cont_comb
#print axioms Miao.FiniteHorizonDP.OCModel.concave_core
#print axioms Miao.FiniteHorizonDP.OCModel.G_subsingleton_core
#print axioms Miao.FiniteHorizonDP.OCModel.G_eq_singleton_core
#print axioms Miao.FiniteHorizonDP.OCModel.continuousOn_g_core
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_3_concave
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_3
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_3_affine
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_3_phi_eq_a
#print axioms Miao.FiniteHorizonDP.isLHC_const
#print axioms Miao.FiniteHorizonDP.isUHC_const
#print axioms Miao.FiniteHorizonDP.oc_flatModel
#print axioms Miao.FiniteHorizonDP.oc_negSq_comb
#print axioms Miao.FiniteHorizonDP.oc_negSq_strict
#print axioms Miao.FiniteHorizonDP.theorem_6_4_3_counterexample
#print axioms Miao.FiniteHorizonDP.oc_hasDerivAt_integral_concave
#print axioms Miao.FiniteHorizonDP.oc_slope_double
#print axioms Miao.FiniteHorizonDP.oc_continuousOn_deriv_of_concave
#print axioms Miao.FiniteHorizonDP.OCModel.envRHS
#print axioms Miao.FiniteHorizonDP.OCModel.focRHS
#print axioms Miao.FiniteHorizonDP.OCModel.LocBounded
#print axioms Miao.FiniteHorizonDP.OCModel.InteriorPolicy
#print axioms Miao.FiniteHorizonDP.OCModel.Partials
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.mk
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.uT
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.ux
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.ua
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.φx
#print axioms Miao.FiniteHorizonDP.OCModel.Partials.φa
#print axioms Miao.FiniteHorizonDP.OCModel.partials_of
#print axioms Miao.FiniteHorizonDP.OCModel.oc_concaveOn_of_pos
#print axioms Miao.FiniteHorizonDP.OCModel.eventually_mem_Γ
#print axioms Miao.FiniteHorizonDP.OCModel.hasDerivAt_cont_x
#print axioms Miao.FiniteHorizonDP.OCModel.hasDerivAt_cont_a
#print axioms Miao.FiniteHorizonDP.OCModel.envelope_step
#print axioms Miao.FiniteHorizonDP.OCModel.foc_step
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_4_core
#print axioms Miao.FiniteHorizonDP.OCModel.locBounded_of_compact
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_4
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_4_4_phi_eq_a
#print axioms Miao.FiniteHorizonDP.OCModel.euler_equations
#print axioms Miao.FiniteHorizonDP.oc_tangent_le
#print axioms Miao.FiniteHorizonDP.oc_supergradient
#print axioms Miao.FiniteHorizonDP.OCModel.path_measurable
#print axioms Miao.FiniteHorizonDP.OCModel.Ha
#print axioms Miao.FiniteHorizonDP.OCModel.Hx
#print axioms Miao.FiniteHorizonDP.OCModel.hamiltonian
#print axioms Miao.FiniteHorizonDP.OCModel.pathHam
#print axioms Miao.FiniteHorizonDP.OCModel.MaxPrinciple
#print axioms Miao.FiniteHorizonDP.OCModel.MaxPrinciple.mk
#print axioms Miao.FiniteHorizonDP.OCModel.MaxPrinciple.foc_a
#print axioms Miao.FiniteHorizonDP.OCModel.MaxPrinciple.foc_x
#print axioms Miao.FiniteHorizonDP.OCModel.MaxPrinciple.terminal
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.mk
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.u_s
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.u_c
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.uT_s
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.uT_c
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.μΔ
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.ux
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.φx
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.φxΔ
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.ua
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.φa
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.φaΔ
#print axioms Miao.FiniteHorizonDP.OCModel.MPIntegrable.uTx
#print axioms Miao.FiniteHorizonDP.OCModel.oc_integral_mul_condExp
#print axioms Miao.FiniteHorizonDP.OCModel.theorem_6_5_1
#print axioms Miao.FiniteHorizonDP.OCModel.pathHam_concave_of_concave
#print axioms Miao.FiniteHorizonDP.OCModel.pathHam_concave_of_affine
#print axioms Miao.FiniteHorizonDP.OCModel.IsMarkovCond
#print axioms Miao.FiniteHorizonDP.OCModel.link_6_38_6_33
#print axioms Miao.FiniteHorizonDP.OCModel.link_6_39_6_31
#print axioms Miao.FiniteHorizonDP.OCModel.maxPrinciple_of_dp
#print axioms Miao.FiniteHorizonDP.OCModel.lam
#print axioms Miao.FiniteHorizonDP.OCModel.eq_6_40_a
#print axioms Miao.FiniteHorizonDP.OCModel.eq_6_40_b
#print axioms Miao.FiniteHorizonDP.OCModel.eq_6_40_terminal
#print axioms Miao.FiniteHorizonDP.OCModel.eq_6_40_terminal_misprint
#print axioms Miao.FiniteHorizonDP.ControlProblem
#print axioms Miao.FiniteHorizonDP.ControlProblem.mk
#print axioms Miao.FiniteHorizonDP.ControlProblem.Q
#print axioms Miao.FiniteHorizonDP.ControlProblem.φ
#print axioms Miao.FiniteHorizonDP.ControlProblem.Γ
#print axioms Miao.FiniteHorizonDP.ControlProblem.u
#print axioms Miao.FiniteHorizonDP.ControlProblem.uT
#print axioms Miao.FiniteHorizonDP.ControlProblem.β
#print axioms Miao.FiniteHorizonDP.controlKernel
#print axioms Miao.FiniteHorizonDP.ControlProblem.toMDP
#print axioms Miao.FiniteHorizonDP.measurable_controlNext
#print axioms Miao.FiniteHorizonDP.controlKernel_apply
#print axioms Miao.FiniteHorizonDP.isMarkovKernel_controlKernel
#print axioms Miao.FiniteHorizonDP.controlKernel_rect
#print axioms Miao.FiniteHorizonDP.controlKernel_rect_of_indep
#print axioms Miao.FiniteHorizonDP.ctrlX
#print axioms Miao.FiniteHorizonDP.controlObj
#print axioms Miao.FiniteHorizonDP.IsFeasibleControl
#print axioms Miao.FiniteHorizonDP.controlV
#print axioms Miao.FiniteHorizonDP.ctrlStep
#print axioms Miao.FiniteHorizonDP.ctrlLift
#print axioms Miao.FiniteHorizonDP.inducedPolicy
#print axioms Miao.FiniteHorizonDP.lastState_ctrlLift
#print axioms Miao.FiniteHorizonDP.snd_ctrlLift
#print axioms Miao.FiniteHorizonDP.measurable_ctrlStep
#print axioms Miao.FiniteHorizonDP.ctrl_hstep
#print axioms Miao.FiniteHorizonDP.controlMDP_isMarkov
#print axioms Miao.FiniteHorizonDP.expRew_control
#print axioms Miao.FiniteHorizonDP.J0T_control
#print axioms Miao.FiniteHorizonDP.J_control
#print axioms Miao.FiniteHorizonDP.measurable_inducedPolicy
#print axioms Miao.FiniteHorizonDP.ctrlX_congr
#print axioms Miao.FiniteHorizonDP.controlObj_congr
#print axioms Miao.FiniteHorizonDP.controlPlan
#print axioms Miao.FiniteHorizonDP.controlPlan_apply
#print axioms Miao.FiniteHorizonDP.controlPlan_feasible
#print axioms Miao.FiniteHorizonDP.inducedPolicy_controlPlan
#print axioms Miao.FiniteHorizonDP.V0_control
#print axioms Miao.FiniteHorizonDP.OCModel.toCP
#print axioms Miao.FiniteHorizonDP.OCModel.toMDP
#print axioms Miao.FiniteHorizonDP.OCModel.wV
#print axioms Miao.FiniteHorizonDP.OCModel.toXZ
#print axioms Miao.FiniteHorizonDP.OCModel.continuous_toXZ
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_toXZ
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_of_continuousOn
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_toCP_φ
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_toCP_u
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_toCP_uT
#print axioms Miao.FiniteHorizonDP.OCModel.toMDP_P
#print axioms Miao.FiniteHorizonDP.OCModel.measurable_next
#print axioms Miao.FiniteHorizonDP.OCModel.bellmanVal_toMDP
#print axioms Miao.FiniteHorizonDP.OCModel.integrable_toMDP
#print axioms Miao.FiniteHorizonDP.OCModel.exists_selection_G
#print axioms Miao.FiniteHorizonDP.OCModel.p175
#print axioms Miao.FiniteHorizonDP.OCModel.p175_date_zero
#print axioms Miao.FiniteHorizonDP.OCModel.measurableSet_graph_toCP
#print axioms Miao.FiniteHorizonDP.OCModel.exists_selection_Γ
#print axioms Miao.FiniteHorizonDP.OCModel.p175_control
#print axioms Miao.FiniteHorizonDP.OCModel.p175_compact
#print axioms Miao.FiniteHorizonDP.OCModel.bounded_of_compact
#print axioms Miao.FiniteHorizonDP.OCModel.p175_compact_XA
#print axioms Miao.FiniteHorizonDP.OCModel.p175_countable
#print axioms Miao.FiniteHorizonDP.CSModel
#print axioms Miao.FiniteHorizonDP.CSModel.mk
#print axioms Miao.FiniteHorizonDP.CSModel.u
#print axioms Miao.FiniteHorizonDP.CSModel.β
#print axioms Miao.FiniteHorizonDP.CSModel.Q
#print axioms Miao.FiniteHorizonDP.CSModel.ρ
#print axioms Miao.FiniteHorizonDP.CSModel.w
#print axioms Miao.FiniteHorizonDP.cash_on_hand
#print axioms Miao.FiniteHorizonDP.CSModel.toOC
#print axioms Miao.FiniteHorizonDP.CSModel.v
#print axioms Miao.FiniteHorizonDP.CSModel.obj
#print axioms Miao.FiniteHorizonDP.CSModel.v_zero
#print axioms Miao.FiniteHorizonDP.CSModel.v_succ
#print axioms Miao.FiniteHorizonDP.CSModel.W_eq
#print axioms Miao.FiniteHorizonDP.CSModel.V_eq
#print axioms Miao.FiniteHorizonDP.CSModel.sav
#print axioms Miao.FiniteHorizonDP.CSModel.cons
#print axioms Miao.FiniteHorizonDP.CSModel.ex_6_5_g0_s0
#print axioms Miao.FiniteHorizonDP.CSModel.obj_eq
#print axioms Miao.FiniteHorizonDP.CSModel.mem_G
#print axioms Miao.FiniteHorizonDP.CSModel.Basic
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.mk
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.β_pos
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.u_cont
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.u_mono
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.u_conc
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.ρ_cont
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.ρ_pos
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.w_cont
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.w_pos
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.feller
#print axioms Miao.FiniteHorizonDP.CSModel.assumption644
#print axioms Miao.FiniteHorizonDP.CSModel.assumption645
#print axioms Miao.FiniteHorizonDP.CSModel.assumption646
#print axioms Miao.FiniteHorizonDP.CSModel.isFeller_const
#print axioms Miao.FiniteHorizonDP.CSModel.standing
#print axioms Miao.FiniteHorizonDP.CSModel.contV
#print axioms Miao.FiniteHorizonDP.CSModel.integrable_next
#print axioms Miao.FiniteHorizonDP.CSModel.obj_le
#print axioms Miao.FiniteHorizonDP.CSModel.sav_mem
#print axioms Miao.FiniteHorizonDP.CSModel.isMaxOn_sav
#print axioms Miao.FiniteHorizonDP.CSModel.not_assumption6410
#print axioms Miao.FiniteHorizonDP.cs_exchange
#print axioms Miao.FiniteHorizonDP.CSModel.ev
#print axioms Miao.FiniteHorizonDP.CSModel.obj_eq_ev
#print axioms Miao.FiniteHorizonDP.CSModel.next_nonneg
#print axioms Miao.FiniteHorizonDP.CSModel.strictConcaveOn_ev
#print axioms Miao.FiniteHorizonDP.CSModel.strictMonoOn_v
#print axioms Miao.FiniteHorizonDP.CSModel.strictConcaveOn_v
#print axioms Miao.FiniteHorizonDP.CSModel.sav_unique
#print axioms Miao.FiniteHorizonDP.CSModel.G_subsingleton
#print axioms Miao.FiniteHorizonDP.CSModel.continuousOn_sav
#print axioms Miao.FiniteHorizonDP.CSModel.continuousOn_cons
#print axioms Miao.FiniteHorizonDP.CSModel.sav_mem'
#print axioms Miao.FiniteHorizonDP.CSModel.monotoneOn_sav
#print axioms Miao.FiniteHorizonDP.CSModel.monotoneOn_cons
#print axioms Miao.FiniteHorizonDP.cs_compare
#print axioms Miao.FiniteHorizonDP.CSModel.Smooth
#print axioms Miao.FiniteHorizonDP.CSModel.Smooth.mk
#print axioms Miao.FiniteHorizonDP.CSModel.Smooth.u_diff
#print axioms Miao.FiniteHorizonDP.CSModel.Smooth.inada
#print axioms Miao.FiniteHorizonDP.CSModel.evd
#print axioms Miao.FiniteHorizonDP.CSModel.detModel
#print axioms Miao.FiniteHorizonDP.CSModel.strictAntiOn_deriv_u
#print axioms Miao.FiniteHorizonDP.CSModel.cons_pos
#print axioms Miao.FiniteHorizonDP.CSModel.hasDerivAt_v
#print axioms Miao.FiniteHorizonDP.CSModel.deriv_v
#print axioms Miao.FiniteHorizonDP.CSModel.continuousOn_deriv_v
#print axioms Miao.FiniteHorizonDP.CSModel.strictAntiOn_deriv_v
#print axioms Miao.FiniteHorizonDP.CSModel.hasDerivAt_ev
#print axioms Miao.FiniteHorizonDP.CSModel.strictAntiOn_evd
#print axioms Miao.FiniteHorizonDP.CSModel.foc
#print axioms Miao.FiniteHorizonDP.CSModel.strictMonoOn_cons
#print axioms Miao.FiniteHorizonDP.CSModel.exists_sav_eq_zero
#print axioms Miao.FiniteHorizonDP.CSModel.not_strictMonoOn_sav
#print axioms Miao.FiniteHorizonDP.CSModel.evd_le_evd
#print axioms Miao.FiniteHorizonDP.CSModel.cons_succ_le
#print axioms Miao.FiniteHorizonDP.CSModel.sav_le_sav_succ
#print axioms Miao.FiniteHorizonDP.CSModel.deriv_v_le
#print axioms Miao.FiniteHorizonDP.CSModel.exists_cons_succ_eq
#print axioms Miao.FiniteHorizonDP.CSModel.Basic.detModel
#print axioms Miao.FiniteHorizonDP.CSModel.isMarkovKernel_detModel
#print axioms Miao.FiniteHorizonDP.CSModel.evd_detModel
#print axioms Miao.FiniteHorizonDP.CSModel.cons_ge_low
#print axioms Miao.FiniteHorizonDP.CSModel.cons_le_high
#print axioms Miao.FiniteHorizonDP.CSModel.v_indep
#print axioms Miao.FiniteHorizonDP.bookModel
#print axioms Miao.FiniteHorizonDP.CSUtility
#print axioms Miao.FiniteHorizonDP.CSUtility.mk
#print axioms Miao.FiniteHorizonDP.CSUtility.cont
#print axioms Miao.FiniteHorizonDP.CSUtility.mono
#print axioms Miao.FiniteHorizonDP.CSUtility.conc
#print axioms Miao.FiniteHorizonDP.CSUtility.diff
#print axioms Miao.FiniteHorizonDP.CSUtility.inada
#print axioms Miao.FiniteHorizonDP.bookModel_isMarkovKernel
#print axioms Miao.FiniteHorizonDP.bookModel_basic
#print axioms Miao.FiniteHorizonDP.ex_6_5_value
#print axioms Miao.FiniteHorizonDP.ex_6_5_v_deriv_mono
#print axioms Miao.FiniteHorizonDP.ex_6_5_policy_x
#print axioms Miao.FiniteHorizonDP.ex_6_5_sav_not_strict
#print axioms Miao.FiniteHorizonDP.ex_6_5_policy_n
#print axioms Miao.FiniteHorizonDP.ex_6_5_n_not_strict
#print axioms Miao.FiniteHorizonDP.ex_6_5_foc
#print axioms Miao.FiniteHorizonDP.ex_6_5_compare
#print axioms Miao.FiniteHorizonDP.markovModel
#print axioms Miao.FiniteHorizonDP.ex_6_6
#print axioms Miao.FiniteHorizonDP.phelpsModel
#print axioms Miao.FiniteHorizonDP.ex_6_7
#print axioms Miao.FiniteHorizonDP.cs_budget
#print axioms Miao.FiniteHorizonDP.cs_optimal_of_euler
#print axioms Miao.FiniteHorizonDP.cs_crra
#print axioms Miao.FiniteHorizonDP.cs_crra_tangent
#print axioms Miao.FiniteHorizonDP.cs_theta
#print axioms Miao.FiniteHorizonDP.cs_wealth
#print axioms Miao.FiniteHorizonDP.cs_cstar
#print axioms Miao.FiniteHorizonDP.cs_astar
#print axioms Miao.FiniteHorizonDP.ex_6_8
#print axioms Miao.FiniteHorizonDP.cs_cara_step
#print axioms Miao.FiniteHorizonDP.cs_cara_v
#print axioms Miao.FiniteHorizonDP.cs_caraAlpha
#print axioms Miao.FiniteHorizonDP.cs_caraM
#print axioms Miao.FiniteHorizonDP.cs_caraA
#print axioms Miao.FiniteHorizonDP.cs_caraL
#print axioms Miao.FiniteHorizonDP.cs_caraS
#print axioms Miao.FiniteHorizonDP.cs_cara_M_pos
#print axioms Miao.FiniteHorizonDP.cs_cara_integral
#print axioms Miao.FiniteHorizonDP.ex_6_9
#print axioms Miao.FiniteHorizonDP.cs_clamp
#print axioms Miao.FiniteHorizonDP.cs_cara_basic
#print axioms Miao.FiniteHorizonDP.ex_6_10
#print axioms Miao.FiniteHorizonDP.ex_6_10_one
