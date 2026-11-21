/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.MDPHistoryTools
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Data.ENat.Basic

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
