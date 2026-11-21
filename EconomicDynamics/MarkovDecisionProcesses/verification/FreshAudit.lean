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
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Distributions.Exponential
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite histories

Copied from `RecursiveMethods/StochasticDP` (module `Histories`, SLP §8.2), with the namespace
renamed. Histories `sᵗ = (s₁, …, s_t)` are functions `Fin t → S`; `lastState s₀ sᵗ` is the most
recent state (`s₀` for the empty history, otherwise `s_t`). Used for Miao, §5.1, pp. 137–139.
-/

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov decision process model

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The measures on histories induced by a plan

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Total discounted expected rewards and the value function

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two ways of building stochastic kernels

Tools for the examples of Miao, §5.2, pp. 143–154.

* `famKernel κ`: for a countable action set with measurable singletons, the kernel
  `P(s, a; ·) = κ_a(s; ·)` built from one kernel per action (the discrete choice, stopping and
  bandit models).
* `pushKernel κ F`: the law of `F(x, ε)` when `ε ~ κ(x, ·)`, i.e. `x ↦ κ(x, ·) ∘ F(x, ·)⁻¹`
  (laws of motion driven by a shock, as in the optimal control model).
-/

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transporting history measures between models

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The measure on infinite histories (Ionescu Tulcea)

Miao, §5.1, p. 139: "In the infinite-horizon case, the sequence of measures `μᵗ(s₀, ·; π)`,
`t = 1, 2, …`, induces a unique measure `μ^∞(s₀, ·; π)` on `S^∞`." The book attributes this to
the Kolmogorov extension theorem; it is the Ionescu Tulcea theorem, available in Mathlib as
`ProbabilityTheory.Kernel.traj`. The plan enters through the kernels
`κ_t(s₀, …, s_t) = P_{t+1}(s_t, π_t(s₁, …, s_t); ·)` (`trajKernel`).

* `muInf M s₀ π`: a probability measure on trajectories `ω = (s₀, s₁, s₂, …)` with `ω₀ = s₀`
  almost surely (`muInf_zero`).
* `muInf_marginal`: the law of `(s₁, …, s_t)` under `μ^∞` is `μᵗ(s₀, ·; π)` of (5.2).
* `muInf_unique`: `μ^∞` is the only measure on `S^ℕ` with these marginals.

Departure: the book's `S^∞` is the space of `(s₁, s₂, …)`; here the trajectory also carries the
initial state `s₀` (as in Mathlib), which is almost surely the given one.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The history `(s₁, …, s_t)` of a trajectory segment `(s₀, …, s_t)`. -/
def histOf (t : ℕ) (y : (i : Finset.Iic t) → S) : Fin t → S :=
  fun i => y ⟨i.val + 1, Finset.mem_Iic.2 (by omega)⟩

theorem measurable_histOf (t : ℕ) : Measurable (histOf (S := S) t) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_lastState₂ (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => lastState p.1 p.2 := by
  cases t with
  | zero => exact measurable_fst
  | succ t => exact (measurable_pi_apply _).comp measurable_snd

/-- The kernel `κ_t(s₀, …, s_t) = P_{t+1}(s_t, π_t(s₁, …, s_t); ·)`. -/
noncomputable def trajKernel (M : MDP S A) (π : Plan S A) (hπ : ∀ t, Measurable (π t))
    (t : ℕ) : Kernel ((i : Finset.Iic t) → S) S :=
  (M.P t).comap (fun y => (lastState (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩) (histOf t y),
      π t (histOf t y)))
    (((measurable_lastState₂ t).comp ((measurable_pi_apply _).prodMk (measurable_histOf t))).prodMk
      ((hπ t).comp (measurable_histOf t)))

theorem isMarkovKernel_trajKernel (M : MDP S A) (hP : M.IsMarkov) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) : IsMarkovKernel (trajKernel M π hπ t) := by
  have := hP t
  unfold trajKernel
  infer_instance

/-- `μ^∞(s₀, ·; π)`, the distribution of the trajectory `(s₀, s₁, …)` (Miao, p. 139), given by
the Ionescu Tulcea theorem. -/
noncomputable def muInf (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) : Measure (ℕ → S) :=
  @Kernel.traj (fun _ => S) _ (trajKernel M π hπ) (isMarkovKernel_trajKernel M hP π hπ) 0
    fun _ => s₀

theorem isProbabilityMeasure_muInf (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) : IsProbabilityMeasure (muInf M hP s₀ π hπ) := by
  have := isMarkovKernel_trajKernel M hP π hπ
  unfold muInf
  infer_instance

/-- The pair `(s₀, (s₁, …, s_t))` of a trajectory segment. -/
def splitSeg (t : ℕ) (y : (i : Finset.Iic t) → S) : S × (Fin t → S) :=
  (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩, histOf t y)

theorem measurable_splitSeg (t : ℕ) : Measurable (splitSeg (S := S) t) :=
  (measurable_pi_apply _).prodMk (measurable_histOf t)

/-- The inverse of `splitSeg`. -/
def joinSeg (t : ℕ) (p : S × (Fin t → S)) : (i : Finset.Iic t) → S :=
  fun i => if h : i.1 = 0 then p.1 else
    p.2 ⟨i.1 - 1, by have := Finset.mem_Iic.1 i.2; omega⟩

theorem measurable_joinSeg (t : ℕ) : Measurable (joinSeg (S := S) t) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i.1 = 0
  · simp only [joinSeg, h, ↓reduceDIte]
    exact measurable_fst
  · simp only [joinSeg, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

omit [MeasurableSpace S] in
theorem joinSeg_splitSeg (t : ℕ) (y : (i : Finset.Iic t) → S) : joinSeg t (splitSeg t y) = y := by
  funext i
  by_cases h : i.1 = 0
  · simp only [joinSeg, splitSeg, h, ↓reduceDIte]
    congr 1
    exact Subtype.ext h.symm
  · simp only [joinSeg, splitSeg, h, ↓reduceDIte, histOf]
    congr 1
    exact Subtype.ext (by simp; omega)

theorem splitSeg_IicProdIoc (t : ℕ) (y : (i : Finset.Iic t) → S) (s : S) :
    splitSeg (t + 1) (IicProdIoc (X := fun _ => S) t (t + 1)
      (y, (MeasurableEquiv.piSingleton (X := fun _ => S) t) s)) =
      (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩, Fin.snoc (histOf t y) s) := by
  refine Prod.ext ?_ ?_
  · simp [splitSeg, IicProdIoc]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [splitSeg, histOf, IicProdIoc, MeasurableEquiv.piSingleton]
    · simp only [splitSeg, histOf, IicProdIoc, Fin.snoc_castSucc, Fin.val_castSucc]
      have : j.1 + 1 ≤ t := j.2
      simp [this]

/-- The law of `(s₀, (s₁, …, s_t))` under the partial trajectory is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)`. -/
theorem partialTraj_map_splitSeg (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 t (fun _ => s₀)).map
      (splitSeg t) = (mu M s₀ π t).map fun h => (s₀, h) := by
  have hk := isMarkovKernel_trajKernel M hP π hπ
  have hm : ∀ t, Measurable fun h : Fin t → S => (s₀, h) :=
    fun _ => measurable_const.prodMk measurable_id
  induction t with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_splitSeg 0),
      mu_zero, Measure.map_dirac' (hm 0)]
    congr 1
    refine Prod.ext rfl ?_
    exact Subsingleton.elim _ _
  | succ t ih =>
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_splitSeg _), lintegral_map hf (hm _),
      mu_succ_lintegral M hP s₀ (hπ t) (f := fun h => f (s₀, h)) (hf.comp (hm _)),
      Kernel.partialTraj_succ_eq_comp (Nat.zero_le t), Kernel.partialTraj_succ_self,
      Kernel.lintegral_comp _ _ _ (g := fun z => f (splitSeg (t + 1) z))
        (hf.comp (measurable_splitSeg _))]
    have := hP t
    have hF : Measurable fun p : S × (Fin t → S) =>
        ∫⁻ s, f (p.1, Fin.snoc p.2 s) ∂M.P t (lastState p.1 p.2, π t p.2) := by
      have hk2 : Measurable fun p : S × (Fin t → S) => (lastState p.1 p.2, π t p.2) :=
        (measurable_lastState₂ t).prodMk ((hπ t).comp measurable_snd)
      exact (hf.comp (measurable_fst.fst.prodMk ((measurable_snoc t).comp
        (measurable_fst.snd.prodMk measurable_snd)))).lintegral_kernel_prod_right'
          (κ := (M.P t).comap _ hk2) |> fun h => h
    have hstep : ∀ y : (i : Finset.Iic t) → S,
        ∫⁻ z, f (splitSeg (t + 1) z) ∂((Kernel.id ×ₖ ((trajKernel M π hπ t).map
          (MeasurableEquiv.piSingleton (X := fun _ => S) t))).map
            (IicProdIoc (X := fun _ => S) t (t + 1))) y =
        (fun p : S × (Fin t → S) =>
          ∫⁻ s, f (p.1, Fin.snoc p.2 s) ∂M.P t (lastState p.1 p.2, π t p.2)) (splitSeg t y) := by
      intro y
      have hg1 : Measurable fun z => f (splitSeg (t + 1) z) := hf.comp (measurable_splitSeg _)
      have hg2 : Measurable fun p => f (splitSeg (t + 1)
          (IicProdIoc (X := fun _ => S) t (t + 1) p)) :=
        hg1.comp (measurable_IicProdIoc (X := fun _ => S) (m := t) (n := t + 1))
      have hg3 : Measurable fun b => f (splitSeg (t + 1)
          (IicProdIoc (X := fun _ => S) t (t + 1) (y, b))) :=
        hg2.comp (measurable_const.prodMk measurable_id)
      rw [Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S)) _ hg1,
        Kernel.lintegral_prod _ _ _ hg2,
        Kernel.id_apply, lintegral_dirac' _ hg2.lintegral_prod_right',
        Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) t).measurable _
          hg3]
      simp only [splitSeg_IicProdIoc]
      rfl
    simp_rw [hstep]
    rw [← lintegral_map hF (measurable_splitSeg t), ih, lintegral_map hF (hm t)]

/-- The trajectory map `ω ↦ (ω₀, (ω₁, …, ω_t))`. -/
def splitTraj (t : ℕ) (ω : ℕ → S) : S × (Fin t → S) := (ω 0, fun i => ω (i.val + 1))

theorem measurable_splitTraj (t : ℕ) : Measurable (splitTraj (S := S) t) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

omit [MeasurableSpace S] in
theorem splitTraj_eq (t : ℕ) : splitTraj (S := S) t = splitSeg t ∘ frestrictLe t := rfl

/-- The law of `(s₀, (s₁, …, s_t))` under `μ^∞` is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)`. -/
theorem muInf_map_splitTraj (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (muInf M hP s₀ π hπ).map (splitTraj t) = (mu M s₀ π t).map fun h => (s₀, h) := by
  have := isMarkovKernel_trajKernel M hP π hπ
  rw [splitTraj_eq, ← Measure.map_map (measurable_splitSeg t) (measurable_frestrictLe t), muInf,
    Kernel.traj_map_frestrictLe_apply, partialTraj_map_splitSeg M hP s₀ π hπ t]

/-- Miao, p. 139: the marginal of `μ^∞(s₀, ·; π)` on `(s₁, …, s_t)` is `μᵗ(s₀, ·; π)`. -/
theorem muInf_marginal (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (muInf M hP s₀ π hπ).map (fun ω (i : Fin t) => ω (i.val + 1)) = mu M s₀ π t := by
  have h := congrArg (Measure.map Prod.snd) (muInf_map_splitTraj M hP s₀ π hπ t)
  have hm : Measurable fun h : Fin t → S => (s₀, h) := measurable_const.prodMk measurable_id
  have e : (Prod.snd ∘ fun h : Fin t → S => (s₀, h)) = id := rfl
  rw [Measure.map_map measurable_snd (measurable_splitTraj t), Measure.map_map measurable_snd hm,
    e, Measure.map_id] at h
  exact h

/-- Under `μ^∞(s₀, ·; π)` the initial state is `s₀` almost surely. -/
theorem muInf_zero (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) :
    (muInf M hP s₀ π hπ).map (fun ω => ω 0) = Measure.dirac s₀ := by
  have h := congrArg (Measure.map Prod.fst) (muInf_map_splitTraj M hP s₀ π hπ 0)
  have hm : Measurable fun h : Fin 0 → S => (s₀, h) := measurable_const.prodMk measurable_id
  rw [Measure.map_map measurable_fst (measurable_splitTraj 0), Measure.map_map measurable_fst hm,
    mu_zero, Measure.map_dirac' (measurable_fst.comp hm)] at h
  exact h

/-- Miao, p. 139: `μ^∞(s₀, ·; π)` is the **unique** measure on trajectories whose law of
`(s₀, (s₁, …, s_t))` is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)` for every `t`. -/
theorem muInf_unique (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (ν : Measure (ℕ → S))
    (hν : ∀ t, ν.map (splitTraj t) = (mu M s₀ π t).map fun h => (s₀, h)) :
    ν = muInf M hP s₀ π hπ := by
  have hk := isMarkovKernel_trajKernel M hP π hπ
  have hjs : ∀ n, joinSeg (S := S) n ∘ splitSeg n = id := fun n => funext (joinSeg_splitSeg n)
  have key : ∀ n, ν.map (frestrictLe n) =
      @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀) := by
    intro n
    have e1 : ν.map (frestrictLe n) = (ν.map (splitTraj n)).map (joinSeg n) := by
      rw [splitTraj_eq, Measure.map_map (measurable_joinSeg n) ((measurable_splitSeg n).comp
        (measurable_frestrictLe n)), ← Function.comp_assoc, hjs, Function.id_comp]
    have e2 : @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀) =
        ((@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)).map
          (splitSeg n)).map (joinSeg n) := by
      rw [Measure.map_map (measurable_joinSeg n) (measurable_splitSeg n), hjs, Measure.map_id]
    rw [e1, e2, hν n, partialTraj_map_splitSeg M hP s₀ π hπ n]
  have hpr : ∀ n, IsProbabilityMeasure
      (@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)) :=
    fun n => inferInstance
  have hfin : ∀ I, IsFiniteMeasure (inducedFamily (X := fun _ => S) (fun n =>
      @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)) I) := by
    intro I
    unfold inducedFamily
    infer_instance
  have hlim :=
    (isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj _ _) ν).2
      fun n => by rw [inducedFamily_Iic]; exact key n
  exact hlim.unique (Kernel.isProjectiveLimit_trajFun _ 0 _)

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 5.1.1: an infinite supremum and a supremum that is not attained

Miao, Example 5.1.1, p. 141. A static problem is the one-period problem (`T = 1`) with no
terminal reward; then `V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a)` (`V0_one`).

* (a) `u₀(s, a) = 1/a + s` on `Γ(s) = {a ∈ [s, 2] : a ≠ 0}`: for `s ∈ (0, 2]`, `V₀(s) = 1/s + s`
  and `a* = s` is optimal (`example_5_1_1a_pos`); for `s ≤ 0`, `V₀(s) = +∞` and no plan attains
  it (`example_5_1_1a_nonpos`). The book states the first case for `s ∈ (0, 2)` and the second
  for `s < 0`; both hold on the larger sets. For `s > 2`, `Γ(s) = ∅` and `V₀(s) = −∞`
  (`example_5_1_1a_empty`; the book's `Γ` is not nonempty-valued there).
* (b) `u₀(s, a) = a` on `Γ(s) = (0, 1)`: `V₀ ≡ 1`, and no action attains it
  (`example_5_1_1b`).
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The one-period problem: `J₀¹(s, π) = u₀(s, π₀)` when there is no terminal reward. -/
theorem J0T_one (M : MDP S A) (huT : M.uT = 0) (s : S) (π : Plan S A) :
    J0T M 1 s π = M.u 0 (s, π 0 Fin.elim0) := by
  simp [J0T, huT, expRew_zero]

/-- The plans feasible for one period are those with `π₀ ∈ Γ(s)`. -/
theorem feasible_one_iff (M : MDP S A) (s : S) (π : Plan S A) :
    π ∈ feasiblePlans M 1 s ↔ π 0 Fin.elim0 ∈ M.Γ s := by
  constructor
  · intro h
    exact h.2 0 (by norm_num) Fin.elim0
  · intro h
    refine ⟨fun t ht => ?_, fun t ht g => ?_⟩
    · have : t = 0 := by exact_mod_cast Order.lt_one_iff.1 ht
      subst this
      exact Subsingleton.measurable
    · have : t = 0 := by exact_mod_cast Order.lt_one_iff.1 ht
      subst this
      have : g = Fin.elim0 := Subsingleton.elim _ _
      subst this
      exact h

/-- A static problem (Miao, Example 5.1.1): with `T = 1` and no terminal reward,
`V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a)`. -/
theorem V0_one (M : MDP S A) (huT : M.uT = 0) (s : S) :
    V0 M 1 s = ⨆ a ∈ M.Γ s, (M.u 0 (s, a) : EReal) := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun a ha => ?_)
  · rw [J0T_one M huT]
    exact le_iSup₂ (f := fun a (_ : a ∈ M.Γ s) => (M.u 0 (s, a) : EReal)) _
      ((feasible_one_iff M s π).1 hπ)
  · have hπ : (fun _ _ => a : Plan S A) ∈ feasiblePlans M 1 s := (feasible_one_iff M s _).2 ha
    have := le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M 1 s) => (J0T M 1 s π : EReal)) _ hπ
    rwa [J0T_one M huT] at this

/-- The problem of Example 5.1.1(a): `sup_{a ∈ [s, 2], a ≠ 0} 1/a + s` (the kernel and the
discount factor play no role). -/
noncomputable def ex511a : MDP ℝ ℝ where
  Γ := fun s => {a | s ≤ a ∧ a ≤ 2 ∧ a ≠ 0}
  P := fun _ => Kernel.deterministic Prod.fst measurable_fst
  u := fun _ x => 1 / x.2 + x.1
  uT := fun _ => 0
  β := 1 / 2

/-- **Example 5.1.1(a)** (Miao, p. 141), `s ∈ (0, 2]`: `V₀(s) = 1/s + s`, attained by `a* = s`.
-/
theorem example_5_1_1a_pos {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    V0 ex511a 1 s = ((1 / s + s : ℝ) : EReal) ∧
      IsOptimalPlan0 ex511a 1 s fun _ _ => s := by
  have hV : V0 ex511a 1 s = ((1 / s + s : ℝ) : EReal) := by
    rw [V0_one _ rfl]
    refine le_antisymm (iSup₂_le fun a ha => ?_) ?_
    · refine EReal.coe_le_coe_iff.2 ?_
      have : 1 / a ≤ 1 / s := one_div_le_one_div_of_le hs0 ha.1
      simp only [ex511a]
      linarith
    · exact le_iSup₂ (f := fun a (_ : a ∈ ex511a.Γ s) => (ex511a.u 0 (s, a) : EReal)) s
        ⟨le_rfl, hs2, hs0.ne'⟩
  refine ⟨hV, (feasible_one_iff _ s _).2 ⟨le_rfl, hs2, hs0.ne'⟩, ?_⟩
  rw [hV, J0T_one _ rfl]
  rfl

/-- **Example 5.1.1(a)** (Miao, p. 141), `s ≤ 0`: `V₀(s) = +∞` and no feasible plan attains the
supremum (the book states this for `s < 0`). -/
theorem example_5_1_1a_nonpos {s : ℝ} (hs : s ≤ 0) :
    V0 ex511a 1 s = ⊤ ∧ ∀ π, ¬ IsOptimalPlan0 ex511a 1 s π := by
  have hV : V0 ex511a 1 s = ⊤ := by
    rw [V0_one _ rfl]
    refine (EReal.eq_top_iff_forall_lt _).2 fun r => ?_
    set a : ℝ := 1 / (max (r - s) 0 + 1)
    have hpos : 0 < max (r - s) 0 + 1 := by positivity
    have ha0 : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      rw [div_le_one hpos]
      linarith [le_max_right (r - s) 0]
    refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun a (_ : a ∈ ex511a.Γ s) =>
      (ex511a.u 0 (s, a) : EReal)) a ⟨hs.trans ha0.le, by linarith, ha0.ne'⟩)
    refine EReal.coe_lt_coe_iff.2 ?_
    simp only [ex511a, a, one_div_one_div]
    linarith [le_max_left (r - s) 0]
  refine ⟨hV, fun π hπ => ?_⟩
  have h := hπ.2
  rw [hV] at h
  exact EReal.coe_ne_top _ h.symm

/-- Example 5.1.1(a) for `s > 2`: `Γ(s) = ∅` and `V₀(s) = −∞`. -/
theorem example_5_1_1a_empty {s : ℝ} (hs : 2 < s) : V0 ex511a 1 s = ⊥ := by
  rw [V0_one _ rfl]
  refine le_bot_iff.1 (iSup₂_le fun a ha => ?_)
  exact absurd (ha.1.trans ha.2.1) (not_le.2 hs)

/-- The problem of Example 5.1.1(b): `sup_{a ∈ (0, 1)} a`. -/
noncomputable def ex511b : MDP ℝ ℝ where
  Γ := fun _ => Set.Ioo 0 1
  P := fun _ => Kernel.deterministic Prod.fst measurable_fst
  u := fun _ x => x.2
  uT := fun _ => 0
  β := 1 / 2

/-- **Example 5.1.1(b)** (Miao, p. 141): `V₀(s) = 1` for every `s ∈ ℝ`, and no plan is
optimal. -/
theorem example_5_1_1b (s : ℝ) :
    V0 ex511b 1 s = 1 ∧ ∀ π, ¬ IsOptimalPlan0 ex511b 1 s π := by
  have hV : V0 ex511b 1 s = 1 := by
    rw [V0_one _ rfl]
    refine le_antisymm (iSup₂_le fun a ha => ?_) ?_
    · exact_mod_cast ha.2.le
    · refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
      by_contra hlt
      push Not at hlt
      have hz1 : z < 1 := by exact_mod_cast hlt
      have hm : max z 0 < 1 := max_lt hz1 one_pos
      set a := (max z 0 + 1) / 2
      have ha : a ∈ ex511b.Γ s := ⟨by positivity, by simp only [a]; linarith⟩
      have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (show z < a by
        simp only [a]; linarith [le_max_left z 0]))
        (le_iSup₂ (f := fun a (_ : a ∈ ex511b.Γ s) => (ex511b.u 0 (s, a) : EReal)) a ha)
      exact absurd hz (not_lt.2 this.le)
  refine ⟨hV, fun π hπ => ?_⟩
  have h := hπ.2
  rw [hV, J0T_one _ rfl] at h
  have h1 : (ex511b.u 0 (s, π 0 Fin.elim0)) = 1 := by exact_mod_cast h.symm
  have h2 := ((feasible_one_iff _ s π).1 hπ.1).2
  simp only [ex511b] at h1
  linarith

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Deterministic decision problems

Miao, p. 142: "This model includes deterministic decision problems as a special case." With the
deterministic kernels `P_{t+1}(s, a; B) = 1_B(f(s, a))` (`detKernel`), a plan determines a single
path `s_{t+1} = f(s_t, π_t(sᵗ))` (`detPath`); the history measure is the point mass at that path
(`mu_det`), and the objective (5.3) is the discounted sum of rewards along it (`J0T_det`), as
in a deterministic problem.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The path of a plan under the law of motion `s_{t+1} = f(s_t, π_t(sᵗ))`. -/
def detPath (f : S × A → S) (s₀ : S) (π : Plan S A) : (t : ℕ) → Fin t → S
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (detPath f s₀ π t) (f (lastState s₀ (detPath f s₀ π t), π t
      (detPath f s₀ π t)))

/-- Miao, p. 142: with deterministic kernels, `μᵗ(s₀, ·; π)` is the point mass at the path. -/
theorem mu_det (M : MDP S A) {f : S × A → S} (hf : Measurable f)
    (hMP : ∀ t, M.P t = detKernel hf) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j < t, Measurable (π j)) : mu M s₀ π t = Measure.dirac (detPath f s₀ π t) := by
  have hP : M.IsMarkov := fun t => by
    rw [hMP t]
    exact inferInstanceAs (IsMarkovKernel (Kernel.deterministic f hf))
  induction t with
  | zero => exact (mu_zero M s₀ π).trans (congrArg _ (Subsingleton.elim _ _))
  | succ t ih =>
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [mu_succ_lintegral M hP s₀ (hπ t (by omega)) hg, ih fun j hj => hπ j (by omega),
      lintegral_dirac' _ ?_, hMP t, detKernel, Kernel.deterministic_apply,
      lintegral_dirac' _ (f := fun s => g (Fin.snoc (detPath f s₀ π t) s))
        (hg.comp ((measurable_snoc t).comp (measurable_const.prodMk measurable_id))),
      lintegral_dirac' _ hg]
    · rfl
    · have := isMarkovKernel_stepKernel M hP s₀ (hπ t (by omega))
      have hm : Measurable fun h => ∫⁻ s, g (Fin.snoc h s) ∂stepKernel M s₀ π t h :=
        (hg.comp (measurable_snoc t)).lintegral_kernel_prod_right'
      simp only [stepKernel_apply M s₀ (hπ t (by omega))] at hm
      exact hm

/-- Miao, p. 142: with deterministic kernels, the objective (5.3) is the discounted sum of the
rewards along the path. -/
theorem J0T_det (M : MDP S A) {f : S × A → S} (hf : Measurable f)
    (hMP : ∀ t, M.P t = detKernel hf) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT)
    (s₀ : S) {T : ℕ} {π : Plan S A} (hπ : ∀ j < T, Measurable (π j)) :
    J0T M T s₀ π = ∑ t ∈ Finset.range T, M.β ^ t *
        M.u t (lastState s₀ (detPath f s₀ π t), π t (detPath f s₀ π t)) +
      M.β ^ T * M.uT (lastState s₀ (detPath f s₀ π T)) := by
  rw [J0T, mu_det M hf hMP s₀ hπ, integral_dirac' (fun h => M.uT (lastState s₀ h)) _
    (huT.comp (measurable_lastState s₀ T)).stronglyMeasurable]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [expRew, mu_det M hf hMP s₀ fun j hj => hπ j (by omega), integral_dirac' (rew M s₀ π t) _
    (measurable_rew M s₀ (hu t) (hπ t ht')).stronglyMeasurable]
  rfl

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Randomized actions

Miao, §5.1, pp. 142–143. The initial state is drawn from `P₀`; a date-`t` history is
`h_t = (s₀, a₀, …, a_{t−1}, s_t)`, here the pair `((s_j, a_j)_{j<t}, s_t)`; a randomized action is
a kernel `π_t(h_t; da)` from histories to actions (`RPlan`).

* `IsFeasibleR`: `π_t(h_t)(Γ(s_t)) = 1`. **Correction:** the book writes the measurability
  requirement as "`Γ(s) ∈ A`"; it should read `Γ(s) ∈ 𝒜` (each `Γ(s)` is a measurable subset of
  the action space), as `π_t(h_t)(Γ(s_t))` is otherwise undefined.
* `rmu M P₀ π t`: the measure `μ_t(ds₀, da₀, …, ds_{t−1}, da_{t−1}; π)` on `(S × A)ᵗ` of p. 143,
  built date by date: `s_t` from `P_t(s_{t−1}, a_{t−1}; ·)` (from `P₀` at `t = 0`), then
  `a_t ~ π_t(h_t; ·)`. `isProbabilityMeasure_rmu`: it is a probability measure.
* `detRPlan`: a deterministic plan as a randomized one, `π_t(h_t) = δ_{π_t(s₁, …, s_t)}`;
  `detRPlan_feasible_iff`: it is feasible exactly when the deterministic plan is
  (`π_t(sᵗ) ∈ Γ(s_t)` for all histories), so the deterministic model is the special case of the
  book's remark.

The infinite-horizon measure is obtained exactly as in `Trajectory` (Ionescu Tulcea); it is not
repeated here.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- A randomized plan: `π_t(((s_j, a_j)_{j<t}, s_t); ·)`, a probability on actions. -/
abbrev RPlan (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  (t : ℕ) → Kernel ((Fin t → S × A) × S) A

/-- Feasibility of a randomized plan (Miao, p. 142): `π_t(h_t)(Γ(s_t)) = 1`. -/
def IsFeasibleR (M : MDP S A) (π : RPlan S A) : Prop :=
  (∀ s, MeasurableSet (M.Γ s)) ∧ ∀ t h s, π t (h, s) (M.Γ s) = 1

/-- The kernel of the next state: `P₀` at date `0`, `P_t(s_{t−1}, a_{t−1}; ·)` after. -/
noncomputable def nextStateK (M : MDP S A) (P₀ : Measure S) :
    (t : ℕ) → Kernel (Fin t → S × A) S
  | 0 => Kernel.const _ P₀
  | t + 1 => (M.P t).comap (fun h => h (Fin.last t)) (measurable_pi_apply _)

/-- `μ_t(ds₀, da₀, …, ds_{t−1}, da_{t−1}; π)` (Miao, p. 143). -/
noncomputable def rmu (M : MDP S A) (P₀ : Measure S) (π : RPlan S A) :
    (t : ℕ) → Measure (Fin t → S × A)
  | 0 => Measure.dirac Fin.elim0
  | t + 1 => ((rmu M P₀ π t) ⊗ₘ (nextStateK M P₀ t ⊗ₖ π t)).map
      fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → S × A)

/-- Miao, p. 143: `μ_t(·; π)` is a probability measure. -/
theorem isProbabilityMeasure_rmu (M : MDP S A) (hP : M.IsMarkov) {P₀ : Measure S}
    [IsProbabilityMeasure P₀] {π : RPlan S A} (hπ : ∀ t, IsMarkovKernel (π t)) (t : ℕ) :
    IsProbabilityMeasure (rmu M P₀ π t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ t ih =>
    have hν : IsMarkovKernel (nextStateK M P₀ t) := by
      cases t with
      | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
      | succ t =>
        have := hP t
        exact inferInstanceAs (IsMarkovKernel (Kernel.comap (M.P t)
          (fun h : Fin (t + 1) → S × A => h (Fin.last t)) (measurable_pi_apply _)))
    have := hπ t
    exact inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The states `(s₁, …, s_t)` of a history `((s_j, a_j)_{j<t}, s_t)` (the deterministic plans of
Definition 5.1.1 depend only on these, `s₀` being known). -/
def statesOf : (t : ℕ) → (Fin t → S × A) → S → Fin t → S
  | 0, _, _ => Fin.elim0
  | t + 1, h, s => Fin.snoc (fun j : Fin t => (h j.succ).1) s

theorem measurable_statesOf (t : ℕ) :
    Measurable fun p : (Fin t → S × A) × S => statesOf t p.1 p.2 := by
  cases t with
  | zero => exact measurable_const
  | succ t =>
    exact (measurable_snoc t).comp ((measurable_pi_iff.2 fun j =>
      ((measurable_pi_apply _).comp measurable_fst).fst).prodMk measurable_snd)

/-- A deterministic plan as a randomized plan: `π_t(h_t) = δ_{π_t(s₁, …, s_t)}`. -/
noncomputable def detRPlan (π : Plan S A) (hπ : ∀ t, Measurable (π t)) : RPlan S A :=
  fun t => Kernel.deterministic (fun p => π t (statesOf t p.1 p.2))
    ((hπ t).comp (measurable_statesOf t))

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem lastState_statesOf (s₀ : S) (t : ℕ) (h : Fin t → S × A) (s : S) :
    lastState s₀ (statesOf t h s) = if t = 0 then s₀ else s := by
  cases t with
  | zero => rfl
  | succ t => simp [statesOf, lastState_snoc]

/-- Miao, p. 142: a deterministic plan is a feasible randomized plan exactly when it is a
feasible plan (here for `t ≥ 1`, and `π₀ ∈ Γ(s₀)` at `t = 0` when `P₀ = δ_{s₀}`): point masses
satisfy `δ_a(Γ(s)) = 1 ↔ a ∈ Γ(s)`. -/
theorem detRPlan_feasible_iff (M : MDP S A) (hΓ : ∀ s, MeasurableSet (M.Γ s)) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) :
    IsFeasibleR M (detRPlan π hπ) ↔
      ∀ t (h : Fin t → S × A) s, π t (statesOf t h s) ∈ M.Γ s := by
  simp only [IsFeasibleR, detRPlan, hΓ, implies_true, true_and]
  refine forall_congr' fun t => forall_congr' fun h => forall_congr' fun s => ?_
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (hΓ s)]
  simp [Set.indicator]

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discrete choice: Rust's replacement problem

Miao, §5.2.1, pp. 143–144. The state `s ≥ 0` is accumulated utilisation; the action `a = 0`
keeps the durable and `a = 1` replaces it. Utilisation grows by an exponential increment with
rate `λ`: `s_{t+1} = s_t + ε` after keeping, `s_{t+1} = ε` after replacing, `ε ~ Exp(λ)`
(`rustKernel`). The reward is `−c(s)` when keeping and `−(P_b − P_s) − c(0)` when replacing.

* `rust_cdf_keep`, `rust_cdf_replace`: the transition probabilities printed on p. 144,
  `P(s, 0; [s, x]) = 1 − exp(−λ(x − s))` and `P(s, 1; [0, x]) = 1 − exp(−λx)`.
  **Correction:** the book calls these the *densities* of the kernels; they are the
  distribution functions (the densities are `λ exp(−λ(x − s))` and `λ exp(−λx)`).
* `rust_nonneg`: the kernel keeps the state in `S = ℝ₊` (the model is set on `ℝ`, with
  `[0, ∞)` invariant; the book takes `S = ℝ₊`).
* `rust_assumptions`: with `c` measurable and bounded, the model satisfies Assumptions
  5.1.1, 5.1.2 (for `β ∈ (0, 1)`) and 5.1.4, and the kernels are stochastic kernels.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

/-- The state from which the next increment is added: `s` if kept, `0` if replaced. -/
def rustBase (x : ℝ × Fin 2) : ℝ := if x.2 = 0 then x.1 else 0

theorem measurable_rustBase : Measurable rustBase :=
  measurable_from_prod_countable_left fun a => by
    by_cases h : a = 0
    · simp only [rustBase, h, ↓reduceIte]
      exact measurable_id
    · simp only [rustBase, h, ↓reduceIte]
      exact measurable_const

theorem measurable_rustNext : Measurable fun p : (ℝ × Fin 2) × ℝ => rustBase p.1 + p.2 :=
  (measurable_rustBase.comp measurable_fst).add measurable_snd

/-- The kernel `P(s, a; ·)`: the law of `rustBase(s, a) + ε`, `ε ~ Exp(λ)`. -/
noncomputable def rustKernel (lam : ℝ) : Kernel (ℝ × Fin 2) ℝ :=
  pushKernel (Kernel.const _ (expMeasure lam)) fun p => rustBase p.1 + p.2

/-- Rust's replacement problem (Miao, §5.2.1). -/
noncomputable def rust (lam β Pb Ps : ℝ) (c : ℝ → ℝ) : MDP ℝ (Fin 2) where
  Γ := fun _ => Set.univ
  P := fun _ => rustKernel lam
  u := fun _ x => if x.2 = 0 then -c x.1 else -(Pb - Ps) - c 0
  uT := fun _ => 0
  β := β

theorem rustKernel_apply {lam : ℝ} (hl : 0 < lam) (x : ℝ × Fin 2) {B : Set ℝ}
    (hB : MeasurableSet B) :
    rustKernel lam x B = expMeasure lam ((fun e => rustBase x + e) ⁻¹' B) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [rustKernel, pushKernel_apply _ measurable_rustNext, Kernel.const_apply]
  exact Measure.map_apply (f := fun e => rustBase x + e) (measurable_const_add _) hB

theorem expMeasure_Iic {lam : ℝ} (hl : 0 < lam) (y : ℝ) :
    expMeasure lam (Set.Iic y) =
      ENNReal.ofReal (if 0 ≤ y then 1 - Real.exp (-(lam * y)) else 0) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [← ofReal_cdf, cdf_expMeasure_eq hl]

/-- Miao, p. 144 (corrected: a distribution function, not a density): after keeping,
`P(s, 0; (−∞, x]) = 1 − exp(−λ(x − s))` for `x ≥ s`, and `0` for `x < s`. -/
theorem rust_cdf_keep {lam : ℝ} (hl : 0 < lam) (s x : ℝ) :
    rustKernel lam (s, 0) (Set.Iic x) =
      ENNReal.ofReal (if s ≤ x then 1 - Real.exp (-(lam * (x - s))) else 0) := by
  rw [rustKernel_apply hl _ measurableSet_Iic]
  have : (fun e => rustBase (s, 0) + e) ⁻¹' Set.Iic x = Set.Iic (x - s) := by
    ext e
    simp only [rustBase, ↓reduceIte, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [this, expMeasure_Iic hl]
  simp only [sub_nonneg]

/-- Miao, p. 144 (corrected: a distribution function, not a density): after replacing,
`P(s, 1; (−∞, x]) = 1 − exp(−λx)` for `x ≥ 0`, and `0` for `x < 0`. -/
theorem rust_cdf_replace {lam : ℝ} (hl : 0 < lam) (s x : ℝ) :
    rustKernel lam (s, 1) (Set.Iic x) =
      ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(lam * x)) else 0) := by
  rw [rustKernel_apply hl _ measurableSet_Iic]
  have : (fun e => rustBase (s, 1) + e) ⁻¹' Set.Iic x = Set.Iic x := by
    ext e
    simp [rustBase]
  rw [this, expMeasure_Iic hl]

/-- The state space `ℝ₊` is invariant: from `s ≥ 0`, the next state is `≥ 0` almost surely. -/
theorem rust_nonneg {lam : ℝ} (hl : 0 < lam) {s : ℝ} (hs : 0 ≤ s) (a : Fin 2) :
    rustKernel lam (s, a) (Set.Iio 0) = 0 := by
  rw [rustKernel_apply hl _ measurableSet_Iio]
  have hb : 0 ≤ rustBase (s, a) := by
    unfold rustBase
    split_ifs
    · exact hs
    · exact le_rfl
  refine le_antisymm ?_ (zero_le)
  calc expMeasure lam ((fun e => rustBase (s, a) + e) ⁻¹' Set.Iio 0)
      ≤ expMeasure lam (Set.Iic 0) := measure_mono fun e he => by
        simp only [Set.mem_preimage, Set.mem_Iio] at he
        exact Set.mem_Iic.2 (by linarith)
    _ = 0 := by rw [expMeasure_Iic hl]; simp

/-- Miao, §5.2.1: Rust's model satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when `c` is
measurable and bounded and `β ∈ (0, 1)`. -/
theorem rust_assumptions {lam β Pb Ps C : ℝ} {c : ℝ → ℝ} (hl : 0 < lam) (hc : Measurable c)
    (hC : ∀ s, |c s| ≤ C) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (rust lam β Pb Ps c).IsMarkov ∧ HasMeasurableSelection (rust lam β Pb Ps c).Γ ∧
      Assumption512 (rust lam β Pb Ps c) ∧ Assumption514 (rust lam β Pb Ps c) := by
  have hP : (rust lam β Pb Ps c).IsMarkov := fun _ => by
    have := isProbabilityMeasure_expMeasure hl
    exact isMarkovKernel_pushKernel _ measurable_rustNext
  refine ⟨hP, ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩, ⟨hβ0, hβ1⟩,
    assumption_5_1_4_of_bounded hP (fun _ => ⟨rfl, rfl⟩) (B := |Pb - Ps| + C) ?_ ?_ hβ0.le hβ1⟩
  · intro t x
    have h0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    simp only [rust]
    split_ifs
    · rw [abs_neg]
      linarith [hC x.1, abs_nonneg (Pb - Ps)]
    · calc |-(Pb - Ps) - c 0| ≤ |-(Pb - Ps)| + |c 0| := abs_sub _ _
        _ ≤ |Pb - Ps| + C := by rw [abs_neg]; linarith [hC 0]
  · intro t
    refine measurable_from_prod_countable_left fun a => ?_
    by_cases h : a = 0
    · simp only [rust, h, ↓reduceIte]
      exact hc.neg
    · simp only [rust, h, ↓reduceIte]
      exact measurable_const

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal stopping as a Markov decision problem

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of optimal stopping problems

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The probabilities of the secretary problem

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The bandit model

Miao, §5.2.3, pp. 149–152, and Exercise 5.4, p. 155. `k` arms with state spaces `X i` and
transition functions `Q^i_{t+1}` (`Bandit.Q i t`); choosing arm `i` pays `u^i_t(s^i_t)`, moves
arm `i` by `Q^i_{t+1}` and freezes the others (`armKernel`). The MDP has state space
`S = X 1 × ⋯ × X k`, actions `A = {1, …, k}` (here `Fin k`) and `Γ(s) = A` (`Bandit.toMDP`).

* `bandit_P_apply`, `bandit_P_rect`: `P_{t+1}(s, i; ·)` is the law of `s` with its `i`-th
  coordinate redrawn from `Q^i_{t+1}(s^i, ·)`; on the sets `{s¹} × ⋯ × Bⁱ × ⋯ × {sᵏ}` of the
  book it is `Q^i_{t+1}(s^i, Bⁱ)` (`bandit_P_rect` uses `{x : xⁱ ∈ Bⁱ}`, which has the same
  measure because the other coordinates are frozen, `bandit_P_frozen`).
* **Correction.** The book adds "`P_{t+1}(s, i; B) = 0` for all other `B`" (p. 150). Taken
  literally this is false: `B = S` is not of the displayed form but has probability one
  (`bandit_book_false`). The correct statement is that `P_{t+1}(s, i; B) = 0` for every
  measurable `B` disjoint from the fibre `{x : xʲ = sʲ for j ≠ i}` (`bandit_P_frozen`).
* `bandit_assumptions`: stochastic kernels, Assumption 5.1.1, and with bounded measurable
  rewards Assumptions 5.1.3 and (stationary, `β < 1`) 5.1.4.
* **A constant arm makes the bandit a stopping problem** (p. 151), proved for a deterministic
  stochastic arm (`ex_bandit_constant_arm`): for any sequence of arm choices over `T` periods
  there is a retirement date `K` such that playing the risky arm `K` times and then the constant
  arm forever does at least as well. The key step is that playing the constant arm once and then
  `K` times the risky arm is the convex combination `β·R_K + (1 − β)·R_0` of two retirement
  payoffs (`retirePay_shift`). (For a stochastic risky arm the same interchange applies along
  each path, but turning it into an inequality between values requires the dynamic programming
  results of Chapters 6–7 and is not formalised.)
* Task selection (p. 151): `taskSelection` with `u^i(s) = R_i p_i(C | s)` on `S_i = [0, 1]`
  (`taskSelection_assumptions`).
* **Exercise 5.4** (Pandora's problem as a bandit): `pandora` (`ex_5_4`, `ex_5_4_collect`).
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {k : ℕ} {X : Fin k → Type*} [∀ i, MeasurableSpace (X i)]

/-- The data of a bandit problem with `k` arms (Miao, p. 150). -/
structure Bandit (k : ℕ) (X : Fin k → Type*) [∀ i, MeasurableSpace (X i)] where
  Q : (i : Fin k) → ℕ → Kernel (X i) (X i)
  r : (i : Fin k) → ℕ → X i → ℝ
  β : ℝ

/-- The kernel of the bandit after choosing arm `i`: redraw `sⁱ` from `Q^i_{t+1}(sⁱ, ·)`, keep
the other coordinates. -/
noncomputable def armKernel (i : Fin k) (Q : Kernel (X i) (X i)) :
    Kernel ((j : Fin k) → X j) ((j : Fin k) → X j) :=
  pushKernel (Q.comap (fun s => s i) (measurable_pi_apply i)) fun p => Function.update p.1 i p.2

/-- The bandit model as a Markov decision process (Miao, p. 150). -/
noncomputable def Bandit.toMDP (b : Bandit k X) : MDP ((j : Fin k) → X j) (Fin k) where
  Γ := fun _ => Set.univ
  P := fun t => famKernel fun i => armKernel i (b.Q i t)
  u := fun t x => b.r x.2 t (x.1 x.2)
  uT := fun _ => 0
  β := b.β

theorem armKernel_apply (i : Fin k) (Q : Kernel (X i) (X i)) [IsMarkovKernel Q]
    (s : (j : Fin k) → X j) : armKernel i Q s = (Q (s i)).map (Function.update s i) :=
  pushKernel_apply _ measurable_update' s

/-- Miao, p. 150: after choosing arm `i`, `P_{t+1}(s, i; C) = Q^i_{t+1}(sⁱ, {y : (s with sⁱ := y)
∈ C})`. -/
theorem bandit_P_apply (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {C : Set ((j : Fin k) → X j)} (hC : MeasurableSet C) :
    b.toMDP.P t (s, i) C = b.Q i t (s i) (Function.update s i ⁻¹' C) := by
  change armKernel i (b.Q i t) s C = _
  rw [armKernel_apply, Measure.map_apply (measurable_update s) hC]

/-- Miao, p. 150: the chosen arm moves by its own transition function,
`P_{t+1}(s, i; {x : xⁱ ∈ Bⁱ}) = Q^i_{t+1}(sⁱ, Bⁱ)`. -/
theorem bandit_P_rect (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {B : Set (X i)} (hB : MeasurableSet B) :
    b.toMDP.P t (s, i) ((fun x => x i) ⁻¹' B) = b.Q i t (s i) B := by
  rw [bandit_P_apply b s (measurable_pi_apply i hB)]
  congr 1
  ext y
  simp

/-- **Correction to Miao, p. 150.** The other arms are frozen: `P_{t+1}(s, i; B) = 0` for every
measurable `B` that contains no point `x` with `xʲ = sʲ` for all `j ≠ i`. -/
theorem bandit_P_frozen (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {B : Set ((j : Fin k) → X j)} (hB : MeasurableSet B)
    (hdisj : ∀ x ∈ B, ∃ j ≠ i, x j ≠ s j) : b.toMDP.P t (s, i) B = 0 := by
  rw [bandit_P_apply b s hB]
  have : Function.update s i ⁻¹' B = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨j, hji, hj⟩ := hdisj _ hy
    exact hj (Function.update_of_ne hji _ _)
  rw [this, measure_empty]

/-- **Correction to Miao, p. 150** (counterexample). With two arms on `Bool` (each moving
deterministically), the whole state space `B = S` is not of the form
`{x : x⁰ ∈ B⁰, x¹ = s¹}` used by the book, yet `P(s, 0; S) = 1 ≠ 0`. -/
theorem bandit_book_false (s : Fin 2 → Bool) :
    (¬ ∃ B : Set Bool, (Set.univ : Set (Fin 2 → Bool)) = {x | x 0 ∈ B ∧ x 1 = s 1}) ∧
      (⟨fun _ _ => Kernel.id, fun _ _ _ => 0, 1 / 2⟩ : Bandit 2 fun _ => Bool).toMDP.P 0 (s, 0)
        Set.univ = 1 := by
  refine ⟨fun ⟨B, hB⟩ => ?_, ?_⟩
  · have hmem : (fun j : Fin 2 => if j = 1 then !s 1 else s 0) ∈
        (Set.univ : Set (Fin 2 → Bool)) := Set.mem_univ _
    rw [hB] at hmem
    have h := hmem.2
    simp at h
  · have : IsMarkovKernel (armKernel (X := fun _ : Fin 2 => Bool) 0 Kernel.id) := by
      unfold armKernel
      exact isMarkovKernel_pushKernel _ measurable_update'
    change (armKernel (X := fun _ : Fin 2 => Bool) 0 Kernel.id) s Set.univ = 1
    exact measure_univ

theorem bandit_isMarkov (b : Bandit k X) (hQ : ∀ i t, IsMarkovKernel (b.Q i t)) :
    b.toMDP.IsMarkov := fun t => by
  change IsMarkovKernel (famKernel fun i => armKernel i (b.Q i t))
  refine isMarkovKernel_famKernel fun i => ?_
  have := hQ i t
  unfold armKernel
  exact isMarkovKernel_pushKernel _ measurable_update'

/-- The bandit MDP satisfies the assumptions of §5.1: stochastic kernels, Assumption 5.1.1, and
with rewards bounded by `B` and measurable, Assumption 5.1.3 for every horizon and, when the arms
are time-homogeneous and `0 ≤ β < 1`, Assumption 5.1.4. -/
theorem bandit_assumptions (b : Bandit k X) (hQ : ∀ i t, IsMarkovKernel (b.Q i t))
    (hr : ∀ i t, Measurable (b.r i t)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i t x, |b.r i t x| ≤ B) :
    b.toMDP.IsMarkov ∧ (k ≠ 0 → HasMeasurableSelection b.toMDP.Γ) ∧
      (∀ T, Assumption513 b.toMDP T) ∧
      ((∀ i t, b.Q i t = b.Q i 0 ∧ b.r i t = b.r i 0) → 0 ≤ b.β → b.β < 1 →
        Assumption514 b.toMDP) := by
  have hP := bandit_isMarkov b hQ
  have hu : ∀ t x, |b.toMDP.u t x| ≤ B := fun t x => hB _ _ _
  have hmu : ∀ t, Measurable (b.toMDP.u t) := fun t =>
    measurable_from_prod_countable_left fun i => (hr i t).comp (measurable_pi_apply i)
  refine ⟨hP, fun hk => ⟨fun _ => ⟨0, Nat.pos_of_ne_zero hk⟩, measurable_const,
    fun _ => Set.mem_univ _⟩, fun T => assumption_5_1_3_of_bounded hP ⟨hu, fun _ => by
      simpa [Bandit.toMDP] using hB0⟩ hmu measurable_const T,
    fun hst hβ0 hβ1 => assumption_5_1_4_of_bounded hP (fun t => ?_) hu hmu hβ0 hβ1⟩
  have h1 : (fun i => b.Q i t) = fun i => b.Q i 0 := funext fun i => (hst i t).1
  have h2 : (fun i => b.r i t) = fun i => b.r i 0 := funext fun i => (hst i t).2
  refine ⟨?_, ?_⟩
  · change (famKernel fun i => armKernel i (b.Q i t)) = famKernel fun i => armKernel i (b.Q i 0)
    simp only [(hst _ t).1]
  · change (fun x : ((j : Fin k) → X j) × Fin k => b.r x.2 t (x.1 x.2)) =
      fun x => b.r x.2 0 (x.1 x.2)
    simp only [(hst _ t).2]

/-- The payoff of a sequence of arm choices in the two-armed bandit with a constant arm: `a = 0`
plays the risky arm, whose rewards in the order they are drawn are `r 0, r 1, …`; `a = 1` plays
the constant arm, paying `c` and leaving the risky arm frozen. -/
def banditPay (β c : ℝ) : (T : ℕ) → (ℕ → Fin 2) → (ℕ → ℝ) → ℝ
  | 0, _, _ => 0
  | T + 1, a, r => if a 0 = 0 then r 0 + β * banditPay β c T (a ∘ Nat.succ) (r ∘ Nat.succ)
      else c + β * banditPay β c T (a ∘ Nat.succ) r

/-- The payoff of retiring at `K`: the risky arm for `K` periods, then the constant arm. -/
def retirePay (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, β ^ j * r j +
    c * (∑ j ∈ Finset.range T, β ^ j - ∑ j ∈ Finset.range K, β ^ j)

/-- Retirement at `K`: the action sequence `0, …, 0, 1, 1, …`. -/
def retireSeq (K : ℕ) (t : ℕ) : Fin 2 := if t < K then 0 else 1

theorem geom_succ (β : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), β ^ j = 1 + β * ∑ j ∈ Finset.range n, β ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem retirePay_succ (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) :
    retirePay β c (T + 1) r (K + 1) = r 0 + β * retirePay β c T (r ∘ Nat.succ) K := by
  simp only [retirePay, geom_succ]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Function.comp_apply]
  have : ∑ j ∈ Finset.range K, β ^ (j + 1) * r (j + 1) =
      β * ∑ j ∈ Finset.range K, β ^ j * r (j + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- Playing the constant arm first and then retiring at `K` is the convex combination
`β·R_K + (1 − β)·R_0` of retirement payoffs. -/
theorem retirePay_shift (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) :
    c + β * retirePay β c T r K =
      β * retirePay β c (T + 1) r K + (1 - β) * retirePay β c (T + 1) r 0 := by
  simp only [retirePay, geom_succ, Finset.range_zero, Finset.sum_empty]
  ring

theorem banditPay_retireSeq (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) {K : ℕ} (hK : K ≤ T) :
    banditPay β c T (retireSeq K) r = retirePay β c T r K := by
  induction T generalizing K r with
  | zero =>
    have : K = 0 := by omega
    subst this
    simp [banditPay, retirePay]
  | succ T ih =>
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      have hseq : retireSeq 0 ∘ Nat.succ = retireSeq 0 := funext fun t => by simp [retireSeq]
      have h0 : retireSeq 0 0 ≠ 0 := by simp [retireSeq]
      simp only [banditPay, h0, ↓reduceIte, hseq, ih r (Nat.zero_le T)]
      simp only [retirePay, geom_succ, Finset.range_zero, Finset.sum_empty]
      ring
    · obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hseq : retireSeq (K' + 1) ∘ Nat.succ = retireSeq K' := funext fun t => by
        simp only [retireSeq, Function.comp_apply]
        split_ifs <;> omega
      have h0 : retireSeq (K' + 1) 0 = 0 := by simp [retireSeq]
      simp only [banditPay, h0, ↓reduceIte, hseq]
      rw [ih _ (by omega), retirePay_succ]

/-- **The two-armed bandit with a constant arm is an optimal stopping problem** (Miao, p. 151),
for a deterministic risky arm with reward sequence `r` and `β ∈ [0, 1]`: every sequence of arm
choices is weakly dominated by a retirement rule, so the best payoff is attained by stopping. -/
theorem ex_bandit_constant_arm {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (c : ℝ) (T : ℕ)
    (a : ℕ → Fin 2) (r : ℕ → ℝ) :
    ∃ K ≤ T, banditPay β c T a r ≤ banditPay β c T (retireSeq K) r := by
  suffices h : ∃ K ≤ T, banditPay β c T a r ≤ retirePay β c T r K by
    obtain ⟨K, hK, h⟩ := h
    exact ⟨K, hK, h.trans_eq (banditPay_retireSeq β c T r hK).symm⟩
  induction T generalizing a r with
  | zero => exact ⟨0, le_rfl, by simp [banditPay, retirePay]⟩
  | succ T ih =>
    by_cases ha : a 0 = 0
    · obtain ⟨K, hK, h⟩ := ih (a ∘ Nat.succ) (r ∘ Nat.succ)
      refine ⟨K + 1, by omega, ?_⟩
      simp only [banditPay, ha, ↓reduceIte]
      rw [retirePay_succ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hβ0)
    · obtain ⟨K, hK, h⟩ := ih (a ∘ Nat.succ) r
      have hpay : banditPay β c (T + 1) a r ≤
          β * retirePay β c (T + 1) r K + (1 - β) * retirePay β c (T + 1) r 0 := by
        simp only [banditPay, ha, ↓reduceIte]
        rw [← retirePay_shift]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hβ0)
      rcases le_total (retirePay β c (T + 1) r 0) (retirePay β c (T + 1) r K) with hle | hle
      · refine ⟨K, by omega, hpay.trans ?_⟩
        nlinarith
      · refine ⟨0, by omega, hpay.trans ?_⟩
        nlinarith

/-- The task selection problem (Miao, p. 151): `k` tasks with completion states in `[0, 1]`,
reward `u^i(s) = R_i p_i(C | s)` when working on task `i`. -/
def taskSelection (Q : (i : Fin k) → Kernel (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1))
    (R : Fin k → ℝ) (p : Fin k → Set.Icc (0 : ℝ) 1 → ℝ) (β : ℝ) :
    Bandit k fun _ => Set.Icc (0 : ℝ) 1 where
  Q := fun i _ => Q i
  r := fun i _ s => R i * p i s
  β := β

/-- The task selection problem satisfies Assumptions 5.1.1 and 5.1.4 (for `k ≥ 1`,
probabilities `p_i ∈ [0, 1]` measurable, `β ∈ [0, 1)`). -/
theorem taskSelection_assumptions {Q : (i : Fin k) → Kernel (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)}
    (hQ : ∀ i, IsMarkovKernel (Q i)) {R : Fin k → ℝ} {p : Fin k → Set.Icc (0 : ℝ) 1 → ℝ}
    (hp : ∀ i, Measurable (p i)) (hp01 : ∀ i s, 0 ≤ p i s ∧ p i s ≤ 1) (hk : k ≠ 0) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (taskSelection Q R p β).toMDP.IsMarkov ∧
      HasMeasurableSelection (taskSelection Q R p β).toMDP.Γ ∧
      Assumption514 (taskSelection Q R p β).toMDP := by
  have hB : ∀ i t x, |(taskSelection Q R p β).r i t x| ≤ ∑ j, |R j| := by
    intro i t x
    simp only [taskSelection, abs_mul]
    calc |R i| * |p i x| ≤ |R i| * 1 := mul_le_mul_of_nonneg_left
          (by rw [abs_of_nonneg (hp01 i x).1]; exact (hp01 i x).2) (abs_nonneg _)
      _ ≤ ∑ j, |R j| := by
          rw [mul_one]
          exact Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)
  obtain ⟨h1, h2, -, h4⟩ := bandit_assumptions (taskSelection Q R p β) (fun i _ => hQ i)
    (fun i _ => measurable_const.mul (hp i)) (Finset.sum_nonneg fun j _ => abs_nonneg _) hB
  exact ⟨h1, h2 hk, h4 (fun _ _ => ⟨rfl, rfl⟩) hβ0 hβ1⟩

/-- The transitions of a box in Pandora's problem: a closed box (`Sum.inl ()`) is opened and its
prize `y ~ F` revealed; an open box (`Sum.inr y`) stays as it is. -/
noncomputable def pandoraKernel {Y : Type*} [MeasurableSpace Y] (F : Measure Y) :
    Kernel (Unit ⊕ Y) (Unit ⊕ Y) where
  toFun := Sum.elim (fun _ => F.map Sum.inr) fun y => Measure.dirac (Sum.inr y)
  measurable' := measurable_const.sumElim (Measure.measurable_dirac.comp measurable_inr)

/-- **Exercise 5.4** (Miao, p. 155): Pandora's problem as a bandit. Box `i` is an arm with
states "closed" and "open with prize `y`"; pulling a closed box costs `cᵢ` and reveals
`y ~ Fᵢ`; pulling an open box with prize `y` pays `(1 − β) vᵢ(y)` and leaves it unchanged, so
that collecting the prize (pulling it forever) is worth `vᵢ(y)` (`ex_5_4_collect`). The outside
option `x₀` is an arm that starts open. Departures: a common discount factor `β` (the book's
`βᵢ = e^{−r tᵢ}` allows box-specific delays, which a bandit with one discount factor cannot
express without a time change), and "collect and stop" is represented by retiring on the open
box. -/
noncomputable def pandora {Y : Fin k → Type*} [∀ i, MeasurableSpace (Y i)]
    (F : (i : Fin k) → Measure (Y i)) (c : Fin k → ℝ) (v : (i : Fin k) → Y i → ℝ) (β : ℝ) :
    Bandit k fun i => Unit ⊕ Y i where
  Q := fun i _ => pandoraKernel (F i)
  r := fun i _ => Sum.elim (fun _ => -c i) fun y => (1 - β) * v i y
  β := β

/-- **Exercise 5.4**: collecting a prize of value `v` from an open box is worth `v`:
`∑ βᵗ (1 − β) v = v`. -/
theorem ex_5_4_collect {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : ℝ) :
    HasSum (fun t : ℕ => β ^ t * ((1 - β) * v)) v := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right ((1 - β) * v)
  have hne : (1 - β) ≠ 0 := by linarith
  convert h using 1
  field_simp

/-- **Exercise 5.4**: with probability distributions `Fᵢ`, measurable bounded prize values and
`β ∈ (0, 1)`, Pandora's bandit satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4. -/
theorem ex_5_4 {Y : Fin k → Type*} [∀ i, MeasurableSpace (Y i)]
    {F : (i : Fin k) → Measure (Y i)} (hF : ∀ i, IsProbabilityMeasure (F i)) (c : Fin k → ℝ)
    {v : (i : Fin k) → Y i → ℝ} (hv : ∀ i, Measurable (v i)) {B : ℝ}
    (hB : ∀ i y, |v i y| ≤ B) (hk : k ≠ 0) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (pandora F c v β).toMDP.IsMarkov ∧ HasMeasurableSelection (pandora F c v β).toMDP.Γ ∧
      Assumption512 (pandora F c v β).toMDP ∧ Assumption514 (pandora F c v β).toMDP := by
  have hQ : ∀ i t, IsMarkovKernel ((pandora F c v β).Q i t) := by
    intro i t
    refine ⟨fun x => ?_⟩
    have := hF i
    cases x with
    | inl _ => exact inferInstanceAs (IsProbabilityMeasure ((F i).map Sum.inr))
    | inr y => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  have hb : ∀ i t x, |(pandora F c v β).r i t x| ≤ ∑ j, |c j| + max B 0 := by
    intro i t x
    have hc : |c i| ≤ ∑ j, |c j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
    have hs : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    cases x with
    | inl _ =>
      simp only [pandora, Sum.elim_inl, abs_neg]
      linarith [le_max_right B 0]
    | inr y =>
      simp only [pandora, Sum.elim_inr, abs_mul]
      have h1 : |1 - β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 : |v i y| ≤ max B 0 := (hB i y).trans (le_max_left _ _)
      nlinarith [abs_nonneg (1 - β), abs_nonneg (v i y), le_max_right B 0]
  obtain ⟨h1, h2, -, h4⟩ := bandit_assumptions (pandora F c v β) hQ
    (fun i _ => measurable_const.sumElim (measurable_const.mul (hv i)))
    (add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (le_max_right B 0)) hb
  exact ⟨h1, h2 hk, ⟨hβ0, hβ1⟩, h4 (fun _ _ => ⟨rfl, rfl⟩) hβ0.le hβ1⟩

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The optimal control model

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

namespace Miao.MarkovDecisionProcesses

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

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 5.5 and 5.6: control problems

Miao, Exercises 5.5–5.6, pp. 155–156.

* `reparam_*`: changing the control variables. If a state-dependent map `Φ(s, ·)` sends the
  feasible actions of one MDP into those of another, with the same kernels and rewards, then
  plans correspond (`reparamPlan`), with equal objectives (`J0T_reparam`, `J_reparam`); with maps
  both ways the value functions agree (`V0_reparam`, `V_reparam`).
* **Exercise 5.5** (stochastic Ramsey model). `ramsey1` uses the controls `(C, I, N)` with
  `C + I = zF(K, N)` and `K′ = (1 − δ)K + I`; `ramsey2` uses `(K′, N)` with
  `C = zF(K, N) + (1 − δ)K − K′`. `ex_5_5`: `(C, I, N) ↦ ((1 − δ)K + I, N)` is a bijection of the
  feasible sets, and the two formulations have the same objectives and value functions, for
  every horizon. `ex_5_5_assumptions`: with `z, F ≥ 0`, `δ ≤ 1` and bounded measurable
  utility, the `(K′, N)` formulation satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4.
  **Correction:** the book writes `F : ℝ₊ → ℝ`; the production function has two arguments,
  `F(K, N)`. The capital stock lives in `ℝ₊` (`NNReal`), the law of motion is truncated at `0`
  off the feasible set (where it plays no role).
* **Exercise 5.6** (inventory management). `inventory`: inventory `x ≥ 0`, an exogenous Markov
  state `z` with demand `d(z) ∈ [0, D]`, orders `q ∈ [0, max(x̄ − x, 0)]` (storage capacity
  `x̄`), sales `min(x + q, d(z))`, next inventory `x + q − sales`; profit = revenue − fixed and
  variable ordering cost − holding cost. `ex_5_6`: Assumptions 5.1.1, 5.1.2 and 5.1.4 hold.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {S A₁ A₂ : Type*} [MeasurableSpace S] [MeasurableSpace A₁] [MeasurableSpace A₂]

/-- `Φ(s, ·)` maps the feasible actions of `M₁` to feasible actions of `M₂` with the same
transition kernels and rewards (and `M₁`, `M₂` share the terminal reward and discount factor). -/
def ReparamOK (M₁ : MDP S A₁) (M₂ : MDP S A₂) (Φ : S × A₁ → A₂) : Prop :=
  (∀ s a, a ∈ M₁.Γ s → Φ (s, a) ∈ M₂.Γ s) ∧
    (∀ t s a, a ∈ M₁.Γ s → M₂.P t (s, Φ (s, a)) = M₁.P t (s, a) ∧
      M₂.u t (s, Φ (s, a)) = M₁.u t (s, a)) ∧ M₂.uT = M₁.uT ∧ M₂.β = M₁.β

/-- The plan of `M₂` corresponding to a plan of `M₁`. -/
def reparamPlan (Φ : S × A₁ → A₂) (s₀ : S) (π : Plan S A₁) : Plan S A₂ :=
  fun t h => Φ (lastState s₀ h, π t h)

theorem reparam_feasible {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} (hΦ : Measurable Φ)
    (hok : ReparamOK M₁ M₂ Φ) {T : ℕ∞} {s₀ : S} {π : Plan S A₁}
    (hπ : π ∈ feasiblePlans M₁ T s₀) : reparamPlan Φ s₀ π ∈ feasiblePlans M₂ T s₀ :=
  ⟨fun t ht => hΦ.comp ((measurable_lastState s₀ t).prodMk (hπ.1 t ht)),
    fun t ht h => hok.1 _ _ (hπ.2 t ht h)⟩

theorem mu_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} (hΦ : Measurable Φ)
    (hok : ReparamOK M₁ M₂ Φ) {T : ℕ∞} {s₀ : S} {π : Plan S A₁}
    (hπ : π ∈ feasiblePlans M₁ T s₀) :
    ∀ t : ℕ, (t : ℕ∞) ≤ T → mu M₂ s₀ (reparamPlan Φ s₀ π) t = mu M₁ s₀ π t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hlt : (t : ℕ∞) < T := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) ht
    have hk : stepKernel M₂ s₀ (reparamPlan Φ s₀ π) t = stepKernel M₁ s₀ π t := by
      ext h : 1
      rw [stepKernel_apply M₂ s₀ ((reparam_feasible hΦ hok hπ).1 t hlt),
        stepKernel_apply M₁ s₀ (hπ.1 t hlt)]
      exact (hok.2.1 t _ _ (hπ.2 t hlt h)).1
    simp only [mu, ih hlt.le, hk]

theorem rew_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂}
    (hok : ReparamOK M₁ M₂ Φ) {T : ℕ∞} {s₀ : S} {π : Plan S A₁}
    (hπ : π ∈ feasiblePlans M₁ T s₀) {t : ℕ} (ht : (t : ℕ∞) < T) :
    rew M₂ s₀ (reparamPlan Φ s₀ π) t = rew M₁ s₀ π t :=
  funext fun h => (hok.2.1 t _ _ (hπ.2 t ht h)).2

/-- Equal objectives (5.3) for corresponding plans. -/
theorem J0T_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} (hΦ : Measurable Φ)
    (hok : ReparamOK M₁ M₂ Φ) {T : ℕ} {s₀ : S} {π : Plan S A₁}
    (hπ : π ∈ feasiblePlans M₁ T s₀) :
    J0T M₂ T s₀ (reparamPlan Φ s₀ π) = J0T M₁ T s₀ π := by
  rw [J0T, J0T, hok.2.2.2, hok.2.2.1, mu_reparam hΦ hok hπ T le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : (t : ℕ∞) < T := by exact_mod_cast Finset.mem_range.1 ht
  rw [expRew, expRew, rew_reparam hok hπ ht', mu_reparam hΦ hok hπ t ht'.le]

/-- Equal objectives (5.4) for corresponding plans. -/
theorem J_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} (hΦ : Measurable Φ)
    (hok : ReparamOK M₁ M₂ Φ) {s₀ : S} {π : Plan S A₁} (hπ : π ∈ feasiblePlans M₁ ⊤ s₀) :
    J M₂ s₀ (reparamPlan Φ s₀ π) = J M₁ s₀ π := by
  have e : partialSum M₂ s₀ (reparamPlan Φ s₀ π) = partialSum M₁ s₀ π := by
    funext n
    rw [partialSum, partialSum, hok.2.2.2]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [expRew, expRew, rew_reparam hok hπ (WithTop.coe_lt_top t),
      mu_reparam hΦ hok hπ t le_top]
  rw [J, J, e]

/-- With reparametrisations both ways, the value functions (5.5) agree. -/
theorem V0_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} {Ψ : S × A₂ → A₁}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (h₁ : ReparamOK M₁ M₂ Φ) (h₂ : ReparamOK M₂ M₁ Ψ)
    (T : ℕ) (s : S) : V0 M₁ T s = V0 M₂ T s := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun π hπ => ?_)
  · rw [← J0T_reparam hΦ h₁ hπ]
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M₂ T s) => (J0T M₂ T s π : EReal)) _
      (reparam_feasible hΦ h₁ hπ)
  · rw [← J0T_reparam hΨ h₂ hπ]
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M₁ T s) => (J0T M₁ T s π : EReal)) _
      (reparam_feasible hΨ h₂ hπ)

/-- With reparametrisations both ways, the value functions (5.6) agree. -/
theorem V_reparam {M₁ : MDP S A₁} {M₂ : MDP S A₂} {Φ : S × A₁ → A₂} {Ψ : S × A₂ → A₁}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (h₁ : ReparamOK M₁ M₂ Φ) (h₂ : ReparamOK M₂ M₁ Ψ)
    (s : S) : V M₁ s = V M₂ s := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun π hπ => ?_)
  · rw [← J_reparam hΦ h₁ hπ]
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M₂ ⊤ s) => J M₂ s π) _
      (reparam_feasible hΦ h₁ hπ)
  · rw [← J_reparam hΨ h₂ hπ]
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M₁ ⊤ s) => J M₁ s π) _
      (reparam_feasible hΨ h₂ hπ)

variable {Z : Type*} [MeasurableSpace Z]

/-- **Exercise 5.5** with controls `(C, I, N)`: `C ≥ 0`, `N ∈ (0, 1)`, `C + I = zF(K, N)`,
`K′ = (1 − δ)K + I ≥ 0`, reward `u(C, 1 − N)`. -/
noncomputable def ramsey1 (Q : Kernel Z Z) (zf : Z → ℝ) (F : ℝ≥0 × ℝ → ℝ) (U : ℝ × ℝ → ℝ)
    (δ β : ℝ) : ControlProblem ℝ≥0 Z (ℝ × ℝ × ℝ) where
  Q := Q
  φ := fun _ p => Real.toNNReal ((1 - δ) * p.1 + p.2.1.2.1)
  Γ := fun s => {a | 0 ≤ a.1 ∧ 0 < a.2.2 ∧ a.2.2 < 1 ∧ a.1 + a.2.1 = zf s.2 * F (s.1, a.2.2) ∧
    0 ≤ (1 - δ) * s.1 + a.2.1}
  u := fun _ p => U (p.2.2.1, 1 - p.2.2.2.2)
  uT := fun _ => 0
  β := β

/-- **Exercise 5.5** with controls `(K′, N)`: `K′ ≥ 0`, `N ∈ (0, 1)`,
`C = zF(K, N) + (1 − δ)K − K′ ≥ 0`, reward `u(C, 1 − N)`. -/
noncomputable def ramsey2 (Q : Kernel Z Z) (zf : Z → ℝ) (F : ℝ≥0 × ℝ → ℝ) (U : ℝ × ℝ → ℝ)
    (δ β : ℝ) : ControlProblem ℝ≥0 Z (ℝ × ℝ) where
  Q := Q
  φ := fun _ p => Real.toNNReal p.2.1.1
  Γ := fun s => {a | 0 ≤ a.1 ∧ 0 < a.2 ∧ a.2 < 1 ∧ 0 ≤ zf s.2 * F (s.1, a.2) + (1 - δ) * s.1 - a.1}
  u := fun _ p => U (zf p.2.1 * F (p.1, p.2.2.2) + (1 - δ) * p.1 - p.2.2.1, 1 - p.2.2.2)
  uT := fun _ => 0
  β := β

/-- `(C, I, N) ↦ (K′, N) = ((1 − δ)K + I, N)`. -/
def ramseyΦ (δ : ℝ) (p : (ℝ≥0 × Z) × (ℝ × ℝ × ℝ)) : ℝ × ℝ :=
  ((1 - δ) * p.1.1 + p.2.2.1, p.2.2.2)

/-- `(K′, N) ↦ (C, I, N) = (zF(K, N) + (1 − δ)K − K′, K′ − (1 − δ)K, N)`. -/
def ramseyΨ (zf : Z → ℝ) (F : ℝ≥0 × ℝ → ℝ) (δ : ℝ) (p : (ℝ≥0 × Z) × (ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  (zf p.1.2 * F (p.1.1, p.2.2) + (1 - δ) * p.1.1 - p.2.1, p.2.1 - (1 - δ) * p.1.1, p.2.2)

theorem measurable_ramseyΦ (δ : ℝ) : Measurable (ramseyΦ (Z := Z) δ) := by
  unfold ramseyΦ
  fun_prop

theorem measurable_ramseyΨ {zf : Z → ℝ} {F : ℝ≥0 × ℝ → ℝ} (hz : Measurable zf)
    (hF : Measurable F) (δ : ℝ) : Measurable (ramseyΨ zf F δ) := by
  unfold ramseyΨ
  have h1 : Measurable fun p : (ℝ≥0 × Z) × (ℝ × ℝ) => F (p.1.1, p.2.2) :=
    hF.comp (measurable_fst.fst.prodMk measurable_snd.snd)
  have h2 : Measurable fun p : (ℝ≥0 × Z) × (ℝ × ℝ) => zf p.1.2 := hz.comp measurable_fst.snd
  fun_prop

theorem ramsey_kernel_eq (Q : Kernel Z Z) [IsMarkovKernel Q] (zf : Z → ℝ) (F : ℝ≥0 × ℝ → ℝ)
    (U : ℝ × ℝ → ℝ) (δ β : ℝ) (t : ℕ) (s : ℝ≥0 × Z) (a : ℝ × ℝ × ℝ) :
    (ramsey2 Q zf F U δ β).toMDP.P t (s, ramseyΦ δ (s, a)) =
      (ramsey1 Q zf F U δ β).toMDP.P t (s, a) := by
  have : IsMarkovKernel (ramsey1 Q zf F U δ β).Q := ‹IsMarkovKernel Q›
  have : IsMarkovKernel (ramsey2 Q zf F U δ β).Q := ‹IsMarkovKernel Q›
  have hm1 : Measurable ((ramsey1 Q zf F U δ β).φ t) := by
    change Measurable fun p : ℝ≥0 × (ℝ × ℝ × ℝ) × Z × Z =>
      Real.toNNReal ((1 - δ) * p.1 + p.2.1.2.1)
    fun_prop
  have hm2 : Measurable ((ramsey2 Q zf F U δ β).φ t) := by
    change Measurable fun p : ℝ≥0 × (ℝ × ℝ) × Z × Z => Real.toNNReal p.2.1.1
    fun_prop
  change controlKernel (ramsey2 Q zf F U δ β) t ((s.1, s.2), _) =
    controlKernel (ramsey1 Q zf F U δ β) t ((s.1, s.2), a)
  rw [controlKernel_apply _ hm1, controlKernel_apply _ hm2]
  rfl

/-- **Exercise 5.5** (Miao, pp. 155–156): one can choose `(C, I, N)` or `(K′, N)` as controls.
The map `(C, I, N) ↦ ((1 − δ)K + I, N)` is a bijection from the feasible set of the first
formulation onto that of the second, and the two Markov decision problems have the same value
functions for every horizon (and, with the plan correspondence `reparamPlan`, the same
objectives plan by plan: `J0T_reparam`, `J_reparam`). -/
theorem ex_5_5 (Q : Kernel Z Z) [IsMarkovKernel Q] {zf : Z → ℝ} {F : ℝ≥0 × ℝ → ℝ}
    (hz : Measurable zf) (hF : Measurable F) (U : ℝ × ℝ → ℝ) (δ β : ℝ) :
    (∀ s, Set.BijOn (fun a => ramseyΦ δ (s, a)) ((ramsey1 Q zf F U δ β).Γ s)
      ((ramsey2 Q zf F U δ β).Γ s)) ∧
    ReparamOK (ramsey1 Q zf F U δ β).toMDP (ramsey2 Q zf F U δ β).toMDP (ramseyΦ δ) ∧
    ReparamOK (ramsey2 Q zf F U δ β).toMDP (ramsey1 Q zf F U δ β).toMDP (ramseyΨ zf F δ) ∧
    (∀ T s, V0 (ramsey1 Q zf F U δ β).toMDP T s = V0 (ramsey2 Q zf F U δ β).toMDP T s) ∧
    ∀ s, V (ramsey1 Q zf F U δ β).toMDP s = V (ramsey2 Q zf F U δ β).toMDP s := by
  have hmaps : ∀ s a, a ∈ (ramsey1 Q zf F U δ β).Γ s →
      ramseyΦ δ (s, a) ∈ (ramsey2 Q zf F U δ β).Γ s := by
    rintro s ⟨C, I, N⟩ ⟨hC, hN0, hN1, hCI, hK⟩
    refine ⟨hK, hN0, hN1, ?_⟩
    simp only [ramseyΦ] at hCI ⊢
    linarith
  have hmaps' : ∀ s b, b ∈ (ramsey2 Q zf F U δ β).Γ s →
      ramseyΨ zf F δ (s, b) ∈ (ramsey1 Q zf F U δ β).Γ s := by
    rintro s ⟨K', N⟩ ⟨hK, hN0, hN1, hC⟩
    refine ⟨hC, hN0, hN1, ?_, ?_⟩
    · simp only [ramseyΨ]
      ring
    · simp only [ramseyΨ]
      linarith
  have h1 : ReparamOK (ramsey1 Q zf F U δ β).toMDP (ramsey2 Q zf F U δ β).toMDP
      (ramseyΦ δ) := by
    refine ⟨hmaps, fun t s a ha => ⟨ramsey_kernel_eq Q zf F U δ β t s a, ?_⟩, rfl, rfl⟩
    obtain ⟨C, I, N⟩ := a
    obtain ⟨-, -, -, hCI, -⟩ := ha
    change U (zf s.2 * F (s.1, N) + (1 - δ) * s.1 - ((1 - δ) * s.1 + I), 1 - N) = U (C, 1 - N)
    congr 2
    simp only at hCI
    linarith
  have h2 : ReparamOK (ramsey2 Q zf F U δ β).toMDP (ramsey1 Q zf F U δ β).toMDP
      (ramseyΨ zf F δ) := by
    refine ⟨hmaps', fun t s b hb => ⟨?_, rfl⟩, rfl, rfl⟩
    have e : ramseyΦ δ (s, ramseyΨ zf F δ (s, b)) = b := by
      simp only [ramseyΦ, ramseyΨ]
      ext <;> simp
    rw [← ramsey_kernel_eq Q zf F U δ β t s, e]
  refine ⟨fun s => ⟨fun a ha => hmaps s a ha, ?_, fun b hb => ?_⟩, h1, h2,
    fun T s => V0_reparam (measurable_ramseyΦ δ) (measurable_ramseyΨ hz hF δ) h1 h2 T s,
    fun s => V_reparam (measurable_ramseyΦ δ) (measurable_ramseyΨ hz hF δ) h1 h2 s⟩
  · rintro ⟨C, I, N⟩ ⟨-, -, -, hCI, -⟩ ⟨C', I', N'⟩ ⟨-, -, -, hCI', -⟩ he
    simp only [ramseyΦ, Prod.mk.injEq] at he hCI hCI'
    obtain ⟨hI, hN⟩ := he
    have hI' : I = I' := by linarith
    subst hI' hN
    have : C = C' := by linarith
    subst this
    rfl
  · refine ⟨ramseyΨ zf F δ (s, b), hmaps' s b hb, ?_⟩
    simp only [ramseyΦ, ramseyΨ]
    ext <;> simp

/-- **Exercise 5.5**: with `z ≥ 0`, `F ≥ 0`, `δ ≤ 1`, measurable `z` and `F`, and a measurable
utility bounded by `B`, the `(K′, N)` formulation satisfies Assumptions 5.1.1, 5.1.2 (for
`β ∈ (0, 1)`) and 5.1.4. -/
theorem ex_5_5_assumptions (Q : Kernel Z Z) [IsMarkovKernel Q] {zf : Z → ℝ}
    {F : ℝ≥0 × ℝ → ℝ} (hz : Measurable zf) (hF : Measurable F) (hz0 : ∀ z, 0 ≤ zf z)
    (hF0 : ∀ x, 0 ≤ F x) {U : ℝ × ℝ → ℝ} (hU : Measurable U) {B : ℝ}
    (hB : ∀ x, |U x| ≤ B) {δ β : ℝ} (hδ : δ ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (ramsey2 Q zf F U δ β).toMDP.IsMarkov ∧
      HasMeasurableSelection (ramsey2 Q zf F U δ β).toMDP.Γ ∧
      Assumption512 (ramsey2 Q zf F U δ β).toMDP ∧
      Assumption514 (ramsey2 Q zf F U δ β).toMDP := by
  have : IsMarkovKernel (ramsey2 Q zf F U δ β).Q := ‹IsMarkovKernel Q›
  have hφ : ∀ t, Measurable ((ramsey2 Q zf F U δ β).φ t) := fun t => by
    change Measurable fun p : ℝ≥0 × (ℝ × ℝ) × Z × Z => Real.toNNReal p.2.1.1
    fun_prop
  have hP := controlMDP_isMarkov _ hφ
  have hu : ∀ t, Measurable ((ramsey2 Q zf F U δ β).toMDP.u t) := fun t => by
    change Measurable fun y : (ℝ≥0 × Z) × ℝ × ℝ =>
      U (zf y.1.2 * F (y.1.1, y.2.2) + (1 - δ) * y.1.1 - y.2.1, 1 - y.2.2)
    have h1 : Measurable fun y : (ℝ≥0 × Z) × ℝ × ℝ => F (y.1.1, y.2.2) :=
      hF.comp (measurable_fst.fst.prodMk measurable_snd.snd)
    have h2 : Measurable fun y : (ℝ≥0 × Z) × ℝ × ℝ => zf y.1.2 := hz.comp measurable_fst.snd
    exact hU.comp (by fun_prop)
  refine ⟨hP, ⟨fun _ => (0, 1 / 2), measurable_const, fun s => ⟨le_rfl, by norm_num,
    by norm_num, ?_⟩⟩, ⟨hβ0, hβ1⟩, assumption_5_1_4_of_bounded hP (fun _ => ⟨rfl, rfl⟩)
      (fun t x => hB _) hu hβ0.le hβ1⟩
  have := mul_nonneg (hz0 s.2) (hF0 (s.1, 1 / 2))
  have : 0 ≤ (1 - δ) * (s.1 : ℝ) := mul_nonneg (by linarith) s.1.2
  simp only
  linarith

/-- **Exercise 5.6** (inventory management): inventory `x ≥ 0`, orders
`q ∈ [0, max(x̄ − x, 0)]`, demand `d(z)` in the current exogenous state, sales `min(x + q, d(z))`,
next inventory `x + q − sales`; profit `p · sales − (κ 1{q > 0} + c q) − h(x)`. -/
noncomputable def inventory (Q : Kernel Z Z) (d : Z → ℝ) (xbar p κ c : ℝ) (hc : ℝ≥0 → ℝ)
    (β : ℝ) : ControlProblem ℝ≥0 Z ℝ where
  Q := Q
  φ := fun _ y => Real.toNNReal (y.1 + y.2.1 - min (y.1 + y.2.1) (d y.2.2.1))
  Γ := fun s => Set.Icc 0 (max (xbar - s.1) 0)
  u := fun _ y => p * min (y.1 + y.2.2) (d y.2.1) -
    (κ * (if 0 < y.2.2 then 1 else 0) + c * y.2.2) - hc y.1
  uT := fun _ => 0
  β := β

/-- **Exercise 5.6** (Miao, p. 156): with demand in `[0, D]`, `x̄ ≥ 0`, a measurable bounded
holding cost and `β ∈ (0, 1)`, the inventory problem is an optimal control problem whose MDP
satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 (the profit is bounded on the feasible set). -/
theorem ex_5_6 (Q : Kernel Z Z) [IsMarkovKernel Q] {d : Z → ℝ} (hd : Measurable d) {D : ℝ}
    (hd0 : ∀ z, 0 ≤ d z) (hdD : ∀ z, d z ≤ D) {xbar : ℝ} (hx : 0 ≤ xbar) (p κ c : ℝ)
    {hc : ℝ≥0 → ℝ} (hhc : Measurable hc) {H : ℝ} (hH : ∀ x, |hc x| ≤ H) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    (inventory Q d xbar p κ c hc β).toMDP.IsMarkov ∧
      HasMeasurableSelection (inventory Q d xbar p κ c hc β).toMDP.Γ ∧
      Assumption512 (inventory Q d xbar p κ c hc β).toMDP ∧
      Assumption514 (inventory Q d xbar p κ c hc β).toMDP := by
  have : IsMarkovKernel (inventory Q d xbar p κ c hc β).Q := ‹IsMarkovKernel Q›
  have hφ : ∀ t, Measurable ((inventory Q d xbar p κ c hc β).φ t) := fun t => by
    change Measurable fun y : ℝ≥0 × ℝ × Z × Z =>
      Real.toNNReal (y.1 + y.2.1 - min (y.1 + y.2.1) (d y.2.2.1))
    have : Measurable fun y : ℝ≥0 × ℝ × Z × Z => d y.2.2.1 := hd.comp measurable_snd.snd.fst
    fun_prop
  have hP := controlMDP_isMarkov _ hφ
  have hu : ∀ t, Measurable ((inventory Q d xbar p κ c hc β).toMDP.u t) := fun t => by
    change Measurable fun y : (ℝ≥0 × Z) × ℝ => p * min (y.1.1 + y.2) (d y.1.2) -
      (κ * (if 0 < y.2 then 1 else 0) + c * y.2) - hc y.1.1
    have h1 : Measurable fun y : (ℝ≥0 × Z) × ℝ => d y.1.2 := hd.comp measurable_fst.snd
    have h2 : Measurable fun y : (ℝ≥0 × Z) × ℝ => hc y.1.1 := hhc.comp measurable_fst.fst
    have h3 : Measurable fun y : (ℝ≥0 × Z) × ℝ => (if 0 < y.2 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
        measurable_const
    fun_prop
  have hB : ∀ t s a, a ∈ (inventory Q d xbar p κ c hc β).toMDP.Γ s →
      |(inventory Q d xbar p κ c hc β).toMDP.u t (s, a)| ≤ |p| * D + |κ| + |c| * xbar + H := by
    rintro t ⟨x, z⟩ q ⟨hq0, hq1⟩
    change q ≤ max (xbar - (x : ℝ)) 0 at hq1
    have hx0 : (0 : ℝ) ≤ x := x.2
    have hqx : q ≤ xbar := hq1.trans (max_le (by linarith) hx)
    have hs0 : 0 ≤ min ((x : ℝ) + q) (d z) := le_min (by linarith) (hd0 z)
    have hs1 : min ((x : ℝ) + q) (d z) ≤ D := (min_le_right _ _).trans (hdD z)
    change |p * min ((x : ℝ) + q) (d z) - (κ * (if 0 < q then 1 else 0) + c * q) - hc x| ≤ _
    have e1 : |p * min ((x : ℝ) + q) (d z)| ≤ |p| * D := by
      rw [abs_mul, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left hs1 (abs_nonneg p)
    have e2 : |κ * (if 0 < q then 1 else 0)| ≤ |κ| := by
      split_ifs <;> simp
    have e3 : |c * q| ≤ |c| * xbar := by
      rw [abs_mul, abs_of_nonneg hq0]
      exact mul_le_mul_of_nonneg_left hqx (abs_nonneg c)
    have f1 := abs_sub (p * min ((x : ℝ) + q) (d z) -
      (κ * (if 0 < q then 1 else 0) + c * q)) (hc x)
    have f2 := abs_sub (p * min ((x : ℝ) + q) (d z)) (κ * (if 0 < q then 1 else 0) + c * q)
    have f3 := abs_add_le (κ * (if 0 < q then (1 : ℝ) else 0)) (c * q)
    linarith [hH x]
  refine ⟨hP, ⟨fun _ => 0, measurable_const, fun s => ⟨le_rfl, le_max_right _ _⟩⟩, ⟨hβ0, hβ1⟩,
    assumption_5_1_4_of_boundedOn hP (fun _ => ⟨rfl, rfl⟩) hB hu hβ0.le hβ1⟩

end Miao.MarkovDecisionProcesses

set_option linter.style.longLine false
#print axioms Miao.MarkovDecisionProcesses.measurable_cons
#print axioms Miao.MarkovDecisionProcesses.measurable_snoc
#print axioms Miao.MarkovDecisionProcesses.measurable_init
#print axioms Miao.MarkovDecisionProcesses.lastState
#print axioms Miao.MarkovDecisionProcesses.measurable_lastState
#print axioms Miao.MarkovDecisionProcesses.lastState_cons
#print axioms Miao.MarkovDecisionProcesses.lastState_snoc
#print axioms Miao.MarkovDecisionProcesses.MDP
#print axioms Miao.MarkovDecisionProcesses.MDP.mk
#print axioms Miao.MarkovDecisionProcesses.MDP.Γ
#print axioms Miao.MarkovDecisionProcesses.MDP.P
#print axioms Miao.MarkovDecisionProcesses.MDP.u
#print axioms Miao.MarkovDecisionProcesses.MDP.uT
#print axioms Miao.MarkovDecisionProcesses.MDP.β
#print axioms Miao.MarkovDecisionProcesses.MDP.NonemptyValued
#print axioms Miao.MarkovDecisionProcesses.MDP.IsMarkov
#print axioms Miao.MarkovDecisionProcesses.MDP.IsStationary
#print axioms Miao.MarkovDecisionProcesses.Plan
#print axioms Miao.MarkovDecisionProcesses.IsPlan
#print axioms Miao.MarkovDecisionProcesses.IsMarkovian
#print axioms Miao.MarkovDecisionProcesses.IsStationaryPlan
#print axioms Miao.MarkovDecisionProcesses.IsFeasible
#print axioms Miao.MarkovDecisionProcesses.feasiblePlans
#print axioms Miao.MarkovDecisionProcesses.HasMeasurableSelection
#print axioms Miao.MarkovDecisionProcesses.selectionPlan
#print axioms Miao.MarkovDecisionProcesses.selectionPlan_isPlan
#print axioms Miao.MarkovDecisionProcesses.selectionPlan_markov
#print axioms Miao.MarkovDecisionProcesses.IsStationaryPlan.isMarkovian
#print axioms Miao.MarkovDecisionProcesses.lemma_5_1_1
#print axioms Miao.MarkovDecisionProcesses.selection_of_feasible
#print axioms Miao.MarkovDecisionProcesses.lemma_5_1_1_iff
#print axioms Miao.MarkovDecisionProcesses.no_selection_example
#print axioms Miao.MarkovDecisionProcesses.detKernel
#print axioms Miao.MarkovDecisionProcesses.detKernel_apply
#print axioms Miao.MarkovDecisionProcesses.stepKernel
#print axioms Miao.MarkovDecisionProcesses.mu
#print axioms Miao.MarkovDecisionProcesses.stepKernel_apply
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_stepKernel
#print axioms Miao.MarkovDecisionProcesses.isSFiniteKernel_stepKernel
#print axioms Miao.MarkovDecisionProcesses.sFinite_mu
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_mu
#print axioms Miao.MarkovDecisionProcesses.mu_zero
#print axioms Miao.MarkovDecisionProcesses.integral_mu_zero
#print axioms Miao.MarkovDecisionProcesses.mu_succ_lintegral
#print axioms Miao.MarkovDecisionProcesses.eq_5_2
#print axioms Miao.MarkovDecisionProcesses.integral_mu_succ
#print axioms Miao.MarkovDecisionProcesses.mu_congr
#print axioms Miao.MarkovDecisionProcesses.mu_eq_of_stepKernel
#print axioms Miao.MarkovDecisionProcesses.rew
#print axioms Miao.MarkovDecisionProcesses.expRew
#print axioms Miao.MarkovDecisionProcesses.J0T
#print axioms Miao.MarkovDecisionProcesses.partialSum
#print axioms Miao.MarkovDecisionProcesses.J
#print axioms Miao.MarkovDecisionProcesses.Assumption512
#print axioms Miao.MarkovDecisionProcesses.Assumption513
#print axioms Miao.MarkovDecisionProcesses.Assumption514
#print axioms Miao.MarkovDecisionProcesses.measurable_rew
#print axioms Miao.MarkovDecisionProcesses.expRew_zero
#print axioms Miao.MarkovDecisionProcesses.eq_5_3
#print axioms Miao.MarkovDecisionProcesses.partialSum_eq
#print axioms Miao.MarkovDecisionProcesses.eq_5_4
#print axioms Miao.MarkovDecisionProcesses.J_spec
#print axioms Miao.MarkovDecisionProcesses.J_welldefined
#print axioms Miao.MarkovDecisionProcesses.BoundedRewards
#print axioms Miao.MarkovDecisionProcesses.integrable_of_bounded
#print axioms Miao.MarkovDecisionProcesses.plan_lt
#print axioms Miao.MarkovDecisionProcesses.assumption_5_1_3_of_bounded
#print axioms Miao.MarkovDecisionProcesses.abs_expRew_le
#print axioms Miao.MarkovDecisionProcesses.tendsto_partialSum_of_bounded
#print axioms Miao.MarkovDecisionProcesses.assumption_5_1_4_of_bounded
#print axioms Miao.MarkovDecisionProcesses.assumption_5_1_4_of_boundedOn
#print axioms Miao.MarkovDecisionProcesses.abs_J_le
#print axioms Miao.MarkovDecisionProcesses.geom_partial_tendsto
#print axioms Miao.MarkovDecisionProcesses.tendsto_partialSum_of_bddAbove
#print axioms Miao.MarkovDecisionProcesses.tendsto_partialSum_of_bddBelow
#print axioms Miao.MarkovDecisionProcesses.V0
#print axioms Miao.MarkovDecisionProcesses.V
#print axioms Miao.MarkovDecisionProcesses.IsValueOf
#print axioms Miao.MarkovDecisionProcesses.isValueOf_iff
#print axioms Miao.MarkovDecisionProcesses.V0_char
#print axioms Miao.MarkovDecisionProcesses.V_char
#print axioms Miao.MarkovDecisionProcesses.IsOptimalPlan0
#print axioms Miao.MarkovDecisionProcesses.IsOptimalPlan
#print axioms Miao.MarkovDecisionProcesses.IsOptimalPlan0.isGreatest
#print axioms Miao.MarkovDecisionProcesses.famKernel
#print axioms Miao.MarkovDecisionProcesses.famKernel_apply
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_famKernel
#print axioms Miao.MarkovDecisionProcesses.pushKernel
#print axioms Miao.MarkovDecisionProcesses.pushKernel_apply
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_pushKernel
#print axioms Miao.MarkovDecisionProcesses.liftHist
#print axioms Miao.MarkovDecisionProcesses.liftHist_snoc
#print axioms Miao.MarkovDecisionProcesses.measurable_liftHist
#print axioms Miao.MarkovDecisionProcesses.mu_simulation
#print axioms Miao.MarkovDecisionProcesses.expRew_simulation
#print axioms Miao.MarkovDecisionProcesses.chainMDP
#print axioms Miao.MarkovDecisionProcesses.chainHist
#print axioms Miao.MarkovDecisionProcesses.chainMDP_isMarkov
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_chainHist
#print axioms Miao.MarkovDecisionProcesses.chainHist_succ_lintegral
#print axioms Miao.MarkovDecisionProcesses.mu_markovian
#print axioms Miao.MarkovDecisionProcesses.histOf
#print axioms Miao.MarkovDecisionProcesses.measurable_histOf
#print axioms Miao.MarkovDecisionProcesses.measurable_lastState₂
#print axioms Miao.MarkovDecisionProcesses.trajKernel
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_trajKernel
#print axioms Miao.MarkovDecisionProcesses.muInf
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_muInf
#print axioms Miao.MarkovDecisionProcesses.splitSeg
#print axioms Miao.MarkovDecisionProcesses.measurable_splitSeg
#print axioms Miao.MarkovDecisionProcesses.joinSeg
#print axioms Miao.MarkovDecisionProcesses.measurable_joinSeg
#print axioms Miao.MarkovDecisionProcesses.joinSeg_splitSeg
#print axioms Miao.MarkovDecisionProcesses.splitSeg_IicProdIoc
#print axioms Miao.MarkovDecisionProcesses.partialTraj_map_splitSeg
#print axioms Miao.MarkovDecisionProcesses.splitTraj
#print axioms Miao.MarkovDecisionProcesses.measurable_splitTraj
#print axioms Miao.MarkovDecisionProcesses.splitTraj_eq
#print axioms Miao.MarkovDecisionProcesses.muInf_map_splitTraj
#print axioms Miao.MarkovDecisionProcesses.muInf_marginal
#print axioms Miao.MarkovDecisionProcesses.muInf_zero
#print axioms Miao.MarkovDecisionProcesses.muInf_unique
#print axioms Miao.MarkovDecisionProcesses.J0T_one
#print axioms Miao.MarkovDecisionProcesses.feasible_one_iff
#print axioms Miao.MarkovDecisionProcesses.V0_one
#print axioms Miao.MarkovDecisionProcesses.ex511a
#print axioms Miao.MarkovDecisionProcesses.example_5_1_1a_pos
#print axioms Miao.MarkovDecisionProcesses.example_5_1_1a_nonpos
#print axioms Miao.MarkovDecisionProcesses.example_5_1_1a_empty
#print axioms Miao.MarkovDecisionProcesses.ex511b
#print axioms Miao.MarkovDecisionProcesses.example_5_1_1b
#print axioms Miao.MarkovDecisionProcesses.detPath
#print axioms Miao.MarkovDecisionProcesses.mu_det
#print axioms Miao.MarkovDecisionProcesses.J0T_det
#print axioms Miao.MarkovDecisionProcesses.RPlan
#print axioms Miao.MarkovDecisionProcesses.IsFeasibleR
#print axioms Miao.MarkovDecisionProcesses.nextStateK
#print axioms Miao.MarkovDecisionProcesses.rmu
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_rmu
#print axioms Miao.MarkovDecisionProcesses.statesOf
#print axioms Miao.MarkovDecisionProcesses.measurable_statesOf
#print axioms Miao.MarkovDecisionProcesses.detRPlan
#print axioms Miao.MarkovDecisionProcesses.lastState_statesOf
#print axioms Miao.MarkovDecisionProcesses.detRPlan_feasible_iff
#print axioms Miao.MarkovDecisionProcesses.rustBase
#print axioms Miao.MarkovDecisionProcesses.measurable_rustBase
#print axioms Miao.MarkovDecisionProcesses.measurable_rustNext
#print axioms Miao.MarkovDecisionProcesses.rustKernel
#print axioms Miao.MarkovDecisionProcesses.rust
#print axioms Miao.MarkovDecisionProcesses.rustKernel_apply
#print axioms Miao.MarkovDecisionProcesses.expMeasure_Iic
#print axioms Miao.MarkovDecisionProcesses.rust_cdf_keep
#print axioms Miao.MarkovDecisionProcesses.rust_cdf_replace
#print axioms Miao.MarkovDecisionProcesses.rust_nonneg
#print axioms Miao.MarkovDecisionProcesses.rust_assumptions
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.mk
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.Q
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.f
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.g
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.h
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.β
#print axioms Miao.MarkovDecisionProcesses.sHat
#print axioms Miao.MarkovDecisionProcesses.contKernel
#print axioms Miao.MarkovDecisionProcesses.contKernel_inl
#print axioms Miao.MarkovDecisionProcesses.contKernel_inr
#print axioms Miao.MarkovDecisionProcesses.stopKernel
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.toMDP
#print axioms Miao.MarkovDecisionProcesses.bookΓ
#print axioms Miao.MarkovDecisionProcesses.bookΓ_infeasible
#print axioms Miao.MarkovDecisionProcesses.stopRule
#print axioms Miao.MarkovDecisionProcesses.aliveSet
#print axioms Miao.MarkovDecisionProcesses.measurableSet_aliveSet
#print axioms Miao.MarkovDecisionProcesses.stopRew
#print axioms Miao.MarkovDecisionProcesses.stopTerm
#print axioms Miao.MarkovDecisionProcesses.stopValue
#print axioms Miao.MarkovDecisionProcesses.stopValueInf
#print axioms Miao.MarkovDecisionProcesses.stopV
#print axioms Miao.MarkovDecisionProcesses.stopVInf
#print axioms Miao.MarkovDecisionProcesses.stopStep
#print axioms Miao.MarkovDecisionProcesses.stopLift
#print axioms Miao.MarkovDecisionProcesses.inducedRule
#print axioms Miao.MarkovDecisionProcesses.measurable_stopStep
#print axioms Miao.MarkovDecisionProcesses.lastState_stopLift
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_contKernel
#print axioms Miao.MarkovDecisionProcesses.toMDP_isMarkov
#print axioms Miao.MarkovDecisionProcesses.measurable_toMDP_u
#print axioms Miao.MarkovDecisionProcesses.measurable_toMDP_uT
#print axioms Miao.MarkovDecisionProcesses.stopStep_eq
#print axioms Miao.MarkovDecisionProcesses.stop_hstep
#print axioms Miao.MarkovDecisionProcesses.rew_stopLift
#print axioms Miao.MarkovDecisionProcesses.term_stopLift
#print axioms Miao.MarkovDecisionProcesses.expRew_toMDP
#print axioms Miao.MarkovDecisionProcesses.J0T_toMDP
#print axioms Miao.MarkovDecisionProcesses.J_toMDP
#print axioms Miao.MarkovDecisionProcesses.measurable_inducedRule
#print axioms Miao.MarkovDecisionProcesses.zOf
#print axioms Miao.MarkovDecisionProcesses.measurable_zOf
#print axioms Miao.MarkovDecisionProcesses.toPlan
#print axioms Miao.MarkovDecisionProcesses.lastState_comp_inl
#print axioms Miao.MarkovDecisionProcesses.stopLift_of_alive
#print axioms Miao.MarkovDecisionProcesses.aliveSet_toPlan
#print axioms Miao.MarkovDecisionProcesses.stopValue_toPlan
#print axioms Miao.MarkovDecisionProcesses.stopValueInf_toPlan
#print axioms Miao.MarkovDecisionProcesses.isPlan_toPlan
#print axioms Miao.MarkovDecisionProcesses.inducedRule_mem
#print axioms Miao.MarkovDecisionProcesses.V0_toMDP
#print axioms Miao.MarkovDecisionProcesses.V_toMDP
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.Bounded
#print axioms Miao.MarkovDecisionProcesses.StoppingProblem.IsStationary
#print axioms Miao.MarkovDecisionProcesses.toMDP_assumptions
#print axioms Miao.MarkovDecisionProcesses.optionExercise
#print axioms Miao.MarkovDecisionProcesses.eq_5_7_5_8
#print axioms Miao.MarkovDecisionProcesses.optionExercise_assumptions
#print axioms Miao.MarkovDecisionProcesses.americanCall_beta
#print axioms Miao.MarkovDecisionProcesses.exitProblem
#print axioms Miao.MarkovDecisionProcesses.eq_5_9_5_10
#print axioms Miao.MarkovDecisionProcesses.exitProblem_assumptions
#print axioms Miao.MarkovDecisionProcesses.bern
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_bern
#print axioms Miao.MarkovDecisionProcesses.bern_one
#print axioms Miao.MarkovDecisionProcesses.secretary
#print axioms Miao.MarkovDecisionProcesses.secretary_Q
#print axioms Miao.MarkovDecisionProcesses.secretary_assumptions
#print axioms Miao.MarkovDecisionProcesses.jobSearch
#print axioms Miao.MarkovDecisionProcesses.ex_5_1_accept
#print axioms Miao.MarkovDecisionProcesses.ex_5_1
#print axioms Miao.MarkovDecisionProcesses.americanPut
#print axioms Miao.MarkovDecisionProcesses.ex_5_2
#print axioms Miao.MarkovDecisionProcesses.rank3
#print axioms Miao.MarkovDecisionProcesses.isProbabilityMeasure_rank3
#print axioms Miao.MarkovDecisionProcesses.secretaryTwo
#print axioms Miao.MarkovDecisionProcesses.ex_5_3
#print axioms Miao.MarkovDecisionProcesses.card_mul_of_equal_partition
#print axioms Miao.MarkovDecisionProcesses.bestOfFirst
#print axioms Miao.MarkovDecisionProcesses.bestOfAll
#print axioms Miao.MarkovDecisionProcesses.card_bestOfAll
#print axioms Miao.MarkovDecisionProcesses.swap_val_le
#print axioms Miao.MarkovDecisionProcesses.card_bestOfFirst
#print axioms Miao.MarkovDecisionProcesses.bestOfAll_subset
#print axioms Miao.MarkovDecisionProcesses.secretary_prob
#print axioms Miao.MarkovDecisionProcesses.Bandit
#print axioms Miao.MarkovDecisionProcesses.Bandit.mk
#print axioms Miao.MarkovDecisionProcesses.Bandit.Q
#print axioms Miao.MarkovDecisionProcesses.Bandit.r
#print axioms Miao.MarkovDecisionProcesses.Bandit.β
#print axioms Miao.MarkovDecisionProcesses.armKernel
#print axioms Miao.MarkovDecisionProcesses.Bandit.toMDP
#print axioms Miao.MarkovDecisionProcesses.armKernel_apply
#print axioms Miao.MarkovDecisionProcesses.bandit_P_apply
#print axioms Miao.MarkovDecisionProcesses.bandit_P_rect
#print axioms Miao.MarkovDecisionProcesses.bandit_P_frozen
#print axioms Miao.MarkovDecisionProcesses.bandit_book_false
#print axioms Miao.MarkovDecisionProcesses.bandit_isMarkov
#print axioms Miao.MarkovDecisionProcesses.bandit_assumptions
#print axioms Miao.MarkovDecisionProcesses.banditPay
#print axioms Miao.MarkovDecisionProcesses.retirePay
#print axioms Miao.MarkovDecisionProcesses.retireSeq
#print axioms Miao.MarkovDecisionProcesses.geom_succ
#print axioms Miao.MarkovDecisionProcesses.retirePay_succ
#print axioms Miao.MarkovDecisionProcesses.retirePay_shift
#print axioms Miao.MarkovDecisionProcesses.banditPay_retireSeq
#print axioms Miao.MarkovDecisionProcesses.ex_bandit_constant_arm
#print axioms Miao.MarkovDecisionProcesses.taskSelection
#print axioms Miao.MarkovDecisionProcesses.taskSelection_assumptions
#print axioms Miao.MarkovDecisionProcesses.pandoraKernel
#print axioms Miao.MarkovDecisionProcesses.pandora
#print axioms Miao.MarkovDecisionProcesses.ex_5_4_collect
#print axioms Miao.MarkovDecisionProcesses.ex_5_4
#print axioms Miao.MarkovDecisionProcesses.ControlProblem
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.mk
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.Q
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.φ
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.Γ
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.u
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.uT
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.β
#print axioms Miao.MarkovDecisionProcesses.controlKernel
#print axioms Miao.MarkovDecisionProcesses.ControlProblem.toMDP
#print axioms Miao.MarkovDecisionProcesses.measurable_controlNext
#print axioms Miao.MarkovDecisionProcesses.controlKernel_apply
#print axioms Miao.MarkovDecisionProcesses.isMarkovKernel_controlKernel
#print axioms Miao.MarkovDecisionProcesses.controlKernel_rect
#print axioms Miao.MarkovDecisionProcesses.controlKernel_rect_of_indep
#print axioms Miao.MarkovDecisionProcesses.ctrlX
#print axioms Miao.MarkovDecisionProcesses.controlObj
#print axioms Miao.MarkovDecisionProcesses.IsFeasibleControl
#print axioms Miao.MarkovDecisionProcesses.controlV
#print axioms Miao.MarkovDecisionProcesses.ctrlStep
#print axioms Miao.MarkovDecisionProcesses.ctrlLift
#print axioms Miao.MarkovDecisionProcesses.inducedPolicy
#print axioms Miao.MarkovDecisionProcesses.lastState_ctrlLift
#print axioms Miao.MarkovDecisionProcesses.snd_ctrlLift
#print axioms Miao.MarkovDecisionProcesses.measurable_ctrlStep
#print axioms Miao.MarkovDecisionProcesses.ctrl_hstep
#print axioms Miao.MarkovDecisionProcesses.controlMDP_isMarkov
#print axioms Miao.MarkovDecisionProcesses.expRew_control
#print axioms Miao.MarkovDecisionProcesses.J0T_control
#print axioms Miao.MarkovDecisionProcesses.J_control
#print axioms Miao.MarkovDecisionProcesses.measurable_inducedPolicy
#print axioms Miao.MarkovDecisionProcesses.ctrlX_congr
#print axioms Miao.MarkovDecisionProcesses.controlObj_congr
#print axioms Miao.MarkovDecisionProcesses.controlPlan
#print axioms Miao.MarkovDecisionProcesses.controlPlan_apply
#print axioms Miao.MarkovDecisionProcesses.controlPlan_feasible
#print axioms Miao.MarkovDecisionProcesses.inducedPolicy_controlPlan
#print axioms Miao.MarkovDecisionProcesses.V0_control
#print axioms Miao.MarkovDecisionProcesses.ReparamOK
#print axioms Miao.MarkovDecisionProcesses.reparamPlan
#print axioms Miao.MarkovDecisionProcesses.reparam_feasible
#print axioms Miao.MarkovDecisionProcesses.mu_reparam
#print axioms Miao.MarkovDecisionProcesses.rew_reparam
#print axioms Miao.MarkovDecisionProcesses.J0T_reparam
#print axioms Miao.MarkovDecisionProcesses.J_reparam
#print axioms Miao.MarkovDecisionProcesses.V0_reparam
#print axioms Miao.MarkovDecisionProcesses.V_reparam
#print axioms Miao.MarkovDecisionProcesses.ramsey1
#print axioms Miao.MarkovDecisionProcesses.ramsey2
#print axioms Miao.MarkovDecisionProcesses.ramseyΦ
#print axioms Miao.MarkovDecisionProcesses.ramseyΨ
#print axioms Miao.MarkovDecisionProcesses.measurable_ramseyΦ
#print axioms Miao.MarkovDecisionProcesses.measurable_ramseyΨ
#print axioms Miao.MarkovDecisionProcesses.ramsey_kernel_eq
#print axioms Miao.MarkovDecisionProcesses.ex_5_5
#print axioms Miao.MarkovDecisionProcesses.ex_5_5_assumptions
#print axioms Miao.MarkovDecisionProcesses.inventory
#print axioms Miao.MarkovDecisionProcesses.ex_5_6
