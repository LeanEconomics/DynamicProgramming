/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.MDPSimulation
import FiniteHorizonDP.MDPKernelTools

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
