/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Simulation
import MarkovDecisionProcesses.KernelTools

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
