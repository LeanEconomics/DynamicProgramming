/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.OptimalControl
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

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
