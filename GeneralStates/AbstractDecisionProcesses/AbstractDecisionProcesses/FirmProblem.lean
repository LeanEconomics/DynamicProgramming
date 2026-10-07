/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDecisionProcesses.ContractingDP
import AbstractDecisionProcesses.NeumannSeries

/-!
# A firm problem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.1.1 (pp. 2–10).

Profits are `π(X_t)` for a Markov state `(X_t)` with stochastic kernel `P` on a measurable space
`X`, `π ∈ bX`, and `β ∈ [0, 1)`.

* **Valuation** (§1.1.1.1): `v = π + βPv` (1.2) has a unique solution in `bX`, given by the
  Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π` (1.3) (Exercise 1.1.1, in its functional form).
* **Control** (§1.1.1.2): the manager may sell the firm for `s`. A policy is a measurable
  `σ : X → {0, 1}` (here `Bool`, `true` meaning sell), with policy operator
  `T_σ v = σs + (1 − σ)(π + βPv)` (1.5), a `β`-contraction on `bX` with fixed point `v_σ`.
* **Theorem 1.1.1** (p. 6): `v* = sup_σ v_σ` is the unique solution in `bX` of the Bellman
  equation `v = s ∨ (π + βPv)` (1.6), an optimal policy exists, and a policy is optimal iff it
  is `v*`-greedy (1.7); Exercises 1.1.2 and 1.1.3; the Bellman operator (1.9) is a
  `β`-contraction and `Tᵏv → v*` (§1.1.1.3); Remark 1.1.2 (sell at ties).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- The firm problem of §1.1.1. -/
structure FirmProblem (X : Type*) [MeasurableSpace X] where
  /-- the stochastic kernel of the state -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the profit function `π` -/
  profit : X → ℝ
  profit_mem : profit ∈ bX X
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the sale price -/
  s : ℝ

/-- Policies (§1.1.1.2): measurable maps `X → {0, 1}`, with `true` meaning sell. -/
def FirmPolicy (X : Type*) [MeasurableSpace X] : Type _ := {σ : X → Bool // Measurable σ}

namespace FirmProblem

variable (F : FirmProblem X)

/-! ### Valuation -/

theorem isMarkovLike_P : IsMarkovLike (markovOp F.P) := by
  have := F.isMarkov
  exact isMarkovLike_markovOp F.P

/-- The valuation operator `v ↦ π + βPv` of (1.2). -/
noncomputable def valOp : (X → ℝ) → X → ℝ := affineOp F.profit F.β (markovOp F.P)

theorem valOp_mapsTo : MapsTo F.valOp (bX X) (bX X) :=
  affineOp_mapsTo F.isMarkovLike_P F.profit_mem F.β_nonneg

theorem valOp_contraction : IsSupContraction (bX X) F.valOp F.β :=
  affineOp_contraction F.isMarkovLike_P F.β_nonneg

/-- (1.2): `v = π + βPv` has a unique solution in `bX`, the limit of iterates from any `v ∈ bX`. -/
theorem valuation_globallyStable :
    ∃ u ∈ bX X, F.valOp u = u ∧ (∀ w ∈ bX X, F.valOp w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.valOp^[n] v) u atTop :=
  affineOp_globallyStable F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one

/-- The value of the firm, the solution of (1.2). -/
noncomputable def value : X → ℝ := F.valuation_globallyStable.choose

theorem value_mem : F.value ∈ bX X := F.valuation_globallyStable.choose_spec.1

/-- (1.2) and **Exercise 1.1.1** (p. 4): `v = π + βPv`. -/
theorem value_eq (x : X) : F.value x = F.profit x + F.β * markovOp F.P F.value x :=
  (congrFun F.valuation_globallyStable.choose_spec.2.1 x).symm

/-- (1.3) (p. 4): the value of the firm is the Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π`. -/
theorem value_hasSum (x : X) :
    HasSum (fun t => F.β ^ t * (markovOp F.P)^[t] F.profit x) (F.value x) :=
  affineOp_hasSum F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one F.value_mem
    F.valuation_globallyStable.choose_spec.2.1 x

/-! ### Control -/

/-- The policy operator (1.5): `T_σ v = s` where `σ` sells and `π + βPv` where it continues. -/
noncomputable def Tσ (σ : X → Bool) (v : X → ℝ) : X → ℝ :=
  fun x => if σ x then F.s else F.profit x + F.β * markovOp F.P v x

/-- (1.5) in the book's form `T_σ v = σs + (1 − σ)(π + βPv)`, with `σ ∈ {0, 1}`. -/
theorem Tσ_eq (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x = (if σ x then 1 else 0) * F.s +
      (1 - if σ x then 1 else 0) * (F.profit x + F.β * markovOp F.P v x) := by
  unfold Tσ
  cases σ x <;> simp

theorem Tσ_mapsTo {σ : X → Bool} (hσ : Measurable σ) : MapsTo (F.Tσ σ) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, M, hM⟩ := F.valOp_mapsTo hv
  refine ⟨Measurable.ite (hσ (measurableSet_singleton true)) measurable_const hm,
    max |F.s| M, fun x => ?_⟩
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact (hM x).trans (le_max_right _ _)

theorem Tσ_mono (σ : X → Bool) {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) (h : v ≤ w) :
    F.Tσ σ v ≤ F.Tσ σ w := by
  have := F.isMarkov
  intro x
  simp only [Tσ]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (markovOp_mono F.P hv hw h x)
      F.β_nonneg)

/-- §1.1.1.2: each `T_σ` is a `β`-contraction on `bX`. -/
theorem Tσ_contraction (σ : X → Bool) : IsSupContraction (bX X) (F.Tσ σ) F.β := by
  intro v hv w hw c h x
  simp only [Tσ]
  split_ifs
  · simpa using mul_nonneg F.β_nonneg ((abs_nonneg _).trans (h x))
  · exact F.valOp_contraction v hv w hw c h x

/-- The policy that sells exactly when `s ≥ π + βPv` is measurable (§2.3.1). -/
theorem measurable_sellPolicy {v : X → ℝ} (hv : v ∈ bX X) :
    Measurable fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s) := by
  refine measurable_to_bool ?_
  have hm := (F.valOp_mapsTo hv).1
  have : (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) ⁻¹' {true} =
      {x | F.valOp v x ≤ F.s} := by
    ext x; simp [valOp, affineOp]
  rw [this]
  exact measurableSet_le hm measurable_const

/-- `T_σ v ≤ s ∨ (π + βPv)`, with equality for the selling policy above. -/
theorem Tσ_le_max (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x ≤ max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Tσ_sellPolicy (v : X → ℝ) (x : X) :
    F.Tσ (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) v x =
      max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  by_cases h : F.profit x + F.β * markovOp F.P v x ≤ F.s
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

/-- The firm problem as a contracting dynamic program on `bX`. -/
noncomputable def toDP : ContractingDP X (FirmPolicy X) where
  V := bX X
  T σ := F.Tσ σ.1
  β := F.β
  β_nonneg := F.β_nonneg
  β_lt_one := F.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd := fun _ h => h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := F.Tσ_mapsTo σ.2
  mono σ _ hv _ hw h := F.Tσ_mono σ.1 hv hw h
  contraction σ := F.Tσ_contraction σ.1
  exists_greedy v hv := ⟨⟨_, F.measurable_sellPolicy hv⟩, fun τ x => by
    change F.Tσ τ.1 v x ≤ F.Tσ _ v x
    rw [F.Tσ_sellPolicy]
    exact F.Tσ_le_max τ.1 v x⟩

/-- The firm's Bellman operator is `Tv = s ∨ (π + βPv)` (1.9). -/
theorem bellman_eq {v : X → ℝ} (hv : v ∈ bX X) (x : X) :
    F.toDP.bellman v x = max F.s (F.profit x + F.β * markovOp F.P v x) := by
  refine le_antisymm (F.Tσ_le_max _ v x) ?_
  rw [← F.Tσ_sellPolicy]
  exact F.toDP.T_le_bellman ⟨_, F.measurable_sellPolicy hv⟩ hv x

/-- `σ` is `v`-greedy in the sense of (1.8): at each `x`, `σ(x)` maximizes
`as + (1 − a)(π(x) + β(Pv)(x))` over `a ∈ {0, 1}`. -/
def IsGreedy (v : X → ℝ) (σ : X → Bool) : Prop :=
  ∀ x, ∀ a : Bool, (if a then F.s else F.profit x + F.β * markovOp F.P v x) ≤ F.Tσ σ v x

/-- (1.8) agrees with greedy policies of the dynamic program (§2.3.1). -/
theorem isGreedy_iff (v : X → ℝ) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.toDP.IsGreedy v σ := by
  constructor
  · intro h τ x
    change F.Tσ τ.1 v x ≤ F.Tσ σ.1 v x
    have := h x (τ.1 x)
    simp only [Tσ] at this ⊢
    exact this
  · intro h x a
    have := h ⟨fun _ => a, measurable_const⟩ x
    change F.Tσ (fun _ => a) v x ≤ F.Tσ σ.1 v x at this
    simpa only [Tσ] using this

/-- **Exercise 1.1.3** (p. 8): `σ` is `v`-greedy iff `Tv = T_σ v`. -/
theorem isGreedy_iff_bellman {v : X → ℝ} (hv : v ∈ bX X) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.Tσ σ.1 v = F.toDP.bellman v :=
  (F.isGreedy_iff v σ).trans (F.toDP.isGreedy_iff hv σ)

/-- **Exercise 1.1.2** (p. 6): if `|π| ≤ M` and `|s| ≤ M`, every `σ`-value function satisfies
`|v_σ| ≤ M/(1 − β)`; in particular `v* = sup_σ v_σ` is a well-defined real function. -/
theorem abs_vσ_le {M : ℝ} (hπ : ∀ x, |F.profit x| ≤ M) (hs : |F.s| ≤ M) (σ : FirmPolicy X)
    (x : X) : |F.toDP.vσ σ x| ≤ M / (1 - F.β) := by
  have := F.isMarkov
  have h1β : 0 < 1 - F.β := sub_pos.2 F.β_lt_one
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hs
  set K := M / (1 - F.β)
  have hK : M + F.β * K = K := by
    have : K * (1 - F.β) = M := div_mul_cancel₀ M h1β.ne'
    linear_combination -this
  have hKM : M ≤ K := by
    rw [le_div_iff₀ h1β]; nlinarith [F.β_nonneg]
  have hup : F.toDP.T σ (fun _ => K) ≤ fun _ => K := fun y => by
    change F.Tσ σ.1 _ y ≤ K
    simp only [Tσ, markovOp_const]
    split_ifs
    · exact (le_abs_self _).trans (hs.trans hKM)
    · linarith [(abs_le.1 (hπ y)).2]
  have hdown : (fun _ => -K) ≤ F.toDP.T σ (fun _ => -K) := fun y => by
    change -K ≤ F.Tσ σ.1 _ y
    simp only [Tσ, markovOp_const]
    split_ifs
    · linarith [(abs_le.1 hs).1]
    · linarith [(abs_le.1 (hπ y)).1]
  rw [abs_le]
  exact ⟨F.toDP.le_vσ (const_mem_bX _) hdown x, F.toDP.vσ_le (const_mem_bX _) hup x⟩

/-- **Theorem 1.1.1** (p. 6): the value function `v* = sup_σ v_σ` is the unique `v ∈ bX` solving
the Bellman equation `v = s ∨ (π + βPv)` (1.6); at least one optimal policy exists; a policy is
optimal iff it is `v*`-greedy (1.7); and VFI converges, `Tᵏv → v*` uniformly (§1.1.1.3). -/
theorem theorem_1_1_1 :
    F.toDP.vstar ∈ bX X ∧ (∀ x, F.toDP.vstar x = ⨆ σ, F.toDP.vσ σ x) ∧
      (∀ x, F.toDP.vstar x = max F.s (F.profit x + F.β * markovOp F.P F.toDP.vstar x)) ∧
      (∀ v ∈ bX X, (∀ x, v x = max F.s (F.profit x + F.β * markovOp F.P v x)) →
        v = F.toDP.vstar) ∧
      (∃ σ, F.toDP.IsOptimal σ) ∧ (∀ σ, F.toDP.IsOptimal σ ↔ F.IsGreedy F.toDP.vstar σ.1) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.toDP.bellman^[n] v) F.toDP.vstar atTop := by
  obtain ⟨-, hsup, hfix, hopt, hex, hvfi⟩ := F.toDP.optimality
  have hmem : F.toDP.vstar ∈ bX X := F.toDP.vstar_mem
  refine ⟨hmem, hsup, fun x => ?_, fun v hv h => (hfix v hv).1 (funext fun x => ?_), hex,
    fun σ => (hopt σ).trans (F.isGreedy_iff _ σ).symm, hvfi⟩
  · rw [← F.bellman_eq hmem x, F.toDP.bellman_vstar]
  · rw [F.bellman_eq hv x]; exact (h x).symm

/-- **Remark 1.1.2** (p. 7): the policy that sells whenever `s ≥ π + βPv*` is optimal. -/
theorem sellPolicy_optimal :
    F.toDP.IsOptimal ⟨_, F.measurable_sellPolicy F.toDP.vstar_mem⟩ := by
  refine (F.toDP.optimality.2.2.2.1 _).2 ((F.isGreedy_iff _ _).1 fun x a => ?_)
  rw [F.Tσ_sellPolicy]
  cases a
  · exact le_max_right _ _
  · exact le_max_left _ _

end FirmProblem

end SargentStachurski.AbstractDecisionProcesses
