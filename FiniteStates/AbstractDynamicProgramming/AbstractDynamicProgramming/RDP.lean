/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDynamicProgramming.OrderFixedPoints

/-!
# Recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.1–§8.1.3.2
(pp. 246–256). Restated from the `FiniteStates/RecursiveDecisionProcesses` project
(Chapter 8), whose optimality results Chapter 9 proves through abstract dynamic programs.

A recursive decision process `(Γ, V, B)` has a nonempty feasible correspondence
`Γ`, a value space `V ⊆ ℝ^X` and an aggregator `B(x, a, v)` that is monotone in
`v` on `V` (8.2) and consistent (8.3): every policy operator
`(T_σ v)(x) = B(x, σ(x), v)` maps `V` into itself.

* Exercise 8.1.6: policy operators are order-preserving self-maps of `V`.
* Well-posedness (unique `σ`-value functions `v_σ`), global stability and
  continuity (§8.1.2).
* Greedy policies (8.13), the Bellman operator, Exercise 8.1.7 (least and
  greatest elements of `{T_σ v}`), Exercise 8.1.8 (`T = ⋁_σ T_σ`, greedy iff
  `T_σ v = Tv`, `T` an order-preserving self-map of `V`) and Exercise 8.1.9
  ((8.14)–(8.15)).
* The value function `v* = ⋁_σ v_σ` (8.19) and optimal policies.
* The Howard operator (8.17), the OPI operator `W_m`, the HPI and OPI sequences
  (Algorithms 8.1–8.2, (8.18)), and Exercise 8.1.10 (OPI with `m = 1` is VFI).
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- A recursive decision process `(Γ, V, B)` (§8.1.1) on finite state and action spaces. The
aggregator is defined on all of `ℝ^X`; monotonicity (8.2) is required on `V` at feasible pairs, and
consistency (8.3) says that every policy operator maps `V` into itself. -/
structure RDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  V : Set (X → ℝ)
  B : X → A → (X → ℝ) → ℝ
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ V, ∀ w ∈ V, v ≤ w → B x a v ≤ B x a w
  consistent : ∀ σ : X → A, (∀ x, σ x ∈ Γ x) → ∀ v ∈ V, (fun x => B x (σ x) v) ∈ V

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- A feasible policy: `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ R.Γ x

/-- The set `Σ` of feasible policies, as a subtype. -/
abbrev Policy := {σ : X → A // R.IsFeasible σ}

/-- A feasible policy, choosing any feasible action in each state. -/
noncomputable def defaultPolicy : R.Policy :=
  ⟨fun x => (R.Γ_nonempty x).choose, fun x => (R.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty R.Policy := ⟨R.defaultPolicy⟩

/-! ### Policy operators (§8.1.2.1) -/

/-- The policy operator (8.12): `(T_σ v)(x) = B(x, σ(x), v)`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => R.B x (σ x) v

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) : R.Tσ σ v x = R.B x (σ x) v := rfl

/-- Exercise 8.1.6 (p. 251): `T_σ` maps `V` into itself. -/
theorem Tσ_mapsTo {σ : X → A} (hσ : R.IsFeasible σ) : MapsTo (R.Tσ σ) R.V R.V :=
  fun v hv => R.consistent σ hσ v hv

/-- Exercise 8.1.6 (p. 251): `T_σ` is order preserving on `V`. -/
theorem Tσ_monotoneOn {σ : X → A} (hσ : R.IsFeasible σ) : MonotoneOn (R.Tσ σ) R.V :=
  fun v hv w hw hvw x => R.mono x (σ x) (hσ x) v hv w hw hvw

/-- `R` is well-posed (§8.1.2.2) if every `T_σ` has a unique fixed point in `V`. -/
def WellPosed : Prop := ∀ σ : X → A, R.IsFeasible σ → ∃! v, v ∈ R.V ∧ IsFixedPt (R.Tσ σ) v

/-- `R` is globally stable (§8.1.2.2) if every `T_σ` is globally stable on `V`. -/
def IsGloballyStable : Prop := ∀ σ : X → A, R.IsFeasible σ → GloballyStableOn (R.Tσ σ) R.V

/-- Every globally stable RDP is well-posed (p. 253). -/
theorem IsGloballyStable.wellPosed {R : RDP X A} (h : R.IsGloballyStable) : R.WellPosed :=
  fun σ hσ => (h σ hσ).existsUnique

/-- `R` is continuous (§8.1.2.3) if `B(x, a, ·)` is sequentially continuous on `V` at feasible
pairs. -/
def IsContinuous : Prop :=
  ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ vk : ℕ → X → ℝ, (∀ k, vk k ∈ R.V) →
    Tendsto vk atTop (𝓝 v) → Tendsto (fun k => R.B x a (vk k)) atTop (𝓝 (R.B x a v))

open Classical in
/-- The `σ`-value function: the unique fixed point of `T_σ` in `V` when it exists (§8.1.2.2). -/
noncomputable def vσ (σ : X → A) : X → ℝ :=
  if h : ∃! v, v ∈ R.V ∧ IsFixedPt (R.Tσ σ) v then h.exists.choose else 0

theorem vσ_spec {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.vσ σ ∈ R.V ∧ IsFixedPt (R.Tσ σ) (R.vσ σ) := by
  classical
  have h := hw σ hσ
  unfold vσ
  split_ifs
  exact h.exists.choose_spec

theorem vσ_mem {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.vσ σ ∈ R.V := (vσ_spec hw hσ).1

theorem isFixedPt_vσ {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    IsFixedPt (R.Tσ σ) (R.vσ σ) := (vσ_spec hw hσ).2

/-- `v_σ` is the only fixed point of `T_σ` in `V`. -/
theorem eq_vσ_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ)
    {v : X → ℝ} (hv : v ∈ R.V) (hfix : IsFixedPt (R.Tσ σ) v) : v = R.vσ σ :=
  (hw σ hσ).unique ⟨hv, hfix⟩ (vσ_spec hw hσ)

/-- Under global stability, `T_σᵏ v → v_σ` for every `v ∈ V`. -/
theorem tendsto_iterate_Tσ {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) {v : X → ℝ} (hv : v ∈ R.V) :
    Tendsto (fun k : ℕ => (R.Tσ σ)^[k] v) atTop (𝓝 (R.vσ σ)) := by
  obtain ⟨u, hu, hfix, -, hconv⟩ := hR σ hσ
  rw [← eq_vσ_of_isFixedPt hR.wellPosed hσ hu hfix]
  exact hconv v hv

/-! ### Greedy policies and the Bellman operator (§8.1.3.1) -/

/-- The Bellman operator: `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a v

theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ R.Γ x) : R.B x a v ≤ R.T v x :=
  Finset.le_sup' (fun a => R.B x a v) ha

theorem Tσ_le_T {σ : X → A} (hσ : R.IsFeasible σ) (v : X → ℝ) : R.Tσ σ v ≤ R.T v := fun x =>
  R.B_le_T v (hσ x)

/-- A `v`-greedy policy (8.13): feasible, with `σ(x)` maximising `B(x, ·, v)` over `Γ(x)`. -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  R.IsFeasible σ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v ≤ R.B x (σ x) v

/-- A `v`-greedy policy, chosen by maximising in each state (p. 254). -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : R.greedy v x ∈ R.Γ x :=
  ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1

/-- At least one `v`-greedy policy exists (p. 254). -/
theorem isGreedy_greedy (v : X → ℝ) : R.IsGreedy v (R.greedy v) :=
  ⟨R.greedy_mem v, fun x a ha =>
    ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : R.Policy := ⟨R.greedy v, R.greedy_mem v⟩

/-- Exercise 8.1.8 (ii) (p. 254): a feasible `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.IsGreedy v σ ↔ R.Tσ σ v = R.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (R.B_le_T v (hσ x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨hσ, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ_apply] at this
    rw [this]
    exact R.B_le_T v ha

theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : R.IsGreedy v σ) :
    R.Tσ σ v = R.T v := (R.isGreedy_iff_Tσ_eq_T v hσ.1).1 hσ

/-- Exercise 8.1.8 (iii) (p. 254): `T` maps `V` into itself, since `Tv = T_σ v` for a `v`-greedy
`σ`. -/
theorem T_mapsTo : MapsTo R.T R.V R.V := fun v hv => by
  rw [← R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
  exact R.Tσ_mapsTo (R.greedy_mem v) hv

/-- Exercise 8.1.8 (iii) (p. 254): `T` is order preserving on `V`. -/
theorem T_monotoneOn : MonotoneOn R.T R.V := fun v hv w hw hvw x =>
  Finset.sup'_mono_fun fun a ha => R.mono x a ha v hv w hw hvw

/-- Exercise 8.1.8 (i) (p. 254): `Tv = ⋁_σ T_σ v`. -/
theorem T_apply_eq_sup' [DecidableEq X] [DecidableEq A] (v : X → ℝ) (x : X) :
    R.T v x = univ.sup' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy =>
      R.Tσ σ.1 v x := by
  apply le_antisymm
  · rw [← congrFun (R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)) x]
    exact Finset.le_sup' (fun σ : R.Policy => R.Tσ σ.1 v x) (mem_univ (R.greedyPolicy v))
  · exact Finset.sup'_le _ _ fun σ _ => R.Tσ_le_T σ.2 v x

/-- Exercise 8.1.7 (p. 254): `{T_σ v}` has a greatest element, `Tv`, attained by the greedy
policies. -/
theorem isGreatest_Tσ (v : X → ℝ) : IsGreatest (Set.range fun σ : R.Policy => R.Tσ σ.1 v) (R.T v) :=
  ⟨⟨R.greedyPolicy v, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)⟩, by
    rintro _ ⟨σ, rfl⟩
    exact R.Tσ_le_T σ.2 v⟩

/-- A policy minimising `B(x, ·, v)` in each state. -/
noncomputable def antiGreedy (v : X → ℝ) : X → A := fun x =>
  ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose

/-- Exercise 8.1.7 (p. 254): `{T_σ v}` has a least element. -/
theorem isLeast_Tσ (v : X → ℝ) :
    IsLeast (Set.range fun σ : R.Policy => R.Tσ σ.1 v) (R.Tσ (R.antiGreedy v) v) :=
  ⟨⟨⟨R.antiGreedy v, fun x =>
      ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1⟩, rfl⟩, by
    rintro _ ⟨σ, rfl⟩ x
    exact ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.2 _
      (σ.2 x)⟩

/-- Exercise 8.1.9 (8.14) (p. 255): `(Tᵏv)(x) = max_{a ∈ Γ(x)} B(x, a, Tᵏ⁻¹v)`. -/
theorem iterate_T_succ (v : X → ℝ) (k : ℕ) (x : X) :
    R.T^[k + 1] v x = (R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a (R.T^[k] v) := by
  rw [iterate_succ_apply']
  rfl

/-- Exercise 8.1.9 (8.15) (p. 255): `(T_σᵏv)(x) = B(x, σ(x), T_σᵏ⁻¹v)`. -/
theorem iterate_Tσ_succ (σ : X → A) (v : X → ℝ) (k : ℕ) (x : X) :
    (R.Tσ σ)^[k + 1] v x = R.B x (σ x) ((R.Tσ σ)^[k] v) := by
  rw [iterate_succ_apply']
  rfl

/-- `Tᵏ` maps `V` into itself and is order preserving on `V`. -/
theorem iterate_T_mono {v w : X → ℝ} (hv : v ∈ R.V) (hw : w ∈ R.V) (hvw : v ≤ w) (k : ℕ) :
    R.T^[k] v ≤ R.T^[k] w := by
  induction k with
  | zero => simpa using hvw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact R.T_monotoneOn (R.T_mapsTo.iterate k hv) (R.T_mapsTo.iterate k hw) ih

theorem iterate_Tσ_mono {σ : X → A} (hσ : R.IsFeasible σ) {v w : X → ℝ} (hv : v ∈ R.V)
    (hw : w ∈ R.V) (hvw : v ≤ w) (k : ℕ) : (R.Tσ σ)^[k] v ≤ (R.Tσ σ)^[k] w := by
  induction k with
  | zero => simpa using hvw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact R.Tσ_monotoneOn hσ ((R.Tσ_mapsTo hσ).iterate k hv) ((R.Tσ_mapsTo hσ).iterate k hw) ih

/-! ### Value function and optimality (§8.1.3.3) -/

variable [DecidableEq X] [DecidableEq A]

/-- The value function (8.19): `v*(x) = max_{σ ∈ Σ} v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy => R.vσ σ.1 x

theorem vσ_le_vstar {σ : X → A} (hσ : R.IsFeasible σ) : R.vσ σ ≤ R.vstar := fun x =>
  Finset.le_sup' (fun τ : R.Policy => R.vσ τ.1 x) (mem_univ (⟨σ, hσ⟩ : R.Policy))

/-- An optimal policy (p. 257): `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := R.IsFeasible σ ∧ R.vσ σ = R.vstar

/-- `R` satisfies Bellman's principle of optimality (p. 257). -/
def PrincipleOfOptimality : Prop := ∀ σ, R.IsFeasible σ → (R.IsOptimal σ ↔ R.IsGreedy R.vstar σ)

/-! ### Algorithms (§8.1.3.2) -/

omit [DecidableEq X] [DecidableEq A] in
/-- The Howard operator (8.17): `Hv = v_σ` for the chosen `v`-greedy `σ`. -/
noncomputable def howard (v : X → ℝ) : X → ℝ := R.vσ (R.greedy v)

omit [DecidableEq X] [DecidableEq A] in
/-- The OPI operator: `W_m v = T_σᵐ v` for the chosen `v`-greedy `σ`. -/
noncomputable def opiW (m : ℕ) (v : X → ℝ) : X → ℝ := (R.Tσ (R.greedy v))^[m] v

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI policies of Algorithm 8.1 started from `σ`: `σ₀ = σ` and `σₖ₊₁` is `v_{σₖ}`-greedy. -/
noncomputable def hpiPolicy (σ : R.Policy) : ℕ → R.Policy
  | 0 => σ
  | k + 1 => R.greedyPolicy (R.vσ (hpiPolicy σ k).1)

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI values: `vₖ = v_{σₖ}`, so `vₖ₊₁ = H vₖ`. -/
noncomputable def hpiValue (σ : R.Policy) (k : ℕ) : X → ℝ := R.vσ (R.hpiPolicy σ k).1

omit [DecidableEq X] [DecidableEq A] in
theorem hpiValue_succ (σ : R.Policy) (k : ℕ) :
    R.hpiValue σ (k + 1) = R.howard (R.hpiValue σ k) := rfl

omit [DecidableEq X] [DecidableEq A] in
/-- The OPI value sequence (8.18): `vₖ = W_mᵏ v_σ`. -/
noncomputable def opiValue (m : ℕ) (σ : X → A) (k : ℕ) : X → ℝ := (R.opiW m)^[k] (R.vσ σ)

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.10 (p. 256): with `m = 1`, OPI is value function iteration, `vₖ = Tᵏv₀`. -/
theorem opiValue_one (σ : X → A) (k : ℕ) : R.opiValue 1 σ k = R.T^[k] (R.vσ σ) := by
  have h : R.opiW 1 = R.T := by
    funext v
    simp only [opiW, iterate_one]
    exact R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)
  simp [opiValue, h]

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.11 (p. 259): for policies `σ₁, σ₂, …` and `v ∈ V`,
`T_{σₖ} ⋯ T_{σ₁} v ≤ Tᵏ v`. -/
theorem nonstationary_le (σs : ℕ → X → A) (hσs : ∀ k, R.IsFeasible (σs k)) {v : X → ℝ}
    (hv : v ∈ R.V) : ∀ k, (Nat.rec v fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k ∈ R.V ∧
      (Nat.rec v fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k ≤ R.T^[k] v := by
  intro k
  induction k with
  | zero => exact ⟨hv, le_rfl⟩
  | succ k ih =>
    refine ⟨R.Tσ_mapsTo (hσs k) ih.1, ?_⟩
    rw [iterate_succ_apply']
    exact (R.Tσ_le_T (hσs k) _).trans (R.T_monotoneOn ih.1 (R.T_mapsTo.iterate k hv) ih.2)

end RDP

end SargentStachurski.AbstractDynamicProgramming
