/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.SupContraction

/-!
# Contracting dynamic programs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Chapter 1: the common structure of the
proofs of Theorems 1.1.1 and 1.2.1–1.2.2 (§1.1.1.4, pp. 9–10).

A *contracting dynamic program* is a family of policy operators `T_σ` on a set `V` of bounded
functions closed under uniform limits, each order preserving and a `β`-contraction for the
supremum distance (`β < 1`), such that every `v ∈ V` has a `v`-greedy policy. This is the
setting of the firm problem (§1.1), finite MDPs (§1.2) and the optimal savings problem (§1.3).

* `v_σ` is the unique fixed point of `T_σ` in `V`, the limit of `T_σⁿ v` from every `v ∈ V`.
* The Bellman operator `Tv = T_σ v` for a `v`-greedy `σ` is the pointwise supremum
  `sup_σ T_σ v`, is order preserving and is a `β`-contraction.
* **Theorem 1.1.1** (abstract form): the value function `v* = sup_σ v_σ` is the greatest
  element of `{v_σ}`, the unique solution of the Bellman equation in `V`, and a policy is
  optimal iff it is `v*`-greedy; an optimal policy exists, and `Tᵏv → v*` (VFI).
* **Theorem 1.2.2**: HPI reaches an optimal policy in finitely many steps when the policy set is
  finite, and, when the policy operators shift constants by `β` (`T_σ(v − c) = T_σ v − βc`),
  OPI converges from every starting point.
* **Lemma 1.2.3**: `Tv ≤ v` implies `v* ≤ v`.
-/

open Filter Topology Set Function

namespace SargentStachurski.ADPTransformations

/-- A contracting dynamic program: policy operators `T_σ` on a set `V` of bounded functions. -/
structure ContractingDP (X P : Type*) where
  /-- the candidate value functions -/
  V : Set (X → ℝ)
  /-- the policy operators -/
  T : P → (X → ℝ) → X → ℝ
  /-- the modulus of contraction -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  nonempty : V.Nonempty
  bdd : ∀ v ∈ V, IsBdd v
  closed : IsUniformlyClosed V
  mapsTo : ∀ σ, MapsTo (T σ) V V
  mono : ∀ σ, ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T σ v ≤ T σ w
  contraction : ∀ σ, IsSupContraction V (T σ) β
  exists_greedy : ∀ v ∈ V, ∃ σ, ∀ τ, T τ v ≤ T σ v

namespace ContractingDP

variable {X P : Type*} (D : ContractingDP X P)

/-- Each policy operator is globally stable on `V` (§1.1.1.2). -/
theorem globallyStable (σ : P) :
    ∃ u ∈ D.V, D.T σ u = u ∧ (∀ w ∈ D.V, D.T σ w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => (D.T σ)^[n] v) u atTop :=
  (D.contraction σ).globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed (D.mapsTo σ) D.nonempty

/-- The `σ`-value function: the unique fixed point of `T_σ` in `V`. -/
noncomputable def vσ (σ : P) : X → ℝ := (D.globallyStable σ).choose

theorem vσ_mem (σ : P) : D.vσ σ ∈ D.V := (D.globallyStable σ).choose_spec.1

theorem T_vσ (σ : P) : D.T σ (D.vσ σ) = D.vσ σ := (D.globallyStable σ).choose_spec.2.1

theorem eq_vσ {σ : P} {w : X → ℝ} (hw : w ∈ D.V) (h : D.T σ w = w) : w = D.vσ σ :=
  (D.globallyStable σ).choose_spec.2.2.1 w hw h

theorem tendsto_vσ (σ : P) {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => (D.T σ)^[n] v) (D.vσ σ) atTop :=
  (D.globallyStable σ).choose_spec.2.2.2 v hv

/-- Order stability of `T_σ`: `v ≤ T_σ v` implies `v ≤ v_σ`. -/
theorem le_vσ {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.T σ v) : v ≤ D.vσ σ :=
  le_of_le_map_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- Order stability of `T_σ`: `T_σ v ≤ v` implies `v_σ ≤ v`. -/
theorem vσ_le {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : D.T σ v ≤ v) : D.vσ σ ≤ v :=
  le_of_map_le_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- `σ` is `v`-greedy: `T_τ v ≤ T_σ v` for every policy `τ`. -/
def IsGreedy (v : X → ℝ) (σ : P) : Prop := ∀ τ, D.T τ v ≤ D.T σ v

include D in
/-- The policy set is nonempty. -/
theorem nonempty_policy : Nonempty P :=
  ⟨(D.exists_greedy _ D.nonempty.some_mem).choose⟩

/-- A chosen `v`-greedy policy (an arbitrary policy off `V`). -/
noncomputable def greedy (v : X → ℝ) : P :=
  @Classical.epsilon P D.nonempty_policy fun σ => v ∈ D.V → D.IsGreedy v σ

theorem isGreedy_greedy {v : X → ℝ} (hv : v ∈ D.V) : D.IsGreedy v (D.greedy v) := by
  obtain ⟨σ, hσ⟩ := D.exists_greedy v hv
  exact @Classical.epsilon_spec P (fun σ => v ∈ D.V → D.IsGreedy v σ) ⟨σ, fun _ => hσ⟩ hv

/-- The Bellman operator `Tv = T_σ v` for the chosen `v`-greedy `σ`. -/
noncomputable def bellman (v : X → ℝ) : X → ℝ := D.T (D.greedy v) v

theorem bellman_mapsTo : MapsTo D.bellman D.V D.V := fun _ hv => D.mapsTo _ hv

theorem T_le_bellman (σ : P) {v : X → ℝ} (hv : v ∈ D.V) : D.T σ v ≤ D.bellman v :=
  D.isGreedy_greedy hv σ

/-- Greedy policies are those attaining the Bellman operator (Exercises 1.1.3 and 1.2.4). -/
theorem isGreedy_iff {v : X → ℝ} (hv : v ∈ D.V) (σ : P) :
    D.IsGreedy v σ ↔ D.T σ v = D.bellman v :=
  ⟨fun h => le_antisymm (D.T_le_bellman σ hv) (h _), fun h τ => h ▸ D.T_le_bellman τ hv⟩

/-- The Bellman operator is the pointwise supremum of the policy operators. -/
theorem bellman_eq_iSup {v : X → ℝ} (hv : v ∈ D.V) (x : X) :
    D.bellman v x = ⨆ σ, D.T σ v x := by
  have := D.nonempty_policy
  refine le_antisymm ?_ (ciSup_le fun σ => D.T_le_bellman σ hv x)
  exact le_ciSup (f := fun σ => D.T σ v x)
    ⟨D.bellman v x, by rintro _ ⟨σ, rfl⟩; exact D.T_le_bellman σ hv x⟩ (D.greedy v)

theorem bellman_mono {v w : X → ℝ} (hv : v ∈ D.V) (hw : w ∈ D.V) (h : v ≤ w) :
    D.bellman v ≤ D.bellman w :=
  (D.mono _ v hv w hw h).trans (D.T_le_bellman _ hw)

/-- The Bellman operator is a `β`-contraction (§1.1.1.3, Exercise 1.2.3). -/
theorem bellman_contraction : IsSupContraction D.V D.bellman D.β := by
  intro v hv w hw c hc x
  have h1 := D.contraction (D.greedy v) v hv w hw c hc x
  have h2 := D.contraction (D.greedy w) v hv w hw c hc x
  have a1 := D.T_le_bellman (D.greedy v) hw x
  have a2 := D.T_le_bellman (D.greedy w) hv x
  rw [abs_le] at h1 h2 ⊢
  simp only [bellman] at a1 a2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem bellman_globallyStable :
    ∃ u ∈ D.V, D.bellman u = u ∧ (∀ w ∈ D.V, D.bellman w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) u atTop :=
  D.bellman_contraction.globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed D.bellman_mapsTo
    D.nonempty

/-- The value function `v*`, the fixed point of the Bellman operator. -/
noncomputable def vstar : X → ℝ := D.bellman_globallyStable.choose

theorem vstar_mem : D.vstar ∈ D.V := D.bellman_globallyStable.choose_spec.1

theorem bellman_vstar : D.bellman D.vstar = D.vstar := D.bellman_globallyStable.choose_spec.2.1

theorem eq_vstar {w : X → ℝ} (hw : w ∈ D.V) (h : D.bellman w = w) : w = D.vstar :=
  D.bellman_globallyStable.choose_spec.2.2.1 w hw h

/-- **VFI** (§1.1.1.3): `Tᵏ v → v*` uniformly for every `v ∈ V`. -/
theorem tendsto_bellman_iterate {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop :=
  D.bellman_globallyStable.choose_spec.2.2.2 v hv

/-- Every `σ`-value function lies below `v*` (the second inequality in the proof of
Theorem 1.1.1). -/
theorem vσ_le_vstar (σ : P) : D.vσ σ ≤ D.vstar :=
  D.vσ_le D.vstar_mem ((D.T_le_bellman σ D.vstar_mem).trans D.bellman_vstar.le)

/-- `σ` attains `v*` iff it is `v*`-greedy. -/
theorem vσ_eq_vstar_iff (σ : P) : D.vσ σ = D.vstar ↔ D.IsGreedy D.vstar σ := by
  rw [D.isGreedy_iff D.vstar_mem, D.bellman_vstar]
  constructor
  · intro h
    rw [← h, D.T_vσ]
  · intro h
    exact (D.eq_vσ D.vstar_mem h).symm

/-- A `σ` is optimal: `v_τ ≤ v_σ` for every `τ`. -/
def IsOptimal (σ : P) : Prop := ∀ τ, D.vσ τ ≤ D.vσ σ

theorem isOptimal_iff (σ : P) : D.IsOptimal σ ↔ D.vσ σ = D.vstar := by
  constructor
  · intro h
    refine le_antisymm (D.vσ_le_vstar σ) ?_
    have hg := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
    exact hg ▸ h _
  · intro h τ
    exact h ▸ D.vσ_le_vstar τ

/-- **Theorem 1.1.1**, abstract form (pp. 6–10): `v*` is the greatest `σ`-value function and the
pointwise supremum of them, it is the unique solution of the Bellman equation in `V`, a policy
is optimal iff it is `v*`-greedy, an optimal policy exists, and VFI converges. -/
theorem optimality :
    IsGreatest (range D.vσ) D.vstar ∧ (∀ x, D.vstar x = ⨆ σ, D.vσ σ x) ∧
      (∀ v ∈ D.V, D.bellman v = v ↔ v = D.vstar) ∧
      (∀ σ, D.IsOptimal σ ↔ D.IsGreedy D.vstar σ) ∧ (∃ σ, D.IsOptimal σ) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop := by
  have hopt := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
  have := D.nonempty_policy
  refine ⟨⟨⟨_, hopt⟩, ?_⟩, fun x => ?_, fun v hv => ⟨D.eq_vstar hv, fun h => h ▸ D.bellman_vstar⟩,
    fun σ => (D.isOptimal_iff σ).trans (D.vσ_eq_vstar_iff σ),
    ⟨_, (D.isOptimal_iff _).2 hopt⟩, fun v hv => D.tendsto_bellman_iterate hv⟩
  · rintro _ ⟨σ, rfl⟩
    exact D.vσ_le_vstar σ
  · refine le_antisymm ?_ (ciSup_le fun σ => D.vσ_le_vstar σ x)
    conv_lhs => rw [← hopt]
    exact le_ciSup ⟨D.vstar x, by rintro _ ⟨σ, rfl⟩; exact D.vσ_le_vstar σ x⟩ _

/-- **Lemma 1.2.3** (p. 25): `Tv ≤ v` implies `v* ≤ v`. -/
theorem vstar_le_of_bellman_le {v : X → ℝ} (hv : v ∈ D.V) (h : D.bellman v ≤ v) :
    D.vstar ≤ v :=
  le_of_map_le_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-- `v ≤ Tv` implies `v ≤ v*`. -/
theorem le_vstar_of_le_bellman {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.bellman v) :
    v ≤ D.vstar :=
  le_of_le_map_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-! ### Howard policy iteration -/

/-- HPI (Algorithm 1.2): `σ₀` given and `σ_{k+1}` a `v_{σ_k}`-greedy policy. -/
noncomputable def hpiPolicy (σ₀ : P) : ℕ → P
  | 0 => σ₀
  | k + 1 => D.greedy (D.vσ (hpiPolicy σ₀ k))

/-- HPI values increase. -/
theorem vσ_hpi_le_succ (σ₀ : P) (k : ℕ) :
    D.vσ (D.hpiPolicy σ₀ k) ≤ D.vσ (D.hpiPolicy σ₀ (k + 1)) := by
  set σ := D.hpiPolicy σ₀ k
  refine D.le_vσ (D.vσ_mem σ) ?_
  change D.vσ σ ≤ D.T (D.greedy (D.vσ σ)) (D.vσ σ)
  calc D.vσ σ = D.T σ (D.vσ σ) := (D.T_vσ σ).symm
    _ ≤ _ := D.isGreedy_greedy (D.vσ_mem σ) σ

/-- A repeated HPI value is `v*`. -/
theorem vσ_hpi_eq_vstar {σ₀ : P} {k : ℕ}
    (h : D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k)) :
    D.vσ (D.hpiPolicy σ₀ k) = D.vstar := by
  set v := D.vσ (D.hpiPolicy σ₀ k)
  refine D.eq_vstar (D.vσ_mem _) ?_
  change D.T (D.greedy v) v = v
  have hτ : D.vσ (D.greedy v) = v := h
  calc D.T (D.greedy v) v = D.T (D.greedy v) (D.vσ (D.greedy v)) := by rw [hτ]
    _ = D.vσ (D.greedy v) := D.T_vσ _
    _ = v := hτ

/-- **Theorem 1.2.2**, HPI part (p. 24): with finitely many policies, HPI reaches `v*` in finitely
many steps, after which every policy it produces is optimal. -/
theorem hpi_terminates [Finite P] (σ₀ : P) :
    ∃ k, ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar ∧ D.IsOptimal (D.hpiPolicy σ₀ j) := by
  have hk : ∃ k, D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k) := by
    by_contra hne
    push Not at hne
    have hsm : StrictMono fun k => D.vσ (D.hpiPolicy σ₀ k) :=
      strictMono_nat_of_lt_succ fun k => lt_of_le_of_ne (D.vσ_hpi_le_succ σ₀ k) (hne k).symm
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (D.hpiPolicy σ₀)
    exact hij (hsm.injective (by simp only [heq]))
  obtain ⟨k, hk⟩ := hk
  have h0 := D.vσ_hpi_eq_vstar hk
  have hall : ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact h0
    | succ j _ ih =>
      change D.vσ (D.greedy (D.vσ (D.hpiPolicy σ₀ j))) = D.vstar
      rw [ih]
      exact (D.vσ_eq_vstar_iff _).2 (D.isGreedy_greedy D.vstar_mem)
  exact ⟨k, fun j hj => ⟨hall j hj, (D.isOptimal_iff _).2 (hall j hj)⟩⟩

/-! ### Optimistic policy iteration -/

/-- OPI (Algorithm 1.3): `v_{n+1} = T_σ^m v_n` for the chosen `v_n`-greedy `σ`. -/
noncomputable def opi (m : ℕ) (v₀ : X → ℝ) : ℕ → X → ℝ
  | 0 => v₀
  | n + 1 => (D.T (D.greedy (opi m v₀ n)))^[m] (opi m v₀ n)

/-- One OPI step from a point mapped up by `T` (Lemmas 2.2.1–2.2.4 of Chapter 2): if `u ≤ Tu`,
`σ` is `u`-greedy and `m ≥ 1`, then `w = T_σ^m u` satisfies `Tu ≤ w ≤ v*` and `w ≤ Tw`. -/
theorem opi_step {m : ℕ} (hm : 1 ≤ m) {u : X → ℝ} (hu : u ∈ D.V) (hup : u ≤ D.bellman u)
    {σ : P} (hσ : D.IsGreedy u σ) :
    (D.T σ)^[m] u ∈ D.V ∧ D.bellman u ≤ (D.T σ)^[m] u ∧ (D.T σ)^[m] u ≤ D.vstar ∧
      (D.T σ)^[m] u ≤ D.bellman ((D.T σ)^[m] u) := by
  have hTu : D.T σ u = D.bellman u := (D.isGreedy_iff hu σ).1 hσ
  have hle : u ≤ D.T σ u := hTu ▸ hup
  -- the iterates `T_σᵏ u` increase
  have hinc : ∀ k, (D.T σ)^[k] u ≤ (D.T σ)^[k + 1] u := by
    intro k
    induction k with
    | zero => simpa using hle
    | succ k ih =>
      have := D.mono σ _ ((D.mapsTo σ).iterate k hu) _ ((D.mapsTo σ).iterate (k + 1) hu) ih
      simpa only [iterate_succ_apply'] using this
  have hmono : Monotone fun k => (D.T σ)^[k] u := monotone_nat_of_le_succ hinc
  have hwV := (D.mapsTo σ).iterate m hu
  refine ⟨hwV, ?_, ?_, ?_⟩
  · rw [← hTu]
    simpa using hmono hm
  · -- `T_σ^m u ≤ T_σ^m v_σ = v_σ ≤ v*`
    have hvσ := D.le_vσ hu hle
    have : ∀ k, (D.T σ)^[k] u ≤ D.vσ σ := by
      intro k
      induction k with
      | zero => exact hvσ
      | succ k ih =>
        rw [iterate_succ_apply']
        calc D.T σ ((D.T σ)^[k] u) ≤ D.T σ (D.vσ σ) :=
              D.mono σ _ ((D.mapsTo σ).iterate k hu) _ (D.vσ_mem σ) ih
          _ = D.vσ σ := D.T_vσ σ
    exact (this m).trans (D.vσ_le_vstar σ)
  · calc (D.T σ)^[m] u ≤ (D.T σ)^[m + 1] u := hinc m
      _ = D.T σ ((D.T σ)^[m] u) := iterate_succ_apply' _ _ _
      _ ≤ D.bellman ((D.T σ)^[m] u) := D.T_le_bellman σ hwV

/-- **Theorem 1.2.2**, OPI part (p. 24): if each `T_σ` shifts constants by `β`, then for every
`m ≥ 1` and every `v₀ ∈ V` the OPI sequence converges uniformly to `v*`. The proof runs OPI from
`v₀ − c`, which is mapped up by `T`, and squeezes it between `Tⁿ(v₀ − c)` and `v*`. -/
theorem tendsto_opi {m : ℕ} (hm : 1 ≤ m)
    (hshift : ∀ σ, ∀ v ∈ D.V, ∀ c : ℝ, D.T σ (fun x => v x - c) = fun x => D.T σ v x - D.β * c)
    (hVshift : ∀ v ∈ D.V, ∀ c : ℝ, (fun x => v x - c) ∈ D.V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ D.V) :
    TendstoUniformly (D.opi m v₀) D.vstar atTop := by
  set β := D.β
  -- shifting commutes with iterates of `T_σ` and with the greedy choice
  have hiter : ∀ σ k, ∀ v ∈ D.V, ∀ c : ℝ,
      (D.T σ)^[k] (fun x => v x - c) = fun x => (D.T σ)^[k] v x - β ^ k * c := by
    intro σ k
    induction k with
    | zero => intro v _ c; simp
    | succ k ih =>
      intro v hv c
      rw [iterate_succ_apply', iterate_succ_apply', ih v hv c,
        hshift σ _ ((D.mapsTo σ).iterate k hv)]
      funext x
      ring
  have hgreedy : ∀ v ∈ D.V, ∀ c : ℝ, D.IsGreedy (fun x => v x - c) (D.greedy v) := by
    intro v hv c τ x
    rw [hshift τ v hv, hshift _ v hv]
    simp only
    linarith [D.isGreedy_greedy hv τ x]
  have hbshift : ∀ v ∈ D.V, ∀ c : ℝ,
      D.bellman (fun x => v x - c) = fun x => D.bellman v x - β * c := by
    intro v hv c
    rw [← (D.isGreedy_iff (hVshift v hv c) _).1 (hgreedy v hv c), hshift _ v hv]
    rfl
  -- the starting shift
  obtain ⟨c₁, hc₁0, hc₁⟩ := (D.bdd _ (D.bellman_mapsTo hv₀)).exists_dist (D.bdd _ hv₀)
  set c := c₁ / (1 - β)
  have h1β : 0 < 1 - β := sub_pos.2 D.β_lt_one
  have hc0 : 0 ≤ c := div_nonneg hc₁0 h1β.le
  have hcc : c₁ = (1 - β) * c := by rw [mul_div_cancel₀ _ h1β.ne']
  set u : ℕ → X → ℝ := fun n x => D.opi m v₀ n x - β ^ (n * m) * c
  have hu0 : u 0 = fun x => v₀ x - c := by funext x; simp [u, opi]
  have hstep : ∀ n, D.opi m v₀ n ∈ D.V → u (n + 1) =
      (D.T (D.greedy (D.opi m v₀ n)))^[m] (u n) := by
    intro n hn
    have : u n = fun x => D.opi m v₀ n x - β ^ (n * m) * c := rfl
    rw [this, hiter _ m _ hn]
    funext x
    simp only [u, opi]
    rw [add_mul, one_mul, pow_add]
    ring
  have hu0V : u 0 ∈ D.V := hu0 ▸ hVshift v₀ hv₀ c
  -- invariants: `u n ∈ V`, `u n ≤ T(u n)`, `Tⁿ u₀ ≤ u n ≤ v*`, and `opi n ∈ V`
  have hinv : ∀ n, D.opi m v₀ n ∈ D.V ∧ u n ∈ D.V ∧ u n ≤ D.bellman (u n) ∧
      D.bellman^[n] (u 0) ≤ u n ∧ u n ≤ D.vstar := by
    intro n
    induction n with
    | zero =>
      have hup : u 0 ≤ D.bellman (u 0) := by
        rw [hu0, hbshift v₀ hv₀ c]
        intro x
        have := (abs_le.1 (hc₁ x)).1
        simp only
        nlinarith
      exact ⟨hv₀, hu0V, hup, le_rfl, D.le_vstar_of_le_bellman hu0V hup⟩
    | succ n ih =>
      obtain ⟨hon, hun, hup, hlow, -⟩ := ih
      have hσ : D.IsGreedy (u n) (D.greedy (D.opi m v₀ n)) := by
        have := hgreedy _ hon (β ^ (n * m) * c)
        exact this
      obtain ⟨hwV, hTw, hwle, hwup⟩ := D.opi_step hm hun hup hσ
      have hon' : D.opi m v₀ (n + 1) ∈ D.V := (D.mapsTo _).iterate m hon
      rw [← hstep n hon] at hwV hTw hwle hwup
      refine ⟨hon', hwV, hwup, ?_, hwle⟩
      rw [iterate_succ_apply']
      exact (D.bellman_mono (D.bellman_mapsTo.iterate n hu0V) hun hlow).trans hTw
  -- squeeze: `Tⁿ u₀ ≤ u n ≤ v*` and `Tⁿ u₀ → v*`, while `opi n − u n = β^{nm} c → 0`
  have hlim := D.tendsto_bellman_iterate hu0V
  have hpow : Tendsto (fun n : ℕ => β ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.β_nonneg D.β_lt_one).mul_const c
  rw [Metric.tendstoUniformly_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim (ε / 2) (half_pos hε), (tendsto_order.1 hpow).2 (ε / 2) (half_pos hε)]
    with n hn hn' x
  obtain ⟨-, -, -, hlow, hup⟩ := hinv n
  have h1 := hn x
  have hpm : β ^ (n * m) ≤ β ^ n :=
    pow_le_pow_of_le_one D.β_nonneg D.β_lt_one.le (Nat.le_mul_of_pos_right n hm)
  have hpm' : β ^ (n * m) * c ≤ β ^ n * c := mul_le_mul_of_nonneg_right hpm hc0
  have hpm0 : 0 ≤ β ^ (n * m) * c := mul_nonneg (pow_nonneg D.β_nonneg _) hc0
  have hl := hlow x
  have hu := hup x
  simp only [u] at hl hu
  rw [Real.dist_eq] at h1 ⊢
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end ContractingDP

end SargentStachurski.ADPTransformations
