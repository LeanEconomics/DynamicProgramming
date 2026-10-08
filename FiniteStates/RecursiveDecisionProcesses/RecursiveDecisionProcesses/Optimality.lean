/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.RDP

/-!
# Optimality for recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.3.3–§8.1.4
(pp. 257–262).

The book states Theorems 8.1.1 and 8.1.2 and defers their proofs to Chapter 9.
Both are proved here from one lemma. Call `R` *comparable* if, for feasible `σ, τ`,
`T_τ v_σ ≤ v_σ` implies `v_τ ≤ v_σ` and `v_σ ≤ T_τ v_σ` implies `v_σ ≤ v_τ`.
Global stability gives this by iterating `T_τ` from `v_σ`; boundedness gives it
by the Knaster–Tarski theorem on `[v₁, v_σ]` and `[v_σ, v₂]`. For a well-posed
comparable RDP:

* HPI improves: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_σ'`; the HPI values are
  monotone and take finitely many values, so some step repeats a value, and there
  the value is a fixed point of `T`.
* Every fixed point `v ∈ V` of `T` is `v_σ` for its greedy `σ` and dominates every
  `v_τ`, so it is `v*`: (i) of Theorem 8.1.1. Then (ii) Bellman's principle,
  (iii) existence and (iv) finite termination of HPI follow.
* Under global stability, (v): VFI from any `v_σ` converges to `v*`, squeezed
  between `T_{σ*}ᵏ v_σ` and `v*`; the OPI values satisfy `Tᵏv₀ ≤ vₖ ≤ v_{σₖ} ≤ v*`, so
  they converge to `v*`, and since there are finitely many policies, each
  suboptimal one falls short of `v*` somewhere and is eventually never greedy.

Also: the nonstationary-policy bound of §8.1.3.5, bounded RDPs with Exercises
8.1.12–8.1.13, and Proposition 8.1.3 on topologically conjugate RDPs with
Exercise 8.1.18.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The comparison property behind Theorems 8.1.1 and 8.1.2. -/
def Comparable : Prop :=
  ∀ σ τ : X → A, R.IsFeasible σ → R.IsFeasible τ →
    (R.Tσ τ (R.vσ σ) ≤ R.vσ σ → R.vσ τ ≤ R.vσ σ) ∧ (R.vσ σ ≤ R.Tσ τ (R.vσ σ) → R.vσ σ ≤ R.vσ τ)

/-- Under global stability, `T_τ v ≤ v` with `v ∈ V` gives `v_τ ≤ v`. -/
theorem vσ_le_of_Tσ_le {R : RDP X A} (hR : R.IsGloballyStable) {τ : X → A}
    (hτ : R.IsFeasible τ) {v : X → ℝ} (hv : v ∈ R.V) (hle : R.Tσ τ v ≤ v) : R.vσ τ ≤ v := by
  have hk : ∀ k, (R.Tσ τ)^[k] v ≤ v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (R.Tσ_monotoneOn hτ ((R.Tσ_mapsTo hτ).iterate k hv) hv ih).trans hle
  intro x
  exact le_of_tendsto' (tendsto_pi_nhds.1 (tendsto_iterate_Tσ hR hτ hv) x) fun k => hk k x

/-- Under global stability, `v ≤ T_τ v` with `v ∈ V` gives `v ≤ v_τ`. -/
theorem le_vσ_of_le_Tσ {R : RDP X A} (hR : R.IsGloballyStable) {τ : X → A}
    (hτ : R.IsFeasible τ) {v : X → ℝ} (hv : v ∈ R.V) (hle : v ≤ R.Tσ τ v) : v ≤ R.vσ τ := by
  have hk : ∀ k, v ≤ (R.Tσ τ)^[k] v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hle.trans (R.Tσ_monotoneOn hτ hv ((R.Tσ_mapsTo hτ).iterate k hv) ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 (tendsto_iterate_Tσ hR hτ hv) x) fun k => hk k x

/-- A globally stable RDP is comparable. -/
theorem IsGloballyStable.comparable {R : RDP X A} (hR : R.IsGloballyStable) : R.Comparable :=
  fun _ _ hσ hτ => ⟨vσ_le_of_Tσ_le hR hτ (vσ_mem hR.wellPosed hσ),
    le_vσ_of_le_Tσ hR hτ (vσ_mem hR.wellPosed hσ)⟩

/-! ### The optimality argument -/

/-- HPI improvement: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_{σ'}`. -/
theorem vσ_le_vσ_greedy {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {σ : X → A}
    (hσ : R.IsFeasible σ) : R.vσ σ ≤ R.vσ (R.greedy (R.vσ σ)) := by
  refine (hc σ _ hσ (R.greedy_mem _)).2 ?_
  rw [R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy _)]
  calc R.vσ σ = R.Tσ σ (R.vσ σ) := (isFixedPt_vσ hw hσ).eq.symm
    _ ≤ R.T (R.vσ σ) := R.Tσ_le_T hσ _

/-- A fixed point `v ∈ V` of `T` is the value of its greedy policy. -/
theorem eq_vσ_greedy_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) {v : X → ℝ} (hv : v ∈ R.V)
    (hfix : IsFixedPt R.T v) : v = R.vσ (R.greedy v) := by
  refine eq_vσ_of_isFixedPt hw (R.greedy_mem v) hv ?_
  change R.Tσ (R.greedy v) v = v
  rw [R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v), hfix.eq]

/-- A fixed point `v ∈ V` of `T` dominates every `v_τ`. -/
theorem vσ_le_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {v : X → ℝ}
    (hv : v ∈ R.V) (hfix : IsFixedPt R.T v) {τ : X → A} (hτ : R.IsFeasible τ) : R.vσ τ ≤ v := by
  have hv' := eq_vσ_greedy_of_isFixedPt hw hv hfix
  have h1 : R.Tσ τ (R.vσ (R.greedy v)) ≤ R.vσ (R.greedy v) := by
    rw [← hv']
    exact (R.Tσ_le_T hτ v).trans_eq hfix.eq
  rw [hv']
  exact (hc _ τ (R.greedy_mem v) hτ).1 h1

variable [DecidableEq X] [DecidableEq A]

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI values are monotone. -/
theorem hpiValue_mono {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) (σ : R.Policy) :
    Monotone (R.hpiValue σ) := by
  classical
  exact
  monotone_nat_of_le_succ fun k => vσ_le_vσ_greedy hw hc (R.hpiPolicy σ k).2

omit [DecidableEq X] [DecidableEq A] in
/-- HPI terminates: some step leaves the value unchanged, since a strictly increasing sequence of
values would make the finitely many policies infinitely many. -/
theorem exists_hpiValue_succ_eq {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable)
    (σ : R.Policy) : ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k := by
  classical
  by_contra hcon
  have hne : ∀ k, R.hpiValue σ k ≠ R.hpiValue σ (k + 1) := fun k h =>
    hcon ⟨k, h.symm⟩
  have hsm : StrictMono (R.hpiValue σ) :=
    strictMono_nat_of_lt_succ fun k =>
      lt_of_le_of_ne (hpiValue_mono hw hc σ (Nat.le_succ k)) (hne k)
  have hinj : Injective (R.hpiPolicy σ) := fun i j hij => hsm.injective (by
    simp only [hpiValue, hij])
  exact not_injective_infinite_finite _ hinj

omit [DecidableEq X] [DecidableEq A] in
/-- Where HPI stops, the value is a fixed point of `T`. -/
theorem isFixedPt_T_hpiValue {R : RDP X A} (hw : R.WellPosed) {σ : R.Policy} {k : ℕ}
    (hk : R.hpiValue σ (k + 1) = R.hpiValue σ k) : IsFixedPt R.T (R.hpiValue σ k) := by
  classical
  have hg := R.isGreedy_greedy (R.hpiValue σ k)
  change R.T (R.hpiValue σ k) = R.hpiValue σ k
  rw [← R.Tσ_eq_T_of_isGreedy hg]
  have h1 : R.vσ (R.greedy (R.hpiValue σ k)) = R.hpiValue σ k := hk
  have h2 := (isFixedPt_vσ hw (R.greedy_mem (R.hpiValue σ k))).eq
  rw [h1] at h2
  exact h2

/-- `T` has a fixed point in `V` that dominates every `v_σ`, so it equals `v*`. -/
theorem vstar_spec {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar := by
  obtain ⟨k, hk⟩ := exists_hpiValue_succ_eq hw hc R.defaultPolicy
  have hfix := isFixedPt_T_hpiValue hw hk
  have hmem : R.hpiValue R.defaultPolicy k ∈ R.V := vσ_mem hw (R.hpiPolicy _ k).2
  have heq : R.vstar = R.hpiValue R.defaultPolicy k := by
    funext x
    refine le_antisymm (Finset.sup'_le _ _ fun τ _ => vσ_le_of_isFixedPt hw hc hmem hfix τ.2 x) ?_
    exact R.vσ_le_vstar (R.hpiPolicy _ k).2 x
  rw [heq]
  exact ⟨hmem, hfix⟩

/-- **Theorem 8.1.1 (i)** / **Theorem 8.1.2 (i)**, uniqueness: `v*` is the only fixed point of `T`
in `V`. -/
theorem eq_vstar_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {v : X → ℝ}
    (hv : v ∈ R.V) (hfix : IsFixedPt R.T v) : v = R.vstar := by
  funext x
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun τ _ => vσ_le_of_isFixedPt hw hc hv hfix τ.2 x)
  rw [eq_vσ_greedy_of_isFixedPt hw hv hfix]
  exact R.vσ_le_vstar (R.greedy_mem v) x

/-- **Theorem 8.1.1 (ii)** / **Theorem 8.1.2 (ii)**: Bellman's principle of optimality. -/
theorem principleOfOptimality {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    R.PrincipleOfOptimality := by
  obtain ⟨hmem, hfix⟩ := vstar_spec hw hc
  intro σ hσ
  constructor
  · rintro ⟨-, h⟩
    rw [R.isGreedy_iff_Tσ_eq_T _ hσ, ← h, (isFixedPt_vσ hw hσ).eq, h, hfix.eq]
  · intro hg
    refine ⟨hσ, (eq_vσ_of_isFixedPt hw hσ hmem ?_).symm⟩
    change R.Tσ σ R.vstar = R.vstar
    rw [R.Tσ_eq_T_of_isGreedy hg, hfix.eq]

/-- **Theorem 8.1.1 (iii)** / **Theorem 8.1.2 (iii)**: an optimal policy exists. -/
theorem exists_isOptimal {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    ∃ σ, R.IsOptimal σ :=
  ⟨_, (principleOfOptimality hw hc _ (R.greedy_mem _)).2 (R.isGreedy_greedy _)⟩

/-- **Theorem 8.1.1 (iv)** / **Theorem 8.1.2 (iv)**: HPI returns an optimal policy in finitely many
steps: from any `σ` there is a `k` with `vₖ₊₁ = vₖ`, where Algorithm 8.1 stops, and the returned
`vₖ`-greedy policy `σₖ₊₁` is optimal. -/
theorem hpi_terminates {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) (σ : R.Policy) :
    ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧ R.IsOptimal (R.hpiPolicy σ (k + 1)).1 := by
  obtain ⟨k, hk⟩ := exists_hpiValue_succ_eq hw hc σ
  refine ⟨k, hk, (R.hpiPolicy σ (k + 1)).2, ?_⟩
  have hmem : R.hpiValue σ k ∈ R.V := vσ_mem hw (R.hpiPolicy σ k).2
  change R.hpiValue σ (k + 1) = R.vstar
  rw [hk]
  exact eq_vstar_of_isFixedPt hw hc hmem (isFixedPt_T_hpiValue hw hk)

/-! ### Theorem 8.1.1 (v): VFI and OPI -/

/-- Value function iteration from any `v_σ` converges to `v*` under global stability. -/
theorem tendsto_iterate_T_vσ {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) : Tendsto (fun k : ℕ => R.T^[k] (R.vσ σ)) atTop (𝓝 R.vstar) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  obtain ⟨hstar, hfix⟩ := vstar_spec hw hc
  obtain ⟨σs, hσs⟩ := exists_isOptimal hw hc
  have hv := vσ_mem hw hσ
  -- lower bound `T_{σ*}ᵏ v_σ ≤ Tᵏ v_σ`, upper bound `Tᵏ v_σ ≤ v*`
  have hlow : ∀ k, (R.Tσ σs)^[k] (R.vσ σ) ≤ R.T^[k] (R.vσ σ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply']
      exact (R.Tσ_monotoneOn hσs.1 ((R.Tσ_mapsTo hσs.1).iterate k hv) (R.T_mapsTo.iterate k hv)
        ih).trans (R.Tσ_le_T hσs.1 _)
  have hup : ∀ k, R.T^[k] (R.vσ σ) ≤ R.vstar := fun k => by
    have := R.iterate_T_mono hv hstar (R.vσ_le_vstar hσ) k
    rwa [(hfix.iterate k).eq] at this
  have hlim := tendsto_iterate_Tσ hR hσs.1 hv
  rw [hσs.2] at hlim
  rw [tendsto_pi_nhds] at hlim ⊢
  intro x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim x) tendsto_const_nhds
    (fun k => hlow k x) (fun k => hup k x)

omit [DecidableEq X] [DecidableEq A] in
/-- The OPI values stay in `{v ∈ V : v ≤ Tv}`, dominate the VFI values `Tᵏv₀` and lie below the
value of their greedy policy. -/
theorem opiValue_spec {R : RDP X A} (hR : R.IsGloballyStable) {m : ℕ} (hm : 1 ≤ m) {σ : X → A}
    (hσ : R.IsFeasible σ) (k : ℕ) :
    R.opiValue m σ k ∈ R.V ∧ R.opiValue m σ k ≤ R.T (R.opiValue m σ k) ∧
      R.T^[k] (R.vσ σ) ≤ R.opiValue m σ k ∧
      R.opiValue m σ k ≤ R.vσ (R.greedy (R.opiValue m σ k)) := by
  classical
  have hw := hR.wellPosed
  -- the key step: `W_m` maps `{v ∈ V : v ≤ Tv}` into itself and `Tv ≤ W_m v`
  have step : ∀ v ∈ R.V, v ≤ R.T v →
      R.opiW m v ∈ R.V ∧ R.opiW m v ≤ R.T (R.opiW m v) ∧ R.T v ≤ R.opiW m v ∧
        v ≤ R.vσ (R.greedy v) := by
    intro v hv hvT
    set g := R.greedy v
    have hg := R.isGreedy_greedy v
    have hgv : v ≤ R.Tσ g v := by rw [R.Tσ_eq_T_of_isGreedy hg]; exact hvT
    have hmon : ∀ j, (R.Tσ g)^[j] v ≤ (R.Tσ g)^[j + 1] v := by
      intro j
      have := R.iterate_Tσ_mono hg.1 hv ((R.Tσ_mapsTo hg.1) hv) hgv j
      rwa [← iterate_succ_apply] at this
    have hge : ∀ j, R.Tσ g v ≤ (R.Tσ g)^[j + 1] v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => exact ih.trans (hmon (j + 1))
    have hWmem : R.opiW m v ∈ R.V := (R.Tσ_mapsTo hg.1).iterate m hv
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨hWmem, ?_, ?_, le_vσ_of_le_Tσ hR hg.1 hv hgv⟩
    · calc R.opiW (m' + 1) v = (R.Tσ g)^[m' + 1] v := rfl
        _ ≤ (R.Tσ g)^[m' + 1 + 1] v := hmon (m' + 1)
        _ = R.Tσ g ((R.Tσ g)^[m' + 1] v) := iterate_succ_apply' _ _ _
        _ ≤ R.T ((R.Tσ g)^[m' + 1] v) := R.Tσ_le_T hg.1 _
    · rw [← R.Tσ_eq_T_of_isGreedy hg]
      exact hge m'
  have hv0 := vσ_mem hw hσ
  have hv0T : R.vσ σ ≤ R.T (R.vσ σ) :=
    ((isFixedPt_vσ hw hσ).eq.symm.le).trans (R.Tσ_le_T hσ _)
  have main : ∀ k, R.opiValue m σ k ∈ R.V ∧ R.opiValue m σ k ≤ R.T (R.opiValue m σ k) ∧
      R.T^[k] (R.vσ σ) ≤ R.opiValue m σ k := by
    intro k
    induction k with
    | zero => exact ⟨hv0, hv0T, le_rfl⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3, -⟩ := step _ h1 h2
      have e : R.opiValue m σ (k + 1) = R.opiW m (R.opiValue m σ k) :=
        iterate_succ_apply' _ _ _
      rw [e, iterate_succ_apply']
      exact ⟨g1, g2, (R.T_monotoneOn (R.T_mapsTo.iterate k hv0) h1 h3).trans g3⟩
  obtain ⟨h1, h2, h3⟩ := main k
  exact ⟨h1, h2, h3, (step _ h1 h2).2.2.2⟩

/-- **Theorem 8.1.1 (v)** (p. 257): under global stability, for every `m ≥ 1` and initial `v_σ`, the
OPI values converge to `v*`, and the greedy policies are optimal from some step on. With `m = 1`
this is value function iteration. -/
theorem opi_converges {R : RDP X A} (hR : R.IsGloballyStable) {m : ℕ} (hm : 1 ≤ m) {σ : X → A}
    (hσ : R.IsFeasible σ) :
    Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) ∧
      ∃ K, ∀ k ≥ K, R.IsOptimal (R.greedy (R.opiValue m σ k)) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  have hspec := opiValue_spec hR hm hσ
  have hup : ∀ k, R.opiValue m σ k ≤ R.vstar := fun k =>
    (hspec k).2.2.2.trans (R.vσ_le_vstar (R.greedy_mem _))
  have hconv : Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) := by
    have hlim := tendsto_iterate_T_vσ hR hσ
    rw [tendsto_pi_nhds] at hlim ⊢
    intro x
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim x) tendsto_const_nhds
      (fun k => (hspec k).2.2.1 x) (fun k => hup k x)
  refine ⟨hconv, ?_⟩
  -- each suboptimal policy falls short of `v*` at some state
  have hgap : ∀ τ : R.Policy, ∀ᶠ k in atTop,
      ¬ R.IsOptimal τ.1 → ∃ x, R.vσ τ.1 x < R.opiValue m σ k x := by
    intro τ
    by_cases hopt : R.IsOptimal τ.1
    · exact Eventually.of_forall fun _ h => absurd hopt h
    · have hlt : ∃ x, R.vσ τ.1 x < R.vstar x := by
        by_contra hcon
        exact hopt ⟨τ.2, le_antisymm (R.vσ_le_vstar τ.2) fun x => not_lt.1 fun h => hcon ⟨x, h⟩⟩
      obtain ⟨x, hx⟩ := hlt
      filter_upwards [(tendsto_pi_nhds.1 hconv x).eventually (lt_mem_nhds hx)] with k hk _
      exact ⟨x, hk⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_all.2 hgap)
  refine ⟨K, fun k hk => ?_⟩
  by_contra hnot
  obtain ⟨x, hx⟩ := hK k hk (R.greedyPolicy (R.opiValue m σ k)) hnot
  exact absurd ((hspec k).2.2.2 x) (not_le.2 hx)

/-- **Theorem 8.1.1** (p. 257): for a globally stable RDP, (i) `v*` is the unique solution of the
Bellman equation in `V`, (ii) Bellman's principle of optimality holds, (iii) an optimal policy
exists, (iv) HPI returns an optimal policy in finitely many steps, and (v) OPI converges, with
eventually optimal greedy policies. -/
theorem optimality_of_globallyStable {R : RDP X A} (hR : R.IsGloballyStable) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      R.PrincipleOfOptimality ∧ (∃ σ, R.IsOptimal σ) ∧
      (∀ σ : R.Policy, ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧
        R.IsOptimal (R.hpiPolicy σ (k + 1)).1) ∧
      ∀ m, 1 ≤ m → ∀ σ, R.IsFeasible σ → Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) ∧
        ∃ K, ∀ k ≥ K, R.IsOptimal (R.greedy (R.opiValue m σ k)) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  exact ⟨⟨(vstar_spec hw hc).1, (vstar_spec hw hc).2,
    fun v hv h => eq_vstar_of_isFixedPt hw hc hv h⟩,
    principleOfOptimality hw hc, exists_isOptimal hw hc, hpi_terminates hw hc,
    fun m hm σ hσ => opi_converges hR hm hσ⟩

/-! ### Nonstationary policies (§8.1.3.5) -/

omit [DecidableEq X] [DecidableEq A] in
/-- §8.1.3.5 (p. 259): under global stability, the finite-horizon values of any policy sequence are
eventually within `ε` of `v*` from below: `T_{σₖ} ⋯ T_{σ₁} v ≤ Tᵏv` and `Tᵏv_σ → v*`, so the
lifetime value `limsup` of a nonstationary policy is at most `v*`. -/
theorem nonstationary_le_vstar [DecidableEq X] [DecidableEq A] {R : RDP X A}
    (hR : R.IsGloballyStable) (σs : ℕ → X → A) (hσs : ∀ k, R.IsFeasible (σs k)) {σ : X → A}
    (hσ : R.IsFeasible σ) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (Nat.rec (R.vσ σ) fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k x ≤ R.vstar x + ε := by
  have hlim := tendsto_pi_nhds.1 (tendsto_iterate_T_vσ hR hσ) x
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : R.vstar x < R.vstar x + ε))]
    with k hk
  exact ((R.nonstationary_le σs hσs (vσ_mem hR.wellPosed hσ) k).2 x).trans hk.le

/-! ### Bounded RDPs (§8.1.3.6) -/

omit [DecidableEq X] [DecidableEq A] in
/-- `R` is bounded (§8.1.3.6) by `v₁ ≤ v₂` in `V` with `[v₁, v₂] ⊆ V` and (8.20):
`v₁(x) ≤ B(x, a, v₁)` and `B(x, a, v₂) ≤ v₂(x)` on `G`. -/
def IsBoundedBy (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ Set.Icc v₁ v₂ ⊆ R.V ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x ≤ R.B x a v₁ ∧ R.B x a v₂ ≤ v₂ x

omit [DecidableEq X] [DecidableEq A] in
/-- Policy operators of a bounded RDP map `[v₁, v₂]` into itself. -/
theorem Tσ_mapsTo_Icc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) : MapsTo (R.Tσ σ) (Set.Icc v₁ v₂) (Set.Icc v₁ v₂) := by
  intro v hv
  have h1 : v₁ ∈ R.V := hb.2.1 ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ R.V := hb.2.1 ⟨hb.1, le_rfl⟩
  exact ⟨fun x => (hb.2.2 x _ (hσ x)).1.trans (R.mono x _ (hσ x) v₁ h1 v (hb.2.1 hv) hv.1),
    fun x => (R.mono x _ (hσ x) v (hb.2.1 hv) v₂ h2 hv.2).trans (hb.2.2 x _ (hσ x)).2⟩

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.12 (p. 259): a bounded RDP restricts to an RDP on `[v₁, v₂]`. -/
def restrictIcc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) : RDP X A where
  Γ := R.Γ
  Γ_nonempty := R.Γ_nonempty
  V := Set.Icc v₁ v₂
  B := R.B
  mono := fun x a ha v hv w hw hvw => R.mono x a ha v (hb.2.1 hv) w (hb.2.1 hw) hvw
  consistent := fun _ hσ _ hv => R.Tσ_mapsTo_Icc hb hσ hv

omit [DecidableEq X] [DecidableEq A] in
/-- A fixed point of `T_σ` in a subinterval `[u, w] ⊆ [v₁, v₂]` with `u ≤ T_σ u` and `T_σ w ≤ w`,
by Knaster–Tarski. -/
theorem exists_fixedPt_Icc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) {u w : X → ℝ} (hu : u ∈ Set.Icc v₁ v₂) (hw : w ∈ Set.Icc v₁ v₂)
    (huw : u ≤ w) (hTu : u ≤ R.Tσ σ u) (hTw : R.Tσ σ w ≤ w) :
    ∃ z ∈ Set.Icc u w, IsFixedPt (R.Tσ σ) z := by
  have hsub : Set.Icc u w ⊆ R.V := fun z hz => hb.2.1 ⟨hu.1.trans hz.1, hz.2.trans hw.2⟩
  have hmono : MonotoneOn (R.Tσ σ) (Set.Icc u w) := (R.Tσ_monotoneOn hσ).mono hsub
  have hmaps : MapsTo (R.Tσ σ) (Set.Icc u w) (Set.Icc u w) := fun z hz =>
    ⟨hTu.trans (hmono ⟨le_rfl, huw⟩ hz hz.1), (hmono hz ⟨huw, le_rfl⟩ hz.2).trans hTw⟩
  obtain ⟨a, ha, -, -, hafix, -⟩ := knaster_tarski huw hmaps hmono
  exact ⟨a, ha, hafix⟩

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.13 (p. 259): in a well-posed bounded RDP, `v_σ ∈ [v₁, v₂]`. -/
theorem vσ_mem_Icc {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂)
    {σ : X → A} (hσ : R.IsFeasible σ) : R.vσ σ ∈ Set.Icc v₁ v₂ := by
  have h1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨hb.1, le_rfl⟩
  obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hσ h1 h2 hb.1
    (fun x => (hb.2.2 x _ (hσ x)).1) (fun x => (hb.2.2 x _ (hσ x)).2)
  rw [← eq_vσ_of_isFixedPt hw hσ (hb.2.1 hz) hzfix]
  exact hz

omit [DecidableEq X] [DecidableEq A] in
/-- A well-posed bounded RDP is comparable, by Knaster–Tarski on `[v₁, v_σ]` and `[v_σ, v₂]`. -/
theorem comparable_of_bounded {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ}
    (hb : R.IsBoundedBy v₁ v₂) : R.Comparable := by
  intro σ τ hσ hτ
  have hvσ := vσ_mem_Icc hw hb hσ
  have h1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨hb.1, le_rfl⟩
  constructor
  · intro hle
    obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hτ h1 hvσ hvσ.1
      (fun x => (hb.2.2 x _ (hτ x)).1) hle
    rw [← eq_vσ_of_isFixedPt hw hτ (hb.2.1 ⟨hz.1, hz.2.trans hvσ.2⟩) hzfix]
    exact hz.2
  · intro hle
    obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hτ hvσ h2 hvσ.2 hle
      (fun x => (hb.2.2 x _ (hτ x)).2)
    rw [← eq_vσ_of_isFixedPt hw hτ (hb.2.1 ⟨hvσ.1.trans hz.1, hz.2⟩) hzfix]
    exact hz.1

/-- **Theorem 8.1.2** (p. 260): for a well-posed bounded RDP, (i) `v*` is the unique solution of the
Bellman equation in `V`, (ii) Bellman's principle of optimality holds, (iii) an optimal policy
exists and (iv) HPI returns an optimal policy in finitely many steps. -/
theorem optimality_of_bounded {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ}
    (hb : R.IsBoundedBy v₁ v₂) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      R.PrincipleOfOptimality ∧ (∃ σ, R.IsOptimal σ) ∧
      ∀ σ : R.Policy, ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧
        R.IsOptimal (R.hpiPolicy σ (k + 1)).1 := by
  have hc := comparable_of_bounded hw hb
  exact ⟨⟨(vstar_spec hw hc).1, (vstar_spec hw hc).2,
    fun v hv h => eq_vstar_of_isFixedPt hw hc hv h⟩,
    principleOfOptimality hw hc, exists_isOptimal hw hc, hpi_terminates hw hc⟩

end RDP

/-! ### Topologically conjugate RDPs (§8.1.4) -/

/-- Exercise 8.1.18 (p. 261): if `φ` is continuous on `M` then `Φv = φ ∘ v` is continuous on
`M^X`. -/
theorem continuousOn_comp_pi {X : Type*} {M : Set ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ M) :
    ContinuousOn (fun v : X → ℝ => φ ∘ v) {v | ∀ x, v x ∈ M} :=
  continuousOn_pi.2 fun x => hφ.comp (continuous_apply x).continuousOn fun _ hv => hv x

/-- **Proposition 8.1.3** (p. 261): if `R = (Γ, M^X, B)` and `R̂ = (Γ, M̂^X, B̂)` are topologically
conjugate under a homeomorphism `φ : M → M̂` with inverse `ψ`, i.e.
`B(x, a, v) = ψ(B̂(x, a, φ ∘ v))`, then `R` is globally stable iff `R̂` is. -/
theorem RDP.isGloballyStable_iff_of_conj {X A : Type*} [Fintype X] [Fintype A] {R R' : RDP X A}
    (hΓ : R.Γ = R'.Γ) {M M' : Set ℝ} (hV : R.V = {v | ∀ x, v x ∈ M})
    (hV' : R'.V = {v | ∀ x, v x ∈ M'}) {φ ψ : ℝ → ℝ} (hφ : MapsTo φ M M') (hψ : MapsTo ψ M' M)
    (hφψ : ∀ t ∈ M', φ (ψ t) = t) (hψφ : ∀ t ∈ M, ψ (φ t) = t) (hφc : ContinuousOn φ M)
    (hψc : ContinuousOn ψ M')
    (hB : ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, R.B x a v = ψ (R'.B x a (φ ∘ v))) :
    R.IsGloballyStable ↔ R'.IsGloballyStable := by
  have hfeas : ∀ σ : X → A, R.IsFeasible σ ↔ R'.IsFeasible σ := fun σ => by
    simp only [RDP.IsFeasible, hΓ]
  have hΦ : MapsTo (fun v : X → ℝ => φ ∘ v) R.V R'.V := fun v hv => by
    rw [hV] at hv; rw [hV']; exact fun x => hφ (hv x)
  have hΨ : MapsTo (fun v : X → ℝ => ψ ∘ v) R'.V R.V := fun v hv => by
    rw [hV'] at hv; rw [hV]; exact fun x => hψ (hv x)
  have hΦΨ : ∀ v ∈ R'.V, (fun v : X → ℝ => φ ∘ v) ((fun v : X → ℝ => ψ ∘ v) v) = v :=
    fun v hv => by rw [hV'] at hv; funext x; exact hφψ _ (hv x)
  have hΨΦ : ∀ v ∈ R.V, (fun v : X → ℝ => ψ ∘ v) ((fun v : X → ℝ => φ ∘ v) v) = v :=
    fun v hv => by rw [hV] at hv; funext x; exact hψφ _ (hv x)
  have hΦc : ContinuousOn (fun v : X → ℝ => φ ∘ v) R.V := by
    rw [hV]; exact continuousOn_comp_pi hφc
  have hΨc : ContinuousOn (fun v : X → ℝ => ψ ∘ v) R'.V := by
    rw [hV']; exact continuousOn_comp_pi hψc
  have key : ∀ σ, R.IsFeasible σ →
      (GloballyStableOn (R.Tσ σ) R.V ↔ GloballyStableOn (R'.Tσ σ) R'.V) := by
    intro σ hσ
    have hσ' := (hfeas σ).1 hσ
    have hconj : ∀ v ∈ R.V, (fun v : X → ℝ => φ ∘ v) (R.Tσ σ v) =
        R'.Tσ σ ((fun v : X → ℝ => φ ∘ v) v) := by
      intro v hv
      have hmem : R'.Tσ σ (φ ∘ v) ∈ R'.V := R'.Tσ_mapsTo hσ' (hΦ hv)
      rw [hV'] at hmem
      funext x
      have e : R.Tσ σ v x = ψ (R'.Tσ σ (φ ∘ v) x) := hB x (σ x) (hσ x) v hv
      change φ (R.Tσ σ v x) = R'.Tσ σ (φ ∘ v) x
      rw [e, hφψ _ (hmem x)]
    exact globallyStableOn_iff_of_conj _ _ hΦ hΨ hΦΨ hΨΦ hΦc hΨc (R.Tσ_mapsTo hσ) hconj
  exact ⟨fun h σ hσ' => (key σ ((hfeas σ).2 hσ')).1 (h σ ((hfeas σ).2 hσ')),
    fun h σ hσ => (key σ hσ).2 (h σ ((hfeas σ).1 hσ))⟩

end SargentStachurski.RecursiveDecisionProcesses
