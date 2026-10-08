/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.OrderStability

/-!
# Abstract dynamic programs and max-optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.2 and §9.2.1.1–§9.2.1.5
(pp. 294–300), with the proofs of §B.4 (pp. 349–351).
Restated from the `FiniteStates/AbstractDynamicProgramming` project (Chapter 9), on which
the optimality theory of continuous-time MDPs in Chapter 10 rests.

An abstract dynamic program (ADP) `(V, {T_σ}_{σ ∈ Σ})` is a family of self-maps of a partially
ordered set `V` such that every `{T_σ v}_σ` has a greatest and a least element. Nothing else is
assumed: no topology, no finiteness of `V`.

* Greedy policies, the Bellman operator `Tv = ⋁_σ T_σ v` (9.5), Exercise 9.2.1, well-posedness,
  `σ`-value functions, `V_u = {v ≼ Tv}` and Exercise 9.2.3 (`V_Σ ⊆ V_u`), the Howard operator
  and HPI.
* Finite, order stable and max-stable ADPs (§9.2.1.3).
* Lemma B.4.1, Proposition 9.2.1 (finite and order stable implies max-stable),
  Proposition 9.2.5 (max-stable ADPs: the value function exists, is the unique fixed point of
  `T`, Bellman's principle of optimality, an optimal policy exists) and **Theorem 9.2.4**
  (max-optimality for finite order stable ADPs, with finite termination of HPI).
-/

open Function Set

namespace SargentStachurski.ContinuousTime

/-- An abstract dynamic program (§9.1.2.2): policy operators `T_σ`, `σ ∈ P`, on a partially
ordered set `V`, such that each `{T_σ v}_σ` has a greatest and a least element. -/
structure ADP (V P : Type*) [PartialOrder V] where
  T : P → V → V
  exists_greedy : ∀ v, ∃ σ, ∀ τ, T τ v ≤ T σ v
  exists_minGreedy : ∀ v, ∃ σ, ∀ τ, T σ v ≤ T τ v

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- `σ` is `v`-greedy (p. 295): `T_τ v ≼ T_σ v` for all `τ`. -/
def IsGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T τ v ≤ A.T σ v

/-- A chosen `v`-greedy policy. -/
noncomputable def greedy (v : V) : P := (A.exists_greedy v).choose

theorem isGreedy_greedy (v : V) : A.IsGreedy v (A.greedy v) := (A.exists_greedy v).choose_spec

/-- The Bellman operator (9.5): `Tv = ⋁_σ T_σ v`, attained at any `v`-greedy policy. -/
noncomputable def bellman (v : V) : V := A.T (A.greedy v) v

theorem T_le_bellman (σ : P) (v : V) : A.T σ v ≤ A.bellman v := A.isGreedy_greedy v σ

/-- `Tv` is the greatest element of `{T_σ v}_σ`. -/
theorem isGreatest_bellman (v : V) : IsGreatest (range fun σ => A.T σ v) (A.bellman v) :=
  ⟨⟨_, rfl⟩, by rintro _ ⟨τ, rfl⟩; exact A.T_le_bellman τ v⟩

/-- **Exercise 9.2.1 (i)** (p. 298): `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff (v : V) (σ : P) : A.IsGreedy v σ ↔ A.T σ v = A.bellman v :=
  ⟨fun h => le_antisymm (A.T_le_bellman σ v) (h _), fun h τ => h ▸ A.T_le_bellman τ v⟩

/-- **Exercise 9.2.1 (ii)** (p. 298): if every `T_σ` is order preserving, so is `T`. -/
theorem monotone_bellman (h : ∀ σ, Monotone (A.T σ)) : Monotone A.bellman :=
  fun _ w hvw => (h _ hvw).trans (A.T_le_bellman _ w)

/-- `A` is well-posed (p. 297): every `T_σ` has a unique fixed point. -/
def WellPosed : Prop := ∀ σ, ∃! v, IsFixedPt (A.T σ) v

/-- The `σ`-value function `v_σ` of a well-posed ADP. -/
noncomputable def vσ (hw : A.WellPosed) (σ : P) : V := (hw σ).exists.choose

variable {A}

theorem isFixedPt_vσ (hw : A.WellPosed) (σ : P) : IsFixedPt (A.T σ) (A.vσ hw σ) :=
  (hw σ).exists.choose_spec

theorem eq_vσ_of_isFixedPt (hw : A.WellPosed) {σ : P} {v : V} (h : IsFixedPt (A.T σ) v) :
    v = A.vσ hw σ :=
  (hw σ).unique h (isFixedPt_vσ hw σ)

variable (A)

/-- `V_u = {v ∈ V : v ≼ Tv}` (p. 299). -/
def Vu : Set V := {v | v ≤ A.bellman v}

/-- **Exercise 9.2.3** (p. 300): `V_Σ ⊆ V_u`. -/
theorem vσ_mem_Vu (hw : A.WellPosed) (σ : P) : A.vσ hw σ ∈ A.Vu :=
  (isFixedPt_vσ hw σ).eq.symm.le.trans (A.T_le_bellman σ _)

/-- The Howard operator: `Hv = v_σ` for the chosen `v`-greedy `σ` (p. 298). -/
noncomputable def howard (hw : A.WellPosed) (v : V) : V := A.vσ hw (A.greedy v)

/-- The HPI policies of Algorithm 8.1 for an ADP: `σ₀` given, `σₖ₊₁` is `v_{σₖ}`-greedy. -/
noncomputable def hpiPolicy (hw : A.WellPosed) (σ₀ : P) : ℕ → P
  | 0 => σ₀
  | k + 1 => A.greedy (A.vσ hw (hpiPolicy hw σ₀ k))

/-- The HPI values `vₖ = v_{σₖ}`, so that `vₖ₊₁ = H vₖ`. -/
noncomputable def hpiValue (hw : A.WellPosed) (σ₀ : P) (k : ℕ) : V :=
  A.vσ hw (A.hpiPolicy hw σ₀ k)

theorem hpiValue_succ (hw : A.WellPosed) (σ₀ : P) (k : ℕ) :
    A.hpiValue hw σ₀ (k + 1) = A.howard hw (A.hpiValue hw σ₀ k) := rfl

/-- `A` is order stable (p. 298): every policy operator is order stable. -/
def IsOrderStable : Prop := ∀ σ, OrderStable (A.T σ)

/-- `A` is max-stable (p. 298): order stable, and `T` has a fixed point. -/
def IsMaxStable : Prop := A.IsOrderStable ∧ ∃ v, IsFixedPt A.bellman v

variable {A}

/-- Order stable ADPs are well-posed. -/
theorem IsOrderStable.wellPosed (h : A.IsOrderStable) : A.WellPosed := fun σ => by
  obtain ⟨u, hu, huniq, -, -⟩ := h σ
  exact ⟨u, hu, huniq⟩

/-- Upward stability of `T_σ` around `v_σ`. -/
theorem IsOrderStable.le_vσ (h : A.IsOrderStable) {σ : P} {v : V} (hv : v ≤ A.T σ v) :
    v ≤ A.vσ h.wellPosed σ := by
  obtain ⟨u, hu, huniq, hup, -⟩ := h σ
  rw [huniq _ (isFixedPt_vσ h.wellPosed σ)]
  exact hup v hv

/-- Downward stability of `T_σ` around `v_σ`. -/
theorem IsOrderStable.vσ_le (h : A.IsOrderStable) {σ : P} {v : V} (hv : A.T σ v ≤ v) :
    A.vσ h.wellPosed σ ≤ v := by
  obtain ⟨u, hu, huniq, -, hdown⟩ := h σ
  rw [huniq _ (isFixedPt_vσ h.wellPosed σ)]
  exact hdown v hv

variable (A)

/-- `σ` is optimal: `v_σ` is the greatest element of `V_Σ = {v_τ}` (p. 300). -/
def IsOptimal (hw : A.WellPosed) (σ : P) : Prop := ∀ τ, A.vσ hw τ ≤ A.vσ hw σ

variable {A}

/-- **Lemma B.4.1 (i)** (p. 350): `v ∈ V_u ⇒ v ≼ Hv`. -/
theorem IsOrderStable.le_howard (h : A.IsOrderStable) {v : V} (hv : v ∈ A.Vu) :
    v ≤ A.howard h.wellPosed v :=
  h.le_vσ (hv.trans (A.isGreedy_greedy v (A.greedy v)) |>.trans_eq rfl)

/-- **Lemma B.4.1 (ii)** (p. 350): if `T v_σ = v_σ` then `v_σ` dominates every `v_τ`. -/
theorem IsOrderStable.isOptimal_of_isFixedPt (h : A.IsOrderStable) {σ : P}
    (hσ : IsFixedPt A.bellman (A.vσ h.wellPosed σ)) : A.IsOptimal h.wellPosed σ :=
  fun τ => h.vσ_le ((A.T_le_bellman τ _).trans_eq hσ.eq)

/-- If `Hv = v` then `v` is the value of the greedy policy and a fixed point of `T`. -/
theorem IsOrderStable.isFixedPt_of_howard (h : A.IsOrderStable) {v : V}
    (hv : A.howard h.wellPosed v = v) : IsFixedPt A.bellman v := by
  have h1 : A.vσ h.wellPosed (A.greedy v) = v := hv
  have h2 := (isFixedPt_vσ h.wellPosed (A.greedy v)).eq
  rw [h1] at h2
  exact h2

/-- **Lemma B.4.1 (iii)** (p. 350): if `Hv = v` then `v = v*` (`v` is the value of an optimal
policy) and `Tv = v`. -/
theorem IsOrderStable.howard_fixed (h : A.IsOrderStable) {v : V}
    (hv : A.howard h.wellPosed v = v) :
    A.IsOptimal h.wellPosed (A.greedy v) ∧ A.vσ h.wellPosed (A.greedy v) = v ∧
      IsFixedPt A.bellman v := by
  have hfix := h.isFixedPt_of_howard hv
  have h1 : A.vσ h.wellPosed (A.greedy v) = v := hv
  refine ⟨h.isOptimal_of_isFixedPt ?_, h1, hfix⟩
  rw [h1]
  exact hfix

/-- The HPI values increase. -/
theorem IsOrderStable.hpiValue_le_succ (h : A.IsOrderStable) (σ₀ : P) (k : ℕ) :
    A.hpiValue h.wellPosed σ₀ k ≤ A.hpiValue h.wellPosed σ₀ (k + 1) :=
  h.le_howard (A.vσ_mem_Vu h.wellPosed _)

/-- **Lemma B.4.1 (iv)** (p. 350), termination: for finite `Σ`, HPI repeats a value after finitely
many steps. -/
theorem IsOrderStable.exists_hpiValue_succ_eq [Finite P] (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k := by
  by_contra hcon
  have hsm : StrictMono (A.hpiValue h.wellPosed σ₀) :=
    strictMono_nat_of_lt_succ fun k => lt_of_le_of_ne (h.hpiValue_le_succ σ₀ k)
      fun he => hcon ⟨k, he.symm⟩
  have hinj : Injective (A.hpiPolicy h.wellPosed σ₀) := fun i j hij =>
    hsm.injective (by simp only [hpiValue, hij])
  exact not_injective_infinite_finite _ hinj

/-- **Lemma B.4.1 (iv)–(v)** (p. 350): for finite `Σ`, HPI from any `σ₀` reaches a `k` with
`vₖ₊₁ = vₖ`; there `vₖ` is a fixed point of `T` and the returned `vₖ`-greedy policy `σₖ₊₁` is
optimal. -/
theorem IsOrderStable.hpi_terminates [Finite P] (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k ∧
      IsFixedPt A.bellman (A.hpiValue h.wellPosed σ₀ k) ∧
      A.IsOptimal h.wellPosed (A.hpiPolicy h.wellPosed σ₀ (k + 1)) := by
  obtain ⟨k, hk⟩ := h.exists_hpiValue_succ_eq σ₀
  obtain ⟨hopt, -, hfix⟩ := h.howard_fixed hk
  exact ⟨k, hk, hfix, hopt⟩

/-- **Proposition 9.2.1** (p. 299): a finite order stable ADP is max-stable. -/
theorem IsOrderStable.isMaxStable [Finite P] [Nonempty P] (h : A.IsOrderStable) :
    A.IsMaxStable := by
  obtain ⟨σ₀⟩ := ‹Nonempty P›
  obtain ⟨k, -, hfix, -⟩ := h.hpi_terminates σ₀
  exact ⟨h, _, hfix⟩

/-- **Proposition 9.2.5** (p. 300): for a max-stable ADP, (i) `V_Σ` has a greatest element `v*`,
(ii) `v*` is the unique fixed point of `T`, (iii) `σ` is optimal iff it is `v*`-greedy and
(iv) an optimal policy exists. -/
theorem IsMaxStable.optimality (h : A.IsMaxStable) :
    ∃ vstar, IsGreatest (range (A.vσ h.1.wellPosed)) vstar ∧
      (∀ v, IsFixedPt A.bellman v ↔ v = vstar) ∧
      (∀ σ, A.IsOptimal h.1.wellPosed σ ↔ A.IsGreedy vstar σ) ∧
      ∃ σ, A.IsOptimal h.1.wellPosed σ := by
  obtain ⟨hs, vbar, hvbar⟩ := h
  have hw := hs.wellPosed
  -- any fixed point `w` of `T` is the value of its greedy policy and dominates every `v_τ`
  have key : ∀ w, IsFixedPt A.bellman w →
      w = A.vσ hw (A.greedy w) ∧ IsGreatest (range (A.vσ hw)) w := by
    intro w hw'
    have e : w = A.vσ hw (A.greedy w) := eq_vσ_of_isFixedPt hw hw'.eq
    refine ⟨e, ⟨⟨_, e.symm⟩, ?_⟩⟩
    rintro _ ⟨τ, rfl⟩
    exact hs.vσ_le ((A.T_le_bellman τ w).trans_eq hw'.eq)
  obtain ⟨e, hgr⟩ := key vbar hvbar
  refine ⟨vbar, hgr, fun v => ⟨fun hv => (key v hv).2.unique hgr, fun hv => hv ▸ hvbar⟩,
    fun σ => ?_, A.greedy vbar, fun τ => e ▸ hgr.2 ⟨τ, rfl⟩⟩
  have hopt : A.IsOptimal hw σ ↔ A.vσ hw σ = vbar :=
    ⟨fun ho => le_antisymm (hgr.2 ⟨σ, rfl⟩) (e ▸ ho _), fun he τ => he ▸ hgr.2 ⟨τ, rfl⟩⟩
  rw [hopt, A.isGreedy_iff, hvbar.eq]
  constructor
  · intro he
    rw [← he]
    exact (isFixedPt_vσ hw σ).eq
  · intro he
    exact (eq_vσ_of_isFixedPt hw he).symm

/-- **Theorem 9.2.4 (max-optimality)** (p. 300): if `A` is finite and order stable, then (i) `V_Σ`
has a greatest element `v*`, (ii) `v*` is the unique solution of the Bellman equation, (iii) `A`
obeys Bellman's principle of optimality, (iv) an optimal policy exists and (v) HPI returns an
optimal policy in finitely many steps. -/
theorem IsOrderStable.maxOptimality [Finite P] [Nonempty P] (h : A.IsOrderStable) :
    ∃ vstar, IsGreatest (range (A.vσ h.wellPosed)) vstar ∧
      (∀ v, IsFixedPt A.bellman v ↔ v = vstar) ∧
      (∀ σ, A.IsOptimal h.wellPosed σ ↔ A.IsGreedy vstar σ) ∧
      (∃ σ, A.IsOptimal h.wellPosed σ) ∧
      ∀ σ₀, ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k ∧
        A.IsOptimal h.wellPosed (A.hpiPolicy h.wellPosed σ₀ (k + 1)) := by
  obtain ⟨vstar, h1, h2, h3, h4⟩ := h.isMaxStable.optimality
  exact ⟨vstar, h1, h2, h3, h4, fun σ₀ => by
    obtain ⟨k, hk, -, hopt⟩ := h.hpi_terminates σ₀
    exact ⟨k, hk, hopt⟩⟩

end ADP

end SargentStachurski.ContinuousTime
