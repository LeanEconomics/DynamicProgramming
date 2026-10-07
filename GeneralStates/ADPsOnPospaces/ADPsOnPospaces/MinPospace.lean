/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.MetricADP
import ADPsOnPospaces.Minimization
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Minimization on pospaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.3 (pp. 101–103).

Min-OPI and min-HPI are defined with min-greedy selectors, and every min-notion is transported
from the dual ADP `(V, 𝕋)^∂` (Exercises 2.2.4 and 2.2.6).

* Global stability transfers to the dual (the dual carries the same topology).
* **Theorem 3.1.6** (min-version of Theorem 3.1.2) and **Theorem 3.1.8** (min-version of
  Theorem 3.1.4).
* **Theorem 3.1.7** (min-version of Theorem 3.1.5). The book's proof applies Theorem 3.1.5 to the
  dual, which needs the metric to be sup-nonexpansive for the *reversed* order, i.e.
  inf-nonexpansive. That does not follow from sup-nonexpansiveness: `vShape_sup_not_inf` is a
  three-point poset with a sup-nonexpansive metric that is not inf-nonexpansive. Theorem 3.1.7 is
  proved here under inf-nonexpansiveness.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnPospaces

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- A min-greedy selector: a choice of `v`-min-greedy policy at every `v`. -/
def IsMinSelector (g : V → P) : Prop := ∀ v, A.IsMinGreedy v (g v)

variable (A) in
/-- min-OPI converges: `W▿ⁿv ↓ v▿*` for all `v ∈ V_D` and every step size `m ≥ 1`. -/
def MinOPIConverges (g : V → P) (vstar : V) : Prop :=
  ∀ m, 1 ≤ m → ∀ v ∈ A.VD, DecreasesTo (fun n => (A.opt m g)^[n] v) vstar

variable (A) in
/-- min-HPI converges: `H▿ⁿv ↓ v▿*` for all `v ∈ V_D`. -/
def MinHPIConverges (hw : A.WellPosed) (g : V → P) (vstar : V) : Prop :=
  ∀ v ∈ A.VD, DecreasesTo (fun n => (A.howard hw g)^[n] v) vstar

/-- Min-greedy selectors of `A` are the greedy selectors of `A^∂`. -/
theorem isMinSelector_iff (g : V → P) :
    A.IsMinSelector g ↔ A.dual.IsSelector (g ∘ OrderDual.ofDual) :=
  ⟨fun h v => h (OrderDual.ofDual v), fun h v => h (OrderDual.toDual v)⟩

/-- Iterates of `W▿` are the iterates of the dual's `W`. -/
theorem dual_opt_iterate (m : ℕ) (g : V → P) (n : ℕ) (v : V) :
    (A.dual.opt m (g ∘ OrderDual.ofDual))^[n] (OrderDual.toDual v) =
      OrderDual.toDual ((A.opt m g)^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    exact (congrArg _ (dualMap_iterate _ m _)).trans (ih _)

/-- Iterates of `H▿` are the iterates of the dual's `H`. -/
theorem dual_howard_iterate (hw : A.WellPosed) (g : V → P) (n : ℕ) (v : V) :
    (A.dual.howard hw.dual (g ∘ OrderDual.ofDual))^[n] (OrderDual.toDual v) =
      OrderDual.toDual ((A.howard hw g)^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    exact (congrArg _ (dual_opt_howard hw 0 g v).2).trans (ih _)

/-- min-OPI convergence for `A` is OPI convergence for `A^∂` (Exercise 2.2.6). -/
theorem minOPIConverges_iff (g : V → P) (vstar : V) :
    A.MinOPIConverges g vstar ↔
      A.dual.OPIConverges (g ∘ OrderDual.ofDual) (OrderDual.toDual vstar) := by
  refine forall₂_congr fun m _ => ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.ofDual v) hv
    have he : (fun n => (A.dual.opt m (g ∘ OrderDual.ofDual))^[n] v) =
        fun n => OrderDual.toDual ((A.opt m g)^[n] (OrderDual.ofDual v)) :=
      funext fun n => dual_opt_iterate m g n (OrderDual.ofDual v)
    rw [he]
    exact ⟨fun a b hab => hm hab, hl⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.toDual v) hv
    rw [funext fun n => dual_opt_iterate m g n v] at hm hl
    exact ⟨fun a b hab => hm hab, hl⟩

/-- min-HPI convergence for `A` is HPI convergence for `A^∂` (Exercise 2.2.6). -/
theorem minHPIConverges_iff (hw : A.WellPosed) (g : V → P) (vstar : V) :
    A.MinHPIConverges hw g vstar ↔
      A.dual.HPIConverges hw.dual (g ∘ OrderDual.ofDual) (OrderDual.toDual vstar) := by
  refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.ofDual v) hv
    have he : (fun n => (A.dual.howard hw.dual (g ∘ OrderDual.ofDual))^[n] v) =
        fun n => OrderDual.toDual ((A.howard hw g)^[n] (OrderDual.ofDual v)) :=
      funext fun n => dual_howard_iterate hw g n (OrderDual.ofDual v)
    rw [he]
    exact ⟨fun a b hab => hm hab, hl⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.toDual v) hv
    rw [funext fun n => dual_howard_iterate hw g n v] at hm hl
    exact ⟨fun a b hab => hm hab, hl⟩

/-- Assembling the min-conclusions from the dual's max-conclusions (Exercise 2.2.6). -/
theorem min_of_dual {hw : A.WellPosed}
    (h : A.dual.FundamentalOptimality hw.dual ∧
      ∃ vstar, A.dual.IsValueFunction vstar ∧ A.dual.VFIConverges vstar ∧
        ∀ g, A.dual.IsSelector g → A.dual.OPIConverges g vstar ∧
          A.dual.HPIConverges hw.dual g vstar) :
    A.MinFundamentalOptimality hw ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧ A.MinHPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, hvs, hvfi, hconv⟩ := h
  refine ⟨(minFundamentalOptimality_iff hw).2 hFO, OrderDual.ofDual vstar, hvs,
    (minVFIConverges_iff _).2 hvfi, fun g hg => ?_⟩
  obtain ⟨h1, h2⟩ := hconv _ ((isMinSelector_iff g).1 hg)
  exact ⟨(minOPIConverges_iff g _).2 h1, (minHPIConverges_iff hw g _).2 h2⟩

variable [TopologicalSpace V]

/-- Global stability is self-dual: `(V, 𝕋)^∂` carries the same topology. -/
theorem IsGloballyStable.dual (h : A.IsGloballyStable) : A.dual.IsGloballyStable := fun σ => by
  obtain ⟨u, hu, huniq, hlim⟩ := h σ
  refine ⟨OrderDual.toDual u, congrArg OrderDual.toDual hu, fun w hw =>
    congrArg OrderDual.toDual (huniq (OrderDual.ofDual w) (congrArg OrderDual.ofDual hw)),
    fun w => ?_⟩
  change Tendsto (fun k => (dualMap (A.T σ))^[k] w) atTop _
  rw [funext fun k => dualMap_iterate (A.T σ) k w]
  exact hlim (OrderDual.ofDual w)

variable [OrderClosedTopology V]

/-- **Theorem 3.1.6** (p. 102): if `(V, 𝕋)` is min-regular and globally stable and `T▿` has a
fixed point, then (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI
and min-HPI all converge. -/
theorem theorem_3_1_6 (hr : A.MinRegular) (hgs : A.IsGloballyStable) {w : V}
    (hfix : A.SolvesMinBellman w) :
    A.MinFundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges hgs.wellPosed g vstar := by
  have hrd := (minRegular_iff A).1 hr
  exact min_of_dual (theorem_3_1_2 hrd hgs.dual
    ((A.dual.solvesBellman_iff (hrd (OrderDual.toDual w))).1 hfix))

/-- **Theorem 3.1.8** (p. 102): if `(V, 𝕋)` is min-regular, globally stable and min-order bounded,
and `V` is countably Dedekind complete, then (i) the fundamental min-optimality properties hold and
(ii) min-VFI, min-OPI and min-HPI all converge. -/
theorem theorem_3_1_8 (hr : A.MinRegular) (hgs : A.IsGloballyStable) (hb : A.MinOrderBounded)
    (hV : CountablyDedekindComplete V) :
    A.MinFundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges hgs.wellPosed g vstar :=
  min_of_dual (theorem_3_1_4 ((minRegular_iff A).1 hr) hgs.dual ((minOrderBounded_iff A).1 hb)
    hV.dual)

end ADP

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

/-- **Theorem 3.1.7** (p. 102), with the inf-nonexpansiveness its proof needs: if `(V, 𝕋)` is
min-regular, the metric is complete and inf-nonexpansive, and each `T_σ` is a contraction of
modulus `β`, then (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI and
min-HPI all converge. -/
theorem theorem_3_1_7 [MetricSpace V] [OrderClosedTopology V] [CompleteSpace V] [Nonempty V]
    (hr : A.MinRegular) (hd : IsInfNonexpansive (dist : V → V → ℝ)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w) :
    A.MinFundamentalOptimality (isGloballyStable_of_contraction ‹_› hβ0 hβ1 hT).wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges (isGloballyStable_of_contraction ‹_› hβ0 hβ1 hT).wellPosed g
            vstar := by
  have : CompleteSpace Vᵒᵈ := ‹CompleteSpace V›
  have : OrderClosedTopology Vᵒᵈ := ⟨isClosed_le_prod' (α := V)⟩
  have hrd := (minRegular_iff A).1 hr
  have hdd : IsSupNonexpansive (dist : Vᵒᵈ → Vᵒᵈ → ℝ) := (isInfNonexpansive_iff _).1 hd
  have hTd : ∀ σ v w, dist (A.dual.T σ v) (A.dual.T σ w) ≤ β * dist v w := fun σ v w =>
    hT σ (OrderDual.ofDual v) (OrderDual.ofDual w)
  obtain ⟨hFO, vstar, -, ⟨hvs, -⟩, hconv⟩ := theorem_3_1_5 (A := A.dual) hdd hβ0 hβ1 hTd
    ⟨isClosed_univ, fun v _ => hrd v, mapsTo_univ _ _⟩ univ_nonempty
  obtain ⟨v', -, -, -, hv'G, hv'b⟩ := hFO.exists_vstar
  obtain ⟨-, w, hw, hvfi, -⟩ := theorem_3_1_2 hrd (isGloballyStable_of_contraction
    (A := A.dual) ⟨OrderDual.toDual (Classical.arbitrary V)⟩ hβ0 hβ1 hTd)
    ((A.dual.solvesBellman_iff hv'G).1 hv'b)
  refine min_of_dual ⟨hFO, vstar, hvs, ?_, hconv hrd⟩
  rw [hvs.unique hw]
  exact hvfi

end ADP

/-! ### Sup-nonexpansive does not imply inf-nonexpansive -/

/-- The three-point poset `0 < 1`, `0 < 2` with `1, 2` incomparable, on `Fin 3`. -/
abbrev vShapeOrder : PartialOrder (Fin 3) where
  le a b := a = 0 ∨ a = b
  lt a b := (a = 0 ∨ a = b) ∧ ¬(b = 0 ∨ b = a)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with h | h
    · exact Or.inl h
    · rcases hbc with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h.trans h')
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · rcases hba with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

/-- The distance on the three-point poset: `d(1, 2) = 1` and `d(0, 1) = d(0, 2) = 3/2`. -/
noncomputable def vShapeDist (a b : Fin 3) : ℝ :=
  if a = b then 0 else if a = 0 ∨ b = 0 then 3 / 2 else 1

/-- `vShapeDist` is a metric. -/
theorem vShapeDist_metric :
    (∀ a, vShapeDist a a = 0) ∧ (∀ a b, vShapeDist a b = vShapeDist b a) ∧
      (∀ a b, vShapeDist a b = 0 → a = b) ∧
        ∀ a b c, vShapeDist a c ≤ vShapeDist a b + vShapeDist b c := by
  refine ⟨fun a => by simp [vShapeDist], fun a b => ?_, fun a b => ?_, fun a b c => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [vShapeDist]
  · fin_cases a <;> fin_cases b <;> norm_num [vShapeDist]
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [vShapeDist]

/-- Suprema in the three-point poset: `⋁ T = 0` forces `T ⊆ {0}`, and `⋁ T = a ≠ 0` forces
`a ∈ T`. -/
theorem vShape_isLUB {T : Set (Fin 3)} {a : Fin 3} (h : @IsLUB (Fin 3) vShapeOrder.toLE T a) :
    (a = 0 → ∀ t ∈ T, t = 0) ∧ (a ≠ 0 → a ∈ T) := by
  refine ⟨fun ha t ht => ?_, fun ha => ?_⟩
  · rcases h.1 ht with h' | h'
    · exact h'
    · exact h'.trans ha
  · by_contra hT
    have hub : (0 : Fin 3) ∈ @upperBounds (Fin 3) vShapeOrder.toLE T := fun t ht => by
      rcases h.1 ht with h' | h'
      · exact Or.inl h'
      · exact absurd (h' ▸ ht) hT
    rcases h.2 hub with h' | h'
    · exact ha h'
    · exact ha h'

/-- **Sup-nonexpansive does not imply inf-nonexpansive.** On the three-point poset, `vShapeDist`
is a sup-nonexpansive metric (the order is closed, the metric being discrete) but it is not
inf-nonexpansive: `⋀{1, 2} = 0` and `⋀{1} = 1`, while `d(1, 1) = 0`, `d(2, 1) = 1` and
`d(0, 1) = 3/2`. -/
theorem vShape_sup_not_inf :
    @IsSupNonexpansive (Fin 3) vShapeOrder vShapeDist ∧
      ¬ @IsInfNonexpansive (Fin 3) vShapeOrder vShapeDist := by
  refine ⟨fun S a b c hc ha hb hS => ?_, fun h => ?_⟩
  · by_cases hab : a = b
    · simp [vShapeDist, hab, hc]
    obtain ⟨ha0, ha1⟩ := vShape_isLUB ha
    obtain ⟨hb0, hb1⟩ := vShape_isLUB hb
    by_cases hA : a = 0
    · obtain ⟨p, hp, hpb⟩ := hb1 (fun h0 => hab (hA.trans h0.symm))
      have hp1 : p.1 = a := (ha0 hA p.1 ⟨p, hp, rfl⟩).trans hA.symm
      have := hS p hp
      rwa [hp1, hpb] at this
    by_cases hB : b = 0
    · obtain ⟨p, hp, hpa⟩ := ha1 hA
      have hp2 : p.2 = b := (hb0 hB p.2 ⟨p, hp, rfl⟩).trans hB.symm
      have := hS p hp
      rwa [hpa, hp2] at this
    · obtain ⟨p, hp, hpa⟩ := ha1 hA
      have hle : vShapeDist a b ≤ vShapeDist p.1 p.2 := by
        rw [hpa]
        rcases hb.1 ⟨p, hp, rfl⟩ with h0 | h0
        · rw [h0]
          revert hA hB hab
          fin_cases a <;> fin_cases b <;> norm_num [vShapeDist]
        · rw [h0]
      exact hle.trans (hS p hp)
  · have hfst : Prod.fst '' ({((1 : Fin 3), (1 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))} :
        Set (Fin 3 × Fin 3)) = {1, 2} := by
      simp [image_insert_eq]
    have hsnd : Prod.snd '' ({((1 : Fin 3), (1 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))} :
        Set (Fin 3 × Fin 3)) = {1} := by
      simp [image_insert_eq]
    have hglb1 : @IsGLB (Fin 3) vShapeOrder.toLE {1, 2} 0 := by
      refine ⟨fun t _ => Or.inl rfl, fun l hl => ?_⟩
      have h1 : l = 0 ∨ l = 1 := hl (mem_insert 1 {2})
      have h2 : l = 0 ∨ l = 2 := hl (mem_insert_of_mem 1 (mem_singleton 2))
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact absurd (h1.symm.trans h2) (by decide)
    have hglb2 : @IsGLB (Fin 3) vShapeOrder.toLE {1} 1 :=
      ⟨fun t ht => Or.inr (mem_singleton_iff.1 ht).symm, fun l hl => hl (mem_singleton 1)⟩
    rw [← hfst] at hglb1
    rw [← hsnd] at hglb2
    have key := h _ 0 1 1 zero_le_one hglb1 hglb2 (by
      intro p hp
      simp only [mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> norm_num [vShapeDist])
    norm_num [vShapeDist] at key

end SargentStachurski.ADPsOnPospaces
