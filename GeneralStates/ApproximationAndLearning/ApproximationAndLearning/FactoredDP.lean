/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.Semiconjugacy
import ApproximationAndLearning.MinPospace

/-!
# Factored dynamic programs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.2–5.2.3 (pp. 166–174).

A factored dynamic program `(V, F, V̂, 𝔾)` has maps `F : V → V̂` and `G_σ : V̂ → V` such that
`{G_σ v̂}_σ` has a greatest element `Gv̂` (5.19) for every `v̂`. It generates the primary ADP
`T_σ = G_σ ∘ F` and the subordinate ADP `T̂_σ = F ∘ G_σ`.

* Order-preserving FDPs: **Lemma 5.2.9**, **Lemma 5.2.10**, **Lemma 5.2.11**, **Lemma 5.2.12**,
  **Theorem 5.2.13** (the fundamental optimality properties hold for the primary ADP iff they
  hold for the subordinate one; (5.23); optimal policies) and **Proposition 5.2.14** (the
  converse under strict monotonicity of `F`).
* Order-reversing FDPs: **Lemma 5.2.15**, **Lemma 5.2.16**, **Lemma 5.2.17**,
  **Exercise 5.2.2** and **Theorem 5.2.18**. An order-reversing FDP becomes order preserving once
  `V̂` is replaced by `V̂^∂`, and its subordinate ADP becomes the dual of the original one; this
  reduces the order-reversing case to the order-preserving one.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

/-- A factored dynamic program `(V, F, V̂, 𝔾)` (§5.2.2.1). -/
structure FDP (V W P : Type*) [PartialOrder V] [PartialOrder W] where
  /-- the map `F : V → V̂` -/
  F : V → W
  /-- the maps `G_σ : V̂ → V` -/
  G : P → W → V
  /-- (iv): `{G_σ v̂}_σ` has a greatest element -/
  greatest : ∀ w, ∃ σ, ∀ τ, G τ w ≤ G σ w
  nonempty : Nonempty P

namespace FDP

variable {V W P : Type*} [PartialOrder V] [PartialOrder W] (M : FDP V W P)

/-- An order-preserving FDP: `F` and every `G_σ` are order preserving. -/
def IsOrderPreserving : Prop := Monotone M.F ∧ ∀ σ, Monotone (M.G σ)

/-- An order-reversing FDP (§5.2.3): `F` and every `G_σ` are order reversing. -/
def IsOrderReversing : Prop := Antitone M.F ∧ ∀ σ, Antitone (M.G σ)

/-- Either case: then every `G_σ ∘ F` and `F ∘ G_σ` is order preserving. -/
def Monotonic : Prop := M.IsOrderPreserving ∨ M.IsOrderReversing

/-- A policy attaining the greatest element of `{G_σ v̂}_σ`. -/
noncomputable def gsel (w : W) : P := (M.greatest w).choose

/-- `Gv̂ = ⋁_σ G_σ v̂` (5.19). -/
noncomputable def Gsup (w : W) : V := M.G (M.gsel w) w

theorem G_le_Gsup (σ : P) (w : W) : M.G σ w ≤ M.Gsup w := (M.greatest w).choose_spec σ

theorem isGreatest_Gsup (w : W) : IsGreatest (range fun σ => M.G σ w) (M.Gsup w) :=
  ⟨⟨_, rfl⟩, by rintro _ ⟨σ, rfl⟩; exact M.G_le_Gsup σ w⟩

/-- The primary ADP `(V, 𝕋)`, `T_σ = G_σ ∘ F`. -/
def primary (h : M.Monotonic) : ADP V P where
  T σ v := M.G σ (M.F v)
  mono σ := by
    rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact (hG σ).comp hF
    · exact (hG σ).comp hF
  nonempty := M.nonempty

/-- The subordinate ADP `(V̂, 𝕋̂)`, `T̂_σ = F ∘ G_σ`. -/
def sub (h : M.Monotonic) : ADP W P where
  T σ w := M.F (M.G σ w)
  mono σ := by
    rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact hF.comp (hG σ)
    · exact hF.comp (hG σ)
  nonempty := M.nonempty

variable {M}

theorem primary_regular (h : M.Monotonic) : (M.primary h).Regular := fun v =>
  ⟨M.gsel (M.F v), fun τ => M.G_le_Gsup τ (M.F v)⟩

theorem primary_bellman (h : M.Monotonic) (v : V) : (M.primary h).bellman v = M.Gsup (M.F v) := by
  have hg := (M.primary h).isGreedy_greedy (primary_regular h v)
  exact le_antisymm (M.G_le_Gsup _ _) (hg (M.gsel (M.F v)))

/-- **Lemma 5.2.9** (p. 167) and **Lemma 5.2.15** (p. 171): (i) the Bellman operator of the
primary ADP is `T = G ∘ F`, and (ii) `σ` is `v`-greedy iff `G_σ F v = G F v`. -/
theorem lemma_5_2_9 (h : M.Monotonic) :
    (∀ v, (M.primary h).bellman v = M.Gsup (M.F v)) ∧
      ∀ v σ, (M.primary h).IsGreedy v σ ↔ M.G σ (M.F v) = M.Gsup (M.F v) := by
  refine ⟨primary_bellman h, fun v σ => ⟨fun hg => ?_, fun he τ => ?_⟩⟩
  · exact le_antisymm (M.G_le_Gsup σ _) (hg (M.gsel (M.F v)))
  · change M.G τ (M.F v) ≤ M.G σ (M.F v)
    rw [he]
    exact M.G_le_Gsup τ _

/-- With order preserving `F`, `gsel v̂` is `v̂`-greedy for the subordinate ADP. -/
theorem sub_isGreedy_of_eq (h : M.Monotonic) (hF : Monotone M.F) {w : W} {σ : P}
    (he : M.G σ w = M.Gsup w) : (M.sub h).IsGreedy w σ := fun τ => by
  change M.F (M.G τ w) ≤ M.F (M.G σ w)
  rw [he]
  exact hF (M.G_le_Gsup τ w)

theorem sub_regular (h : M.Monotonic) (hF : Monotone M.F) : (M.sub h).Regular := fun w =>
  ⟨M.gsel w, sub_isGreedy_of_eq h hF rfl⟩

theorem sub_bellman (h : M.Monotonic) (hF : Monotone M.F) (w : W) :
    (M.sub h).bellman w = M.F (M.Gsup w) :=
  (((M.sub h).isGreedy_iff (sub_regular h hF w) _).1 (sub_isGreedy_of_eq h hF rfl)).symm

/-- **Lemma 5.2.10** (p. 168): for an order-preserving FDP, (i) the Bellman operator of the
subordinate ADP is `T̂ = F ∘ G`, and (ii) `G_σ v̂ = Gv̂` implies that `σ` is `v̂`-greedy. -/
theorem lemma_5_2_10 (h : M.Monotonic) (hP : M.IsOrderPreserving) :
    (∀ w, (M.sub h).bellman w = M.F (M.Gsup w)) ∧
      ∀ w σ, M.G σ w = M.Gsup w → (M.sub h).IsGreedy w σ :=
  ⟨sub_bellman h hP.1, fun _ _ he => sub_isGreedy_of_eq h hP.1 he⟩

/-- **Lemma 5.2.11** (p. 168): `(V, T)` and `(V̂, T̂)` are strongly semiconjugate under `F, G`. -/
theorem lemma_5_2_11 (h : M.Monotonic) (hP : M.IsOrderPreserving) :
    IsStronglySemiconj (M.primary h).bellman (M.sub h).bellman M.F M.Gsup :=
  ⟨primary_bellman h, sub_bellman h hP.1⟩

/-- Each pair of policy systems is strongly semiconjugate under `F, G_σ` (5.20). -/
theorem policy_semiconj (h : M.Monotonic) (σ : P) :
    IsStronglySemiconj ((M.primary h).T σ) ((M.sub h).T σ) M.F (M.G σ) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Lemma 5.2.12** (p. 168) and **Exercise 5.2.2** (p. 172): (i) `(V̂, 𝕋̂)` is well-posed iff
`(V, 𝕋)` is, (ii) order stability transfers (for order-preserving and order-reversing FDPs
alike), and the `σ`-value functions obey `v̂_σ = Fv_σ` and `v_σ = G_σ v̂_σ` (5.22), (5.25). -/
theorem lemma_5_2_12 (h : M.Monotonic) :
    ((M.sub h).WellPosed ↔ (M.primary h).WellPosed) ∧
      ((M.sub h).IsOrderStable ↔ (M.primary h).IsOrderStable) ∧
      ∀ (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) σ,
        M.F ((M.primary h).vσ hw σ) = (M.sub h).vσ hw' σ ∧
          M.G σ ((M.sub h).vσ hw' σ) = (M.primary h).vσ hw σ := by
  refine ⟨forall_congr' fun σ => (policy_semiconj h σ).existsUnique_iff.symm,
    forall_congr' fun σ => ((policy_semiconj h σ).lemma_5_2_2_i ?_).symm,
    fun hw hw' σ => ⟨?_, ?_⟩⟩
  · rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact Or.inl ⟨hF, hG σ⟩
    · exact Or.inr ⟨hF, hG σ⟩
  · exact ADP.eq_vσ hw' ((policy_semiconj h σ).fixed_F (ADP.T_vσ hw σ))
  · exact ADP.eq_vσ hw ((policy_semiconj h σ).fixed_G (ADP.T_vσ hw' σ))

/-! ### Optimality for order-preserving FDPs -/

/-- If `v*` is the primary value function and attained, `Fv*` is the subordinate one. -/
theorem sub_isValueFunction (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) {v : V}
    (hv : (M.primary h).IsValueFunction v) {σ₀ : P} (hσ₀ : (M.primary h).IsOptimal hw σ₀) :
    (M.sub h).IsValueFunction (M.F v) := by
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  have hv₀ : (M.primary h).vσ hw σ₀ = v := (ADP.isOptimal_iff hv).1 hσ₀
  refine ⟨?_, fun b hb => ?_⟩
  · rw [ADP.VSig_eq_range hw']
    rintro _ ⟨σ, rfl⟩
    rw [← (h522 σ).1]
    exact hP.1 (hv.1 ⟨σ, ADP.T_vσ hw σ⟩)
  · rw [← hv₀, (h522 σ₀).1]
    exact hb ⟨σ₀, ADP.T_vσ hw' σ₀⟩

/-- If `v̂*` is the subordinate value function and Bellman's principle holds there, `Gv̂*` is the
primary value function, attained by any `σ` with `G_σ v̂* = Gv̂*`. -/
theorem primary_isValueFunction (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) {w : W}
    (hv : (M.sub h).IsValueFunction w) (hbp : (M.sub h).BellmanPrinciple hw') {σ : P}
    (hσ : M.G σ w = M.Gsup w) :
    (M.primary h).IsValueFunction (M.Gsup w) ∧ (M.primary h).vσ hw σ = M.Gsup w := by
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  have hopt : (M.sub h).IsOptimal hw' σ := (hbp σ).2 ⟨w, hv, sub_isGreedy_of_eq h hP.1 hσ⟩
  have hvσ : (M.primary h).vσ hw σ = M.Gsup w := by
    rw [← (h522 σ).2, (ADP.isOptimal_iff hv).1 hopt, hσ]
  refine ⟨IsGreatest.isLUB ⟨⟨σ, hvσ ▸ ADP.T_vσ hw σ⟩, ?_⟩, hvσ⟩
  rw [ADP.VSig_eq_range hw]
  rintro _ ⟨τ, rfl⟩
  rw [← (h522 τ).2]
  exact ((hP.2 τ) (hv.1 ⟨τ, ADP.T_vσ hw' τ⟩)).trans (M.G_le_Gsup τ w)

theorem fo_sub_of_primary (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.primary h).FundamentalOptimality hw) : (M.sub h).FundamentalOptimality hw' := by
  obtain ⟨⟨σ₀, hσ₀⟩, ⟨v, hv, -, hb, huniq⟩, -⟩ := hfo
  have hbv : (M.primary h).bellman v = v :=
    ((M.primary h).solvesBellman_iff (primary_regular h v)).1 hb
  refine (ADP.fundamentalOptimality_iff hw').2 ⟨M.F v, sub_isValueFunction h hP hw hw' hv hσ₀,
    sub_regular h hP.1 _, ?_, fun w' hw'G hw'b => ?_⟩
  · rw [ADP.solvesBellman_iff _ (sub_regular h hP.1 _), sub_bellman h hP.1,
      ← primary_bellman h, hbv]
  · have h1 : (M.sub h).bellman w' = w' := ((M.sub h).solvesBellman_iff hw'G).1 hw'b
    have h2 : (M.primary h).bellman (M.Gsup w') = M.Gsup w' := by
      rw [primary_bellman h, ← sub_bellman h hP.1, h1]
    have h3 : M.Gsup w' = v := huniq _ (primary_regular h _)
      (((M.primary h).solvesBellman_iff (primary_regular h _)).2 h2)
    rw [← h1, sub_bellman h hP.1, h3]

theorem fo_primary_of_sub (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.sub h).FundamentalOptimality hw') : (M.primary h).FundamentalOptimality hw := by
  obtain ⟨-, ⟨w, hv, -, hb, huniq⟩, hbp⟩ := hfo
  have hbw : (M.sub h).bellman w = w :=
    ((M.sub h).solvesBellman_iff (sub_regular h hP.1 w)).1 hb
  refine (ADP.fundamentalOptimality_iff hw).2 ⟨M.Gsup w,
    (primary_isValueFunction h hP hw hw' hv hbp (σ := M.gsel w) rfl).1, primary_regular h _, ?_,
    fun v' hv'G hv'b => ?_⟩
  · rw [ADP.solvesBellman_iff _ (primary_regular h _), primary_bellman h, ← sub_bellman h hP.1,
      hbw]
  · have h1 : (M.primary h).bellman v' = v' := ((M.primary h).solvesBellman_iff hv'G).1 hv'b
    have h2 : (M.sub h).bellman (M.F v') = M.F v' := by
      rw [sub_bellman h hP.1, ← primary_bellman h, h1]
    have h3 : M.F v' = w := huniq _ (sub_regular h hP.1 _)
      (((M.sub h).solvesBellman_iff (sub_regular h hP.1 _)).2 h2)
    rw [← h1, primary_bellman h, h3]

/-- **Theorem 5.2.13** (p. 169): for an order-preserving FDP, (a) the fundamental optimality
properties hold for the primary ADP iff (b) they hold for the subordinate ADP. In that case,
(i) `v* = Gv̂*` and `v̂* = Fv*` (5.23), (ii) `G_σ v̂* = Gv̂*` implies that `σ` is optimal for the
primary ADP, and (iii) optimal policies for the primary ADP are optimal for the subordinate
one. -/
theorem theorem_5_2_13 (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) :
    ((M.primary h).FundamentalOptimality hw ↔ (M.sub h).FundamentalOptimality hw') ∧
      ((M.primary h).FundamentalOptimality hw →
        (∀ v w, (M.primary h).IsValueFunction v → (M.sub h).IsValueFunction w →
          v = M.Gsup w ∧ w = M.F v) ∧
        (∀ w σ, (M.sub h).IsValueFunction w → M.G σ w = M.Gsup w →
          (M.primary h).IsOptimal hw σ) ∧
        ∀ σ, (M.primary h).IsOptimal hw σ → (M.sub h).IsOptimal hw' σ) := by
  refine ⟨⟨fo_sub_of_primary h hP hw hw', fo_primary_of_sub h hP hw hw'⟩, fun hfo => ?_⟩
  have hfo' := fo_sub_of_primary h hP hw hw' hfo
  have hbp := hfo'.2.2
  obtain ⟨σ₀, hσ₀⟩ := hfo.1
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  refine ⟨fun v w hv hw₀ => ⟨?_, ?_⟩, fun w σ hw₀ hσ => ?_, fun σ hσ => ?_⟩
  · exact hv.unique (primary_isValueFunction h hP hw hw' hw₀ hbp (σ := M.gsel w) rfl).1
  · exact hw₀.unique (sub_isValueFunction h hP hw hw' hv hσ₀)
  · obtain ⟨hv, hvσ⟩ := primary_isValueFunction h hP hw hw' hw₀ hbp hσ
    exact (ADP.isOptimal_iff hv).2 hvσ
  · have hv := hσ.isValueFunction
    rw [ADP.isOptimal_iff (sub_isValueFunction h hP hw hw' hv hσ)]
    exact ((h522 σ).1).symm

/-- **Proposition 5.2.14** (p. 171): if the fundamental optimality properties hold for the
subordinate ADP and `F` is strictly order preserving, then (i) they hold for the primary ADP and
(ii) every policy optimal for the subordinate ADP is optimal for the primary ADP. -/
theorem proposition_5_2_14 (h : M.Monotonic) (hP : M.IsOrderPreserving) (hstrict : StrictMono M.F)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.sub h).FundamentalOptimality hw') :
    (M.primary h).FundamentalOptimality hw ∧
      ∀ σ, (M.sub h).IsOptimal hw' σ → (M.primary h).IsOptimal hw σ := by
  have hfoP := fo_primary_of_sub h hP hw hw' hfo
  refine ⟨hfoP, fun σ hσ => ?_⟩
  obtain ⟨w, hv, hg⟩ := (hfo.2.2 σ).1 hσ
  have hwG : w ∈ (M.sub h).VG := ⟨σ, hg⟩
  have heq : M.F (M.G σ w) = M.F (M.Gsup w) := by
    rw [← sub_bellman h hP.1]
    exact ((M.sub h).isGreedy_iff hwG σ).1 hg
  have hGσ : M.G σ w = M.Gsup w := by
    by_contra hne
    exact (hstrict (lt_of_le_of_ne (M.G_le_Gsup σ w) hne)).ne heq
  exact ((theorem_5_2_13 h hP hw hw').2 hfoP).2.1 w σ hv hGσ

/-! ### Order-reversing FDPs -/

variable (M) in
/-- An FDP read with `V̂^∂` in place of `V̂`. -/
def dualize : FDP V Wᵒᵈ P where
  F := OrderDual.toDual ∘ M.F
  G σ w := M.G σ (OrderDual.ofDual w)
  greatest w := M.greatest (OrderDual.ofDual w)
  nonempty := M.nonempty

theorem dualize_isOrderPreserving (hR : M.IsOrderReversing) : M.dualize.IsOrderPreserving :=
  ⟨fun _ _ h => hR.1 h, fun σ _ _ h => hR.2 σ h⟩

theorem dualize_monotonic (hR : M.IsOrderReversing) : M.dualize.Monotonic :=
  Or.inl (dualize_isOrderPreserving hR)

/-- Dualizing `V̂` leaves the primary ADP unchanged … -/
theorem dualize_primary (h : M.Monotonic) (hR : M.IsOrderReversing) :
    M.dualize.primary (dualize_monotonic hR) = M.primary h := rfl

/-- … and turns the subordinate ADP into its dual. -/
theorem dualize_sub (h : M.Monotonic) (hR : M.IsOrderReversing) :
    M.dualize.sub (dualize_monotonic hR) = (M.sub h).dual := rfl

theorem dualize_Gsup (w : W) : M.dualize.Gsup (OrderDual.toDual w) = M.Gsup w := rfl

/-- **Lemma 5.2.16** (p. 172): for an order-reversing FDP, (i) the Bellman min-operator of the
subordinate ADP is `T̂▿ = F ∘ G`, with min-greedy policies everywhere, and (ii) `G_σ v̂ = Gv̂`
implies that `σ` is `v̂`-min-greedy. -/
theorem lemma_5_2_16 (h : M.Monotonic) (hR : M.IsOrderReversing) :
    (M.sub h).MinRegular ∧ (∀ w, (M.sub h).IsMinBellmanValue w (M.F (M.Gsup w))) ∧
      ∀ w σ, M.G σ w = M.Gsup w → (M.sub h).IsMinGreedy w σ := by
  have hP := dualize_isOrderPreserving hR
  have hd := dualize_monotonic hR
  refine ⟨((M.sub h).minRegular_iff).2 (sub_regular hd hP.1), fun w => ?_,
    fun w σ he => sub_isGreedy_of_eq hd hP.1 (w := OrderDual.toDual w) he⟩
  have hreg := sub_regular hd hP.1
  have h1 := (M.dualize.sub hd).isBellmanValue_bellman (hreg (OrderDual.toDual w))
  rw [sub_bellman hd hP.1] at h1
  exact h1

/-- **Lemma 5.2.17** (p. 172): for an order-reversing FDP, `(V, T)` and `(V̂, T̂▿)` are strongly
semiconjugate under `F, G`, where `T̂▿ = F ∘ G` is the Bellman min-operator (Lemma 5.2.16). -/
theorem lemma_5_2_17 (h : M.Monotonic) :
    IsStronglySemiconj (M.primary h).bellman (fun w => M.F (M.Gsup w)) M.F M.Gsup :=
  ⟨primary_bellman h, fun _ => rfl⟩

/-- **Theorem 5.2.18** (p. 173): for an order-reversing FDP, (a) the fundamental max-optimality
properties hold for the primary ADP iff (b) the fundamental min-optimality properties hold for the
subordinate ADP. In that case (i) `v* = Gv̂▿*` and `v̂▿* = Fv*` (5.26), (ii) `G_σ v̂▿* = Gv̂▿*`
implies that `σ` is optimal, and (iii) optimal policies are min-optimal for the subordinate ADP;
if `F` is strictly order reversing, (iv) min-optimal policies of the subordinate ADP are
optimal for the primary ADP. -/
theorem theorem_5_2_18 (h : M.Monotonic) (hR : M.IsOrderReversing)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) :
    ((M.primary h).FundamentalOptimality hw ↔ (M.sub h).MinFundamentalOptimality hw') ∧
      ((M.primary h).FundamentalOptimality hw →
        (∀ v w, (M.primary h).IsValueFunction v → (M.sub h).IsMinValueFunction w →
          v = M.Gsup w ∧ w = M.F v) ∧
        (∀ w σ, (M.sub h).IsMinValueFunction w → M.G σ w = M.Gsup w →
          (M.primary h).IsOptimal hw σ) ∧
        (∀ σ, (M.primary h).IsOptimal hw σ → (M.sub h).IsMinOptimal hw' σ) ∧
        (StrictAnti M.F → ∀ σ, (M.sub h).IsMinOptimal hw' σ → (M.primary h).IsOptimal hw σ)) := by
  have hP := dualize_isOrderPreserving hR
  have hd := dualize_monotonic hR
  have hwd : (M.dualize.sub hd).WellPosed := hw'
  have key := theorem_5_2_13 hd hP hw hwd
  refine ⟨key.1.trans ((M.sub h).minFundamentalOptimality_iff hw').symm, fun hfo => ?_⟩
  obtain ⟨h1, h2, h3⟩ := key.2 hfo
  refine ⟨fun v w hv hw₀ => ?_, fun w σ hw₀ hσ => h2 (OrderDual.toDual w) σ hw₀ hσ,
    fun σ hσ => ((M.sub h).isMinOptimal_iff hw' σ).2 (h3 σ hσ), fun hstrict σ hσ => ?_⟩
  · obtain ⟨e1, e2⟩ := h1 v (OrderDual.toDual w) hv hw₀
    exact ⟨e1, congrArg OrderDual.ofDual e2⟩
  · have hfo' : (M.dualize.sub hd).FundamentalOptimality hwd := key.1.1 hfo
    exact (proposition_5_2_14 hd hP (fun _ _ hab => hstrict hab) hw hwd hfo').2 σ
      (((M.sub h).isMinOptimal_iff hw' σ).1 hσ)

end FDP

end SargentStachurski.ApproximationAndLearning
