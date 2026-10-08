/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.Conjugacy
import ADPTransformations.MinPospace
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Isomorphic and anti-isomorphic ADPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.2 (pp. 151–157).

* Isomorphic ADPs (§5.1.2.1): the same policy set and `F ∘ T_σ = T̂_σ ∘ F` (5.1) for an order
  isomorphism `F`. **Example 5.1.4** (the exponential transformation of the savings problem) and
  **Lemma 5.1.4** / **Exercise 5.1.4** (an equivalence relation).
* §5.1.2.2: **Theorem 5.1.5** (greedy policies, regularity, well-posedness, order stability and
  optimal policies transfer), **Theorem 5.1.6** (Bellman operators are conjugate, `v̂* = Fv*`,
  the fundamental optimality properties transfer) and **Theorem 5.1.7** / **Exercise 5.1.5**
  ((5.5), (5.6) and convergence of VFI, OPI and HPI transfer).
* §5.1.2.3: anti-isomorphic ADPs. **Exercise 5.1.6** (anti-isomorphic iff isomorphic to the
  dual), **Theorem 5.1.8**, **Theorem 5.1.9** / **Exercise 5.1.7** and **Theorem 5.1.10** /
  **Exercise 5.1.8**: maximization in one ADP is minimization in the other.

OPI and HPI are run with a greedy *selector* `g`; a selector `g` of `(V, 𝕋)` corresponds to the
selector `g ∘ F⁻¹` of `(V̂, 𝕋̂)`.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace ADP

variable {V W U P : Type*} [PartialOrder V] [PartialOrder W] [PartialOrder U]

/-- `(V, 𝕋)` and `(V̂, 𝕋̂)` are isomorphic under the order isomorphism `F` (§5.1.2.1): they share
the policy set and `F ∘ T_σ = T̂_σ ∘ F` for every `σ` (5.1). -/
def IsIsomorphic (A : ADP V P) (B : ADP W P) (F : V ≃o W) : Prop :=
  ∀ σ, IsOrderConjugate F (A.T σ) (B.T σ)

/-- **Lemma 5.1.4** (p. 152) and **Exercise 5.1.4**: isomorphism is reflexive, … -/
theorem IsIsomorphic.refl (A : ADP V P) : A.IsIsomorphic A (OrderIso.refl V) := fun _ _ => rfl

/-- … symmetric, … -/
theorem IsIsomorphic.symm {A : ADP V P} {B : ADP W P} {F : V ≃o W} (h : A.IsIsomorphic B F) :
    B.IsIsomorphic A F.symm := fun σ => (h σ).symm

/-- … and transitive. -/
theorem IsIsomorphic.trans {A : ADP V P} {B : ADP W P} {C : ADP U P} {F : V ≃o W} {G : W ≃o U}
    (h : A.IsIsomorphic B F) (h' : B.IsIsomorphic C G) : A.IsIsomorphic C (F.trans G) :=
  fun σ => (h σ).trans (h' σ)

namespace IsIsomorphic

variable {A : ADP V P} {B : ADP W P} {F : V ≃o W}

theorem T_apply (h : A.IsIsomorphic B F) (σ : P) (v : V) : F (A.T σ v) = B.T σ (F v) := h σ v

theorem range_T (h : A.IsIsomorphic B F) (v : V) :
    range (fun σ => B.T σ (F v)) = F '' range fun σ => A.T σ v := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun σ => (h σ v).symm)

theorem isBellmanValue_iff (h : A.IsIsomorphic B F) (v w : V) :
    A.IsBellmanValue v w ↔ B.IsBellmanValue (F v) (F w) := by
  unfold IsBellmanValue
  rw [h.range_T]
  exact (F.isLUB_image' (s := range fun σ => A.T σ v)).symm

theorem solvesBellman_iff (h : A.IsIsomorphic B F) (v : V) :
    A.SolvesBellman v ↔ B.SolvesBellman (F v) :=
  h.isBellmanValue_iff v v

/-- **Theorem 5.1.5 (i)** (p. 153): `σ` is `v`-greedy for `(V, 𝕋)` iff it is `Fv`-greedy for
`(V̂, 𝕋̂)`. -/
theorem isGreedy_iff (h : A.IsIsomorphic B F) (v : V) (σ : P) :
    A.IsGreedy v σ ↔ B.IsGreedy (F v) σ := by
  refine forall_congr' fun τ => ?_
  rw [← h.T_apply, ← h.T_apply]
  exact F.le_iff_le.symm

theorem mem_VG_iff (h : A.IsIsomorphic B F) (v : V) : v ∈ A.VG ↔ F v ∈ B.VG :=
  exists_congr fun σ => h.isGreedy_iff v σ

/-- **Theorem 5.1.5 (ii)**: `(V, 𝕋)` is regular iff `(V̂, 𝕋̂)` is. -/
theorem regular_iff (h : A.IsIsomorphic B F) : A.Regular ↔ B.Regular := by
  refine ⟨fun hr w => ?_, fun hr v => (h.mem_VG_iff v).2 (hr (F v))⟩
  rw [← F.apply_symm_apply w]
  exact (h.mem_VG_iff _).1 (hr _)

/-- **Theorem 5.1.5 (iii)**: `(V, 𝕋)` is well-posed iff `(V̂, 𝕋̂)` is. -/
theorem wellPosed_iff (h : A.IsIsomorphic B F) : A.WellPosed ↔ B.WellPosed := by
  refine forall_congr' fun σ => ?_
  have hc : IsConjugate F.toEquiv (A.T σ) (B.T σ) := h σ
  constructor
  · rintro ⟨v, hv, huniq⟩
    refine ⟨F v, (hc.fixed_iff v).1 hv, fun w hw => ?_⟩
    rw [← huniq _ ((hc.fixed_iff_symm w).1 hw)]
    exact (F.apply_symm_apply w).symm
  · rintro ⟨w, hw, huniq⟩
    refine ⟨F.symm w, (hc.fixed_iff_symm w).1 hw, fun v hv => ?_⟩
    rw [← huniq _ ((hc.fixed_iff v).1 hv)]
    exact (F.symm_apply_apply v).symm

/-- The `σ`-value functions are linked by `F v_σ = v̂_σ`. -/
theorem vσ_eq (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (σ : P) :
    F (A.vσ hw σ) = B.vσ hw' σ :=
  eq_vσ hw' (by rw [← h.T_apply, T_vσ])

theorem VSig_eq (h : A.IsIsomorphic B F) : B.VSig = F '' A.VSig := by
  ext w
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨F.symm w, ⟨σ, ?_⟩, F.apply_symm_apply w⟩
    apply F.injective
    rw [h.T_apply, F.apply_symm_apply, hσ]
  · rintro ⟨v, ⟨σ, hσ⟩, rfl⟩
    exact ⟨σ, by rw [← h.T_apply, hσ]⟩

/-- **Theorem 5.1.6 (ii)** (p. 154): `v̂* = Fv*`. -/
theorem isValueFunction_iff (h : A.IsIsomorphic B F) (v : V) :
    A.IsValueFunction v ↔ B.IsValueFunction (F v) := by
  unfold IsValueFunction
  rw [h.VSig_eq]
  exact (F.isLUB_image' (s := A.VSig)).symm

/-- **Theorem 5.1.5 (v)**: `σ` is optimal for `(V, 𝕋)` iff it is optimal for `(V̂, 𝕋̂)`. -/
theorem isOptimal_iff (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (σ : P) :
    A.IsOptimal hw σ ↔ B.IsOptimal hw' σ := by
  unfold IsOptimal
  rw [← h.vσ_eq hw hw' σ, h.VSig_eq]
  constructor
  · rintro ⟨ha, hup⟩
    exact ⟨⟨_, ha, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact F.monotone (hup hx)⟩
  · rintro ⟨⟨b, hb, hba⟩, hup⟩
    exact ⟨F.injective hba ▸ hb, fun x hx => F.le_iff_le.1 (hup ⟨x, hx, rfl⟩)⟩

theorem orderStable_iff (h : A.IsIsomorphic B F) : A.IsOrderStable ↔ B.IsOrderStable :=
  forall_congr' fun σ => (IsOrderConjugate.lemma_5_1_3 (h σ)).1

theorem stronglyOrderStable_iff (h : A.IsIsomorphic B F) :
    A.IsStronglyOrderStable ↔ B.IsStronglyOrderStable :=
  forall_congr' fun σ => (IsOrderConjugate.lemma_5_1_3 (h σ)).2

/-- **Theorem 5.1.6 (i)** (5.4): `F ∘ T = T̂ ∘ F` at every `v ∈ V_G`. -/
theorem bellman_eq (h : A.IsIsomorphic B F) {v : V} (hv : v ∈ A.VG) :
    F (A.bellman v) = B.bellman (F v) := by
  have hg := A.isGreedy_greedy hv
  have hg' := (h.isGreedy_iff v _).1 hg
  rw [← (B.isGreedy_iff ((h.mem_VG_iff v).1 hv) _).1 hg']
  exact h.T_apply _ v

theorem bellmanPrinciple (h : A.IsIsomorphic B F) {hw : A.WellPosed} {hw' : B.WellPosed}
    (hb : A.BellmanPrinciple hw) : B.BellmanPrinciple hw' := by
  intro σ
  rw [← h.isOptimal_iff hw hw' σ, hb σ]
  constructor
  · rintro ⟨v, hv, hg⟩
    exact ⟨F v, (h.isValueFunction_iff v).1 hv, (h.isGreedy_iff v σ).1 hg⟩
  · rintro ⟨w, hv, hg⟩
    refine ⟨F.symm w, (h.isValueFunction_iff _).2 ?_, (h.isGreedy_iff _ σ).2 ?_⟩
    · rwa [F.apply_symm_apply]
    · rwa [F.apply_symm_apply]

theorem fundamentalOptimality (h : A.IsIsomorphic B F) {hw : A.WellPosed} {hw' : B.WellPosed}
    (hfo : A.FundamentalOptimality hw) : B.FundamentalOptimality hw' := by
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, hvG, hb, huniq⟩, hbp⟩ := hfo
  refine ⟨⟨σ, (h.isOptimal_iff hw hw' σ).1 hσ⟩, ⟨F v, (h.isValueFunction_iff v).1 hv,
    (h.mem_VG_iff v).1 hvG, (h.solvesBellman_iff v).1 hb, fun w hwG hwb => ?_⟩,
    h.bellmanPrinciple hbp⟩
  rw [← F.apply_symm_apply w]
  refine congrArg F (huniq _ ?_ ?_)
  · rw [h.mem_VG_iff, F.apply_symm_apply]; exact hwG
  · rw [h.solvesBellman_iff, F.apply_symm_apply]; exact hwb

/-- **Theorem 5.1.6 (iii)**: the fundamental optimality properties hold for `(V, 𝕋)` iff they hold
for `(V̂, 𝕋̂)`. -/
theorem fundamentalOptimality_iff (h : A.IsIsomorphic B F) (hw : A.WellPosed)
    (hw' : B.WellPosed) : A.FundamentalOptimality hw ↔ B.FundamentalOptimality hw' :=
  ⟨h.fundamentalOptimality, h.symm.fundamentalOptimality⟩

theorem mem_VU_iff (h : A.IsIsomorphic B F) (v : V) : v ∈ A.VU ↔ F v ∈ B.VU := by
  constructor
  · rintro ⟨hvG, hle⟩
    refine ⟨(h.mem_VG_iff v).1 hvG, ?_⟩
    rw [← h.bellman_eq hvG]
    exact F.monotone hle
  · rintro ⟨hvG, hle⟩
    have hvG' := (h.mem_VG_iff v).2 hvG
    refine ⟨hvG', ?_⟩
    rw [← h.bellman_eq hvG'] at hle
    exact F.le_iff_le.1 hle

theorem isSelector_iff (h : A.IsIsomorphic B F) (g : V → P) :
    A.IsSelector g ↔ B.IsSelector (g ∘ F.symm) := by
  refine ⟨fun hg w => ?_, fun hg v => ?_⟩
  · have := (h.isGreedy_iff (F.symm w) (g (F.symm w))).1 (hg _)
    rwa [F.apply_symm_apply] at this
  · have := hg (F v)
    simp only [Function.comp_apply, F.symm_apply_apply] at this
    exact (h.isGreedy_iff v _).2 this

/-- **Theorem 5.1.7 (i)** (5.5): `F ∘ W = Ŵ ∘ F`, with the selector `g` of `(V, 𝕋)` read as the
selector `g ∘ F⁻¹` of `(V̂, 𝕋̂)`. -/
theorem opt_eq (h : A.IsIsomorphic B F) (m : ℕ) (g : V → P) :
    Semiconj F (A.opt m g) (B.opt m (g ∘ F.symm)) := fun v => by
  change F ((A.T (g v))^[m] v) = (B.T (g (F.symm (F v))))^[m] (F v)
  rw [F.symm_apply_apply]
  exact (Semiconj.iterate_right (h (g v)) m) v

/-- **Theorem 5.1.7 (ii)** (5.6): `F ∘ H = Ĥ ∘ F`. -/
theorem howard_eq (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) (g : V → P) :
    Semiconj F (A.howard hw g) (B.howard hw' (g ∘ F.symm)) := fun v => by
  change F (A.vσ hw (g v)) = B.vσ hw' (g (F.symm (F v)))
  rw [F.symm_apply_apply]
  exact h.vσ_eq hw hw' _

theorem bellman_semiconj (h : A.IsIsomorphic B F) (hr : A.Regular) :
    Semiconj F A.bellman B.bellman := fun v => h.bellman_eq (hr v)

theorem vfiConverges (h : A.IsIsomorphic B F) (hr : A.Regular) {vstar : V}
    (hv : A.VFIConverges vstar) : B.VFIConverges (F vstar) := by
  intro w hw
  have hw' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hw
  have := orderIso_increasesTo F (hv _ hw')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.bellman_semiconj hr) n) (F.symm w), F.apply_symm_apply]

theorem opiConverges (h : A.IsIsomorphic B F) {vstar : V}
    (hv : ∀ g, A.IsSelector g → A.OPIConverges g vstar) :
    ∀ g, B.IsSelector g → B.OPIConverges g (F vstar) := by
  intro g' hg' m hm w hw
  have hg : A.IsSelector (g' ∘ F) := by
    rw [h.isSelector_iff]
    convert hg' using 1
    funext w; simp
  have hw' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hw
  have := orderIso_increasesTo F (hv _ hg m hm _ hw')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.opt_eq m _) n) (F.symm w), F.apply_symm_apply]
  congr 2
  funext w; simp

theorem hpiConverges (h : A.IsIsomorphic B F) (hw : A.WellPosed) (hw' : B.WellPosed) {vstar : V}
    (hv : ∀ g, A.IsSelector g → A.HPIConverges hw g vstar) :
    ∀ g, B.IsSelector g → B.HPIConverges hw' g (F vstar) := by
  intro g' hg' w hwU
  have hg : A.IsSelector (g' ∘ F) := by
    rw [h.isSelector_iff]
    convert hg' using 1
    funext w; simp
  have hwU' : F.symm w ∈ A.VU := by rw [h.mem_VU_iff, F.apply_symm_apply]; exact hwU
  have := orderIso_increasesTo F (hv _ hg _ hwU')
  refine (congrArg (IncreasesTo · (F vstar)) (funext fun n => ?_)).mp this
  simp only [Function.comp_apply]
  rw [(Semiconj.iterate_right (h.howard_eq hw hw' _) n) (F.symm w), F.apply_symm_apply]
  congr 2
  funext w; simp

end IsIsomorphic

variable {A : ADP V P} {B : ADP W P} {F : V ≃o W}

/-- **Theorem 5.1.5** (p. 153): if `(V, 𝕋)` and `(V̂, 𝕋̂)` are isomorphic under `F`, then (i) `σ`
is `v`-greedy iff it is `Fv`-greedy, (ii) regularity, (iii) well-posedness and (iv) order
stability transfer, and (v) the optimal policies coincide. -/
theorem theorem_5_1_5 (h : A.IsIsomorphic B F) :
    (∀ v σ, A.IsGreedy v σ ↔ B.IsGreedy (F v) σ) ∧ (A.Regular ↔ B.Regular) ∧
      (A.WellPosed ↔ B.WellPosed) ∧ (A.IsOrderStable ↔ B.IsOrderStable) ∧
      ∀ (hw : A.WellPosed) (hw' : B.WellPosed) σ, A.IsOptimal hw σ ↔ B.IsOptimal hw' σ :=
  ⟨h.isGreedy_iff, h.regular_iff, h.wellPosed_iff, h.orderStable_iff, h.isOptimal_iff⟩

/-- **Theorem 5.1.6** (p. 153): for regular, well-posed isomorphic ADPs, (i) `F ∘ T = T̂ ∘ F`
(5.4), (ii) `v̂* = Fv*` and (iii) the fundamental optimality properties transfer. -/
theorem theorem_5_1_6 (h : A.IsIsomorphic B F) (hr : A.Regular) (hw : A.WellPosed)
    (hw' : B.WellPosed) :
    Semiconj F A.bellman B.bellman ∧ (∀ v, A.IsValueFunction v → B.IsValueFunction (F v)) ∧
      (A.FundamentalOptimality hw ↔ B.FundamentalOptimality hw') :=
  ⟨h.bellman_semiconj hr, fun v => (h.isValueFunction_iff v).1, h.fundamentalOptimality_iff hw hw'⟩

/-- **Theorem 5.1.7** (p. 154) and **Exercise 5.1.5**: for regular, well-posed isomorphic ADPs,
(i) `F ∘ W = Ŵ ∘ F` (5.5), (ii) `F ∘ H = Ĥ ∘ F` (5.6), and (iii) VFI, (iv) OPI and (v) HPI
converge for `(V, 𝕋)` iff they converge for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_7 (h : A.IsIsomorphic B F) (hr : A.Regular) (hw : A.WellPosed)
    (hw' : B.WellPosed) (vstar : V) :
    (∀ m g, Semiconj F (A.opt m g) (B.opt m (g ∘ F.symm))) ∧
      (∀ g, Semiconj F (A.howard hw g) (B.howard hw' (g ∘ F.symm))) ∧
      (A.VFIConverges vstar ↔ B.VFIConverges (F vstar)) ∧
      ((∀ g, A.IsSelector g → A.OPIConverges g vstar) ↔
        ∀ g, B.IsSelector g → B.OPIConverges g (F vstar)) ∧
      ((∀ g, A.IsSelector g → A.HPIConverges hw g vstar) ↔
        ∀ g, B.IsSelector g → B.HPIConverges hw' g (F vstar)) := by
  have hr' := h.regular_iff.1 hr
  refine ⟨h.opt_eq, h.howard_eq hw hw', ⟨h.vfiConverges hr, fun hv => ?_⟩,
    ⟨h.opiConverges, fun hv => ?_⟩, ⟨h.hpiConverges hw hw', fun hv => ?_⟩⟩
  · simpa using h.symm.vfiConverges hr' hv
  · simpa using h.symm.opiConverges hv
  · simpa using h.symm.hpiConverges hw' hw hv

/-! ### Example 5.1.4 -/

/-- The additive savings ADP (5.2), `(T_σ v)(w) = u(σ(w)) + βv(w − σ(w))`, on `ℝ^ℝ`. -/
def savingsAdd (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) : ADP (ℝ → ℝ) (ℝ → ℝ) where
  T σ v w := u (σ w) + β * v (w - σ w)
  mono _ _ _ h _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (h _) hβ)
  nonempty := ⟨id⟩

/-- The multiplicative savings ADP (5.3), `(T̂_σ v̂)(w) = û(σ(w)) v̂(w − σ(w))^β` with
`û = exp ∘ u`, on positive functions. -/
noncomputable def savingsMul (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    ADP (ℝ → Ioi (0 : ℝ)) (ℝ → ℝ) where
  T σ v w := ⟨Real.exp (u (σ w)) * (v (w - σ w) : ℝ) ^ β,
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (v (w - σ w)).2 β)⟩
  mono _ _ _ h _ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_of_lt (Subtype.prop _)) (h _) hβ) (Real.exp_pos _).le
  nonempty := ⟨id⟩

/-- `v ↦ exp ∘ v`, an order isomorphism from `ℝ^Z` onto the positive functions
(Exercise A.1.10). -/
noncomputable def expPi (Z : Type*) : (Z → ℝ) ≃o (Z → Ioi (0 : ℝ)) where
  toEquiv := Equiv.piCongrRight fun _ => Real.expOrderIso.toEquiv
  map_rel_iff' {v w} := by
    change (∀ z, Real.expOrderIso (v z) ≤ Real.expOrderIso (w z)) ↔ ∀ z, v z ≤ w z
    exact forall_congr' fun z => Real.expOrderIso.le_iff_le

/-- **Example 5.1.4** (p. 152): `F v = exp ∘ v` makes the additive and multiplicative savings
ADPs isomorphic. -/
theorem example_5_1_4 (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    (savingsAdd u hβ).IsIsomorphic (savingsMul u hβ)
      (expPi ℝ) := fun σ v => by
  funext w
  apply Subtype.ext
  change Real.exp (u (σ w) + β * v (w - σ w)) = Real.exp (u (σ w)) * Real.exp (v (w - σ w)) ^ β
  rw [Real.exp_add, ← Real.exp_mul, mul_comm β]

/-! ### Anti-isomorphic ADPs -/

/-- `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F` (§5.1.2.3): `F` is an order
anti-isomorphism (an order isomorphism onto `V̂^∂`) and `F ∘ T_σ = T̂_σ ∘ F` (5.1). -/
def IsAntiIsomorphic (A : ADP V P) (B : ADP W P) (F : V ≃o Wᵒᵈ) : Prop :=
  ∀ σ v, OrderDual.ofDual (F (A.T σ v)) = B.T σ (OrderDual.ofDual (F v))

/-- **Exercise 5.1.6** (p. 155): `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F` iff `(V, 𝕋)`
and `(V̂, 𝕋̂)^∂` are isomorphic under `F`. -/
theorem exercise_5_1_6 (F : V ≃o Wᵒᵈ) : A.IsAntiIsomorphic B F ↔ A.IsIsomorphic B.dual F :=
  ⟨fun h σ v => congrArg OrderDual.toDual (h σ v), fun h σ v => congrArg OrderDual.ofDual (h σ v)⟩

namespace IsAntiIsomorphic

variable {F : V ≃o Wᵒᵈ}

theorem iso (h : A.IsAntiIsomorphic B F) : A.IsIsomorphic B.dual F := (exercise_5_1_6 F).1 h

theorem orderStable_iff (h : A.IsAntiIsomorphic B F) : A.IsOrderStable ↔ B.IsOrderStable :=
  h.iso.orderStable_iff.trans (forall_congr' fun σ => orderStable_dual_iff (B.T σ))

theorem minSelector_iff (h : A.IsAntiIsomorphic B F) (g : V → P) :
    A.IsSelector g ↔ B.IsMinSelector (g ∘ F.symm ∘ OrderDual.toDual) := by
  rw [h.iso.isSelector_iff, B.isMinSelector_iff]
  rfl

end IsAntiIsomorphic

/-- **Theorem 5.1.8** (p. 155): if `(V, 𝕋)` and `(V̂, 𝕋̂)` are anti-isomorphic under `F`, then (i)
`σ` is `v`-max-greedy iff it is `Fv`-min-greedy, (ii) max-regularity of `(V, 𝕋)` is
min-regularity of `(V̂, 𝕋̂)`, (iii) well-posedness and (iv) order stability transfer, and (v)
max-optimal policies of `(V, 𝕋)` are the min-optimal policies of `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_8 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) :
    (∀ v σ, A.IsGreedy v σ ↔ B.IsMinGreedy (OrderDual.ofDual (F v)) σ) ∧
      (A.Regular ↔ B.MinRegular) ∧ (A.WellPosed ↔ B.WellPosed) ∧
      (A.IsOrderStable ↔ B.IsOrderStable) ∧
      ∀ (hw : A.WellPosed) (hw' : B.WellPosed) σ, A.IsOptimal hw σ ↔ B.IsMinOptimal hw' σ :=
  ⟨fun v σ => (h.iso.isGreedy_iff v σ).trans (B.isMinGreedy_iff _ σ).symm,
    h.iso.regular_iff.trans (B.minRegular_iff).symm, h.iso.wellPosed_iff, h.orderStable_iff,
    fun hw hw' σ => (h.iso.isOptimal_iff hw hw'.dual σ).trans (B.isMinOptimal_iff hw' σ).symm⟩

/-- **Theorem 5.1.9** (p. 156) and **Exercise 5.1.7**: for anti-isomorphic, well-posed ADPs with
`(V, 𝕋)` max-regular, (i) `F ∘ T = T̂▿ ∘ F` (5.7), the min-Bellman operator `T̂▿` being the
Bellman operator of `(V̂, 𝕋̂)^∂`, (ii) `v̂▿* = Fv*`, and (iii) the fundamental max-optimality
properties hold for `(V, 𝕋)` iff the fundamental min-optimality properties hold for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_9 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) (hr : A.Regular)
    (hw : A.WellPosed) (hw' : B.WellPosed) :
    Semiconj F A.bellman B.dual.bellman ∧
      (∀ v, A.IsValueFunction v → B.IsMinValueFunction (OrderDual.ofDual (F v))) ∧
      (A.FundamentalOptimality hw ↔ B.MinFundamentalOptimality hw') :=
  ⟨h.iso.bellman_semiconj hr, fun v hv => (h.iso.isValueFunction_iff v).1 hv,
    (h.iso.fundamentalOptimality_iff hw hw'.dual).trans (B.minFundamentalOptimality_iff hw').symm⟩

/-- **Theorem 5.1.10** (p. 156) and **Exercise 5.1.8**: for anti-isomorphic, well-posed ADPs with
`(V, 𝕋)` max-regular, (i) `F ∘ W = Ŵ▿ ∘ F` (5.8), (ii) `F ∘ H = Ĥ▿ ∘ F` (5.9), and (iii)
max-VFI, (iv) max-OPI and (v) max-HPI converge for `(V, 𝕋)` iff min-VFI, min-OPI and min-HPI
converge for `(V̂, 𝕋̂)`. -/
theorem theorem_5_1_10 {F : V ≃o Wᵒᵈ} (h : A.IsAntiIsomorphic B F) (hr : A.Regular)
    (hw : A.WellPosed) (hw' : B.WellPosed) (vstar : V) :
    (∀ m g, Semiconj F (A.opt m g) (B.dual.opt m (g ∘ F.symm))) ∧
      (∀ g, Semiconj F (A.howard hw g) (B.dual.howard hw'.dual (g ∘ F.symm))) ∧
      (A.VFIConverges vstar ↔ B.MinVFIConverges (OrderDual.ofDual (F vstar))) ∧
      ((∀ g, A.IsSelector g → A.OPIConverges g vstar) ↔
        ∀ g, B.IsMinSelector g → B.MinOPIConverges g (OrderDual.ofDual (F vstar))) ∧
      ((∀ g, A.IsSelector g → A.HPIConverges hw g vstar) ↔
        ∀ g, B.IsMinSelector g → B.MinHPIConverges hw' g (OrderDual.ofDual (F vstar))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_5_1_7 h.iso hr hw hw'.dual vstar
  refine ⟨h1, h2, h3.trans (B.minVFIConverges_iff _).symm, h4.trans ?_, h5.trans ?_⟩
  · constructor
    · intro hv g hg
      exact (B.minOPIConverges_iff g _).2 (hv _ ((B.isMinSelector_iff g).1 hg))
    · intro hv g hg
      have := (B.minOPIConverges_iff (g ∘ OrderDual.toDual) _).1
        (hv _ ((B.isMinSelector_iff _).2 hg))
      exact this
  · constructor
    · intro hv g hg
      exact (B.minHPIConverges_iff hw' g _).2 (hv _ ((B.isMinSelector_iff g).1 hg))
    · intro hv g hg
      have := (B.minHPIConverges_iff hw' (g ∘ OrderDual.toDual) _).1
        (hv _ ((B.isMinSelector_iff _).2 hg))
      exact this

end ADP

end SargentStachurski.ADPTransformations
