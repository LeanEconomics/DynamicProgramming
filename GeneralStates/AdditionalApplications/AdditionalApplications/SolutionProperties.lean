/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.WeightedRDP

/-!
# Properties of solutions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.3 (pp. 223–225), with Lemma A.2.6
(p. 346).

The setting is that of Proposition 7.2.5 (`WRDP.ContinuousCase`).

* **Lemma A.2.6**: a closed set that is invariant under a map whose iterates converge to `v̄`
  contains `v̄`.
* **Exercise 7.2.1**: the increasing functions in `bℓcX₊` form a closed set.
* **Proposition 7.2.6**: under Assumption 7.2.8 (`Γ` increasing and `B(x, a, v) ≤ B(x', a, v)` for
  `x ⪯ x'` and increasing `v`), `v*` is increasing.
* **Proposition 7.2.7**: under Assumption 7.2.9 (`G` convex and `B` concave on `G` for concave `v`),
  `v*` is concave. The state space is a convex set `S` in a vector space `X` (the book takes `X`
  itself convex in a vector space); `G` and the concavity of `v*` are restricted to `S`.
* **Proposition 7.2.8**: under Assumption 7.2.10 (strict concavity in `a`), the optimal policy is
  unique and, with the last claim of Theorem A.3.3 for `Γ`, continuous.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- **Lemma A.2.6** (p. 346): if `Sⁿu → v̄` for every `u ∈ U`, `U` is closed and nonempty, and
`SU ⊆ U`, then `v̄ ∈ U`. -/
theorem lemma_A_2_6 {V : Type*} [TopologicalSpace V] {S : V → V} {vbar : V} {U : Set V}
    (hS : ∀ u ∈ U, Tendsto (fun n => S^[n] u) atTop (𝓝 vbar)) (hU : IsClosed U)
    (hSU : MapsTo S U U) (hne : U.Nonempty) : vbar ∈ U := by
  obtain ⟨u, hu⟩ := hne
  exact hU.mem_of_tendsto (hS u hu) (Eventually.of_forall fun n => hSU.iterate n hu)

/-- A strictly concave function has at most one maximizer. -/
theorem eq_of_isMax_of_strictConcaveOn {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    {f : E → ℝ} (hf : StrictConcaveOn ℝ s f) {a b : E} (ha : a ∈ s) (hb : b ∈ s)
    (hamax : ∀ c ∈ s, f c ≤ f a) (hbmax : ∀ c ∈ s, f c ≤ f b) : a = b := by
  by_contra hne
  have hlt := hf.2 ha hb hne (one_half_pos (α := ℝ)) one_half_pos (add_halves 1)
  have hmid := hamax _ (hf.1 ha hb (one_half_pos (α := ℝ)).le one_half_pos.le (add_halves 1))
  have hab : f a = f b := le_antisymm (hbmax a ha) (hamax b hb)
  rw [smul_eq_mul, smul_eq_mul, hab] at hlt
  rw [hab] at hmid
  linarith

/-- Geometric convergence of VFI on `V₀` gives `Tⁿv → v*` for `v ∈ V₀`. -/
theorem ADP.VFIGeometric.tendsto {V P : Type*} [PartialOrder V] [MetricSpace V] {A : ADP V P}
    {V₀ : Set V} {vstar : V} (h : A.VFIGeometric V₀ vstar) {v : V} (hv : v ∈ V₀) :
    Tendsto (fun n => A.bellman^[n] v) atTop (𝓝 vstar) := by
  obtain ⟨-, β, hβ0, hβ1, hC⟩ := h
  obtain ⟨C, hC⟩ := hC v hv
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hC ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [TopologicalSpace X]
  [TopologicalSpace A]

/-- The zero of `bX₊`. -/
noncomputable def coneZero (X : Type*) [MeasurableSpace X] : posCone X :=
  ⟨0, BM.le_def.2 fun _ => le_rfl⟩

omit [TopologicalSpace X] in
theorem wev_coneZero (ℓ : X → ℝ) : wev ℓ (coneZero X) = 0 :=
  funext fun x => by simp [wev, wevB, coneZero, BM.zero_apply]

/-- **Exercise 7.2.1** (p. 223): the increasing functions in `bℓcX₊` form a closed set. -/
theorem exercise_7_2_1 [Preorder X] (ℓ : X → ℝ) :
    IsClosed {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev ℓ h)} := by
  refine isClosed_bcPlus.inter (isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_)
  have hlim' : Tendsto (fun n => (hs n).1) atTop (𝓝 h.1) :=
    (continuous_subtype_val.tendsto h).comp hlim
  intro x y hxy
  exact le_of_tendsto_of_tendsto' (exercise_A_5_24 hlim' x) (exercise_A_5_24 hlim' y)
    fun n => hhs n hxy

namespace WRDP

variable (M : WRDP X A)

/-- The hypotheses of Proposition 7.2.5: (U1)–(U2) with `λ ∈ [0, 1)` and Assumption 7.2.6. -/
structure ContinuousCase : Prop where
  ℓ_continuous : Continuous M.ℓ
  maxSel : HasMaxSelections M.Γ
  blackwell : ∃ lam, 0 ≤ lam ∧ lam < 1 ∧ M.IsBlackwell lam
  continuousOn : ∀ v ∈ blPlus M.ℓ, Continuous v →
    ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}

variable {M}

/-- Proposition 7.2.5 in the form used below. -/
theorem ContinuousCase.prop [Nonempty X] (hM : M.ContinuousCase) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.VFIGeometric (bcPlus X) vstar := by
  obtain ⟨lam, hlam0, hlam1, hB⟩ := hM.blackwell
  obtain ⟨hw, hFO, vstar, hv, -, hgeo, -⟩ := M.proposition_7_2_5 hM.ℓ_continuous hM.maxSel hlam0
    hlam1 hB hM.continuousOn
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-- The value function lies in every closed `T`-invariant subset of `bℓcX₊` that contains `0`
(Lemma A.2.6). -/
theorem ContinuousCase.vstar_mem [Nonempty X] (hM : M.ContinuousCase) {U : Set (posCone X)}
    (hU : IsClosed U) (hUV : U ⊆ bcPlus X) (hT : MapsTo M.toRDP.adp.bellman U U)
    (h0 : coneZero X ∈ U) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ U, M.toRDP.adp.VFIGeometric (bcPlus X) vstar := by
  obtain ⟨hw, hFO, vstar, -, hgeo⟩ := hM.prop
  exact ⟨hw, hFO, vstar, lemma_A_2_6 (fun u hu => hgeo.tendsto (hUV hu)) hU hT ⟨_, h0⟩, hgeo⟩

/-- **Proposition 7.2.6** (p. 224): under the conditions of Proposition 7.2.5 and Assumption 7.2.8
(`Γ(x) ⊆ Γ(x')` and `B(x, a, v) ≤ B(x', a, v)` for `x ⪯ x'`, `a ∈ Γ(x)` and increasing
`v ∈ bℓcX₊`), the value function `v*` is increasing. -/
theorem proposition_7_2_6 [Nonempty X] [Preorder X] (hM : M.ContinuousCase)
    (hΓmono : ∀ x x', x ≤ x' → M.Γ x ⊆ M.Γ x')
    (hBmono : ∀ x x', x ≤ x' → ∀ v ∈ blPlus M.ℓ, Continuous v → Monotone v →
      ∀ a ∈ M.Γ x, M.B x a v ≤ M.B x' a v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) := by
  have hT : MapsTo M.toRDP.adp.bellman {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev M.ℓ h)}
      {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev M.ℓ h)} := by
    rintro h ⟨hc, hmono⟩
    obtain ⟨-, hTb, -, hgr⟩ := M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hc
    refine ⟨hTb, fun x x' hxx' => ?_⟩
    obtain ⟨⟨a, ha, hax⟩, -⟩ := hgr x
    rw [← hax]
    exact (hBmono x x' hxx' _ (wev_mem M.measurable_ℓ M.one_le_ℓ h)
      (hM.ℓ_continuous.mul hc) hmono a ha).trans ((hgr x').2 ⟨a, hΓmono x x' hxx' ha, rfl⟩)
  obtain ⟨hw, hFO, vstar, hv, hgeo⟩ := hM.vstar_mem (exercise_7_2_1 M.ℓ) (fun _ h => h.1) hT
    ⟨zero_mem_bcPlus, by rw [wev_coneZero]; exact monotone_const⟩
  exact ⟨hw, hFO, vstar, hv.1, hgeo.1, hv.2⟩

variable [AddCommGroup X] [Module ℝ X] [AddCommGroup A] [Module ℝ A]

omit [MeasurableSpace A] [TopologicalSpace A] [AddCommGroup A] [Module ℝ A] in
/-- The functions in `bℓcX₊` that are concave on `S` form a closed set. -/
theorem isClosed_concave (ℓ : X → ℝ) (S : Set X) (hS : Convex ℝ S) :
    IsClosed {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev ℓ h)} := by
  refine isClosed_bcPlus.inter (isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_)
  have hlim' : Tendsto (fun n => (hs n).1) atTop (𝓝 h.1) :=
    (continuous_subtype_val.tendsto h).comp hlim
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  exact le_of_tendsto_of_tendsto' (((exercise_A_5_24 hlim' x).const_smul a).add
    ((exercise_A_5_24 hlim' y).const_smul b)) (exercise_A_5_24 hlim' _)
    fun n => (hhs n).2 hx hy ha hb hab

/-- The graph of `Γ` over `S`. -/
def feasibleOn (Γ : X → Set A) (S : Set X) : Set (X × A) := {p | p.1 ∈ S ∧ p.2 ∈ Γ p.1}

/-- **Proposition 7.2.7** (p. 224): under the conditions of Proposition 7.2.5 and Assumption 7.2.9
(the feasible pairs over a convex `S` form a convex set and `(x, a) ↦ B(x, a, v)` is concave on
them whenever `v ∈ bℓcX₊` is concave on `S`), the value function `v*` is concave on `S`. -/
theorem proposition_7_2_7 [Nonempty X] (hM : M.ContinuousCase) {S : Set X} (hS : Convex ℝ S)
    (hG : Convex ℝ (feasibleOn M.Γ S))
    (hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      ConcaveOn ℝ (feasibleOn M.Γ S) fun p => M.B p.1 p.2 v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.IsValueFunction vstar ∧ ConcaveOn ℝ S (wev M.ℓ vstar) := by
  have hT : MapsTo M.toRDP.adp.bellman
      {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev M.ℓ h)}
      {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev M.ℓ h)} := by
    rintro h ⟨hc, hconc⟩
    obtain ⟨-, hTb, ⟨σ, hσ⟩, hgr⟩ :=
      M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hc
    obtain ⟨-, hval, -⟩ := M.toRDP.bellman_of_isArgmax hσ
    refine ⟨hTb, hS, fun x hx y hy a b ha hb hab => ?_⟩
    have hp : (x, σ.1 x) ∈ feasibleOn M.Γ S := ⟨hx, σ.2.2 x⟩
    have hq : (y, σ.1 y) ∈ feasibleOn M.Γ S := ⟨hy, σ.2.2 y⟩
    have hmem := hG hp hq ha hb hab
    have hineq := (hBc _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) (hM.ℓ_continuous.mul hc)
      hconc).2 hp hq ha hb hab
    change a • wev M.ℓ (M.toRDP.adp.bellman h) x + b • wev M.ℓ (M.toRDP.adp.bellman h) y ≤
      wev M.ℓ (M.toRDP.adp.bellman h) (a • x + b • y)
    have h1 : wev M.ℓ (M.toRDP.adp.bellman h) x = M.B x (σ.1 x) (wev M.ℓ h) := hval x
    have h2 : wev M.ℓ (M.toRDP.adp.bellman h) y = M.B y (σ.1 y) (wev M.ℓ h) := hval y
    rw [h1, h2]
    exact hineq.trans ((hgr _).2 ⟨_, hmem.2, rfl⟩)
  obtain ⟨hw, hFO, vstar, hv, hgeo⟩ := hM.vstar_mem (isClosed_concave M.ℓ S hS)
    (fun _ h => h.1) hT ⟨zero_mem_bcPlus, by rw [wev_coneZero]; exact concaveOn_const 0 hS⟩
  exact ⟨hw, hFO, vstar, hv.1, hgeo.1, hv.2⟩

/-- **Proposition 7.2.8** (p. 225): under the conditions of Proposition 7.2.7 and
Assumption 7.2.10 (`a ↦ B(x, a, v)` strictly concave on `Γ(x)` for every `x` and every `v ∈ bℓcX₊`
concave on `S`), the optimal policy is unique; it is continuous when `Γ` has the last claim of
Theorem A.3.3 (`HasContinuousUniqueMax`). -/
theorem proposition_7_2_8 [Nonempty X] (hM : M.ContinuousCase) {S : Set X} (hS : Convex ℝ S)
    (hG : Convex ℝ (feasibleOn M.Γ S))
    (hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      ConcaveOn ℝ (feasibleOn M.Γ S) fun p => M.B p.1 p.2 v)
    (hstrict : ∀ x, ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      StrictConcaveOn ℝ (M.Γ x) fun a => M.B x a v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ σ, M.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, M.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        (HasContinuousUniqueMax M.Γ → Continuous σ.1) := by
  obtain ⟨hw, hFO, vstar, hv, hvf, hconc⟩ := M.proposition_7_2_7 hM hS hG hBc
  have hvc : Continuous (wev M.ℓ vstar) := hM.ℓ_continuous.mul hv
  have hvm := wev_mem M.measurable_ℓ M.one_le_ℓ vstar
  obtain ⟨hiff, -, -, -, -, hcont⟩ := M.toRDP.lemma_7_1_2 hM.maxSel vstar
    (hM.continuousOn _ hvm hvc)
  obtain ⟨-, -, ⟨σ, hσ⟩, -⟩ :=
    M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hv
  -- maximizers of the strictly concave `a ↦ B(x, a, v*)` coincide
  have huniq : ∀ x, ∀ a ∈ M.Γ x, M.B x (σ.1 x) (wev M.ℓ vstar) ≤ M.B x a (wev M.ℓ vstar) →
      a = σ.1 x := fun x a ha hle =>
    eq_of_isMax_of_strictConcaveOn (hstrict x _ hvm hvc hconc) ha (σ.2.2 x)
      (fun c hc => (hσ x c hc).trans hle) (hσ x)
  have hopt : ∀ τ, M.toRDP.adp.IsOptimal hw τ ↔ M.toRDP.IsArgmax vstar τ := fun τ => by
    rw [hFO.2.2 τ]
    constructor
    · rintro ⟨w, hw', hg⟩
      rw [hw'.unique hvf] at hg
      exact (hiff τ).1 hg
    · exact fun h => ⟨vstar, hvf, (hiff τ).2 h⟩
  refine ⟨hw, hFO, σ, (hopt σ).2 hσ, fun τ hτ => ?_, fun hU => hcont hU σ hσ huniq⟩
  have hτ' := (hopt τ).1 hτ
  exact Subtype.ext (funext fun x => huniq x _ (τ.2.2 x) (hτ' x _ (σ.2.2 x)))

end WRDP

end SargentStachurski.AdditionalApplications
