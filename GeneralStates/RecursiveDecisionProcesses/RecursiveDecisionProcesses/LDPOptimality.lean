/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.LDP
import RecursiveDecisionProcesses.Correspondences
import RecursiveDecisionProcesses.MetricADP

/-!
# Optimality for linear decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.3 (pp. 192–194).

* **Proposition 6.1.2** (finite LDPs): if `𝕋_LDP` is finite and `ρ(K_σ) < 1` for every `σ`, the
  fundamental optimality properties hold and VFI, OPI and HPI converge. The book calls regularity
  "obvious in the finite case"; it holds because finitely many policy operators can be pasted
  into one measurable policy that is pointwise best (`regular_of_isFinite`).
* Feller properties: `K` is weak Feller if `Kh ∈ bcG` for `h ∈ bcX`, strong Feller if `Kh` is
  continuous on `G` for every `h ∈ bX`.
* **Proposition 6.1.3** (Feller LDPs): under Assumption 6.1.1 (with the maximum theorem,
  Theorem A.3.3, for `Γ`), a weak Feller `K` and a discount operator `D ≥ K_σ` on `bX₊`, the
  fundamental optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`; if
  `K` is strong Feller, OPI and HPI converge (Theorem 4.1.8 with `V₀ = bcX`).
* §6.1.3.2: greedy policies are exactly the pointwise maximizers (6.8), and the Bellman operator
  is (6.9), `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v(x')K(x, a, dx')}`, for all `v ∈ bX` under
  strong Feller and for `v ∈ bcX` under weak Feller.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Measurable least maximizers over a finite set -/

/-- The maximizers of `a ↦ h(x, a)` over a finite type. -/
noncomputable def argmaxSet {X I : Type*} [Fintype I] (h : X → I → ℝ) (x : X) : Finset I :=
  Finset.univ.filter fun i => ∀ j, h x j ≤ h x i

theorem argmaxSet_nonempty {X I : Type*} [Fintype I] [Nonempty I] (h : X → I → ℝ) (x : X) :
    (argmaxSet h x).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (h x) Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩

/-- The least maximizer. -/
noncomputable def argmaxSel {X I : Type*} [Fintype I] [Nonempty I] [LinearOrder I]
    (h : X → I → ℝ) (x : X) : I :=
  (argmaxSet h x).min' (argmaxSet_nonempty h x)

theorem argmaxSel_max {X I : Type*} [Fintype I] [Nonempty I] [LinearOrder I] (h : X → I → ℝ)
    (x : X) (j : I) : h x j ≤ h x (argmaxSel h x) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (argmaxSet_nonempty h x))).2 j

/-- The least maximizer is measurable when each `x ↦ h(x, i)` is. -/
theorem measurable_argmaxSel {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Fintype I] [Nonempty I] [LinearOrder I] {h : X → I → ℝ}
    (hm : ∀ i, Measurable fun x => h x i) : Measurable (argmaxSel h) := by
  classical
  refine measurable_to_countable' fun i => ?_
  have hset : argmaxSel h ⁻¹' {i} =
      {x | ∀ j, h x j ≤ h x i} ∩ ⋂ j, ({x | ∀ k, h x k ≤ h x j}ᶜ ∪ {_x | i ≤ j}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨argmaxSel_max h x, fun j => ?_⟩
      by_cases hj : ∀ k, h x k ≤ h x j
      · exact Or.inr (Finset.min'_le (argmaxSet h x) j
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
      · exact Or.inl hj
    · rintro ⟨hmax, hmin⟩
      refine le_antisymm (Finset.min'_le (argmaxSet h x) i
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax⟩))
        (Finset.le_min' (argmaxSet h x) (argmaxSet_nonempty h x) i fun j hj => ?_)
      rcases hmin j with h1 | h1
      · exact absurd (Finset.mem_filter.1 hj).2 h1
      · exact h1
  rw [hset]
  have hmeas : ∀ j, MeasurableSet {x | ∀ k, h x k ≤ h x j} := fun j => by
    have : {x | ∀ k, h x k ≤ h x j} = ⋂ k, {x | h x k ≤ h x j} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iInter fun k => measurableSet_le (hm k) (hm j)
  refine (hmeas i).inter (MeasurableSet.iInter fun j => (hmeas j).compl.union ?_)
  by_cases h' : i ≤ j
  · simp [h']
  · simp [h']

namespace LDP

attribute [local instance] LDP.P_markov

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : LDP X A)

/-- With finitely many policy operators, the LDP is regular: paste the finitely many operators
into a measurable policy that is best at every state. -/
theorem regular_of_isFinite (hfin : M.adp.IsFinite) : M.adp.Regular := by
  classical
  have : Finite (range M.adp.T) := hfin.to_subtype
  let k := Nat.card (range M.adp.T)
  let f : range M.adp.T ≃ Fin k := Finite.equivFin _
  let e : Fin k → M.Policy := fun j => (f.symm j).2.choose
  have he : ∀ j, M.adp.T (e j) = (f.symm j).1 := fun j => (f.symm j).2.choose_spec
  have hall : ∀ σ, ∃ j, M.adp.T σ = M.adp.T (e j) := fun σ =>
    ⟨f ⟨_, σ, rfl⟩, by rw [he, Equiv.symm_apply_apply]⟩
  obtain ⟨σ₀⟩ := M.nonempty_policy
  have : Nonempty (Fin k) := ⟨(hall σ₀).choose⟩
  intro v
  let h : X → Fin k → ℝ := fun x j => (M.adp.T (e j) v).toFun x
  let i := argmaxSel h
  have hi : Measurable i := measurable_argmaxSel fun j => (M.adp.T (e j) v).measurable'
  let σ : X → A := fun x => (e (i x)).1 x
  have hσm : Measurable σ := by
    have hF : Measurable fun p : X × Fin k => (e p.2).1 p.1 :=
      measurable_from_prod_countable_left fun j => (e j).2.1
    exact hF.comp (measurable_id.prodMk hi)
  let σp : M.Policy := ⟨σ, hσm, fun x => (e (i x)).2.2 x⟩
  refine ⟨σp, fun τ x => ?_⟩
  obtain ⟨j, hj⟩ := hall τ
  rw [hj]
  change h x j ≤ M.obj v (x, (e (i x)).1 x)
  exact argmaxSel_max h x j

/-- **Proposition 6.1.2** (p. 192): if `𝕋_LDP` is finite and `ρ(K_σ) < 1` for every `σ`, then the
fundamental optimality properties hold and VFI, OPI and HPI all converge. -/
theorem proposition_6_1_2 (hfin : M.adp.IsFinite)
    (hρ : ∀ σ, BanachLattice.specRad (M.K σ) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have : Nonempty (BM X) := ⟨0⟩
  exact BanachLattice.theorem_4_1_7 ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩ M.adp
    (M.regular_of_isFinite hfin) hfin M.isAdditive hρ

/-! ### Feller LDPs -/

variable [TopologicalSpace X] [TopologicalSpace A]

/-- The feasible state-action pairs `G = graph Γ` (6.3). -/
def G : Set (X × A) := {p | p.2 ∈ M.Γ p.1}

/-- `K` is weak Feller: `Kh` is continuous on `G` whenever `h ∈ bcX` (§6.1.1). -/
def IsWeakFeller : Prop :=
  ∀ h : BM X, Continuous h.toFun →
    ContinuousOn (fun p => M.β.toFun p * ∫ x', h.toFun x' ∂(M.P p)) M.G

/-- `K` is strong Feller: `Kh` is continuous on `G` for every `h ∈ bX` (§6.1.1). -/
def IsStrongFeller : Prop :=
  ∀ h : BM X, ContinuousOn (fun p => M.β.toFun p * ∫ x', h.toFun x' ∂(M.P p)) M.G

theorem IsStrongFeller.isWeakFeller {M : LDP X A} (h : M.IsStrongFeller) : M.IsWeakFeller :=
  fun f _ => h f

/-- `bcX`, the bounded continuous functions, inside `bX`. -/
def bc (X : Type*) [MeasurableSpace X] [TopologicalSpace X] : Set (BM X) :=
  {v | Continuous v.toFun}

theorem isClosed_bc : IsClosed (bc X) := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  exact (BM.tendstoUniformly_of_tendsto hlim).continuous (Frequently.of_forall hvs)

theorem zero_mem_bc : (0 : BM X) ∈ bc X := continuous_const

/-- Assumption 6.1.1 (ii) and the Feller property make the objective continuous on `G`. -/
theorem continuousOn_obj (hr : ContinuousOn M.r.toFun M.G) {v : BM X}
    (hK : ContinuousOn (fun p => M.β.toFun p * ∫ x', v.toFun x' ∂(M.P p)) M.G) :
    ContinuousOn (M.obj v) M.G :=
  hr.add hK

/-- With the maximum theorem for `Γ` and a continuous objective, a greedy policy exists, it attains
the maximum at each state, and the Bellman operator is continuous. -/
theorem greedy_of_continuousOn (hB : HasMaxSelections M.Γ) {v : BM X}
    (hc : ContinuousOn (M.obj v) M.G) :
    ∃ σ : M.Policy, M.adp.IsGreedy v σ ∧
      (∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      Continuous (M.adp.bellman v).toFun := by
  obtain ⟨σ, hσm, hσΓ, hmax, hcont⟩ := hB _ hc
  let σp : M.Policy := ⟨σ, hσm, hσΓ⟩
  have hg : M.adp.IsGreedy v σp := M.isGreedy_of_argmax v σp hmax
  refine ⟨σp, hg, hmax, ?_⟩
  have heq : M.adp.bellman v = M.adp.T σp v := ((M.adp.isGreedy_iff ⟨σp, hg⟩ σp).1 hg).symm
  rw [heq]
  exact hcont

/-- **Proposition 6.1.3** (p. 192): under Assumption 6.1.1 (`Γ` with the maximum theorem,
Theorem A.3.3, and `r` continuous on `G`), if `K` is weak Feller and `K_σ ≤ D` on `bX₊` for a
discount operator `D`, then (i) the fundamental optimality properties hold, (ii) `v* ∈ bcX` and
(iii) VFI converges geometrically on `bcX`; if `K` is strong Feller, OPI and HPI converge. -/
theorem proposition_6_1_3 (hB : HasMaxSelections M.Γ) (hr : ContinuousOn M.r.toFun M.G)
    (hK : M.IsWeakFeller) {D : BM X → BM X} (hD : BanachLattice.IsDiscountOperator D)
    (hKD : ∀ σ h, 0 ≤ h → M.K σ h ≤ D h) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ bc X,
      M.adp.VFIGeometric (bc X) vstar ∧
        (M.IsStrongFeller →
          ∀ g, M.adp.IsSelector g →
            M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar) := by
  have : Nonempty (BM X) := ⟨0⟩
  have hsr : M.adp.IsSemiRegular (bc X) := by
    refine ⟨isClosed_bc, fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨σ, hg, -, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
      exact ⟨σ, hg⟩
    · obtain ⟨-, -, -, hc⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
      exact hc
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩ M.adp M.isAdditive hD hKD hsr
    ⟨0, zero_mem_bc⟩
  refine ⟨hw, hFO, vstar, hv, hgeo, fun hS => hconv fun v => ?_⟩
  obtain ⟨σ, hg, -, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hS v))
  exact ⟨σ, hg⟩

/-- §6.1.3.2 (pp. 193–194): if `Γ` has the maximum theorem, `r` is continuous on `G` and `K` is
strong Feller, then for every `v ∈ bX` a policy satisfying (6.8) exists, a policy is `v`-greedy iff
it satisfies (6.8), and the Bellman operator is (6.9),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v(x')K(x, a, dx')}`. -/
theorem implications [MeasurableSingletonClass X] (hB : HasMaxSelections M.Γ)
    (hr : ContinuousOn M.r.toFun M.G) (hK : M.IsStrongFeller) (v : BM X) :
    (∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      (∀ σ : M.Policy, M.adp.IsGreedy v σ ↔
        ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      ∀ x, IsGreatest ((fun a => M.obj v (x, a)) '' M.Γ x) ((M.adp.bellman v).toFun x) := by
  obtain ⟨σ, hg, hmax, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v))
  have heq : M.adp.bellman v = M.adp.T σ v := ((M.adp.isGreedy_iff ⟨σ, hg⟩ σ).1 hg).symm
  refine ⟨⟨σ, hmax⟩, fun τ => ⟨M.argmax_of_isGreedy v τ, M.isGreedy_of_argmax v τ⟩,
    fun x => ⟨⟨σ.1 x, σ.2.2 x, ?_⟩, ?_⟩⟩
  · rw [heq]
    rfl
  · rintro _ ⟨a, ha, rfl⟩
    rw [heq]
    exact hmax x a ha

/-- §6.1.3.2 (p. 194), weak Feller case: the expressions (6.8)–(6.9) remain valid for `v ∈ bcX`:
a policy attaining the maximum exists and `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v dK(x, a)}`. -/
theorem implications_bc (hB : HasMaxSelections M.Γ) (hr : ContinuousOn M.r.toFun M.G)
    (hK : M.IsWeakFeller) {v : BM X} (hv : v ∈ bc X) :
    (∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      ∀ x, IsGreatest ((fun a => M.obj v (x, a)) '' M.Γ x) ((M.adp.bellman v).toFun x) := by
  obtain ⟨σ, hg, hmax, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
  have heq : M.adp.bellman v = M.adp.T σ v := ((M.adp.isGreedy_iff ⟨σ, hg⟩ σ).1 hg).symm
  refine ⟨⟨σ, hmax⟩, fun x => ⟨⟨σ.1 x, σ.2.2 x, ?_⟩, ?_⟩⟩
  · rw [heq]
    rfl
  · rintro _ ⟨a, ha, rfl⟩
    rw [heq]
    exact hmax x a ha

end LDP

end SargentStachurski.RecursiveDecisionProcesses
