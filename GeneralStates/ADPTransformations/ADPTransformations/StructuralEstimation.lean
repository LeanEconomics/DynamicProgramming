/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.BMOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Structural estimation

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.3.1, §4.2.3.3 and §4.2.3.4
(pp. 140–146).

Post-action value functions `g ∈ bG`, `G = X × A`, with `A` finite. For a certainty equivalent
operator `M : bX → bG` (order preserving, `M(v + κ𝟙) = Mv + κ𝟙`) the policy operators are
`T̂_σ g = M H_σ g` with `(H_σ g)(x') = r(x', σ(x')) + βg(x', σ(x'))`.

* **Exercise 4.2.4**: a Borel `σ` with `σ(x) ∈ argmax_a [r(x, a) + βg(x, a)]` (4.22), the least
  maximizer for a fixed order on `A`; such `σ` is `g`-greedy, so the ADP is regular.
* **Proposition 4.2.6** (§4.2.3.3): optimality, VFI, OPI and HPI for every certainty equivalent
  `M`, by Theorem 4.1.3 and (4.28); the Bellman operator is `T̂g = MHg` (4.26).
* §4.2.3.1: `M` the expectation under a stochastic kernel `P` from `G` to `X`, giving (4.21), the
  Bellman equation (4.20), **Exercise 4.2.5** (contraction of modulus `β`) and
  **Proposition 4.2.4**.
* §4.2.3.4: the risk-sensitive certainty equivalent `Mf = −γ⁻¹ ln ∫ exp(−γf) dP`, `γ ≠ 0`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Exercise 4.2.4: measurable greedy policies -/

/-- The maximizers of `a ↦ h(x, a)`. -/
noncomputable def argmaxSet [Fintype A] (h : X → A → ℝ) (x : X) : Finset A :=
  Finset.univ.filter fun a => ∀ a', h x a' ≤ h x a

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem argmaxSet_nonempty [Fintype A] [Nonempty A] (h : X → A → ℝ) (x : X) :
    (argmaxSet h x).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (h x) Finset.univ_nonempty
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a' => ha a' (Finset.mem_univ _)⟩⟩

/-- The least maximizer of `a ↦ h(x, a)`. -/
noncomputable def argmaxSel [Fintype A] [Nonempty A] [LinearOrder A] (h : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet h x).min' (argmaxSet_nonempty h x)

omit [MeasurableSpace X] [MeasurableSpace A] in
theorem argmaxSel_max [Fintype A] [Nonempty A] [LinearOrder A] (h : X → A → ℝ) (x : X) (a : A) :
    h x a ≤ h x (argmaxSel h x) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (argmaxSet_nonempty h x))).2 a

/-- **Exercise 4.2.4** (p. 142): if `x ↦ h(x, a)` is measurable for each `a`, the least maximizer
is a Borel measurable selection from `argmax_a h(x, a)`. -/
theorem measurable_argmaxSel [Fintype A] [Nonempty A] [LinearOrder A] {h : X → A → ℝ}
    (hm : ∀ a, Measurable fun x => h x a) : Measurable (argmaxSel h) := by
  classical
  refine measurable_to_countable' fun a => ?_
  have hset : argmaxSel h ⁻¹' {a} =
      {x | ∀ a', h x a' ≤ h x a} ∩ ⋂ a', ({x | ∀ a'', h x a'' ≤ h x a'}ᶜ ∪ {_x | a ≤ a'}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨argmaxSel_max h x, fun a' => ?_⟩
      by_cases ha' : ∀ a'', h x a'' ≤ h x a'
      · exact Or.inr (Finset.min'_le (argmaxSet h x) a'
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha'⟩))
      · exact Or.inl ha'
    · rintro ⟨hmax, hmin⟩
      refine le_antisymm (Finset.min'_le (argmaxSet h x) a
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax⟩))
        (Finset.le_min' (argmaxSet h x) (argmaxSet_nonempty h x) a fun a' ha' => ?_)
      rcases hmin a' with h1 | h1
      · exact absurd (Finset.mem_filter.1 ha').2 h1
      · exact h1
  rw [hset]
  have hmeas : ∀ b, MeasurableSet {x | ∀ a', h x a' ≤ h x b} := fun b => by
    have : {x | ∀ a', h x a' ≤ h x b} = ⋂ a', {x | h x a' ≤ h x b} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iInter fun a' => measurableSet_le (hm a') (hm b)
  refine (hmeas a).inter (MeasurableSet.iInter fun a' => (hmeas a').compl.union ?_)
  by_cases h' : a ≤ a'
  · simp [h']
  · simp [h']

/-! ### The post-action ADP with a certainty equivalent operator -/

/-- Policies: Borel maps `X → A`. -/
def SEPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] : Type _ :=
  {σ : X → A // Measurable σ}

/-- A certainty equivalent operator from `bX` to `bG` (§4.2.3.3). -/
def IsCEOperator (M : BM X → BM (X × A)) : Prop :=
  Monotone M ∧ ∀ v (κ : ℝ), 0 ≤ κ → M (v + κ • BM.const 1) = M v + κ • BM.const 1

/-- The structural estimation model: a reward `r ∈ bG`, a discount factor `β ∈ [0, 1)` and a
certainty equivalent operator `M`. -/
structure PostAction (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the reward -/
  r : BM (X × A)
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the certainty equivalent operator -/
  M : BM X → BM (X × A)

namespace PostAction

variable (S : PostAction X A)

/-- `(H_σ g)(x') = r(x', σ(x')) + βg(x', σ(x'))`. -/
noncomputable def H (σ : SEPolicy X A) (g : BM (X × A)) : BM X :=
  ⟨fun x => S.r.toFun (x, σ.1 x) + S.β * g.toFun (x, σ.1 x),
    (S.r.measurable'.comp (measurable_id.prodMk σ.2)).add
      (measurable_const.mul (g.measurable'.comp (measurable_id.prodMk σ.2))),
    ⟨‖S.r‖ + |S.β| * ‖g‖, fun _ => (abs_add_le _ _).trans (add_le_add (BM.abs_le_norm _ _)
      ((abs_mul S.β _).trans_le (mul_le_mul_of_nonneg_left (BM.abs_le_norm _ _)
        (abs_nonneg _))))⟩⟩

theorem H_mono (σ : SEPolicy X A) : Monotone (S.H σ) := fun _ _ h _ =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (h _) S.β_nonneg)

theorem H_shift (σ : SEPolicy X A) (g : BM (X × A)) (κ : ℝ) :
    S.H σ (g + κ • BM.const 1) = S.H σ g + (S.β * κ) • BM.const 1 :=
  BM.ext fun x => by
    simp only [H, BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
    ring

/-- The policy operators `T̂_σ g = M H_σ g`. -/
noncomputable def adp [Nonempty A] (hM : IsCEOperator S.M) : ADP (BM (X × A)) (SEPolicy X A) where
  T σ g := S.M (S.H σ g)
  mono σ _ _ h := hM.1 (S.H_mono σ h)
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

/-- (4.28): Blackwell's condition with `e = 𝟙`, `λ = β`. -/
theorem blackwell [Nonempty A] (hM : IsCEOperator S.M) (σ : SEPolicy X A) (g : BM (X × A))
    (κ : ℝ) (hκ : 0 ≤ κ) :
    (S.adp hM).T σ (g + κ • BM.const 1) ≤ (S.adp hM).T σ g + (S.β * κ) • BM.const 1 := by
  change S.M (S.H σ (g + κ • BM.const 1)) ≤ _
  rw [S.H_shift, hM.2 _ _ (mul_nonneg S.β_nonneg hκ)]
  exact le_rfl

/-- The `g`-greedy policy (4.27): the least maximizer of `r(x, ·) + βg(x, ·)`. -/
noncomputable def greedySE [Fintype A] [Nonempty A] [LinearOrder A] (g : BM (X × A)) :
    SEPolicy X A :=
  ⟨argmaxSel fun x a => S.r.toFun (x, a) + S.β * g.toFun (x, a), measurable_argmaxSel fun _ =>
    (S.r.measurable'.comp (measurable_id.prodMk measurable_const)).add
      (measurable_const.mul (g.measurable'.comp (measurable_id.prodMk measurable_const)))⟩

/-- `H_τ g ≤ H_σ g` for the greedy `σ`, with `H_σ g = Hg = max_a [r + βg]`. -/
theorem H_le_greedy [Fintype A] [Nonempty A] [LinearOrder A] (g : BM (X × A))
    (τ : SEPolicy X A) : S.H τ g ≤ S.H (S.greedySE g) g :=
  fun x => argmaxSel_max (fun x a => S.r.toFun (x, a) + S.β * g.toFun (x, a)) x (τ.1 x)

/-- (4.27): the greedy policy is `g`-greedy for `(bG, 𝕋̂_SE)`. -/
theorem greedySE_isGreedy [Fintype A] [Nonempty A] [LinearOrder A] (hM : IsCEOperator S.M)
    (g : BM (X × A)) : (S.adp hM).IsGreedy g (S.greedySE g) := fun τ => hM.1 (S.H_le_greedy g τ)

/-- **Exercise 4.2.4** (p. 142): a measurable `g`-greedy policy exists, so `(bG, 𝕋̂_SE)` is
regular. -/
theorem adp_regular [Finite A] [Nonempty A] (hM : IsCEOperator S.M) : (S.adp hM).Regular :=
  fun g => by
    have := Fintype.ofFinite A
    let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
    exact ⟨_, S.greedySE_isGreedy hM g⟩

/-- (4.26): the Bellman operator is `T̂g = MHg`, `(Hg)(x') = max_{a'} [r(x', a') + βg(x', a')]`. -/
theorem adp_bellman [Fintype A] [Nonempty A] [LinearOrder A] (hM : IsCEOperator S.M)
    (g : BM (X × A)) : (S.adp hM).bellman g = S.M (S.H (S.greedySE g) g) :=
  le_antisymm (S.greedySE_isGreedy hM g _) ((S.adp hM).isGreedy_greedy (S.adp_regular hM g) _)

/-- **Proposition 4.2.6** (p. 145): for every certainty equivalent operator `M`, the fundamental
optimality properties hold for `(bG, 𝕋̂_SE)`, VFI converges (geometrically), and OPI and HPI
converge. -/
theorem proposition_4_2_6 [Nonempty X] [Finite A] [Nonempty A] (hM : IsCEOperator S.M) :
    ∃ hw : (S.adp hM).WellPosed, (S.adp hM).FundamentalOptimality hw ∧ ∃ gstar,
      (S.adp hM).VFIGeometric univ gstar ∧ (S.adp hM).VFIConverges gstar ∧
        ∀ g, (S.adp hM).IsSelector g → (S.adp hM).OPIConverges g gstar ∧
          (S.adp hM).HPIConverges hw g gstar := by
  have hsr : (S.adp hM).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => S.adp_regular hM v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, gstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one (S.adp hM) S.β_nonneg S.β_lt_one (S.blackwell hM) hsr
    univ_nonempty
  have hT : ∀ σ v w, dist ((S.adp hM).T σ v) ((S.adp hM).T σ w) ≤ S.β * dist v w :=
    fun σ v w => by
      rw [dist_eq_norm, dist_eq_norm]
      exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one ((S.adp hM).mono σ)
        S.β_nonneg (S.blackwell hM σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg S.β_lt_one hT
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 (S.adp_regular hM) hgs
    (((S.adp hM).solvesBellman_iff hwG).1 hwb)
  obtain rfl : gstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, gstar, hgeo, hvfi, hconv (S.adp_regular hM)⟩

end PostAction

/-! ### Expected utility: §4.2.3.1 -/

/-- The expectation operator `(Mv)(x, a) = ∫ v(x')P(x, a, dx')` of a stochastic kernel from
`G = X × A` to `X`. -/
noncomputable def expectOp (P : Kernel (X × A) X) [IsMarkovKernel P] (v : BM X) : BM (X × A) :=
  ⟨fun p => ∫ x', v.toFun x' ∂(P p),
    (v.measurable'.stronglyMeasurable.integral_kernel (κ := P)).measurable,
    ⟨‖v‖, fun p => by
      have := norm_integral_le_of_norm_le_const (μ := P p) (f := v.toFun) (C := ‖v‖)
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)
      simpa using this⟩⟩

theorem integrable_BM (μ : Measure X) [IsProbabilityMeasure μ] (v : BM X) : Integrable v.toFun μ :=
  Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)

/-- The expectation operator is a certainty equivalent operator. -/
theorem isCEOperator_expectOp (P : Kernel (X × A) X) [IsMarkovKernel P] :
    IsCEOperator (A := A) (expectOp P) := by
  refine ⟨fun v w h p => integral_mono (integrable_BM _ v) (integrable_BM _ w) h,
    fun v κ _ => BM.ext fun p => ?_⟩
  change ∫ x', (v + κ • BM.const 1).toFun x' ∂(P p) = ∫ x', v.toFun x' ∂(P p) + κ * 1
  simp only [BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
  rw [integral_add (integrable_BM _ v) (integrable_const κ), integral_const, probReal_univ,
    one_smul]

/-- (4.21): the expected-utility post-action model. -/
noncomputable def postActionEU (r : BM (X × A)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] : PostAction X A :=
  ⟨r, β, hβ0, hβ1, expectOp P⟩

/-- **Exercise 4.2.5** (p. 142): each `T̂_σ` is a contraction of modulus `β` on `bG`. -/
theorem exercise_4_2_5 [Nonempty X] [Nonempty A] (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (σ : SEPolicy X A) (g g' : BM (X × A)) :
    ‖((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).T σ g -
      ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).T σ g'‖ ≤ β * ‖g - g'‖ :=
  BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one
    (((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).mono σ) hβ0
    ((postActionEU r β hβ0 hβ1 P).blackwell (isCEOperator_expectOp P) σ) g g'

/-- (4.20): the Bellman operator of the expected-utility model is
`(T̂g)(x, a) = ∫ max_{a'} [r(x', a') + βg(x', a')] P(x, a, dx')`. -/
theorem bellman_EU [Fintype A] [Nonempty A] (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (g : BM (X × A)) (p : X × A) :
    (((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).bellman g).toFun p =
      ∫ x', (Finset.univ.sup' Finset.univ_nonempty fun a' =>
        r.toFun (x', a') + β * g.toFun (x', a')) ∂(P p) := by
  let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
  rw [(postActionEU r β hβ0 hβ1 P).adp_bellman (isCEOperator_expectOp P)]
  refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
  refine le_antisymm (Finset.le_sup' (fun a' => r.toFun (x', a') + β * g.toFun (x', a'))
    (Finset.mem_univ _)) (Finset.sup'_le _ _ fun a' _ => ?_)
  exact argmaxSel_max (fun x a => r.toFun (x, a) + β * g.toFun (x, a)) x' a'

/-- **Proposition 4.2.4** (p. 143): for the structural estimation ADP `(bG, 𝕋̂_SE)` the
fundamental optimality properties hold, and VFI, OPI and HPI all converge. -/
theorem proposition_4_2_4 [Nonempty X] [Finite A] [Nonempty A] (r : BM (X × A)) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X) [IsMarkovKernel P] :
    ∃ hw : ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).WellPosed,
      ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).FundamentalOptimality hw ∧
        ∃ gstar, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).VFIGeometric
          univ gstar ∧
          ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).VFIConverges gstar ∧
          ∀ g, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsSelector g →
            ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).OPIConverges g gstar ∧
            ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).HPIConverges hw g
              gstar :=
  (postActionEU r β hβ0 hβ1 P).proposition_4_2_6 (isCEOperator_expectOp P)

/-! ### The risk-sensitive case: §4.2.3.4 -/

/-- The risk-sensitive certainty equivalent `(Mf)(x, a) = −γ⁻¹ ln ∫ exp(−γf(x')) P(x, a, dx')`. -/
noncomputable def riskSensitive (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ} (hγ : γ ≠ 0)
    (f : BM X) : BM (X × A) :=
  ⟨fun p => -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)),
    measurable_const.mul (Real.measurable_log.comp
      (((measurable_const.mul f.measurable').exp).stronglyMeasurable.integral_kernel
        (κ := P)).measurable),
    ⟨‖f‖, fun p => by
      have hb : ∀ x', Real.exp (-|γ| * ‖f‖) ≤ Real.exp (-γ * f.toFun x') ∧
          Real.exp (-γ * f.toFun x') ≤ Real.exp (|γ| * ‖f‖) := fun x' => by
        have h1 := BM.abs_le_norm f x'
        have h2 : |γ * f.toFun x'| ≤ |γ| * ‖f‖ := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        rw [abs_le] at h2
        constructor <;> (apply Real.exp_le_exp.2; linarith)
      have hint : Integrable (fun x' => Real.exp (-γ * f.toFun x')) (P p) :=
        Integrable.of_bound ((measurable_const.mul f.measurable').exp.aestronglyMeasurable)
          (Real.exp (|γ| * ‖f‖)) (Eventually.of_forall fun x' => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x').2)
      have hlo : Real.exp (-|γ| * ‖f‖) ≤ ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) := by
        have := integral_mono (integrable_const (Real.exp (-|γ| * ‖f‖))) hint fun x' => (hb x').1
        simpa using this
      have hhi : ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) ≤ Real.exp (|γ| * ‖f‖) := by
        have := integral_mono hint (integrable_const (Real.exp (|γ| * ‖f‖))) fun x' => (hb x').2
        simpa using this
      have hpos := (Real.exp_pos _).trans_le hlo
      have hlog : |Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p))| ≤ |γ| * ‖f‖ := by
        rw [abs_le]
        constructor
        · have := Real.log_le_log (Real.exp_pos _) hlo
          rw [Real.log_exp] at this
          linarith
        · have := Real.log_le_log hpos hhi
          rwa [Real.log_exp] at this
      rw [abs_mul, abs_neg, abs_inv]
      have hγ' : 0 < |γ| := abs_pos.2 hγ
      rw [inv_mul_le_iff₀ hγ']
      exact hlog⟩⟩

/-- §4.2.3.4: the risk-sensitive operator is a certainty equivalent operator, for any `γ ≠ 0`. -/
theorem isCEOperator_riskSensitive (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ}
    (hγ : γ ≠ 0) : IsCEOperator (A := A) (riskSensitive P hγ) := by
  have hint : ∀ (f : BM X) p, Integrable (fun x' => Real.exp (-γ * f.toFun x')) (P p) :=
    fun f p => Integrable.of_bound ((measurable_const.mul f.measurable').exp.aestronglyMeasurable)
      (Real.exp (|γ| * ‖f‖)) (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have := (abs_le.1 ((abs_mul γ (f.toFun x')).trans_le
          (mul_le_mul_of_nonneg_left (BM.abs_le_norm f x') (abs_nonneg γ)))).1
        linarith)
  have hpos : ∀ (f : BM X) p, 0 < ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) := fun f p =>
    integral_exp_pos (hint f p)
  refine ⟨fun f g hfg p => ?_, fun f κ _ => BM.ext fun p => ?_⟩
  · change -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)) ≤
      -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * g.toFun x') ∂(P p))
    rcases lt_or_gt_of_ne hγ with hneg | hpos'
    · have hle : ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) ≤
          ∫ x', Real.exp (-γ * g.toFun x') ∂(P p) :=
        integral_mono (hint f p) (hint g p) fun x' => Real.exp_le_exp.2 (by nlinarith [hfg x'])
      have := Real.log_le_log (hpos f p) hle
      have hc : 0 < -γ⁻¹ := neg_pos.2 (inv_lt_zero.2 hneg)
      nlinarith
    · have hle : ∫ x', Real.exp (-γ * g.toFun x') ∂(P p) ≤
          ∫ x', Real.exp (-γ * f.toFun x') ∂(P p) :=
        integral_mono (hint g p) (hint f p) fun x' => Real.exp_le_exp.2 (by nlinarith [hfg x'])
      have := Real.log_le_log (hpos g p) hle
      have hc : -γ⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hpos')
      nlinarith
  · change -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * (f + κ • BM.const 1).toFun x') ∂(P p)) =
      -γ⁻¹ * Real.log (∫ x', Real.exp (-γ * f.toFun x') ∂(P p)) + κ * 1
    have hshift : (fun x' => Real.exp (-γ * (f + κ • BM.const 1).toFun x')) =
        fun x' => Real.exp (-γ * κ) * Real.exp (-γ * f.toFun x') := by
      funext x'
      simp only [BM.add_apply, BM.smul_apply, BM.const_apply, mul_one]
      rw [← Real.exp_add]
      ring_nf
    rw [hshift, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (hpos f p).ne',
      Real.log_exp]
    field_simp
    ring

/-- §4.2.3.4 (p. 146): with the risk-sensitive certainty equivalent, Proposition 4.2.6 applies: a
unique solution `g*` of the functional equation exists in `bG`, policies are optimal iff they
choose `σ(x) ∈ argmax_a [r(x, a) + βg*(x, a)]`, and VFI, OPI and HPI converge. -/
theorem riskSensitive_optimality [Nonempty X] [Finite A] [Nonempty A] (r : BM (X × A)) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X) [IsMarkovKernel P] {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ hw : ((⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).adp
      (isCEOperator_riskSensitive P hγ)).WellPosed,
      ((⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).adp
        (isCEOperator_riskSensitive P hγ)).FundamentalOptimality hw := by
  obtain ⟨hw, hFO, -⟩ := (⟨r, β, hβ0, hβ1, riskSensitive P hγ⟩ : PostAction X A).proposition_4_2_6
    (isCEOperator_riskSensitive P hγ)
  exact ⟨hw, hFO⟩

end SargentStachurski.ADPTransformations
