/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearDecisionProcesses.ExogenousLDP
import LinearDecisionProcesses.Feller
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Natural resource management

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.2.1 (pp. 199–203).

The Bellman equation is
`v(y, z) = max_{0 ≤ e ≤ y} {π(e) + β(z) ∫ ∑_{z'} v(f(y − e)ξ, z')Q(z, z')φ(dξ)}`: stock `y`, usage
`e`, profit `π` (bounded, continuous), growth `f` (continuous), multiplicative shock `ξ ∼ φ`, and a
finite exogenous state `z` (stochastic matrix `Q`) driving the discount factor `β(z) ≥ 0`.

* `finiteKernel Q`: the stochastic kernel of a stochastic matrix,
  `∫ g dQ(z) = ∑_{z'} g(z')Q(z, z')`.
* `ResourceModel.ldp`: the model as an LDP on `X = ℝ × Z` with `Γ(y, z) = [0, max(y, 0)]` (the
  stock is nonnegative on every path), `r = π(e)`, endogenous kernel
  `R(y, z, e) = law of f(y − e)ξ`,
  and `P = R ⊗ Q(z, ·)`.
* **Proposition 6.2.1**: if `ρ(K_Q) < 1`, the fundamental optimality properties hold, `v* ∈ bcX`,
  and
  VFI converges geometrically on `bcX` (Proposition 6.1.6; Exercise A.3.1 for `Γ`, dominated
  convergence for Assumption 6.1.2).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### The kernel of a stochastic matrix -/

/-- The distribution `Q(z, ·)` as a probability mass function. -/
noncomputable def rowPMF {Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (z : Z) : PMF Z :=
  PMF.ofFintype (fun z' => ENNReal.ofReal (Q z z')) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => hQ0 z z', hQ1 z, ENNReal.ofReal_one])

/-- The stochastic kernel of the stochastic matrix `Q`. -/
noncomputable def finiteKernel {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) : Kernel Z Z :=
  Kernel.ofFunOfCountable fun z => (rowPMF Q hQ0 hQ1 z).toMeasure

theorem finiteKernel_isMarkov {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) : IsMarkovKernel (finiteKernel Q hQ0 hQ1) :=
  ⟨fun z => by
    change IsProbabilityMeasure (rowPMF Q hQ0 hQ1 z).toMeasure
    infer_instance⟩

/-- `∫ g dQ(z) = ∑_{z'} g(z')Q(z, z')`. -/
theorem integral_finiteKernel {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (Q : Z → Z → ℝ) (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (g : Z → ℝ) (z : Z) :
    ∫ z', g z' ∂(finiteKernel Q hQ0 hQ1 z) = ∑ z', g z' * Q z z' := by
  change ∫ z', g z' ∂(rowPMF Q hQ0 hQ1 z).toMeasure = _
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun z' _ => ?_
  simp only [rowPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hQ0 z z'), smul_eq_mul]
  ring

/-! ### The model -/

/-- The natural resource management model of §6.2.1. -/
structure ResourceModel (Z : Type*) [Fintype Z] where
  /-- the profit function -/
  π : ℝ → ℝ
  π_cont : Continuous π
  π_bdd : ∃ C, ∀ e, |π e| ≤ C
  /-- the growth function -/
  f : ℝ → ℝ
  f_cont : Continuous f
  /-- the distribution of the multiplicative shock -/
  φ : Measure ℝ
  [φ_prob : IsProbabilityMeasure φ]
  /-- the discount factor function -/
  βz : Z → ℝ
  βz_nonneg : ∀ z, 0 ≤ βz z
  /-- the exogenous stochastic matrix -/
  Q : Z → Z → ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1

namespace ResourceModel

attribute [local instance] ResourceModel.φ_prob

variable {Z : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  (M : ResourceModel Z)

omit [MeasurableSingletonClass Z] in
theorem measurable_next :
    Measurable (uncurry fun (p : (ℝ × Z) × ℝ) (ξ : ℝ) => M.f (p.1.1 - p.2) * ξ) :=
  ((M.f_cont.measurable.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
    (measurable_snd.comp measurable_fst))).mul measurable_snd)

/-- The endogenous kernel `R(y, z, e) = law of f(y − e)ξ`. -/
noncomputable def R : Kernel ((ℝ × Z) × ℝ) ℝ :=
  shockKernel (fun (p : (ℝ × Z) × ℝ) (ξ : ℝ) => M.f (p.1.1 - p.2) * ξ) M.measurable_next M.φ

/-- The exogenous kernel `Q(z, ·)`, read on state-action pairs. -/
noncomputable def Qk : Kernel ((ℝ × Z) × ℝ) Z :=
  (finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p => p.1.2)
    (measurable_snd.comp measurable_fst)

omit [MeasurableSingletonClass Z] in
theorem R_isMarkov : IsMarkovKernel M.R := shockKernel_isMarkov _ _ _

theorem Qk_isMarkov : IsMarkovKernel M.Qk := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  unfold Qk
  infer_instance

/-- The model as an LDP on `X = ℝ × Z`, `A = ℝ`. -/
noncomputable def ldp : LDP (ℝ × Z) ℝ :=
  have := M.R_isMarkov
  have := M.Qk_isMarkov
  { Γ := fun x => Icc 0 (max x.1 0)
    r := ⟨fun p => M.π p.2, M.π_cont.measurable.comp measurable_snd,
      ⟨M.π_bdd.choose, fun _ => M.π_bdd.choose_spec _⟩⟩
    β := ⟨fun p => M.βz p.1.2, (measurable_of_countable M.βz).comp
      (measurable_snd.comp measurable_fst),
      ⟨∑ z, |M.βz z|, fun p => Finset.single_le_sum (f := fun z => |M.βz z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1.2)⟩⟩
    β_nonneg := fun p => M.βz_nonneg p.1.2
    P := M.R ×ₖ M.Qk
    exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ }

/-- The integral identity for the kernel:
`∫ h dP(y, z, e) = ∫ ∑_{z'} h(y', z')Q(z, z') R(y, z, e, dy')`. -/
theorem integral_P (h : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    ∫ x', h.toFun x' ∂(M.ldp.P p) = ∫ y', ∑ z', h.toFun (y', z') * M.Q p.1.2 z' ∂(M.R p) := by
  have := M.R_isMarkov
  have := M.Qk_isMarkov
  change ∫ x', h.toFun x' ∂((M.R ×ₖ M.Qk) p) = _
  rw [Kernel.prod_apply, integral_prod _ (Integrable.of_bound h.measurable'.aestronglyMeasurable
    ‖h‖ (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h x))]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  change ∫ z', h.toFun (y', z') ∂(finiteKernel M.Q M.Q_nonneg M.Q_sum p.1.2) = _
  exact integral_finiteKernel _ _ _ _ _

/-- **Proposition 6.2.1** (p. 200): for the natural resource model, if `ρ(K_Q) < 1`, then the
fundamental optimality properties hold, the value function `v*` lies in `bcX`, and VFI converges
geometrically on `bcX`. -/
theorem proposition_6_2_1 [TopologicalSpace Z] [DiscreteTopology Z]
    (hρ : BanachLattice.specRad (Exo.K M.βz M.Q) < 1) :
    ∃ hw : M.ldp.adp.WellPosed, M.ldp.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ LDP.bc (ℝ × Z),
      M.ldp.adp.VFIGeometric (LDP.bc (ℝ × Z)) vstar := by
  have := M.R_isMarkov
  have hB : HasMaxSelections M.ldp.Γ := hasMaxSelections_Icc (X := ℝ × Z) (g := fun _ => 0)
    (h := fun x => max x.1 0) continuous_const (continuous_fst.max continuous_const)
    fun x => le_max_right _ _
  refine M.ldp.proposition_6_1_6 hB (M.π_cont.comp continuous_snd).continuousOn M.βz_nonneg
    M.Q_nonneg (fun _ => rfl) M.R M.integral_P (fun z g hg => ?_) hρ
  -- Assumption 6.1.2: dominated convergence
  have heq : ∀ q : ℝ × ℝ, ∫ y', g.toFun y' ∂(M.R ((q.1, z), q.2)) =
      ∫ ξ, g.toFun (M.f (q.1 - q.2) * ξ) ∂M.φ := fun q =>
    integral_shockKernel _ _ _ g.measurable' _
  simp_rw [heq]
  refine (continuous_of_dominated (bound := fun _ => ‖g‖)
    (fun _ => (g.measurable'.comp ((measurable_const.mul measurable_id))).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm g _)
    (integrable_const _) (Eventually.of_forall fun ξ => ?_)).continuousOn
  exact hg.comp ((M.f_cont.comp (continuous_fst.sub continuous_snd)).mul continuous_const)

end ResourceModel

end SargentStachurski.LinearDecisionProcesses
