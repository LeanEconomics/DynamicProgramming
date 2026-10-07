/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearDecisionProcesses.NaturalResource
import LinearDecisionProcesses.GeneralMDP
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Stochastic rates of return

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.2.2 (pp. 203–206).

Wealth `w ≥ 0`, a finite exogenous state `z` (stochastic matrix `Q`), consumption `c ∈ [0, w]`,
bounded continuous utility `u`, a constant `β ∈ [0, 1)`, and
`∫ v(x')P(x, c, dx') = ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z'] φ(ds') Q(z, z')`: the return
`R(z')` and labour income `y(z', s')` depend on the next exogenous state and an iid shock `s' ∼ φ`.

* `mixKernel κ F φ`: draw `z' ∼ κ(d)`, then `s' ∼ φ`, and move to `F(d, z', s')`, with
  `∫ g dP(d) = ∫ ∫ g(F(d, z', s'))φ(ds')κ(d, dz')`.
* `section_6_2_2`: Proposition 6.1.7 applies (Exercise A.3.1 for `Γ`, dominated convergence for the
  weak Feller property), so the fundamental optimality properties hold, `v* ∈ bcX`, VFI converges
  geometrically on `bcX`, and the Bellman operator is
  `(Tv)(w, z) = max_{0 ≤ c ≤ w} {u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')}`
  for
  `v ∈ bcX`.
* **Exercise 6.2.1**: with survival probabilities `q(t) ∈ [0, 1]` and age `t` in the state,
  `K = βq(t)P` and Proposition 6.1.3 applies with the discount operator `Dh = β (sup h) 𝟙`.

Wealth is a real state with `Γ(w, z) = [0, max(w, 0)]`; it stays nonnegative when `R, y ≥ 0`, but
nothing in the optimality results needs that.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Mixtures of shock kernels -/

/-- Draw `z' ∼ κ(d)`, then `s' ∼ φ`, and move to `F(d, z', s')`. -/
noncomputable def mixKernel {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ] :
    Kernel D E :=
  have := shockKernel_isMarkov F hF φ
  Kernel.snd (κ ⊗ₖ shockKernel F hF φ)

theorem mixKernel_isMarkov {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ] :
    IsMarkovKernel (mixKernel κ F hF φ) := by
  have := shockKernel_isMarkov F hF φ
  unfold mixKernel
  infer_instance

/-- `∫ g dP(d) = ∫ ∫ g(F(d, z', s'))φ(ds')κ(d, dz')` for bounded measurable `g`. -/
theorem integral_mixKernel {D Z S E : Type*} [MeasurableSpace D] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace E] (κ : Kernel D Z) [IsMarkovKernel κ]
    (F : D × Z → S → E) (hF : Measurable (uncurry F)) (φ : Measure S) [IsProbabilityMeasure φ]
    (g : BM E) (d : D) :
    ∫ x, g.toFun x ∂(mixKernel κ F hF φ d) = ∫ z', ∫ s, g.toFun (F (d, z') s) ∂φ ∂(κ d) := by
  have := shockKernel_isMarkov F hF φ
  change ∫ x, g.toFun x ∂(Kernel.snd (κ ⊗ₖ shockKernel F hF φ) d) = _
  have hcp := ProbabilityTheory.integral_compProd (κ := κ) (η := shockKernel F hF φ) (a := d)
    (f := fun x : Z × E => g.toFun x.2)
    (Integrable.of_bound (g.measurable'.comp measurable_snd).aestronglyMeasurable ‖g‖
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm g _))
  rw [Kernel.snd_apply, integral_map measurable_snd.aemeasurable
    g.measurable'.aestronglyMeasurable, hcp]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  exact integral_shockKernel F hF φ g.measurable' (d, z')

/-! ### The model -/

/-- The optimal savings model with stochastic returns of §6.2.2. -/
structure ReturnsModel (Z S : Type*) [Fintype Z] [MeasurableSpace S] where
  /-- the utility function -/
  u : ℝ → ℝ
  u_cont : Continuous u
  u_bdd : ∃ C, ∀ c, |u c| ≤ C
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the exogenous stochastic matrix -/
  Q : Z → Z → ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1
  /-- the gross return `R(z')` -/
  Rz : Z → ℝ
  /-- labour income `y(z', s')` -/
  yf : Z → S → ℝ
  yf_meas : ∀ z, Measurable (yf z)
  /-- the distribution of the iid income shock -/
  φ : Measure S
  [φ_prob : IsProbabilityMeasure φ]

namespace ReturnsModel

attribute [local instance] ReturnsModel.φ_prob

variable {Z S : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [MeasurableSpace S] (M : ReturnsModel Z S)

omit [Fintype Z] [MeasurableSingletonClass Z] in
theorem measurable_zproj : Measurable fun p : (ℝ × Z) × ℝ => p.1.2 :=
  measurable_snd.comp measurable_fst

omit [Fintype Z] [MeasurableSingletonClass Z] in
theorem measurable_zprojT : Measurable fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1 :=
  (measurable_fst.comp measurable_snd).comp measurable_fst

/-- The reward `u(c)` as an element of `bG`. -/
noncomputable def reward {X : Type*} [MeasurableSpace X] : BM (X × ℝ) :=
  ⟨fun p => M.u p.2, M.u_cont.measurable.comp measurable_snd,
    ⟨M.u_bdd.choose, fun _ => M.u_bdd.choose_spec _⟩⟩

omit [MeasurableSingletonClass Z] in
theorem measurable_income {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass Z] :
    Measurable fun p : (T × Z) × S => M.Rz p.1.2 * 0 + M.yf p.1.2 p.2 := by
  simp only [mul_zero, zero_add]
  exact (measurable_from_prod_countable_right (f := fun zs : Z × S => M.yf zs.1 zs.2)
    fun z => M.yf_meas z).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Next period's state `(R(z')(w − c) + y(z', s'), z')`. -/
def next (q : ((ℝ × Z) × ℝ) × Z) (s : S) : ℝ × Z :=
  (M.Rz q.2 * (q.1.1.1 - q.1.2) + M.yf q.2 s, q.2)

theorem measurable_next : Measurable (uncurry M.next) := by
  have hy : Measurable fun p : (((ℝ × Z) × ℝ) × Z) × S => M.yf p.1.2 p.2 := by
    have := M.measurable_income (T := (ℝ × Z) × ℝ)
    simpa using this
  refine Measurable.prodMk (Measurable.add (Measurable.mul
    ((measurable_of_countable M.Rz).comp (measurable_snd.comp measurable_fst))
    (((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
      (measurable_snd.comp (measurable_fst.comp measurable_fst))))) hy)
    (measurable_snd.comp measurable_fst)

theorem finiteKernel_comap_isMarkov :
    IsMarkovKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × Z) × ℝ => p.1.2)
      measurable_zproj) := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  infer_instance

/-- The transition kernel `P` of §6.2.2. -/
noncomputable def P : Kernel ((ℝ × Z) × ℝ) (ℝ × Z) :=
  have := M.finiteKernel_comap_isMarkov
  mixKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × Z) × ℝ => p.1.2)
    measurable_zproj) M.next M.measurable_next M.φ

theorem P_isMarkov : IsMarkovKernel M.P := by
  have := M.finiteKernel_comap_isMarkov
  exact mixKernel_isMarkov _ _ _ _

/-- `∫ v dP(w, z, c) = ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds') Q(z, z')`. -/
theorem integral_P (v : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    ∫ x, v.toFun x ∂(M.P p) = ∑ z', (∫ s, v.toFun (M.next (p, z') s) ∂M.φ) * M.Q p.1.2 z' := by
  have := M.finiteKernel_comap_isMarkov
  change ∫ x, v.toFun x ∂(mixKernel _ M.next M.measurable_next M.φ p) = _
  rw [integral_mixKernel]
  exact integral_finiteKernel M.Q M.Q_nonneg M.Q_sum _ p.1.2

/-- The model as an MDP on `X = ℝ × Z`, `A = ℝ`, `Γ(w, z) = [0, max(w, 0)]`. -/
noncomputable def ldp : LDP (ℝ × Z) ℝ :=
  have := M.P_isMarkov
  ofMDP (fun x => Icc 0 (max x.1 0)) M.reward M.β_nonneg M.P
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- The objective `u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')`. -/
theorem obj_apply (v : BM (ℝ × Z)) (p : (ℝ × Z) × ℝ) :
    M.ldp.obj v p =
      M.u p.2 + M.β * ∑ z', (∫ s, v.toFun (M.next (p, z') s) ∂M.φ) * M.Q p.1.2 z' := by
  rw [show M.ldp.obj v p = M.u p.2 + M.β * ∫ x, v.toFun x ∂(M.P p) from rfl, M.integral_P]

/-- For continuous `v`, the expected continuation `(w, c) ↦ ∫ v dP(w, z, c)` is continuous on `G`
(dominated convergence, slice by slice). -/
theorem weakFeller [TopologicalSpace Z] [DiscreteTopology Z] (v : BM (ℝ × Z))
    (hv : Continuous v.toFun) :
    ContinuousOn (fun p => ∫ x, v.toFun x ∂(M.P p)) {p | p.2 ∈ Icc 0 (max p.1.1 0)} := by
  simp_rw [M.integral_P]
  refine continuousOn_of_slices fun z => ?_
  have hcont : ∀ z' : Z, Continuous fun q : ℝ × ℝ =>
      ∫ s, v.toFun (M.Rz z' * (q.1 - q.2) + M.yf z' s, z') ∂M.φ := fun z' =>
    continuous_of_dominated (bound := fun _ => ‖v‖)
      (fun _ => (v.measurable'.comp ((measurable_const.add (M.yf_meas z')).prodMk
        measurable_const)).aestronglyMeasurable)
      (fun _ => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
      (integrable_const _) (Eventually.of_forall fun s => hv.comp
        (((continuous_const.mul (continuous_fst.sub continuous_snd)).add
          continuous_const).prodMk continuous_const))
  change ContinuousOn (fun q : ℝ × ℝ =>
    ∑ z', (∫ s, v.toFun (M.Rz z' * (q.1 - q.2) + M.yf z' s, z') ∂M.φ) * M.Q z z') _
  exact (continuous_finsetSum _ fun z' _ => (hcont z').mul continuous_const).continuousOn

/-- §6.2.2 (p. 205): Proposition 6.1.7 applies to the savings model with stochastic returns: the
fundamental optimality properties hold, `v* ∈ bcX`, VFI converges geometrically on `bcX`, and for
`v ∈ bcX` the Bellman operator is
`(Tv)(w, z) = max_{0 ≤ c ≤ w} {u(c) + β ∑_{z'} ∫ v[R(z')(w − c) + y(z', s'), z']φ(ds')Q(z, z')}`. -/
theorem section_6_2_2 [TopologicalSpace Z] [DiscreteTopology Z] :
    ∃ hw : M.ldp.adp.WellPosed, M.ldp.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × Z), M.ldp.adp.VFIGeometric (LDP.bc (ℝ × Z)) vstar ∧
        ∀ v ∈ LDP.bc (ℝ × Z), ∀ x, IsGreatest ((fun c => M.ldp.obj v (x, c)) '' Icc 0 (max x.1 0))
          ((M.ldp.adp.bellman v).toFun x) := by
  have := M.P_isMarkov
  have hB : HasMaxSelections fun x : ℝ × Z => Icc (0 : ℝ) (max x.1 0) :=
    hasMaxSelections_Icc (X := ℝ × Z) (g := fun _ => 0) (h := fun x => max x.1 0)
      continuous_const (continuous_fst.max continuous_const) fun x => le_max_right _ _
  have hr : ContinuousOn M.ldp.r.toFun M.ldp.G := (M.u_cont.comp continuous_snd).continuousOn
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := proposition_6_1_7 (fun x : ℝ × Z => Icc 0 (max x.1 0))
    M.reward M.β_nonneg M.β_lt_one M.P
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ hB hr M.weakFeller
  refine ⟨hw, hFO, vstar, hv, hgeo, fun v hv' x => ?_⟩
  exact (M.ldp.implications_bc hB hr (fun h hc => continuousOn_const.mul (M.weakFeller h hc))
    hv').2 x

/-! ### Exercise 6.2.1: mortality -/

/-- Next period's state with age: `(R(z')(w − c) + y(z', s'), z', t + 1)`. -/
def nextT (q : ((ℝ × (Z × ℕ)) × ℝ) × Z) (s : S) : ℝ × (Z × ℕ) :=
  (M.Rz q.2 * (q.1.1.1 - q.1.2) + M.yf q.2 s, (q.2, q.1.1.2.2 + 1))

theorem measurable_nextT : Measurable (uncurry M.nextT) := by
  have hy : Measurable fun p : (((ℝ × (Z × ℕ)) × ℝ) × Z) × S => M.yf p.1.2 p.2 := by
    have := M.measurable_income (T := (ℝ × (Z × ℕ)) × ℝ)
    simpa using this
  refine Measurable.prodMk (Measurable.add (Measurable.mul
    ((measurable_of_countable M.Rz).comp (measurable_snd.comp measurable_fst))
    (((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
      (measurable_snd.comp (measurable_fst.comp measurable_fst))))) hy)
    ((measurable_snd.comp measurable_fst).prodMk ((measurable_of_countable (· + 1)).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst))))))

theorem finiteKernel_comapT_isMarkov :
    IsMarkovKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap
      (fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1) measurable_zprojT) := by
  have := finiteKernel_isMarkov M.Q M.Q_nonneg M.Q_sum
  infer_instance

/-- The transition kernel with age. -/
noncomputable def PT : Kernel ((ℝ × (Z × ℕ)) × ℝ) (ℝ × (Z × ℕ)) :=
  have := M.finiteKernel_comapT_isMarkov
  mixKernel ((finiteKernel M.Q M.Q_nonneg M.Q_sum).comap (fun p : (ℝ × (Z × ℕ)) × ℝ => p.1.2.1)
    measurable_zprojT) M.nextT M.measurable_nextT M.φ

theorem PT_isMarkov : IsMarkovKernel M.PT := by
  have := M.finiteKernel_comapT_isMarkov
  exact mixKernel_isMarkov _ _ _ _

theorem integral_PT (v : BM (ℝ × (Z × ℕ))) (p : (ℝ × (Z × ℕ)) × ℝ) :
    ∫ x, v.toFun x ∂(M.PT p) = ∑ z', (∫ s, v.toFun (M.nextT (p, z') s) ∂M.φ) * M.Q p.1.2.1 z' := by
  have := M.finiteKernel_comapT_isMarkov
  change ∫ x, v.toFun x ∂(mixKernel _ M.nextT M.measurable_nextT M.φ p) = _
  rw [integral_mixKernel]
  exact integral_finiteKernel M.Q M.Q_nonneg M.Q_sum _ p.1.2.1

/-- The model with survival probabilities `q(t) ∈ [0, 1]` (Exercise 6.2.1): an LDP on
`X = ℝ × Z × ℤ₊` with `K(x, c, dx') = βq(t)P(x, c, dx')`. -/
noncomputable def ldpT (q : ℕ → ℝ) (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1) :
    LDP (ℝ × (Z × ℕ)) ℝ :=
  have := M.PT_isMarkov
  { Γ := fun x => Icc 0 (max x.1 0)
    r := M.reward
    β := ⟨fun p => M.β * q p.1.2.2, measurable_const.mul ((measurable_of_countable q).comp
        (measurable_snd.comp (measurable_snd.comp measurable_fst))),
      ⟨M.β, fun p => by
        rw [abs_of_nonneg (mul_nonneg M.β_nonneg (hq0 _))]
        exact mul_le_of_le_one_right M.β_nonneg (hq1 _)⟩⟩
    β_nonneg := fun p => mul_nonneg M.β_nonneg (hq0 _)
    P := M.PT
    exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ }

/-- **Exercise 6.2.1** (p. 205): with survival probabilities `q(t) ∈ [0, 1]`, Proposition 6.1.3
applies (with `Dh = β (sup h) 𝟙`, since `q ≤ 1`): the fundamental optimality properties hold,
`v* ∈ bcX` and VFI converges geometrically on `bcX`. -/
theorem exercise_6_2_1 [TopologicalSpace Z] [DiscreteTopology Z] (q : ℕ → ℝ)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1) :
    ∃ hw : (M.ldpT q hq0 hq1).adp.WellPosed, (M.ldpT q hq0 hq1).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × (Z × ℕ)),
        (M.ldpT q hq0 hq1).adp.VFIGeometric (LDP.bc (ℝ × (Z × ℕ))) vstar := by
  have := M.PT_isMarkov
  have hB : HasMaxSelections fun x : ℝ × (Z × ℕ) => Icc (0 : ℝ) (max x.1 0) :=
    hasMaxSelections_Icc (X := ℝ × (Z × ℕ)) (g := fun _ => 0) (h := fun x => max x.1 0)
      continuous_const (continuous_fst.max continuous_const) fun x => le_max_right _ _
  have hr : ContinuousOn (M.ldpT q hq0 hq1).r.toFun (M.ldpT q hq0 hq1).G :=
    (M.u_cont.comp continuous_snd).continuousOn
  have hK : (M.ldpT q hq0 hq1).IsWeakFeller := by
    intro h hc
    change ContinuousOn (fun p => M.β * q p.1.2.2 * ∫ x, h.toFun x ∂(M.PT p)) _
    simp_rw [M.integral_PT]
    refine continuousOn_of_slices fun zt => ?_
    have hcont : ∀ z' : Z, Continuous fun c : ℝ × ℝ =>
        ∫ s, h.toFun (M.Rz z' * (c.1 - c.2) + M.yf z' s, (z', zt.2 + 1)) ∂M.φ := fun z' =>
      continuous_of_dominated (bound := fun _ => ‖h‖)
        (fun _ => (h.measurable'.comp ((measurable_const.add (M.yf_meas z')).prodMk
          measurable_const)).aestronglyMeasurable)
        (fun _ => Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)
        (integrable_const _) (Eventually.of_forall fun s => hc.comp
          (((continuous_const.mul (continuous_fst.sub continuous_snd)).add
            continuous_const).prodMk continuous_const))
    change ContinuousOn (fun c : ℝ × ℝ => M.β * q zt.2 * ∑ z',
      (∫ s, h.toFun (M.Rz z' * (c.1 - c.2) + M.yf z' s, (z', zt.2 + 1)) ∂M.φ) * M.Q zt.1 z') _
    exact (continuous_const.mul (continuous_finsetSum _ fun z' _ =>
      (hcont z').mul continuous_const)).continuousOn
  have hKD : ∀ σ h, 0 ≤ h → (M.ldpT q hq0 hq1).K σ h ≤ Dsup M.β h := fun σ h hh x => by
    rw [LDP.K_apply]
    change M.β * q (x, σ.1 x).1.2.2 * _ ≤ M.β * ⨆ y, h.toFun y
    have hb : BddAbove (range h.toFun) :=
      ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h y)⟩
    have h1 : 0 ≤ ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) := integral_nonneg hh
    have h2 : ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) ≤ ⨆ y, h.toFun y :=
      (integral_mono (Integrable.of_bound h.measurable'.aestronglyMeasurable ‖h‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h y))
        (integrable_const _) fun y => le_ciSup hb y).trans_eq (by simp)
    calc M.β * q (x, σ.1 x).1.2.2 * ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x))
        ≤ M.β * ∫ x', h.toFun x' ∂(M.PT (x, σ.1 x)) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right M.β_nonneg (hq1 _)) h1
      _ ≤ M.β * ⨆ y, h.toFun y := mul_le_mul_of_nonneg_left h2 M.β_nonneg
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := (M.ldpT q hq0 hq1).proposition_6_1_3 hB hr hK
    (Dsup_isDiscountOperator M.β_nonneg M.β_lt_one) hKD
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

end ReturnsModel

end SargentStachurski.LinearDecisionProcesses
