/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.JobSearchL1
import AdditionalApplications.DuTheorem
import AdditionalApplications.PowerMean
import AdditionalApplications.BMOperators
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Job search with nonlinear discounting and nonlinear expectations

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.1–§8.2.2 (pp. 261–264).

Offers are `P`-Markov on a state space `X`, with the offer `w(x) ∈ [w₁, w₂]`, `0 < c < w₁`. The
book takes `X = W = [w₁, w₂]` with `w(x) = x`.

* §8.2.1, nonlinear discounting: the continuation value is `c + ∫ β[v(w')]P(w, dw')` with a
  discount function `β`. The book's `β(x) = b(1 − e^{−λx})` (`bexp`) is continuous, increasing,
  concave on `ℝ₊`, with `β(0) = 0` and `β < b`; these properties are all that is used.
  * **Exercises 8.2.1–8.2.2**: `(Hg)(w) = w + β(g(w))` is an order preserving self-map of
    `V = [0, v̄]`, `v̄ = (c + w₂)/(1 − b)`, satisfies Du's conditions, and has a unique fixed point
    `e ∈ V`, the lifetime value of a constant wage stream.
  * **Exercises 8.2.3–8.2.4**: each `T_σ` maps `V` into itself, is concave and satisfies Du's
    conditions; with the greedy policy, Theorem 4.1.11 applies: the fundamental optimality
    properties hold and VFI, OPI and HPI converge.
* §8.2.2, nonlinear expectations: `T_σ v = σe + (1 − σ)(c + βRv)` with the Kreps–Porteus operator
  `(Rv)(w) = (∫ v^{1−γ} dP(w, ·))^{1/(1−γ)}`, `γ ≠ 1`, on `V = [c, v̄]`, `v̄ = (c + w₂)/(1 − β)`.
  * **Exercise 8.2.5**: `R` is order preserving and fixes constants; it is concave for `γ ≥ 0` and
    convex for `γ ≤ 0` (power means, `PowerMean`).
  * The `ε` bounds of p. 264 and Theorem 4.1.11: the fundamental optimality properties hold and
    VFI, OPI and HPI converge, for every `γ ≠ 1`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X : Type*} [MeasurableSpace X]

/-- A continuous function of a bounded function is bounded. -/
theorem bdd_comp {f : ℝ → ℝ} (hf : Continuous f) (g : BM X) : ∃ C, ∀ x, |f (g.toFun x)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -‖g‖) (b := ‖g‖)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun x => by
    have := hC (g.toFun x) (abs_le.1 (BM.abs_le_norm g x))
    rwa [Real.norm_eq_abs] at this⟩

/-- The book's discount function `β(x) = b(1 − e^{−λx})`. -/
noncomputable def bexp (b lam : ℝ) (x : ℝ) : ℝ := b * (1 - Real.exp (-lam * x))

/-- `β(x) = b(1 − e^{−λx})` is continuous, increasing, concave, `β(0) = 0` and `β < b`. -/
theorem bexp_properties {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    Continuous (bexp b lam) ∧ Monotone (bexp b lam) ∧ ConcaveOn ℝ (Ici 0) (bexp b lam) ∧
      bexp b lam 0 = 0 ∧ ∀ x, bexp b lam x < b := by
  refine ⟨continuous_const.mul (continuous_const.sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))),
    fun x y h => mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.exp_le_exp.2
      (by nlinarith)) 1) hb.le, ⟨convex_Ici 0, fun x _ y _ a c ha hc hac => ?_⟩, by simp [bexp],
    fun x => by
      unfold bexp
      have := Real.exp_pos (-lam * x)
      nlinarith⟩
  have hconv := convexOn_exp.2 (mem_univ (-lam * x)) (mem_univ (-lam * y)) ha hc hac
  simp only [smul_eq_mul] at hconv ⊢
  have heq : a * (-lam * x) + c * (-lam * y) = -lam * (a * x + c * y) := by ring
  rw [heq] at hconv
  unfold bexp
  nlinarith

/-! ### Nonlinear discounting -/

/-- Job search with nonlinear discounting (§8.2.1). -/
structure NLDiscount (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  w₁ : ℝ
  w₂ : ℝ
  w₁_lt : w₁ < w₂
  wage_mem : ∀ x, wage x ∈ Icc w₁ w₂
  /-- unemployment compensation -/
  c : ℝ
  c_pos : 0 < c
  c_lt : c < w₁
  /-- the bound `b` of the discount function -/
  b : ℝ
  b_pos : 0 < b
  b_lt_one : b < 1
  w₂_ge : 1 - b ≤ w₂
  /-- the discount function -/
  βf : ℝ → ℝ
  continuous_βf : Continuous βf
  monotone_βf : Monotone βf
  concave_βf : ConcaveOn ℝ (Ici 0) βf
  βf_zero : βf 0 = 0
  βf_lt : ∀ x, βf x < b

namespace NLDiscount

attribute [local instance] NLDiscount.isMarkov

variable (M : NLDiscount X)

/-- `v̄ = (c + w₂)/(1 − b)`. -/
noncomputable def vbarR : ℝ := (M.c + M.w₂) / (1 - M.b)

/-- `v̄` as a constant function. -/
noncomputable def vbar : BM X := BM.const M.vbarR

theorem one_sub_b_pos : 0 < 1 - M.b := sub_pos.2 M.b_lt_one

theorem w₂_add_b_le : M.w₂ + M.b ≤ M.vbarR := by
  rw [vbarR, le_div_iff₀ M.one_sub_b_pos]
  have := M.w₂_ge
  have := M.c_pos
  have := M.b_pos
  nlinarith

theorem c_add_b_le : M.c + M.b ≤ M.vbarR := by
  have := M.w₂_add_b_le
  have := M.c_lt
  have := M.w₁_lt
  linarith

theorem w₁_pos : 0 < M.w₁ := M.c_pos.trans M.c_lt

theorem w₁_lt_vbar : M.w₁ < M.vbarR := by
  have := M.w₂_add_b_le
  have := M.w₁_lt
  have := M.b_pos
  linarith

theorem vbar_pos : 0 < M.vbarR := M.w₁_pos.trans M.w₁_lt_vbar

theorem zero_le_vbar : (0 : BM X) ≤ M.vbar := BM.le_def.2 fun _ => M.vbar_pos.le

/-- `(Hg)(w) = w + β(g(w))` (8.31). -/
noncomputable def H (g : BM X) : BM X :=
  ⟨fun x => M.wage x + M.βf (g.toFun x),
    M.measurable_wage.add (M.continuous_βf.measurable.comp g.measurable'), by
    obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf g
    refine ⟨|M.w₁| + |M.w₂| + C, fun x => ?_⟩
    have h1 := M.wage_mem x
    refine (abs_add_le _ _).trans (add_le_add ?_ (hC x))
    rw [abs_le]
    constructor <;> linarith [neg_abs_le M.w₁, le_abs_self M.w₂, abs_nonneg M.w₁,
      abs_nonneg M.w₂, h1.1, h1.2]⟩

theorem H_apply (g : BM X) (x : X) : (M.H g).toFun x = M.wage x + M.βf (g.toFun x) := rfl

/-- **Exercise 8.2.1** (p. 262): `H` is an order preserving self-map of `V = [0, v̄]`. -/
theorem exercise_8_2_1 : Monotone M.H ∧ MapsTo M.H (Icc 0 M.vbar) (Icc 0 M.vbar) := by
  refine ⟨fun g g' h => BM.le_def.2 fun x => add_le_add le_rfl
    (M.monotone_βf (BM.le_def.1 h x)), fun g hg => ⟨BM.le_def.2 fun x => ?_,
      BM.le_def.2 fun x => ?_⟩⟩
  · have h0 : M.βf 0 ≤ M.βf (g.toFun x) := M.monotone_βf (BM.le_def.1 hg.1 x)
    rw [M.βf_zero] at h0
    change (0 : ℝ) ≤ M.wage x + M.βf (g.toFun x)
    linarith [(M.wage_mem x).1, M.w₁_pos]
  · change M.wage x + M.βf (g.toFun x) ≤ M.vbarR
    linarith [(M.wage_mem x).2, M.βf_lt (g.toFun x), M.w₂_add_b_le]

theorem concaveOn_H : ConcaveOn ℝ (Icc 0 M.vbar) M.H := by
  refine ⟨convex_Icc _ _, fun g hg g' hg' a b ha hb hab => BM.le_def.2 fun x => ?_⟩
  have h0 : g.toFun x ∈ Ici (0 : ℝ) := BM.le_def.1 hg.1 x
  have h0' : g'.toFun x ∈ Ici (0 : ℝ) := BM.le_def.1 hg'.1 x
  have hc := M.concave_βf.2 h0 h0' ha hb hab
  simp only [smul_eq_mul] at hc
  change a * (M.wage x + M.βf (g.toFun x)) + b * (M.wage x + M.βf (g'.toFun x)) ≤
    M.wage x + M.βf (a * g.toFun x + b * g'.toFun x)
  have : a * M.wage x + b * M.wage x = M.wage x := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- **Exercise 8.2.2** (p. 262): `H` satisfies Du's conditions on `V` (concave, with
`H0 = w ≥ w₁ ≥ ε v̄`), so it is globally stable on `V` (Theorem 4.1.10). -/
theorem exercise_8_2_2 :
    BanachLattice.DuConditions 0 M.vbar M.H ∧
      BanachLattice.GloballyStableOn M.H (Icc 0 M.vbar) := by
  have hdu : BanachLattice.DuConditions 0 M.vbar M.H := by
    refine Or.inl ⟨M.concaveOn_H, M.w₁ / M.vbarR, div_pos M.w₁_pos M.vbar_pos,
      (div_lt_one M.vbar_pos).2 M.w₁_lt_vbar, BM.le_def.2 fun x => ?_⟩
    change 0 + M.w₁ / M.vbarR * (M.vbarR - 0) ≤ M.wage x + M.βf 0
    rw [M.βf_zero, div_mul_eq_mul_div, sub_zero, mul_div_assoc, div_self M.vbar_pos.ne']
    linarith [(M.wage_mem x).1]
  exact ⟨hdu, BanachLattice.theorem_4_1_10 M.zero_le_vbar M.exercise_8_2_1.2
    (M.exercise_8_2_1.1.monotoneOn _) hdu⟩

/-- The lifetime value `e ∈ V` of a constant wage stream: the unique fixed point of `H`. -/
noncomputable def e : BM X := M.exercise_8_2_2.2.choose

theorem e_mem : M.e ∈ Icc 0 M.vbar := M.exercise_8_2_2.2.choose_spec.1

theorem H_e : M.H M.e = M.e := M.exercise_8_2_2.2.choose_spec.2.1

theorem e_ge_w₁ (x : X) : M.w₁ ≤ M.e.toFun x := by
  have h := congrArg (fun g : BM X => g.toFun x) M.H_e
  simp only [H_apply] at h
  have h0 : M.βf 0 ≤ M.βf (M.e.toFun x) := M.monotone_βf (BM.le_def.1 M.e_mem.1 x)
  rw [M.βf_zero] at h0
  linarith [(M.wage_mem x).1]

/-- The continuation value `c + ∫ β[v(w')]P(w, dw')`. -/
noncomputable def cont (v : BM X) (x : X) : ℝ := M.c + ∫ y, M.βf (v.toFun y) ∂(M.P x)

theorem measurable_cont (v : BM X) : Measurable (M.cont v) :=
  measurable_const.add (measurable_markovOp M.P (M.continuous_βf.measurable.comp v.measurable'))

theorem integrable_βf (v : BM X) (x : X) : Integrable (fun y => M.βf (v.toFun y)) (M.P x) := by
  obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf v
  exact Integrable.of_bound (M.continuous_βf.measurable.comp v.measurable').aestronglyMeasurable C
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)

theorem cont_bounds {v : BM X} (hv : v ∈ Icc 0 M.vbar) (x : X) :
    M.c ≤ M.cont v x ∧ M.cont v x ≤ M.c + M.b := by
  constructor
  · refine le_add_of_nonneg_right (integral_nonneg fun y => ?_)
    have := M.monotone_βf (BM.le_def.1 hv.1 y)
    rw [BM.zero_apply, M.βf_zero] at this
    exact this
  · refine add_le_add le_rfl ?_
    calc ∫ y, M.βf (v.toFun y) ∂(M.P x) ≤ ∫ _, M.b ∂(M.P x) :=
          integral_mono (M.integrable_βf v x) (integrable_const _) fun y => (M.βf_lt _).le
      _ = M.b := by simp

/-- `(T_σ v)(w) = σ(w)e(w) + (1 − σ(w))[c + ∫ β[v(w')]P(w, dw')]`. -/
noncomputable def Tfun (σ : StopPolicy X) (v : BM X) : BM X :=
  ⟨fun x => if σ.1 x then M.e.toFun x else M.cont v x,
    Measurable.ite (σ.2 (measurableSet_singleton true)) M.e.measurable' (M.measurable_cont v), by
    obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf v
    refine ⟨‖M.e‖ + |M.c| + C, fun x => ?_⟩
    split_ifs
    · exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (BM.abs_le_norm _ _) (abs_nonneg _))
        ((abs_nonneg _).trans (hC x))
    · refine (abs_add_le _ _).trans ?_
      refine add_le_add (le_add_of_nonneg_left (norm_nonneg _)) ?_
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ y, |M.βf (v.toFun y)| ∂(M.P x) ≤ ∫ _, C ∂(M.P x) :=
            integral_mono (M.integrable_βf v x).abs (integrable_const _) fun y => hC y
        _ = C := by simp⟩

/-- **Exercise 8.2.3** (p. 263): every `T_σ` maps `V = [0, v̄]` into itself. -/
theorem exercise_8_2_3 (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc 0 M.vbar) :
    M.Tfun σ v ∈ Icc 0 M.vbar := by
  refine ⟨BM.le_def.2 fun x => ?_, BM.le_def.2 fun x => ?_⟩
  · change (0 : ℝ) ≤ if σ.1 x then M.e.toFun x else M.cont v x
    split_ifs
    · exact BM.le_def.1 M.e_mem.1 x
    · linarith [(M.cont_bounds hv x).1, M.c_pos]
  · change (if σ.1 x then M.e.toFun x else M.cont v x) ≤ M.vbarR
    split_ifs
    · exact BM.le_def.1 M.e_mem.2 x
    · linarith [(M.cont_bounds hv x).2, M.c_add_b_le]

theorem cont_mono {v w : BM X} (h : v ≤ w) (x : X) : M.cont v x ≤ M.cont w x :=
  add_le_add le_rfl (integral_mono (M.integrable_βf v x) (M.integrable_βf w x) fun y =>
    M.monotone_βf (BM.le_def.1 h y))

/-- The nonlinear discount ADP `(V, 𝕋)` on `V = [0, v̄]`. -/
noncomputable def adp : ADP (Icc 0 M.vbar) (StopPolicy X) where
  T σ v := ⟨M.Tfun σ v, M.exercise_8_2_3 σ v.2⟩
  mono σ v w h := BM.le_def.2 fun x => by
    change (if σ.1 x then M.e.toFun x else M.cont v x) ≤
      (if σ.1 x then M.e.toFun x else M.cont w x)
    split_ifs
    · exact le_rfl
    · exact M.cont_mono h x
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The greedy policy: accept when `e(w) ≥ c + ∫ β[v(w')]P(w, dw')`. -/
noncomputable def accept (v : BM X) : StopPolicy X :=
  acceptWhere (s := M.e.toFun) (h := M.cont v) M.e.measurable' (M.measurable_cont v)

theorem regular : M.adp.Regular := fun v => ⟨M.accept v, fun τ => BM.le_def.2 fun x => by
  change (if τ.1 x then M.e.toFun x else M.cont v x) ≤
    (if (M.accept v).1 x then M.e.toFun x else M.cont v x)
  rw [accept, acceptWhere_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _⟩

theorem concaveOn_T (σ : StopPolicy X) :
    ConcaveOn ℝ (Icc 0 M.vbar) (BanachLattice.extendIcc (M.adp.T σ)) := by
  refine ⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩
  have hvw : a • v + b • w ∈ Icc 0 M.vbar := convex_Icc _ _ hv hw ha hb hab
  rw [show v = ((⟨v, hv⟩ : Icc 0 M.vbar) : BM X) from rfl,
    show w = ((⟨w, hw⟩ : Icc 0 M.vbar) : BM X) from rfl,
    BanachLattice.extendIcc_apply, BanachLattice.extendIcc_apply,
    show a • v + b • w = ((⟨a • v + b • w, hvw⟩ : Icc 0 M.vbar) : BM X) from rfl,
    BanachLattice.extendIcc_apply]
  refine BM.le_def.2 fun x => ?_
  change a * (if σ.1 x then M.e.toFun x else M.cont v x) +
    b * (if σ.1 x then M.e.toFun x else M.cont w x) ≤
      if σ.1 x then M.e.toFun x else M.cont (a • v + b • w) x
  split_ifs
  · rw [← add_mul, hab, one_mul]
  · have hpt : ∀ y, a * M.βf (v.toFun y) + b * M.βf (w.toFun y) ≤
        M.βf ((a • v + b • w).toFun y) := fun y => by
      have hc := M.concave_βf.2 (show v.toFun y ∈ Ici (0 : ℝ) from BM.le_def.1 hv.1 y)
        (show w.toFun y ∈ Ici (0 : ℝ) from BM.le_def.1 hw.1 y) ha hb hab
      simpa using hc
    have hI : ∫ y, (a * M.βf (v.toFun y) + b * M.βf (w.toFun y)) ∂(M.P x) ≤
        ∫ y, M.βf ((a • v + b • w).toFun y) ∂(M.P x) :=
      integral_mono (((M.integrable_βf v x).const_mul a).add
        ((M.integrable_βf w x).const_mul b)) (M.integrable_βf _ x) hpt
    rw [integral_add ((M.integrable_βf v x).const_mul a) ((M.integrable_βf w x).const_mul b),
      integral_const_mul, integral_const_mul] at hI
    change a * (M.c + ∫ y, M.βf (v.toFun y) ∂(M.P x)) +
      b * (M.c + ∫ y, M.βf (w.toFun y) ∂(M.P x)) ≤
        M.c + ∫ y, M.βf ((a • v + b • w).toFun y) ∂(M.P x)
    have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
    nlinarith

/-- **Exercise 8.2.4** (p. 263): the nonlinear discount ADP satisfies the conditions of
Theorem 4.1.11 (regular; every `T_σ` concave with `T_σ 0 ≥ c ≥ ε v̄`; `bW` countably Dedekind
complete), so the fundamental optimality properties hold and VFI, OPI and HPI all converge. -/
theorem exercise_8_2_4 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  refine BanachLattice.theorem_4_1_11 M.zero_le_vbar M.adp M.regular (fun σ => Or.inl
    ⟨M.concaveOn_T σ, M.c / M.vbarR, div_pos M.c_pos M.vbar_pos,
      (div_lt_one M.vbar_pos).2 (M.c_lt.trans M.w₁_lt_vbar), ?_⟩)
    (Or.inl BM.countablyDedekindComplete)
  have h0 : BanachLattice.extendIcc (M.adp.T σ) (0 : BM X) = M.Tfun σ 0 :=
    BanachLattice.extendIcc_apply (M.adp.T σ) ⟨0, le_rfl, M.zero_le_vbar⟩
  rw [h0]
  refine BM.le_def.2 fun x => ?_
  change 0 + M.c / M.vbarR * (M.vbarR - 0) ≤
    if σ.1 x then M.e.toFun x else M.cont 0 x
  rw [zero_add, sub_zero, div_mul_cancel₀ _ M.vbar_pos.ne']
  have hc := (M.cont_bounds ⟨le_rfl, M.zero_le_vbar⟩ x).1
  split_ifs
  · linarith [M.e_ge_w₁ x, M.c_lt]
  · exact hc

end NLDiscount

/-! ### Nonlinear expectations -/

/-- Job search with Kreps–Porteus expectations (§8.2.2). -/
structure KPSearch (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  w₁ : ℝ
  w₂ : ℝ
  w₁_lt : w₁ < w₂
  wage_mem : ∀ x, wage x ∈ Icc w₁ w₂
  /-- unemployment compensation -/
  c : ℝ
  c_pos : 0 < c
  c_lt : c < w₁
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  /-- the risk parameter `γ ≠ 1` -/
  γ : ℝ
  γ_ne : γ ≠ 1

namespace KPSearch

attribute [local instance] KPSearch.isMarkov

variable (M : KPSearch X)

theorem p_ne : 1 - M.γ ≠ 0 := sub_ne_zero.2 M.γ_ne.symm

/-- The Kreps–Porteus operator `(Rv)(w) = (∫ v^{1−γ} dP(w, ·))^{1/(1−γ)}`. -/
noncomputable def Rf (v : X → ℝ) (x : X) : ℝ := pmean (M.P x) (1 - M.γ) v

/-- **Exercise 8.2.5** (p. 264): (i) `R` is order preserving and maps constants to themselves;
(ii) `R` is concave when `γ ≥ 0` and convex when `γ ≤ 0`, on positive bounded measurable
functions. -/
theorem exercise_8_2_5 :
    (∀ v w : X → ℝ, PosBdd v → PosBdd w → v ≤ w → M.Rf v ≤ M.Rf w) ∧
    (∀ k : ℝ, 0 < k → M.Rf (fun _ => k) = fun _ => k) ∧
    (0 ≤ M.γ → ∀ v w : X → ℝ, PosBdd v → PosBdd w → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ x, a * M.Rf v x + b * M.Rf w x ≤ M.Rf (a • v + b • w) x) ∧
    (M.γ ≤ 0 → ∀ v w : X → ℝ, PosBdd v → PosBdd w → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ x, M.Rf (a • v + b • w) x ≤ a * M.Rf v x + b * M.Rf w x) :=
  ⟨fun _ _ hv hw h x => pmean_mono M.p_ne hv hw h, fun _ hk => funext fun _ =>
    pmean_const M.p_ne hk, fun hγ _ _ hv hw _ _ ha hb hab _ =>
      pmean_concave M.p_ne (by linarith) hv hw ha hb hab,
    fun hγ _ _ hv hw _ _ ha hb hab _ => pmean_convex (by linarith) hv hw ha hb hab⟩

/-- `v̄ = (c + w₂)/(1 − β)`. -/
noncomputable def vbarR : ℝ := (M.c + M.w₂) / (1 - M.β)

/-- The order interval `V = [c, v̄]` in `bW`. -/
noncomputable def lo : BM X := BM.const M.c

noncomputable def vbar : BM X := BM.const M.vbarR

theorem one_sub_β_pos : 0 < 1 - M.β := sub_pos.2 M.β_lt_one

theorem w₂_pos : 0 < M.w₂ := M.c_pos.trans (M.c_lt.trans M.w₁_lt)

theorem vbar_eq : M.vbarR * (1 - M.β) = M.c + M.w₂ := div_mul_cancel₀ _ M.one_sub_β_pos.ne'

theorem c_lt_vbar : M.c < M.vbarR := by
  rw [vbarR, lt_div_iff₀ M.one_sub_β_pos]
  have := M.w₂_pos
  have := M.β_pos
  nlinarith [M.c_pos]

theorem lo_le_vbar : M.lo ≤ M.vbar := BM.le_def.2 fun _ => M.c_lt_vbar.le

/-- `e(w) = w/(1 − β)`. -/
noncomputable def efun (x : X) : ℝ := M.wage x / (1 - M.β)

theorem efun_bounds (x : X) :
    M.c + M.β * M.c ≤ M.efun x ∧ M.efun x ≤ M.vbarR - M.c / (1 - M.β) := by
  have h := M.wage_mem x
  have hp := M.one_sub_β_pos
  constructor
  · rw [efun, le_div_iff₀ hp]
    have h2 : (M.c + M.β * M.c) * (1 - M.β) ≤ M.c := by nlinarith [M.c_pos, sq_nonneg M.β]
    linarith [h.1, M.c_lt]
  · rw [efun, vbarR, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [h.2]) hp.le

theorem measurable_efun : Measurable M.efun := M.measurable_wage.div_const _

theorem posBdd {v : BM X} (hv : v ∈ Icc M.lo M.vbar) : PosBdd v.toFun :=
  ⟨v.measurable', M.c, M.vbarR, M.c_pos, fun x => ⟨BM.le_def.1 hv.1 x, BM.le_def.1 hv.2 x⟩⟩

theorem Rf_bounds {v : BM X} (hv : v ∈ Icc M.lo M.vbar) (x : X) :
    M.c ≤ M.Rf v.toFun x ∧ M.Rf v.toFun x ≤ M.vbarR := by
  obtain ⟨hmono, hconst, -, -⟩ := M.exercise_8_2_5
  have h1 := hmono _ _ (posBdd_const M.c_pos) (M.posBdd hv) (fun x => BM.le_def.1 hv.1 x) x
  have h2 := hmono _ _ (M.posBdd hv) (posBdd_const (M.c_pos.trans M.c_lt_vbar))
    (fun x => BM.le_def.1 hv.2 x) x
  rw [hconst _ M.c_pos] at h1
  rw [hconst _ (M.c_pos.trans M.c_lt_vbar)] at h2
  exact ⟨h1, h2⟩

theorem measurable_Rf (v : BM X) : Measurable (M.Rf v.toFun) :=
  (measurable_markovOp M.P (v.measurable'.pow_const _)).pow_const _

/-- The value of `T_σ v`: `σe + (1 − σ)(c + βRv)`. -/
noncomputable def Tval (σ : StopPolicy X) (v : BM X) (x : X) : ℝ :=
  if σ.1 x then M.efun x else M.c + M.β * M.Rf v.toFun x

theorem Tval_bounds (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc M.lo M.vbar) (x : X) :
    M.c ≤ M.Tval σ v x ∧ M.Tval σ v x ≤ M.vbarR := by
  have he := M.efun_bounds x
  have hR := M.Rf_bounds hv x
  have hβ := M.β_pos
  have hp := M.one_sub_β_pos
  have hcp : 0 < M.c / (1 - M.β) := div_pos M.c_pos hp
  have hv1 := M.vbar_eq
  unfold Tval
  split_ifs
  · constructor <;> nlinarith [M.c_pos]
  · constructor <;> nlinarith [M.c_pos, M.w₂_pos]

/-- `T_σ` on `V = [c, v̄]`. -/
noncomputable def Tfun (σ : StopPolicy X) (v : Icc M.lo M.vbar) : Icc M.lo M.vbar :=
  ⟨⟨M.Tval σ v, Measurable.ite (σ.2 (measurableSet_singleton true))
      (M.measurable_wage.div_const _) (measurable_const.add (measurable_const.mul
        (M.measurable_Rf v))),
    ⟨M.vbarR, fun x => by
      have h := M.Tval_bounds σ v.2 x
      rw [abs_le]
      constructor <;> linarith [M.c_pos]⟩⟩,
    BM.le_def.2 fun x => (M.Tval_bounds σ v.2 x).1, BM.le_def.2 fun x => (M.Tval_bounds σ v.2 x).2⟩

/-- The Kreps–Porteus job search ADP `(V, 𝕋)` of §8.2.2. -/
noncomputable def adp : ADP (Icc M.lo M.vbar) (StopPolicy X) where
  T := M.Tfun
  mono σ v w h := BM.le_def.2 fun x => by
    change M.Tval σ v x ≤ M.Tval σ w x
    unfold Tval
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (M.exercise_8_2_5.1 _ _ (M.posBdd v.2)
        (M.posBdd w.2) (fun y => BM.le_def.1 h y) x) M.β_pos.le)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem regular : M.adp.Regular := fun v => ⟨acceptWhere (s := M.efun)
    (h := fun x => M.c + M.β * M.Rf v.1.toFun x) M.measurable_efun
    (measurable_const.add (measurable_const.mul (M.measurable_Rf v))),
  fun τ => BM.le_def.2 fun x => by
    change M.Tval τ v x ≤ M.Tval _ v x
    unfold Tval
    rw [acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _⟩

theorem extendIcc_eq (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc M.lo M.vbar) :
    BanachLattice.extendIcc (M.adp.T σ) v = ⟨M.Tval σ v, (M.Tfun σ ⟨v, hv⟩).1.measurable',
      (M.Tfun σ ⟨v, hv⟩).1.bdd'⟩ :=
  BanachLattice.extendIcc_apply (M.adp.T σ) ⟨v, hv⟩

/-- §8.2.2 (p. 264): for every `γ ≠ 1`, the policy operators satisfy Du's conditions — concave
with `T_σ c ≥ c + ε(v̄ − c)` when `γ ≥ 0`, convex with `T_σ v̄ ≤ v̄ − ε(v̄ − c)` when `γ ≤ 0` — so,
by Theorem 4.1.11, the fundamental optimality properties hold and VFI, OPI and HPI converge. -/
theorem section_8_2_2 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  obtain ⟨-, -, hconc, hconv⟩ := M.exercise_8_2_5
  have hp := M.one_sub_β_pos
  have hβ := M.β_pos
  have hvc := M.c_lt_vbar
  have hv1 := M.vbar_eq
  have hcomb : ∀ {v w : BM X}, v ∈ Icc M.lo M.vbar → w ∈ Icc M.lo M.vbar → ∀ {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 → a • v + b • w ∈ Icc M.lo M.vbar :=
    fun hv hw _ _ ha hb hab => convex_Icc _ _ hv hw ha hb hab
  refine BanachLattice.theorem_4_1_11 M.lo_le_vbar M.adp M.regular (fun σ => ?_)
    (Or.inl BM.countablyDedekindComplete)
  rcases le_total 0 M.γ with hγ | hγ
  · -- concave case
    refine Or.inl ⟨⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩,
      M.β * M.c / (M.vbarR - M.c), div_pos (mul_pos hβ M.c_pos) (sub_pos.2 hvc), ?_, ?_⟩
    · rw [M.extendIcc_eq σ hv, M.extendIcc_eq σ hw, M.extendIcc_eq σ (hcomb hv hw ha hb hab)]
      refine BM.le_def.2 fun x => ?_
      change a * M.Tval σ v x + b * M.Tval σ w x ≤ M.Tval σ (a • v + b • w) x
      unfold Tval
      split_ifs
      · rw [← add_mul, hab, one_mul]
      · have h := hconc hγ _ _ (M.posBdd hv) (M.posBdd hw) a b ha hb hab x
        have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
        change a * (M.c + M.β * M.Rf v.toFun x) + b * (M.c + M.β * M.Rf w.toFun x) ≤
          M.c + M.β * M.Rf (a • v.toFun + b • w.toFun) x
        nlinarith
    · rw [div_lt_one (sub_pos.2 hvc)]
      nlinarith [M.c_pos, M.w₂_pos]
    · rw [M.extendIcc_eq σ ⟨le_rfl, M.lo_le_vbar⟩]
      refine BM.le_def.2 fun x => ?_
      change M.c + M.β * M.c / (M.vbarR - M.c) * (M.vbarR - M.c) ≤ M.Tval σ M.lo x
      rw [div_mul_cancel₀ _ (sub_pos.2 hvc).ne']
      have he := M.efun_bounds x
      have hR := M.Rf_bounds ⟨le_rfl, M.lo_le_vbar⟩ x
      unfold Tval
      split_ifs
      · exact he.1
      · nlinarith
  · -- convex case
    have hm : 0 < min (M.c / (1 - M.β)) M.w₂ := lt_min (div_pos M.c_pos hp) M.w₂_pos
    have hmlt : min (M.c / (1 - M.β)) M.w₂ < M.vbarR - M.c := by
      refine (min_le_left _ _).trans_lt ?_
      rw [div_lt_iff₀ hp]
      nlinarith [M.c_pos, M.w₂_pos, M.c_lt, M.w₁_lt]
    refine Or.inr ⟨⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩,
      min (M.c / (1 - M.β)) M.w₂ / (M.vbarR - M.c), div_pos hm (sub_pos.2 hvc),
      (div_lt_one (sub_pos.2 hvc)).2 hmlt, ?_⟩
    · rw [M.extendIcc_eq σ hv, M.extendIcc_eq σ hw, M.extendIcc_eq σ (hcomb hv hw ha hb hab)]
      refine BM.le_def.2 fun x => ?_
      change M.Tval σ (a • v + b • w) x ≤ a * M.Tval σ v x + b * M.Tval σ w x
      unfold Tval
      split_ifs
      · rw [← add_mul, hab, one_mul]
      · have h := hconv hγ _ _ (M.posBdd hv) (M.posBdd hw) a b ha hb hab x
        have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
        change M.c + M.β * M.Rf (a • v.toFun + b • w.toFun) x ≤
          a * (M.c + M.β * M.Rf v.toFun x) + b * (M.c + M.β * M.Rf w.toFun x)
        nlinarith
    · rw [M.extendIcc_eq σ ⟨M.lo_le_vbar, le_rfl⟩]
      refine BM.le_def.2 fun x => ?_
      change M.Tval σ M.vbar x ≤
        M.vbarR - min (M.c / (1 - M.β)) M.w₂ / (M.vbarR - M.c) * (M.vbarR - M.c)
      rw [div_mul_cancel₀ _ (sub_pos.2 hvc).ne']
      have he := M.efun_bounds x
      have hR := M.Rf_bounds ⟨M.lo_le_vbar, le_rfl⟩ x
      unfold Tval
      split_ifs
      · linarith [min_le_left (M.c / (1 - M.β)) M.w₂]
      · have : M.c + M.β * M.vbarR = M.vbarR - M.w₂ := by nlinarith
        nlinarith [min_le_right (M.c / (1 - M.β)) M.w₂]

end KPSearch

end SargentStachurski.AdditionalApplications
