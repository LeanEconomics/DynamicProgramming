/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.JobSearchL1
import AdditionalApplications.BMOperators
import AdditionalApplications.FactoredDP
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Optimal harvests

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.2 (pp. 281–284).

A plantation with biomass `s` faces an iid price `p ~ φ`. Harvesting (`a = 1`) earns
`ps − m(s)` and regrowth starts from `q(0)`; waiting (`a = 0`) costs `c(s)` and biomass grows to
`q(s)`. So `r(s, p, a) = a(ps − m(s)) − (1 − a)c(s)` and `f(s, a) = q[(1 − a)s]`.

We work with general measurable spaces of biomass and prices, a bounded measurable harvest
revenue `rev(s, p)` (the book's `ps − m(s)` on compact `S × E`), a bounded measurable cost
`cost(s)`, a measurable growth map `q`, and a point `s₀` (the book's biomass `0`). Actions are
`Bool` (`true` = harvest), `V = b(S × E)` and `V̂ = b(S × {0, 1})`.

* **Exercise 8.3.4**: `(V, F, V̂, 𝔾)` with `(Fv)(s, a) = ∫ v(f(s, a), p') φ(dp')` and
  `G_σ w = r_σ + βw(s, σ(s, p))` is an order-preserving FDP whose primary ADP is the harvest ADP,
  and `T̂_σ w = FG_σ w` is the subordinate policy operator of §8.3.2.2.
* **§8.3.2.2**: by Theorem 5.2.13, the fundamental optimality properties hold for both ADPs, the
  subordinate Bellman operator `T̂` has a unique fixed point `ŵ*`, and any `σ` with
  `σ(s, p) ∈ argmax_a {r(s, p, a) + βŵ*(s, a)}` is optimal for the harvest problem.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The optimal harvest model (§8.3.2.1). -/
structure Harvest (S E : Type*) [MeasurableSpace S] [MeasurableSpace E] where
  /-- the iid price distribution -/
  φ : Measure E
  [isProb : IsProbabilityMeasure φ]
  /-- the harvest revenue `ps − m(s)` -/
  rev : S × E → ℝ
  measurable_rev : Measurable rev
  bdd_rev : ∃ C, ∀ x, |rev x| ≤ C
  /-- the maintenance cost `c(s)` -/
  cost : S → ℝ
  measurable_cost : Measurable cost
  bdd_cost : ∃ C, ∀ s, |cost s| ≤ C
  /-- the growth map -/
  q : S → S
  measurable_q : Measurable q
  /-- the biomass left after a harvest -/
  s₀ : S
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace Harvest

variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] (H : Harvest S E)

attribute [local instance] Harvest.isProb

/-- Next period's biomass `f(s, a) = q[(1 − a)s]`. -/
def f (s : S) (a : Bool) : S := if a then H.q H.s₀ else H.q s

/-- The reward `r(s, p, a) = a(ps − m(s)) − (1 − a)c(s)`. -/
def r (x : S × E) (a : Bool) : ℝ := if a then H.rev x else -H.cost x.1

theorem measurable_f : Measurable fun y : S × Bool => H.f y.1 y.2 :=
  Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
    (H.measurable_q.comp measurable_fst)

theorem integrable_section (v : BM (S × E)) (s : S) : Integrable (fun p => v.toFun (s, p)) H.φ :=
  Integrable.of_bound
    (v.measurable'.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

theorem abs_integral_le (v : BM (S × E)) (s : S) : |∫ p, v.toFun (s, p) ∂H.φ| ≤ ‖v‖ := by
  have := norm_integral_le_of_norm_le_const (μ := H.φ) (f := fun p => v.toFun (s, p)) (C := ‖v‖)
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
  simpa using this

/-- `(Fv)(s, a) = ∫ v(f(s, a), p') φ(dp')`. -/
noncomputable def F (v : BM (S × E)) : BM (S × Bool) :=
  ⟨fun y => ∫ p, v.toFun (H.f y.1 y.2, p) ∂H.φ,
    (v.measurable'.comp ((H.measurable_f.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable,
    ⟨‖v‖, fun _ => H.abs_integral_le v _⟩⟩

theorem measurable_r (σ : StopPolicy (S × E)) : Measurable fun x => H.r x (σ.1 x) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) H.measurable_rev
    (H.measurable_cost.comp measurable_fst).neg

/-- `(G_σ w)(s, p) = r_σ(s, p) + βw(s, σ(s, p))`. -/
noncomputable def G (σ : StopPolicy (S × E)) (w : BM (S × Bool)) : BM (S × E) :=
  ⟨fun x => H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x),
    (H.measurable_r σ).add (measurable_const.mul (w.measurable'.comp
      (measurable_fst.prodMk σ.2))), by
    obtain ⟨C₁, hC₁⟩ := H.bdd_rev
    obtain ⟨C₂, hC₂⟩ := H.bdd_cost
    refine ⟨C₁ + C₂ + H.β * ‖w‖, fun x => (abs_add_le _ _).trans ?_⟩
    have hw := BM.abs_le_norm w (x.1, σ.1 x)
    have hr : |H.r x (σ.1 x)| ≤ C₁ + C₂ := by
      unfold r
      split_ifs
      · linarith [hC₁ x, (abs_nonneg _).trans (hC₂ x.1)]
      · rw [abs_neg]
        linarith [hC₂ x.1, (abs_nonneg _).trans (hC₁ x)]
    rw [abs_mul, abs_of_nonneg H.β_nonneg]
    linarith [mul_le_mul_of_nonneg_left hw H.β_nonneg]⟩

theorem G_apply (σ : StopPolicy (S × E)) (w : BM (S × Bool)) (x : S × E) :
    (H.G σ w).toFun x = if σ.1 x then H.rev x + H.β * w.toFun (x.1, true)
      else -H.cost x.1 + H.β * w.toFun (x.1, false) := by
  change H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) = _
  rcases σ.1 x with _ | _ <;> simp [r]

/-- The policy harvesting when `r(s, p, 1) + βw(s, 1) ≥ r(s, p, 0) + βw(s, 0)`. -/
noncomputable def harvestWhere (w : BM (S × Bool)) : StopPolicy (S × E) :=
  acceptWhere (s := fun x => H.rev x + H.β * w.toFun (x.1, true))
    (h := fun x => -H.cost x.1 + H.β * w.toFun (x.1, false))
    (H.measurable_rev.add (measurable_const.mul (w.measurable'.comp
      (measurable_fst.prodMk measurable_const))))
    ((H.measurable_cost.comp measurable_fst).neg.add (measurable_const.mul
      (w.measurable'.comp (measurable_fst.prodMk measurable_const))))

theorem G_harvestWhere (w : BM (S × Bool)) (x : S × E) :
    (H.G (H.harvestWhere w) w).toFun x = max (H.rev x + H.β * w.toFun (x.1, true))
      (-H.cost x.1 + H.β * w.toFun (x.1, false)) := by
  rw [G_apply]
  exact acceptWhere_apply _ _ x

theorem G_le_G_harvestWhere (σ : StopPolicy (S × E)) (w : BM (S × Bool)) :
    H.G σ w ≤ H.G (H.harvestWhere w) w := BM.le_def.2 fun x => by
  rw [G_harvestWhere, G_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The FDP `(V, F, V̂, 𝔾)` of §8.3.2.2. -/
noncomputable def fdp : FDP (BM (S × E)) (BM (S × Bool)) (StopPolicy (S × E)) where
  F := H.F
  G := H.G
  greatest w := ⟨H.harvestWhere w, fun τ => H.G_le_G_harvestWhere τ w⟩
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem isOrderPreserving : H.fdp.IsOrderPreserving := by
  refine ⟨fun v w hvw => BM.le_def.2 fun y => integral_mono (H.integrable_section v _)
    (H.integrable_section w _) fun p => BM.le_def.1 hvw _,
    fun σ w w' hww => BM.le_def.2 fun x => ?_⟩
  change H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) ≤
    H.r x (σ.1 x) + H.β * w'.toFun (x.1, σ.1 x)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (BM.le_def.1 hww _) H.β_nonneg)

/-- **Exercise 8.3.4** (p. 283): (i) `(V, F, V̂, 𝔾)` is an order-preserving FDP and (ii) its primary
ADP has the harvest policy operators
`(T_σ v)(s, p) = r_σ(s, p) + β ∫ v[f(s, σ(s, p)), p'] φ(dp')`, while its subordinate ADP has
`(T̂_σ w)(s, a) = ∫ {r_σ(f(s, a), p') + βw[f(s, a), σ(f(s, a), p')]} φ(dp')`. -/
theorem exercise_8_3_4 :
    H.fdp.IsOrderPreserving ∧
      (∀ σ v x, ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ v).toFun x =
        H.r x (σ.1 x) + H.β * ∫ p, v.toFun (H.f x.1 (σ.1 x), p) ∂H.φ) ∧
      ∀ σ w y, ((H.fdp.sub (Or.inl H.isOrderPreserving)).T σ w).toFun y =
        ∫ p, (H.r (H.f y.1 y.2, p) (σ.1 (H.f y.1 y.2, p)) +
          H.β * w.toFun (H.f y.1 y.2, σ.1 (H.f y.1 y.2, p))) ∂H.φ :=
  ⟨H.isOrderPreserving, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem abs_F_sub_le (v w : BM (S × E)) (y : S × Bool) :
    |(H.F v).toFun y - (H.F w).toFun y| ≤ dist v w := by
  have h : (H.F v).toFun y - (H.F w).toFun y = ∫ p, (v - w).toFun (H.f y.1 y.2, p) ∂H.φ := by
    change ∫ p, v.toFun (H.f y.1 y.2, p) ∂H.φ - ∫ p, w.toFun (H.f y.1 y.2, p) ∂H.φ = _
    rw [← integral_sub (H.integrable_section v _) (H.integrable_section w _)]
    rfl
  rw [h, dist_eq_norm]
  exact H.abs_integral_le (v - w) _

theorem primary_contraction (σ : StopPolicy (S × E)) (v w : BM (S × E)) :
    dist ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ v)
      ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ w) ≤ H.β * dist v w := by
  refine BM.dist_le (mul_nonneg H.β_nonneg dist_nonneg) fun x => ?_
  change |(H.r x (σ.1 x) + H.β * (H.F v).toFun (x.1, σ.1 x)) -
    (H.r x (σ.1 x) + H.β * (H.F w).toFun (x.1, σ.1 x))| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg H.β_nonneg]
  exact mul_le_mul_of_nonneg_left (H.abs_F_sub_le v w _) H.β_nonneg

/-- `G_σ w = Gw` iff `σ(s, p) ∈ argmax_a {r(s, p, a) + βw(s, a)}` at every `(s, p)`. -/
theorem G_eq_Gsup_iff (σ : StopPolicy (S × E)) (w : BM (S × Bool)) :
    H.fdp.G σ w = H.fdp.Gsup w ↔ ∀ x, H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) =
      max (H.rev x + H.β * w.toFun (x.1, true)) (-H.cost x.1 + H.β * w.toFun (x.1, false)) := by
  have hsup : H.fdp.Gsup w = H.G (H.harvestWhere w) w := by
    obtain ⟨⟨τ, hτ⟩, -⟩ := H.fdp.isGreatest_Gsup w
    refine le_antisymm ?_ (H.fdp.G_le_Gsup (H.harvestWhere w) w)
    rw [← hτ]
    exact H.G_le_G_harvestWhere τ w
  rw [hsup]
  constructor
  · intro h x
    rw [← H.G_harvestWhere w x, ← h]
    rfl
  · intro h
    exact BM.ext fun x => by rw [H.G_harvestWhere w x, ← h x]; rfl

/-- §8.3.2.2 (p. 283), via Theorem 5.2.13: the fundamental optimality properties hold for the
harvest ADP and for the subordinate ADP; the subordinate Bellman operator `T̂` has a unique fixed
point `ŵ*`, the subordinate value function; and any `σ` with
`σ(s, p) ∈ argmax_a {r(s, p, a) + βŵ*(s, a)}` is optimal for the harvest problem. -/
theorem section_8_3_2_2 :
    ∃ hw : (H.fdp.primary (Or.inl H.isOrderPreserving)).WellPosed,
    ∃ hw' : (H.fdp.sub (Or.inl H.isOrderPreserving)).WellPosed,
      (H.fdp.primary (Or.inl H.isOrderPreserving)).FundamentalOptimality hw ∧
      (H.fdp.sub (Or.inl H.isOrderPreserving)).FundamentalOptimality hw' ∧
      ∃ wstar, (H.fdp.sub (Or.inl H.isOrderPreserving)).IsValueFunction wstar ∧
        (H.fdp.sub (Or.inl H.isOrderPreserving)).bellman wstar = wstar ∧
        (∀ w, (H.fdp.sub (Or.inl H.isOrderPreserving)).bellman w = w → w = wstar) ∧
        ∀ σ : StopPolicy (S × E), (∀ x, H.r x (σ.1 x) + H.β * wstar.toFun (x.1, σ.1 x) =
          max (H.rev x + H.β * wstar.toFun (x.1, true))
            (-H.cost x.1 + H.β * wstar.toFun (x.1, false))) →
          (H.fdp.primary (Or.inl H.isOrderPreserving)).IsOptimal hw σ := by
  have hP := H.isOrderPreserving
  obtain ⟨hFO, -, -, -, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive H.β_nonneg H.β_lt_one
    H.primary_contraction (V₀ := univ)
    ⟨isClosed_univ, fun v _ => FDP.primary_regular _ v, mapsTo_univ _ _⟩ univ_nonempty
  set hw := (ADP.isGloballyStable_of_contraction ⟨(univ_nonempty (α := BM (S × E))).some⟩
    H.β_nonneg H.β_lt_one H.primary_contraction).wellPosed
  have hw' : (H.fdp.sub (Or.inl hP)).WellPosed := ((FDP.lemma_5_2_12 (Or.inl hP)).1).2 hw
  have h513 := FDP.theorem_5_2_13 (Or.inl hP) hP hw hw'
  have hFO' := h513.1.1 hFO
  obtain ⟨wstar, hval, -, hsolve, huniq⟩ := hFO'.2.1
  have hreg := FDP.sub_regular (Or.inl hP) hP.1
  refine ⟨hw, hw', hFO, hFO', wstar, hval,
    ((H.fdp.sub _).solvesBellman_iff (hreg wstar)).1 hsolve,
    fun w hw₀ => huniq w (hreg w) (((H.fdp.sub _).solvesBellman_iff (hreg w)).2 hw₀),
    fun σ hσ => (h513.2 hFO).2.1 wstar σ hval ((H.G_eq_Gsup_iff σ wstar).2 hσ)⟩

end Harvest

end SargentStachurski.AdditionalApplications
