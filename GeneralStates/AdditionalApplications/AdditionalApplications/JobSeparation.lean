/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.JobSearchL1
import AdditionalApplications.BMOperators

/-!
# Job search with separation

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.4 (pp. 269–272).

Offers are `P`-Markov on a state space `X` with offer `w(x) ∈ [0, M]`; a match dissolves with
probability `α`. Eliminating the employed value with (8.41), `v_e = h + γPv_u`,
`h = w/(1 − β(1 − α))`, `γ = αβ/(1 − β(1 − α))`, the policy operators on `bW` are (8.42),
`T_σ v = σ(h + γPv) + (1 − σ)(c + βPv)`.

* (8.41): solving (8.39) for the employed value.
* The policy (8.43) is greedy, so `(bW, 𝕋)` is regular.
* **Exercise 8.2.12**: each `T_σ` is a contraction of modulus `β ∨ γ < 1`.
* **Proposition 8.2.2**: well-posedness, the fundamental optimality properties, and convergence
  of VFI, OPI and HPI (Theorem 3.1.5).
* **Exercise 8.2.13**: (8.46) has a unique solution `v*_u ∈ bW`, computed by iterating the
  Bellman operator from any starting point; with `v*_e = h + γPv*_u`, the pair solves
  (8.44)–(8.45), and it is the only solution in `bW × bW`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- (8.41): `v_e = w + β[α s + (1 − α)v_e]` iff `v_e = (w + αβ s)/(1 − β(1 − α))`, for `0 ≤ α`
and `0 ≤ β < 1`. -/
theorem eq_8_41 {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (w s ve : ℝ) :
    ve = w + β * (α * s + (1 - α) * ve) ↔ ve = (w + α * β * s) / (1 - β * (1 - α)) := by
  have hd : 0 < 1 - β * (1 - α) := by nlinarith
  rw [eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

variable {X : Type*} [MeasurableSpace X]

/-- Job search with separation (§8.2.4). -/
structure Separation (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  /-- the upper bound of offers -/
  M : ℝ
  wage_mem : ∀ x, wage x ∈ Icc 0 M
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  /-- the separation probability -/
  α : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1

namespace Separation

attribute [local instance] Separation.isMarkov

variable (S : Separation X)

theorem denom_pos : 0 < 1 - S.β * (1 - S.α) := by
  nlinarith [S.β_pos, S.β_lt_one, S.α_pos, S.α_lt_one]

/-- `h(w) = w/(1 − β(1 − α))`. -/
noncomputable def h (x : X) : ℝ := S.wage x / (1 - S.β * (1 - S.α))

/-- `γ = αβ/(1 − β(1 − α))`. -/
noncomputable def γ : ℝ := S.α * S.β / (1 - S.β * (1 - S.α))

theorem γ_nonneg : 0 ≤ S.γ := div_nonneg (mul_pos S.α_pos S.β_pos).le S.denom_pos.le

theorem γ_lt_one : S.γ < 1 := by
  rw [γ, div_lt_one S.denom_pos]
  nlinarith [S.β_lt_one, S.α_pos]

/-- The Markov operator `P` on `bW`. -/
noncomputable def Pop : BM X →L[ℝ] BM X := BM.markovCLM S.P

theorem abs_Pop_sub_le (v w : BM X) (x : X) :
    |(S.Pop v).toFun x - (S.Pop w).toFun x| ≤ ‖v - w‖ := by
  have h1 : (S.Pop v).toFun x - (S.Pop w).toFun x = (S.Pop (v - w)).toFun x := by
    rw [map_sub, BM.sub_apply]
  rw [h1, Pop, BM.markovCLM_apply]
  exact abs_markovOp_le S.P (BM.abs_le_norm (v - w)) x

/-- The stop value `h + γPv` and the continuation value `c + βPv`. -/
noncomputable def stopV (v : BM X) (x : X) : ℝ := S.h x + S.γ * (S.Pop v).toFun x

noncomputable def contV (v : BM X) (x : X) : ℝ := S.c + S.β * (S.Pop v).toFun x

/-- (8.42): `T_σ v = σ(h + γPv) + (1 − σ)(c + βPv)`. -/
noncomputable def T (σ : StopPolicy X) (v : BM X) : BM X :=
  ⟨fun x => if σ.1 x then S.stopV v x else S.contV v x,
    Measurable.ite (σ.2 (measurableSet_singleton true))
      ((S.measurable_wage.div_const _).add (measurable_const.mul (S.Pop v).measurable'))
      (measurable_const.add (measurable_const.mul (S.Pop v).measurable')), by
    refine ⟨S.M / (1 - S.β * (1 - S.α)) + S.γ * ‖S.Pop v‖ + |S.c| + S.β * ‖S.Pop v‖,
      fun x => ?_⟩
    have hw := S.wage_mem x
    have hP := BM.abs_le_norm (S.Pop v) x
    have hh : |S.h x| ≤ S.M / (1 - S.β * (1 - S.α)) := by
      rw [h, abs_div, abs_of_pos S.denom_pos, abs_of_nonneg hw.1]
      exact div_le_div_of_nonneg_right hw.2 S.denom_pos.le
    have hγ := S.γ_nonneg
    have hβ := S.β_pos.le
    split_ifs
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hγ]
      nlinarith [abs_nonneg S.c, mul_nonneg hβ (norm_nonneg (S.Pop v)),
        mul_le_mul_of_nonneg_left hP hγ]
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos S.β_pos]
      nlinarith [abs_nonneg (S.h x), mul_nonneg hγ (norm_nonneg (S.Pop v)),
        mul_le_mul_of_nonneg_left hP hβ, (abs_nonneg (S.h x)).trans hh]⟩

theorem T_apply (σ : StopPolicy X) (v : BM X) (x : X) :
    (S.T σ v).toFun x = if σ.1 x then S.stopV v x else S.contV v x := rfl

/-- The ADP `(bW, 𝕋)` of (8.42). -/
noncomputable def adp : ADP (BM X) (StopPolicy X) where
  T := S.T
  mono σ v w hvw := BM.le_def.2 fun x => by
    have hP := BM.le_def.1 ((BM.markovCLM_isPositive S.P).mono hvw) x
    change (if σ.1 x then S.stopV v x else S.contV v x) ≤
      (if σ.1 x then S.stopV w x else S.contV w x)
    split_ifs
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hP S.γ_nonneg)
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hP S.β_pos.le)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy (8.43): accept when `h + γPv ≥ c + βPv`. -/
noncomputable def accept (v : BM X) : StopPolicy X :=
  acceptWhere (s := S.stopV v) (h := S.contV v)
    ((S.measurable_wage.div_const _).add (measurable_const.mul (S.Pop v).measurable'))
    (measurable_const.add (measurable_const.mul (S.Pop v).measurable'))

/-- (8.43): the policy `𝟙{h + γPv ≥ c + βPv}` is `v`-greedy, and `Tv = (h + γPv) ∨ (c + βPv)`. -/
theorem accept_isGreedy (v : BM X) :
    S.adp.IsGreedy v (S.accept v) ∧
      ∀ x, (S.adp.bellman v).toFun x = max (S.stopV v x) (S.contV v x) := by
  have hval : ∀ x, (S.adp.T (S.accept v) v).toFun x = max (S.stopV v x) (S.contV v x) :=
    fun x => acceptWhere_apply _ _ x
  have hg : S.adp.IsGreedy v (S.accept v) := fun τ => BM.le_def.2 fun x => by
    rw [hval]
    change (if τ.1 x then S.stopV v x else S.contV v x) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : S.adp.bellman v = S.adp.T (S.accept v) v :=
    le_antisymm (hg _) (S.adp.isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun x => by rw [heq, hval]⟩

theorem regular : S.adp.Regular := fun v => ⟨_, (S.accept_isGreedy v).1⟩

/-- **Exercise 8.2.12** (p. 271): each `T_σ` is a contraction of modulus `λ = β ∨ γ ∈ (0, 1)`. -/
theorem exercise_8_2_12 :
    0 < max S.β S.γ ∧ max S.β S.γ < 1 ∧
      ∀ σ v w, dist (S.adp.T σ v) (S.adp.T σ w) ≤ max S.β S.γ * dist v w := by
  refine ⟨lt_max_of_lt_left S.β_pos, max_lt S.β_lt_one S.γ_lt_one, fun σ v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg (le_max_of_le_left S.β_pos.le) (norm_nonneg _)) fun x => ?_
  have hP := S.abs_Pop_sub_le v w x
  change |(if σ.1 x then S.stopV v x else S.contV v x) -
    (if σ.1 x then S.stopV w x else S.contV w x)| ≤ _
  split_ifs
  · rw [stopV, stopV, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.γ_nonneg]
    exact mul_le_mul (le_max_right _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)
  · rw [contV, contV, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos S.β_pos]
    exact mul_le_mul (le_max_left _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)

/-- **Proposition 8.2.2** (p. 271): `(bW, 𝕋)` is well-posed, (i) the fundamental optimality
properties hold, and (ii) VFI, OPI and HPI all converge (Exercise 8.2.12 and Theorem 3.1.5). -/
theorem proposition_8_2_2 :
    ∃ hw : S.adp.WellPosed, S.adp.FundamentalOptimality hw ∧ ∃ vstar,
      S.adp.VFIGeometric univ vstar ∧
        ∀ g, S.adp.IsSelector g → S.adp.OPIConverges g vstar ∧ S.adp.HPIConverges hw g vstar := by
  obtain ⟨h0, h1, hT⟩ := S.exercise_8_2_12
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive h0.le h1 hT
    (V₀ := univ) ⟨isClosed_univ, fun v _ => S.regular v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨_, hFO, vstar, hgeo, hconv S.regular⟩

/-- The Bellman operator of (8.46): `v ↦ (h + γPv) ∨ (c + βPv)`. -/
theorem bellman_apply (v : BM X) (x : X) :
    (S.adp.bellman v).toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x) :=
  (S.accept_isGreedy v).2 x

theorem bellman_contracting : ContractingWith ⟨max S.β S.γ, (lt_max_of_lt_left S.β_pos).le⟩
    S.adp.bellman := by
  obtain ⟨-, h1, -⟩ := S.exercise_8_2_12
  refine ⟨h1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg (le_max_of_le_left S.β_pos.le) (norm_nonneg _)) fun x => ?_
  have hP := S.abs_Pop_sub_le v w x
  rw [BM.sub_apply, S.bellman_apply, S.bellman_apply]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.γ_nonneg]
    exact mul_le_mul (le_max_right _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos S.β_pos]
    exact mul_le_mul (le_max_left _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)

/-- **Exercise 8.2.13** (p. 272): (8.46) has a unique solution `v*_u ∈ bW`; iterating the Bellman
operator from any `v ∈ bW` converges to it (a convergent method), and `v*_e = h + γPv*_u`. The pair
`(v*_e, v*_u)` solves (8.44)–(8.45) and is the only solution in `bW × bW`. -/
theorem exercise_8_2_13 :
    ∃ vu : BM X, (∀ x, vu.toFun x = max (S.h x + S.γ * (S.Pop vu).toFun x)
        (S.c + S.β * (S.Pop vu).toFun x)) ∧
      (∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
        (S.c + S.β * (S.Pop v).toFun x)) → v = vu) ∧
      (∀ v, Tendsto (fun n => S.adp.bellman^[n] v) atTop (𝓝 vu)) ∧
      ∀ ve u : BM X, ((∀ x, u.toFun x = max (ve.toFun x) (S.c + S.β * (S.Pop u).toFun x)) ∧
        ∀ x, ve.toFun x = S.wage x + S.β * (S.α * (S.Pop u).toFun x + (1 - S.α) * ve.toFun x)) ↔
        (u = vu ∧ ∀ x, ve.toFun x = S.h x + S.γ * (S.Pop vu).toFun x) := by
  have hc := S.bellman_contracting
  set vu := ContractingWith.fixedPoint _ hc
  have hfix : S.adp.bellman vu = vu := ContractingWith.fixedPoint_isFixedPt hc
  have hsol : ∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x)) ↔ S.adp.bellman v = v := fun v =>
    ⟨fun h => BM.ext fun x => by rw [S.bellman_apply, h x], fun h x => by
      rw [← S.bellman_apply, h]⟩
  have huniq : ∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x)) → v = vu := fun v h =>
    ContractingWith.fixedPoint_unique hc ((hsol v).1 h)
  -- (8.45) is (8.41) with `s = Pv_u`
  have h841 : ∀ (ve u : BM X) (x : X), ve.toFun x =
      S.wage x + S.β * (S.α * (S.Pop u).toFun x + (1 - S.α) * ve.toFun x) ↔
      ve.toFun x = S.h x + S.γ * (S.Pop u).toFun x := fun ve u x => by
    rw [eq_8_41 S.α_pos.le S.β_pos.le S.β_lt_one, h, γ]
    constructor <;> intro hx <;> rw [hx] <;> field_simp
  refine ⟨vu, (hsol vu).2 hfix, huniq, fun v => ContractingWith.tendsto_iterate_fixedPoint hc v,
    fun ve u => ⟨fun ⟨h44, h45⟩ => ?_, fun ⟨hu, hve⟩ => ?_⟩⟩
  · have hve : ∀ x, ve.toFun x = S.h x + S.γ * (S.Pop u).toFun x := fun x => (h841 ve u x).1 (h45 x)
    have hu : u = vu := huniq u fun x => by rw [h44 x, hve x]
    subst hu
    exact ⟨rfl, hve⟩
  · subst hu
    refine ⟨fun x => ?_, fun x => (h841 ve vu x).2 (hve x)⟩
    rw [hve x]
    exact (hsol vu).2 hfix x

end Separation

end SargentStachurski.AdditionalApplications
