/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.JobSearchL1
import AdditionalApplications.BoundedRDP

/-!
# Job search with bounded offers

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.1.2 (pp. 248–249).

Offers lie in a bounded Borel set `W ⊆ ℝ`, drawn iid from `φ`, and
`(T_σ v)(w) = σ(w) w/(1 − β) + (1 − σ(w))[c + β ∫ v dφ]` (8.4) acts on bounded functions.

* **Exercise 8.1.4**: `(bW, 𝕋)` is an ADP with Bellman operator (8.7), and the Bellman operator
  maps `bcW`, `ibcW` and (for `W ⊆ ℝ₊`) `ibcW₊` into themselves. The exercise also asserts that
  `(V, 𝕋)` is an ADP for these three spaces; that is false, since a policy operator `T_σ` with a
  discontinuous `σ` does not map `bcW` into itself (`exercise_8_1_4_counterexample`).
* **Exercise 8.1.5**: the problem is an RDP on `bW` with `Γ(w) = {0, 1}` and aggregator (8.8).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace BoundedSearch

variable {W : Set ℝ} (φ : Measure W) [IsProbabilityMeasure φ] (c β : ℝ)

/-- The continuation value `c + β ∫ v dφ`. -/
noncomputable def cont (v : BM W) : ℝ := c + β * ∫ w, v.toFun w ∂φ

/-- (8.4): `(T_σ v)(w) = σ(w) w/(1 − β) + (1 − σ(w))[c + β ∫ v dφ]`. -/
noncomputable def T (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (σ : StopPolicy W) (v : BM W) : BM W :=
  ⟨fun w => if σ.1 w then (w : ℝ) / (1 - β) else cont φ c β v,
    Measurable.ite (σ.2 (measurableSet_singleton true))
      (measurable_subtype_coe.div_const _) measurable_const, by
    obtain ⟨K, hK⟩ := hW
    refine ⟨K / |1 - β| + |cont φ c β v|, fun w => ?_⟩
    split_ifs
    · rw [abs_div]
      exact le_add_of_le_of_nonneg (div_le_div_of_nonneg_right (hK w w.2) (abs_nonneg _))
        (abs_nonneg _)
    · exact le_add_of_nonneg_left (div_nonneg ((abs_nonneg _).trans (hK w w.2))
        (abs_nonneg _))⟩

omit [IsProbabilityMeasure φ] in
theorem T_apply (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (σ : StopPolicy W) (v : BM W) (w : W) :
    (T φ c β hW σ v).toFun w = if σ.1 w then (w : ℝ) / (1 - β) else cont φ c β v := rfl

theorem cont_mono (hβ : 0 ≤ β) {v v' : BM W} (h : v ≤ v') : cont φ c β v ≤ cont φ c β v' :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v w))
    (Integrable.of_bound v'.measurable'.aestronglyMeasurable ‖v'‖
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v' w))
    fun w => BM.le_def.1 h w) hβ)

/-- The job search ADP `(bW, 𝕋)` (Exercise 8.1.4). -/
noncomputable def adp (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) : ADP (BM W) (StopPolicy W) where
  T := T φ c β hW
  mono σ v v' h := BM.le_def.2 fun w => by
    rw [T_apply, T_apply]
    split_ifs
    · exact le_rfl
    · exact cont_mono φ c β hβ h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy (8.5): accept when `w/(1 − β) ≥ c + β ∫ v dφ`. -/
noncomputable def accept (v : BM W) : StopPolicy W :=
  acceptWhere (s := fun w : W => (w : ℝ) / (1 - β)) (h := fun _ => cont φ c β v)
    (measurable_subtype_coe.div_const _) measurable_const

/-- **Exercise 8.1.4** (p. 248), first part: `(bW, 𝕋)` is an ADP, the policy (8.5) is
`v`-greedy, and the Bellman operator is (8.7), `(Tv)(w) = max{w/(1 − β), c + β ∫ v dφ}`. -/
theorem exercise_8_1_4 (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) (v : BM W) :
    (adp φ c β hW hβ).IsGreedy v (accept φ c β v) ∧
      ∀ w, ((adp φ c β hW hβ).bellman v).toFun w = max ((w : ℝ) / (1 - β)) (cont φ c β v) := by
  have hval : ∀ w, ((adp φ c β hW hβ).T (accept φ c β v) v).toFun w =
      max ((w : ℝ) / (1 - β)) (cont φ c β v) := fun w =>
    acceptWhere_apply (s := fun w : W => (w : ℝ) / (1 - β)) (h := fun _ => cont φ c β v)
      (measurable_subtype_coe.div_const _) measurable_const w
  have hg : (adp φ c β hW hβ).IsGreedy v (accept φ c β v) := fun τ => BM.le_def.2 fun w => by
    rw [hval]
    change (if τ.1 w then (w : ℝ) / (1 - β) else cont φ c β v) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : (adp φ c β hW hβ).bellman v = (adp φ c β hW hβ).T (accept φ c β v) v :=
    le_antisymm (hg _) ((adp φ c β hW hβ).isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun w => by rw [heq, hval]⟩

/-- **Exercise 8.1.4** (p. 248), second part: the Bellman operator maps `bcW`, `ibcW` and, when
`W ⊆ ℝ₊` and `β < 1`, `ibcW₊` into themselves. -/
theorem exercise_8_1_4_bellman (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (v : BM W) :
    Continuous ((adp φ c β hW hβ).bellman v).toFun ∧
      Monotone ((adp φ c β hW hβ).bellman v).toFun ∧
      ((∀ w ∈ W, 0 ≤ w) → ∀ w, 0 ≤ ((adp φ c β hW hβ).bellman v).toFun w) := by
  have hb := (exercise_8_1_4 φ c β hW hβ v).2
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  refine ⟨?_, fun w w' h => ?_, fun hW0 w => ?_⟩
  · rw [show ((adp φ c β hW hβ).bellman v).toFun = fun w : W =>
      max ((w : ℝ) / (1 - β)) (cont φ c β v) from funext hb]
    exact (continuous_subtype_val.div_const _).max continuous_const
  · rw [hb, hb]
    exact max_le_max (div_le_div_of_nonneg_right (Subtype.coe_le_coe.2 h) hpos.le) le_rfl
  · rw [hb]
    exact le_max_of_le_left (div_nonneg (hW0 w w.2) hpos.le)

/-- **Exercise 8.1.4** is false for `bcW`: with `W = [0, 1]`, `β = 1/2`, `c = 0` and
`σ = 𝟙{w ≥ 1/2}`, `T_σ 0 = 2w 𝟙{w ≥ 1/2}` is discontinuous, so `T_σ` does not map `bcW` (nor
`ibcW`, `ibcW₊`) into itself. -/
theorem exercise_8_1_4_counterexample :
    ∃ (φ : Measure (Icc (0 : ℝ) 1)) (_ : IsProbabilityMeasure φ)
      (hW : ∃ K, ∀ w ∈ Icc (0 : ℝ) 1, |w| ≤ K) (σ : StopPolicy (Icc (0 : ℝ) 1)),
      ¬ Continuous (T φ 0 (1 / 2) hW σ 0).toFun := by
  let φ : Measure (Icc (0 : ℝ) 1) := Measure.dirac ⟨0, le_rfl, zero_le_one⟩
  have hW : ∃ K, ∀ w ∈ Icc (0 : ℝ) 1, |w| ≤ K :=
    ⟨1, fun w hw => by rw [abs_of_nonneg hw.1]; exact hw.2⟩
  let σ : StopPolicy (Icc (0 : ℝ) 1) :=
    acceptWhere (s := fun w : Icc (0 : ℝ) 1 => (w : ℝ)) (h := fun _ => 1 / 2)
      measurable_subtype_coe measurable_const
  refine ⟨φ, inferInstance, hW, σ, fun hc => ?_⟩
  let F : ℝ → ℝ := fun t => (T φ 0 (1 / 2) hW σ 0).toFun (projIcc 0 1 zero_le_one t)
  have hF : ∀ t, F t = if (1 : ℝ) / 2 ≤ (projIcc 0 1 zero_le_one t : ℝ)
      then (projIcc 0 1 zero_le_one t : ℝ) / (1 - 1 / 2) else 0 := fun t => by
    simp only [F, T_apply, σ, acceptWhere, cont, BM.zero_apply, integral_zero, mul_zero,
      add_zero, decide_eq_true_eq]
  have hcF : Continuous F := hc.comp continuous_projIcc
  -- `F = 0` to the left of `1/2` and `F(1/2) = 1`
  have hleft : F =ᶠ[𝓝[<] ((1 : ℝ) / 2)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hF]
    have hlt : (projIcc 0 1 zero_le_one t : ℝ) < 1 / 2 := by
      rw [coe_projIcc]
      exact max_lt (by norm_num) (min_lt_of_right_lt ht)
    simp only [not_le.2 hlt, ↓reduceIte]
  have hhalf : F (1 / 2) = 1 := by
    rw [hF, projIcc_of_mem _ ⟨by norm_num, by norm_num⟩]
    norm_num
  have h1 : Tendsto F (𝓝[<] ((1 : ℝ) / 2)) (𝓝 (F (1 / 2))) :=
    (hcF.continuousAt (x := 1 / 2)).tendsto.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hleft.symm)
  rw [hhalf] at h2
  norm_num at h2

/-- The aggregator (8.8): `B(w, a, v) = a w/(1 − β) + (1 − a)[c + β ∫ v dφ]`. -/
noncomputable def Bagg (w : W) (a : ℝ) (v : W → ℝ) : ℝ :=
  a * ((w : ℝ) / (1 - β)) + (1 - a) * (c + β * ∫ x, v x ∂φ)

/-- **Exercise 8.1.5** (p. 249): with `Γ(w) = {0, 1}` and `V = bW`, the job search problem is an
RDP with aggregator (8.8): `B` is measurable in `(w, a)`, monotone in `v` and bounded on `G` for
each `v`. -/
noncomputable def exercise_8_1_5 (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) : BRDP W ℝ where
  Γ _ := {0, 1}
  B := Bagg φ c β
  measurable v := (measurable_snd.mul
    ((measurable_subtype_coe.comp measurable_fst).div_const _)).add
    ((measurable_const.sub measurable_snd).mul measurable_const)
  mono w a ha v v' h := by
    have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (cont_mono φ c β hβ h) h1)
  bdd v := by
    obtain ⟨K, hK⟩ := hW
    refine ⟨K / |1 - β| + |cont φ c β v|, fun w a ha => ?_⟩
    rcases ha with rfl | rfl
    · simp only [Bagg, zero_mul, sub_zero, one_mul, zero_add]
      exact le_add_of_nonneg_left (div_nonneg ((abs_nonneg _).trans (hK w w.2)) (abs_nonneg _))
    · simp only [Bagg, one_mul, sub_self, zero_mul, add_zero]
      rw [abs_div]
      exact le_add_of_le_of_nonneg (div_le_div_of_nonneg_right (hK w w.2) (abs_nonneg _))
        (abs_nonneg _)
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

end BoundedSearch

end SargentStachurski.AdditionalApplications
