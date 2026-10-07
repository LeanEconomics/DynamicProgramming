/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.JobSearchL1
import AdditionalApplications.FactoredDP
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Basic.Real.ENatENNReal

/-!
# Continuation values and the reservation wage

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.2 (pp. 250–254).

In the iid model, `g(h) = c + β ∫ max{w/(1 − β), h} φ(dw)` (8.14).

* **Exercise 8.1.6**: `g` is a contraction of modulus `β`, via (8.15); its fixed point `h*` is the
  optimal continuation value. **Exercise 8.1.7**: `g` maps `[0, K]` into itself.
* §8.1.2.1: `h* = c + β ∫ v* dφ`, `v* = max{e, h*}`, and the policy (8.12)–(8.13) accepting when
  `w ≥ w* = (1 − β)h*` is optimal.
* §8.1.2.2: `(L¹(φ), F, ℝ, 𝔾)` with `Fv = c + β ∫ v dφ` and `G_σ h = σe + (1 − σ)h` is an
  order-preserving FDP whose primary ADP is the job search ADP and whose subordinate Bellman
  operator is `g`; Theorem 5.2.13 gives the optimality of (8.16) at `h*`.
* §8.1.2.3: Proposition A.5.20 for contractions on `ℝ`; **Example 8.1.1**, **Exercises 8.1.9,
  8.1.10, 8.1.12, 8.1.13**: `h*` and `w*` increase with `c`; `h*` increases with `β`; `w*`
  increases with `β` when `c ≤ w̄`, under first order stochastic dominance and under
  mean-preserving spreads.
* **Exercise 8.1.11**: the mean first passage time to employment increases with `c`, since the
  first passage time is pathwise increasing in `w*`.

Exercise 8.1.8 is computational.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

variable {X : Type*} [MeasurableSpace X]

/-- (8.14): `g(h) = c + β ∫ max{w(x)/(1 − β), h} φ(dx)`. -/
noncomputable def gfun (φ : Measure X) (wage : X → ℝ) (c β h : ℝ) : ℝ :=
  c + β * ∫ x, max (wage x / (1 - β)) h ∂φ

theorem integrable_max_wage {φ : Measure X} [IsFiniteMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (β h : ℝ) : Integrable (fun x => max (wage x / (1 - β)) h) φ :=
  (hi.div_const _).sup (integrable_const h)

/-- **Exercise 8.1.6** (p. 251): by (8.15), `|g(h) − g(h')| ≤ β|h − h'|`. -/
theorem exercise_8_1_6 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (h h' : ℝ) :
    |gfun φ wage c β h - gfun φ wage c β h'| ≤ β * |h - h'| := by
  rw [gfun, gfun, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0,
    ← integral_sub (integrable_max_wage hi β h) (integrable_max_wage hi β h')]
  refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans ?_) hβ0
  calc ∫ x, |max (wage x / (1 - β)) h - max (wage x / (1 - β)) h'| ∂φ
      ≤ ∫ _, |h - h'| ∂φ := integral_mono
        ((integrable_max_wage hi β h).sub (integrable_max_wage hi β h')).abs
        (integrable_const _) fun x => by
          rw [max_comm _ h, max_comm _ h']
          exact abs_max_sub_max_le_abs _ _ _
    _ = |h - h'| := by simp

theorem gfun_contracting {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith ⟨β, hβ0⟩ (gfun φ wage c β) :=
  ⟨hβ1, LipschitzWith.of_dist_le_mul fun h h' => by
    rw [Real.dist_eq, Real.dist_eq]
    exact exercise_8_1_6 hi c hβ0 h h'⟩

theorem gfun_mono {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) : Monotone (gfun φ wage c β) :=
  fun h h' hh => add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (integrable_max_wage hi β h) (integrable_max_wage hi β h') fun _ => max_le_max le_rfl hh) hβ0)

/-- The optimal continuation value `h*`, the unique fixed point of `g`. -/
noncomputable def hstar (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ℝ :=
  ContractingWith.fixedPoint _ (gfun_contracting hi c hβ0 hβ1)

theorem hstar_eq (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    gfun φ wage c β (hstar φ hi c hβ0 hβ1) = hstar φ hi c hβ0 hβ1 :=
  ContractingWith.fixedPoint_isFixedPt _

theorem hstar_unique (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {h : ℝ}
    (hh : gfun φ wage c β h = h) : h = hstar φ hi c hβ0 hβ1 :=
  ContractingWith.fixedPoint_unique _ hh

/-- The reservation wage `w* = (1 − β)h*` (8.13). -/
noncomputable def wstar (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ℝ :=
  (1 - β) * hstar φ hi c hβ0 hβ1

/-- **Exercise 8.1.7** (p. 251): with nonnegative wages and `c ≥ 0`, `g` maps `[0, K]` into
itself, `K = (c + β w̄/(1 − β))/(1 − β)`. -/
theorem exercise_8_1_7 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (hw : ∀ x, 0 ≤ wage x) {c : ℝ} (hc : 0 ≤ c) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    MapsTo (gfun φ wage c β) (Icc 0 ((c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β)))
      (Icc 0 ((c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β))) := by
  intro h hh
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  have hI : ∫ x, wage x / (1 - β) ∂φ = (∫ x, wage x ∂φ) / (1 - β) := integral_div _ _
  have hw0 : 0 ≤ ∫ x, wage x ∂φ := integral_nonneg hw
  have hlow : (∫ x, wage x ∂φ) / (1 - β) ≤ ∫ x, max (wage x / (1 - β)) h ∂φ := by
    rw [← hI]
    exact integral_mono (hi.div_const _) (integrable_max_wage hi β h) fun _ => le_max_left _ _
  have hup : ∫ x, max (wage x / (1 - β)) h ∂φ ≤ (∫ x, wage x ∂φ) / (1 - β) + h := by
    have h1 : ∫ x, max (wage x / (1 - β)) h ∂φ ≤ ∫ x, (wage x / (1 - β) + h) ∂φ :=
      integral_mono (integrable_max_wage hi β h) ((hi.div_const _).add (integrable_const h))
        fun x => max_le (le_add_of_nonneg_right hh.1)
          (le_add_of_nonneg_left (div_nonneg (hw x) hpos.le))
    rw [integral_add (hi.div_const _) (integrable_const h), hI] at h1
    simpa using h1
  constructor
  · exact add_nonneg hc (mul_nonneg hβ0 ((div_nonneg hw0 hpos.le).trans hlow))
  · have hK : (c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β) * (1 - β) =
        c + β * (∫ x, wage x ∂φ) / (1 - β) := div_mul_cancel₀ _ hpos.ne'
    have h2 := mul_le_mul_of_nonneg_left hup hβ0
    have h3 := mul_le_mul_of_nonneg_left hh.2 hβ0
    change c + β * ∫ x, max (wage x / (1 - β)) h ∂φ ≤ _
    have : β * ((∫ x, wage x ∂φ) / (1 - β)) = β * (∫ x, wage x ∂φ) / (1 - β) := by ring
    nlinarith

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

/-- §8.1.2.1 (pp. 250–251): in the iid model, the value function satisfies `v* = max{e, h*}`
almost everywhere with `h* = c + β ∫ v* dφ` the fixed point of `g`, and the policy (8.12)
accepting when `w/(1 − β) ≥ h*`, i.e. `w ≥ w* = (1 − β)h*` (8.13), is optimal. -/
theorem section_8_1_2_1 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ hw : (iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed, ∃ vstar,
      (iid φ wage hm hi c β hβ0 hβ1).adp.IsValueFunction vstar ∧
      hstar φ hi c hβ0 hβ1 = c + β * ∫ x, vstar x ∂φ ∧
      ⇑vstar =ᵐ[φ] (fun x => max (wage x / (1 - β)) (hstar φ hi c hβ0 hβ1)) ∧
      (iid φ wage hm hi c β hβ0 hβ1).adp.IsOptimal hw
        (acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => hstar φ hi c hβ0 hβ1)
          (hm.div_const _) measurable_const) := by
  set M := iid φ wage hm hi c β hβ0 hβ1
  obtain ⟨hw, hFO, -⟩ := proposition_8_1_1 φ wage hm hi c β hβ0 hβ1
  obtain ⟨vstar, -, hv, -, hvG, hb⟩ := hFO.exists_vstar
  have hbell : M.adp.bellman vstar = vstar := (M.adp.solvesBellman_iff hvG).1 hb
  have hT := (exercise_8_1_2_3 φ wage hm hi c β hβ0 hβ1 vstar).2
  rw [hbell] at hT
  -- `h₀ = c + β ∫ v*` is a fixed point of `g`
  set h₀ := c + β * ∫ x, vstar x ∂φ
  have hfix : gfun φ wage c β h₀ = h₀ := by
    change c + β * ∫ x, max (wage x / (1 - β)) h₀ ∂φ = c + β * ∫ x, vstar x ∂φ
    rw [integral_congr_ae hT.symm]
  have hh₀ : h₀ = hstar φ hi c hβ0 hβ1 := hstar_unique φ hi c hβ0 hβ1 hfix
  refine ⟨hw, vstar, hv, hh₀.symm, ?_, ?_⟩
  · rw [← hh₀]
    exact hT
  · -- the policy (8.12) is `v*`-greedy, hence optimal
    set σ := acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => hstar φ hi c hβ0 hβ1)
      (hm.div_const _) measurable_const
    have hTσ : M.adp.T σ vstar = M.adp.bellman vstar := by
      refine Lp.ext ?_
      filter_upwards [M.T_coeFn σ vstar, iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 vstar,
        (exercise_8_1_2_3 φ wage hm hi c β hβ0 hβ1 vstar).2] with x h1 h2 h3
      rw [h1, h2, h3]
      have h4 := acceptWhere_apply (s := fun x => wage x / (1 - β))
        (h := fun _ => hstar φ hi c hβ0 hβ1) (hm.div_const _) measurable_const x
      have e : c + β * ∫ y, vstar y ∂φ = hstar φ hi c hβ0 hβ1 := hh₀
      change (if σ.1 x then wage x / (1 - β) else c + β * ∫ y, vstar y ∂φ) = _
      rw [e]
      exact h4
    exact (hFO.2.2 σ).2 ⟨vstar, hv, ((M.adp.isGreedy_iff hvG σ).2 hTσ)⟩

end JobSearch

/-! ### The FDP perspective -/

namespace JobSearchFDP


/-- `e = w/(1 − β)` in `L¹(φ)`. -/
noncomputable def eL (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) : Lp ℝ 1 φ :=
  (memLp_one_iff_integrable.2 (hi.div_const (1 - β))).toLp fun x => wage x / (1 - β)

/-- `G_σ h = σe + (1 − σ)h`. -/
noncomputable def G (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) (σ : StopPolicy X) (h : ℝ) : Lp ℝ 1 φ :=
  L1.mulCLM φ (measurable_polInd σ) (abs_polInd_le σ) (eL φ wage hi β) +
    L1.mulCLM φ (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _)

theorem G_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) (σ : StopPolicy X) (h : ℝ) :
    ⇑(G φ wage hi β σ h) =ᵐ[φ]
      fun x => if σ.1 x then wage x / (1 - β) else h := by
  filter_upwards [Lp.coeFn_add (L1.mulCLM φ (measurable_polInd σ) (abs_polInd_le σ)
      (eL φ wage hi β))
      (L1.mulCLM φ (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _)),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (eL φ wage hi β),
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _),
    (memLp_one_iff_integrable.2 (hi.div_const (1 - β))).coeFn_toLp,
    (memLp_const (μ := φ) h).coeFn_toLp]
    with x h1 h2 h3 h4 h5
  rw [G, h1, Pi.add_apply, h2, h3]
  change polInd σ x * (eL φ wage hi β) x + polCont σ x * ((memLp_const h).toLp _) x = _
  rw [eL, h4, h5]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- The order-preserving FDP `(L¹(φ), F, ℝ, 𝔾)` of §8.1.2.2, `Fv = c + β ∫ v dφ`. -/
noncomputable def fdp (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) :
    FDP (Lp ℝ 1 φ) ℝ (StopPolicy X) where
  F v := c + β * ∫ x, v x ∂φ
  G := G φ wage hi β
  greatest h := ⟨acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => h)
    (hm.div_const _) measurable_const, fun τ => by
    rw [← Lp.coeFn_le]
    filter_upwards [G_coeFn φ wage hi β τ h, G_coeFn φ wage hi β _ h]
      with x h1 h2
    rw [h1, h2, acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _⟩
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem isOrderPreserving (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) :
    (fdp φ wage hm hi c β).IsOrderPreserving := by
  refine ⟨fun v w hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono_ae (L1.integrable_coeFn v) (L1.integrable_coeFn w)
      ((Lp.coeFn_le _ _).2 hvw)) hβ0), fun σ h h' hh => ?_⟩
  rw [← Lp.coeFn_le]
  filter_upwards [G_coeFn φ wage hi β σ h, G_coeFn φ wage hi β σ h']
    with x h1 h2
  change (G φ wage hi β σ h) x ≤ (G φ wage hi β σ h') x
  rw [h1, h2]
  split_ifs
  · exact le_rfl
  · exact hh

/-- `Gh = max{e, h}` almost everywhere. -/
theorem Gsup_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β h : ℝ) :
    ⇑((fdp φ wage hm hi c β).Gsup h) =ᵐ[φ] fun x => max (wage x / (1 - β)) h := by
  set σ := acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => h)
    (hm.div_const _) measurable_const
  have hσ : (fdp φ wage hm hi c β).Gsup h = G φ wage hi β σ h := by
    refine le_antisymm ?_ ((fdp φ wage hm hi c β).G_le_Gsup σ h)
    have hg := (fdp φ wage hm hi c β).isGreatest_Gsup h
    obtain ⟨⟨τ, hτ⟩, -⟩ := hg
    rw [← hτ]
    rw [← Lp.coeFn_le]
    filter_upwards [G_coeFn φ wage hi β τ h, G_coeFn φ wage hi β σ h]
      with x h1 h2
    change (G φ wage hi β τ h) x ≤ (G φ wage hi β σ h) x
    rw [h1, h2, acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [hσ]
  filter_upwards [G_coeFn φ wage hi β σ h] with x hx
  rw [hx, acceptWhere_apply]

theorem ADP.ext_T {V P : Type*} [PartialOrder V] {A B : ADP V P} (h : A.T = B.T) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- §8.1.2.2 (pp. 252–253): the FDP `(L¹(φ), F, ℝ, 𝔾)` is order preserving, (i) its primary ADP
is the job search ADP `(L¹(φ), 𝕋)`, (ii) the Bellman operator of its subordinate ADP is `g` of
(8.14), (iii) by Theorem 5.2.13 the subordinate ADP has the fundamental optimality properties
with value function `h*`, and every `σ` with `G_σ h* = Gh*`, such as (8.16) at `h*`, is optimal
for the job search problem. -/
theorem section_8_1_2_2 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (fdp φ wage hm hi c β).primary (Or.inl (isOrderPreserving φ wage hm hi c hβ0)) =
        (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp ∧
      (∀ h, ((fdp φ wage hm hi c β).sub
        (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).bellman h =
          gfun φ wage c β h) ∧
      ∃ hw' : ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).WellPosed,
        ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).FundamentalOptimality hw' ∧
        ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).IsValueFunction
            (hstar φ hi c hβ0 hβ1) ∧
        ∀ hw : (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed, ∀ σ,
          G φ wage hi β σ (hstar φ hi c hβ0 hβ1) =
              (fdp φ wage hm hi c β).Gsup (hstar φ hi c hβ0 hβ1) →
            (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp.IsOptimal hw σ := by
  set M := JobSearch.iid φ wage hm hi c β hβ0 hβ1
  set D := fdp φ wage hm hi c β
  have hP := isOrderPreserving φ wage hm hi c hβ0
  have hprim : D.primary (Or.inl hP) = M.adp := by
    refine ADP.ext_T (funext fun σ => funext fun v => Lp.ext ?_)
    filter_upwards [G_coeFn φ wage hi β σ (c + β * ∫ x, v x ∂φ), M.T_coeFn σ v,
      JobSearch.iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 v] with x h1 h2 h3
    change (G φ wage hi β σ (c + β * ∫ x, v x ∂φ)) x = _
    rw [h1, h2, h3]
    rfl
  have hsubT : ∀ h, (D.sub (Or.inl hP)).bellman h = gfun φ wage c β h := fun h => by
    rw [(FDP.lemma_5_2_10 (Or.inl hP) hP).1]
    change c + β * ∫ x, (D.Gsup h) x ∂φ = c + β * ∫ x, max (wage x / (1 - β)) h ∂φ
    rw [integral_congr_ae (Gsup_coeFn φ wage hm hi c β h)]
  obtain ⟨hw, hFO, -⟩ := JobSearch.proposition_8_1_1 φ wage hm hi c β hβ0 hβ1
  have hwP : (D.primary (Or.inl hP)).WellPosed := by rw [hprim]; exact hw
  have hw' : (D.sub (Or.inl hP)).WellPosed := ((FDP.lemma_5_2_12 (Or.inl hP)).1).2 hwP
  have hFOP : (D.primary (Or.inl hP)).FundamentalOptimality hwP := by
    revert hwP
    rw [hprim]
    intro hwP
    exact hFO
  have h513 := FDP.theorem_5_2_13 (Or.inl hP) hP hwP hw'
  have hFO' := h513.1.1 hFOP
  -- the subordinate value function solves `g w = w`, so it is `h*`
  obtain ⟨w, hwv, hwG, hwb, -⟩ := hFO'.2.1
  have hwfix : gfun φ wage c β w = w := by
    rw [← hsubT]
    exact ((D.sub (Or.inl hP)).solvesBellman_iff hwG).1 hwb
  have hwh : w = hstar φ hi c hβ0 hβ1 := hstar_unique φ hi c hβ0 hβ1 hwfix
  rw [hwh] at hwv
  refine ⟨hprim, hsubT, hw', hFO', hwv, fun hw₀ σ hσ => ?_⟩
  have hopt := (h513.2 hFOP).2.1 _ σ hwv hσ
  revert hopt
  have : ∀ (A : ADP (Lp ℝ 1 φ) (StopPolicy X)) (h₁ : A.WellPosed) (h₂ : M.adp.WellPosed),
      A = M.adp → A.IsOptimal h₁ σ → M.adp.IsOptimal h₂ σ := by
    rintro A h₁ h₂ rfl hA
    exact hA
  exact this _ hwP hw₀ hprim

end JobSearchFDP

/-! ### Parametric monotonicity -/

/-- **Proposition A.5.20** (p. 380) for contractions: if `g₂` is an increasing contraction of a
complete space with a closed order, `g₁ ≤ g₂` pointwise and `g₁ h₁ = h₁`, then `h₁` lies below the
fixed point of `g₂`. -/
theorem fixedPoint_ge_of_le {V : Type*} [MetricSpace V] [CompleteSpace V] [Nonempty V]
    [PartialOrder V] [OrderClosedTopology V] {g₁ g₂ : V → V} {K : NNReal}
    (hg₂ : ContractingWith K g₂)
    (hmono : Monotone g₂) (hle : ∀ h, g₁ h ≤ g₂ h) {h₁ : V} (hh₁ : g₁ h₁ = h₁) :
    h₁ ≤ ContractingWith.fixedPoint g₂ hg₂ := by
  have hiter : ∀ n, h₁ ≤ g₂^[n] h₁ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc h₁ = g₁ h₁ := hh₁.symm
        _ ≤ g₂ h₁ := hle h₁
        _ ≤ g₂ (g₂^[n] h₁) := hmono ih
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint hg₂ h₁) hiter

/-- **Example 8.1.1** (p. 253) and **Exercise 8.1.9**, first part (p. 254): `h*` and the
reservation wage `w*` are increasing in unemployment compensation `c`. -/
theorem example_8_1_1 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    hstar φ hi c₁ hβ0 hβ1 ≤ hstar φ hi c₂ hβ0 hβ1 ∧
      wstar φ hi c₁ hβ0 hβ1 ≤ wstar φ hi c₂ hβ0 hβ1 := by
  have h := fixedPoint_ge_of_le (gfun_contracting hi c₂ hβ0 hβ1) (gfun_mono hi c₂ hβ0)
    (fun h => add_le_add hc le_rfl) (hstar_eq φ hi c₁ hβ0 hβ1)
  exact ⟨h, mul_le_mul_of_nonneg_left h (sub_nonneg.2 hβ1.le)⟩

/-- **Exercise 8.1.9**, second part (p. 254): with nonnegative wages, `h*` is increasing in
`β`. -/
theorem exercise_8_1_9 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (hw : ∀ x, 0 ≤ wage x) (c : ℝ) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁)
    (h12 : β₁ ≤ β₂) (h1 : β₂ < 1) :
    hstar φ hi c h0 (h12.trans_lt h1) ≤ hstar φ hi c (h0.trans h12) h1 := by
  refine fixedPoint_ge_of_le (gfun_contracting hi c (h0.trans h12) h1)
    (gfun_mono hi c (h0.trans h12)) (fun h => ?_) (hstar_eq φ hi c h0 (h12.trans_lt h1))
  have hp1 : 0 < 1 - β₁ := sub_pos.2 (h12.trans_lt h1)
  have hp2 : 0 < 1 - β₂ := sub_pos.2 h1
  have hint : ∀ x, max (wage x / (1 - β₁)) h ≤ max (wage x / (1 - β₂)) h := fun x =>
    max_le_max (div_le_div_of_nonneg_left (hw x) hp2 (by linarith)) le_rfl
  have hI0 : 0 ≤ ∫ x, max (wage x / (1 - β₁)) h ∂φ :=
    (integral_nonneg fun x => div_nonneg (hw x) hp1.le).trans
      (integral_mono (hi.div_const _) (integrable_max_wage hi β₁ h) fun _ => le_max_left _ _)
  have hmono := integral_mono (integrable_max_wage hi β₁ h) (integrable_max_wage hi β₂ h) hint
  change c + β₁ * ∫ x, max (wage x / (1 - β₁)) h ∂φ ≤ c + β₂ * ∫ x, max (wage x / (1 - β₂)) h ∂φ
  nlinarith

/-- (8.17): `f(w) = c(1 − β) + β ∫ max{w', w} φ(dw')`. -/
noncomputable def ffun (φ : Measure X) (wage : X → ℝ) (c β w : ℝ) : ℝ :=
  c * (1 - β) + β * ∫ x, max (wage x) w ∂φ

theorem ffun_contracting {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith ⟨β, hβ0⟩ (ffun φ wage c β) := by
  have hI : ∀ w, Integrable (fun x => max (wage x) w) φ := fun w => hi.sup (integrable_const w)
  refine ⟨hβ1, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, ffun, ffun, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg hβ0, ← integral_sub (hI w) (hI w')]
  refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans ?_) hβ0
  calc ∫ x, |max (wage x) w - max (wage x) w'| ∂φ
      ≤ ∫ _, |w - w'| ∂φ := integral_mono
        ((hI w).sub (hI w')).abs
        (integrable_const _) fun x => by
          rw [max_comm _ w, max_comm _ w']
          exact abs_max_sub_max_le_abs _ _ _
    _ = |w - w'| := by simp

theorem ffun_mono {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) : Monotone (ffun φ wage c β) :=
  fun w w' hww => add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (hi.sup (integrable_const w)) (hi.sup (integrable_const w')) fun _ =>
      max_le_max le_rfl hww) hβ0)

/-- The reservation wage is the fixed point of `f` in (8.17). -/
theorem wstar_eq_fixedPoint {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    wstar φ hi c hβ0 hβ1 = ContractingWith.fixedPoint _ (ffun_contracting hi c hβ0 hβ1) := by
  refine ContractingWith.fixedPoint_unique _ ?_
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  have hg := hstar_eq φ hi c hβ0 hβ1
  change c * (1 - β) + β * ∫ x, max (wage x) ((1 - β) * hstar φ hi c hβ0 hβ1) ∂φ =
    (1 - β) * hstar φ hi c hβ0 hβ1
  have hmax : ∀ x, max (wage x) ((1 - β) * hstar φ hi c hβ0 hβ1) =
      (1 - β) * max (wage x / (1 - β)) (hstar φ hi c hβ0 hβ1) := fun x => by
    rw [mul_max_of_nonneg _ _ hpos.le, mul_div_cancel₀ _ hpos.ne']
  simp_rw [hmax]
  rw [integral_const_mul]
  conv_rhs => rw [← hg]
  rw [gfun]
  ring

/-- **Exercise 8.1.10** (p. 254): if `c ≤ w̄ = ∫ w φ(dw)`, the reservation wage is increasing in
`β`. -/
theorem exercise_8_1_10 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {c : ℝ} (hc : c ≤ ∫ x, wage x ∂φ) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁)
    (h12 : β₁ ≤ β₂) (h1 : β₂ < 1) :
    wstar φ hi c h0 (h12.trans_lt h1) ≤ wstar φ hi c (h0.trans h12) h1 := by
  rw [wstar_eq_fixedPoint hi c (h0.trans h12) h1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ wage c β₁) (ffun_contracting hi c (h0.trans h12) h1)
    (ffun_mono hi c (h0.trans h12)) (fun w => ?_) ?_
  · have hI : c ≤ ∫ x, max (wage x) w ∂φ :=
      hc.trans (integral_mono hi (hi.sup (integrable_const w)) fun _ => le_max_left _ _)
    change c * (1 - β₁) + β₁ * ∫ x, max (wage x) w ∂φ ≤ c * (1 - β₂) + β₂ * ∫ x, max (wage x) w ∂φ
    nlinarith
  · rw [wstar_eq_fixedPoint hi c h0 (h12.trans_lt h1)]
    exact ContractingWith.fixedPoint_isFixedPt _

/-- First order stochastic dominance `φ ⪯_F ψ` (§A.5.5): `∫ u dφ ≤ ∫ u dψ` for every bounded,
increasing, measurable `u`. -/
def FOSDle (φ ψ : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → Measurable u → (∃ C, ∀ x, |u x| ≤ C) → ∫ x, u x ∂φ ≤ ∫ x, u x ∂ψ

/-- **Exercise 8.1.12** (p. 254): if `ψ` first order stochastically dominates `φ` and both are
supported on `[0, M]`, then `w*_φ ≤ w*_ψ`. -/
theorem exercise_8_1_12 {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ) {M : ℝ} (hφM : ∀ᵐ x ∂φ, x ∈ Icc 0 M)
    (hψM : ∀ᵐ x ∂ψ, x ∈ Icc 0 M) (hFOSD : FOSDle φ ψ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : wstar φ hiφ c hβ0 hβ1 ≤ wstar ψ hiψ c hβ0 hβ1 := by
  rw [wstar_eq_fixedPoint hiψ c hβ0 hβ1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ id c β) (ffun_contracting hiψ c hβ0 hβ1)
    (ffun_mono hiψ c hβ0) (fun w => ?_) ?_
  · -- clamp to `[0, M]`: a bounded increasing function equal to `max(·, w)` on the supports
    let u : ℝ → ℝ := fun x => max (max 0 (min x M)) w
    have hu : Monotone u := fun x y h => max_le_max (max_le_max le_rfl (min_le_min h le_rfl)) le_rfl
    have hum : Measurable u := (measurable_const.max (measurable_id.min measurable_const)).max
      measurable_const
    have hub : ∃ C, ∀ x, |u x| ≤ C := ⟨|M| + |w|, fun x => by
      simp only [u]
      rw [abs_le]
      constructor
      · have := le_max_right (max 0 (min x M)) w
        linarith [neg_abs_le w, abs_nonneg M]
      · refine max_le ?_ ?_
        · refine max_le (by positivity) ((min_le_right _ _).trans ?_)
          linarith [le_abs_self M, abs_nonneg w]
        · linarith [le_abs_self w, abs_nonneg M]⟩
    have heq : ∀ μ : Measure ℝ, (∀ᵐ x ∂μ, x ∈ Icc 0 M) →
        ∫ x, max (id x) w ∂μ = ∫ x, u x ∂μ := fun μ hμ => integral_congr_ae (by
      filter_upwards [hμ] with x hx
      simp only [id, u, min_eq_left hx.2, max_eq_right hx.1])
    change c * (1 - β) + β * ∫ x, max (id x) w ∂φ ≤ c * (1 - β) + β * ∫ x, max (id x) w ∂ψ
    rw [heq φ hφM, heq ψ hψM]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hFOSD u hu hum hub) hβ0)
  · rw [wstar_eq_fixedPoint hiφ c hβ0 hβ1]
    exact ContractingWith.fixedPoint_isFixedPt _

/-- `ψ` is a mean-preserving spread of `φ` (p. 391): there are random variables `W` and `Z` on a
probability space with `W ∼ φ`, `W + Z ∼ ψ` and `𝔼[Z | W] = 0`. -/
def IsMPS (ψ φ : Measure ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (W Z : Ω → ℝ), Measurable W ∧ Measurable Z ∧ Integrable W P ∧ Integrable Z P ∧
      P.map W = φ ∧ P.map (W + Z) = ψ ∧
      P[Z | MeasurableSpace.comap W inferInstance] =ᵐ[P] 0

/-- (8.18), by conditional expectations: if `ψ` is a mean-preserving spread of `φ`, then
`∫ max{w', w} φ(dw') ≤ ∫ max{w', w} ψ(dw')`. -/
theorem integral_max_le_of_isMPS {ψ φ : Measure ℝ} (h : IsMPS ψ φ) (w : ℝ) :
    ∫ x, max x w ∂φ ≤ ∫ x, max x w ∂ψ := by
  obtain ⟨Ω, mΩ, P, _, W, Z, hWm, hZm, hWi, hZi, hW, hWZ, hZ⟩ := h
  have hm : MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ) ≤ mΩ := hWm.comap_le
  have hmeas : Measurable fun x : ℝ => max x w := measurable_id.max measurable_const
  rw [← hW, ← hWZ, integral_map hWm.aemeasurable hmeas.aestronglyMeasurable,
    integral_map (hWm.add hZm).aemeasurable hmeas.aestronglyMeasurable]
  have hY : Integrable (fun ω => max ((W + Z) ω) w) P := (hWi.add hZi).sup (integrable_const w)
  -- `𝔼[max(W + Z, w) | W] ≥ max(W, w)`
  have hWst : StronglyMeasurable[MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ)] W :=
    (comap_measurable W).stronglyMeasurable
  have h1 : P[W + Z | MeasurableSpace.comap W inferInstance] =ᵐ[P] W := by
    filter_upwards [condExp_add hWi hZi (MeasurableSpace.comap W inferInstance), hZ]
      with ω h1 h2
    rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable hm hWst hWi, h2]
    simp
  have h2 : P[W + Z | MeasurableSpace.comap W inferInstance] ≤ᵐ[P]
      P[fun ω => max ((W + Z) ω) w | MeasurableSpace.comap W inferInstance] :=
    condExp_mono (hWi.add hZi) hY (Eventually.of_forall fun ω => le_max_left _ _)
  have h3 : P[fun _ => w | MeasurableSpace.comap W inferInstance] ≤ᵐ[P]
      P[fun ω => max ((W + Z) ω) w | MeasurableSpace.comap W inferInstance] :=
    condExp_mono (integrable_const w) hY (Eventually.of_forall fun ω => le_max_right _ _)
  rw [condExp_const hm] at h3
  rw [← integral_condExp hm (μ := P) (f := fun ω => max ((W + Z) ω) w)]
  refine integral_mono_ae (hWi.sup (integrable_const w)) integrable_condExp ?_
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1] at e2
  exact max_le e2 e3

/-- **Exercise 8.1.13** (p. 254): if `ψ` is a mean-preserving spread of `φ`, then
`w*_φ ≤ w*_ψ`. -/
theorem exercise_8_1_13 {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ) (hMPS : IsMPS ψ φ) (c : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : wstar φ hiφ c hβ0 hβ1 ≤ wstar ψ hiψ c hβ0 hβ1 := by
  rw [wstar_eq_fixedPoint hiψ c hβ0 hβ1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ id c β) (ffun_contracting hiψ c hβ0 hβ1)
    (ffun_mono hiψ c hβ0) (fun w => add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_max_le_of_isMPS hMPS w) hβ0)) ?_
  rw [wstar_eq_fixedPoint hiφ c hβ0 hβ1]
  exact ContractingWith.fixedPoint_isFixedPt _

/-- The optimal policy (8.16) accepts exactly the offers `w ≥ w* = (1 − β)h*`. -/
theorem accept_iff {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : X) :
    hstar φ hi c hβ0 hβ1 ≤ wage x / (1 - β) ↔ wstar φ hi c hβ0 hβ1 ≤ wage x := by
  rw [wstar, le_div_iff₀ (sub_pos.2 hβ1), mul_comm]

/-- The first passage time to employment `τ = inf{t ≥ 0 : σ*(W_t) = 1}` along an offer path `ω`,
when `σ*` accepts the offers `w(x) ≥ w*` (`⊤` if no offer is accepted). -/
noncomputable def firstPassage (wage : X → ℝ) (w : ℝ) (ω : ℕ → X) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : w ≤ wage (ω t)), (t : ℕ∞)

omit [MeasurableSpace X] in
theorem firstPassage_mono (wage : X → ℝ) {w₁ w₂ : ℝ} (h : w₁ ≤ w₂) (ω : ℕ → X) :
    firstPassage wage w₁ ω ≤ firstPassage wage w₂ ω :=
  iInf₂_mono' fun t ht => ⟨t, h.trans ht, le_rfl⟩

/-- **Exercise 8.1.11** (p. 254): with iid offers `W_t = w(ξ_t)`, `ξ_t ~ φ`, the mean first
passage time to employment `𝔼τ` is increasing in unemployment compensation `c`: `w*` increases
with `c` (Exercise 8.1.9), so `τ` does along every path. -/
theorem exercise_8_1_11 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    ∫⁻ ω, (firstPassage wage (wstar φ hi c₁ hβ0 hβ1) ω : ENNReal)
        ∂(Measure.infinitePi fun _ : ℕ => φ) ≤
      ∫⁻ ω, (firstPassage wage (wstar φ hi c₂ hβ0 hβ1) ω : ENNReal)
        ∂(Measure.infinitePi fun _ : ℕ => φ) :=
  lintegral_mono fun ω =>
    ENat.toENNReal_mono (firstPassage_mono wage (example_8_1_1 hi hβ0 hβ1 hc).2 ω)

end SargentStachurski.AdditionalApplications
