/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.ConsumptionSavings

/-!
# A consumption–savings problem: value, policy and the induction

SLP §5.17, Exercise 5.17b–h. From `ConsumptionSavings`, the optimal plan from `x ≥ 0` is the plan
of any multiplier `μ` with `Ξ(μ) = x` (`muOf`; all such plans coincide, `planN_eq`). On `ℝ₊`
define the value `v` (`vR`), the policy `g` (`gR`) and initial consumption `c₀ = I + x − g(x)/R`
(`cR`).

* `c₀` is continuous and strictly increasing from `c₀(0) = I` onto `[I, ∞)`.
* `v(z) ≤ v(x) + U'(c₀(x))(z − x)` (`vR_le_tangent`, from the summation-by-parts bound), and
  `U'(c₀)` is continuous, so `v` is differentiable on `ℝ₊` with `v'(x) = U'(I + x − g(x)/R)`
  (`hasDerivWithinAt_vR`). Since `v' > 0` and `v'` falls strictly, `v` is strictly increasing
  and strictly concave.

The book's induction runs over intervals `(m_{n−1}, m_n]`. Its objects are global here:
* `m₁` solves `U'(I + m₁) = RβU'(I)` (`m1`);
* `h(y) = Ξ(RβU'(c₀(y)))` (`hfun`) solves (2) for every `y > 0`;
* `m_{n+1} = h(m_n)`, with `m_n = Ξ((Rβ)ⁿU'(I)) → ∞` (`mSeq`).

Exercises 5.17b–h follow (`ex_5_17b` … `ex_5_17h`).

**Correction to 5.17h.** The book claims `g(x') − g(x) < x' − x`. That holds when `R ≤ 1`, but not
in general when `R > 1`. What does hold is `g(x') − g(x) < R(x' − x)`, i.e. consumption rises
strictly with wealth (`ex_5_17h_slope`). See `ConsumptionSavingsCounterexample`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {U U' : ℝ → ℝ} {β R I : ℝ}

/-! ### Plans from the same wealth coincide -/

theorem CSHyp.planN_eq (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) : planN h hν = planN h hμ := by
  have hW : wealthN h hν = wealthN h hμ := Subtype.ext hw.symm
  have hfeas : planN h hν ∈ Feasible (csΓ R I) (wealthN h hμ) := by
    rw [← hW]; exact h.planN_feasible hν
  refine (h.optimal_iff hμ hfeas).1 ?_
  rw [h.plan_total hν, ← h.vstar_eq hν, hW]

theorem CSHyp.planμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) (t : ℕ) :
    planμ U' β R I ν t = planμ U' β R I μ t :=
  congrArg Subtype.val (congrFun (h.planN_eq hμ hν hw) t)

theorem CSHyp.consμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) (t : ℕ) :
    consμ U' β R I ν t = consμ U' β R I μ t := by
  rw [← h.consOf_planN hν, ← h.consOf_planN hμ, h.planN_eq hμ hν hw]

theorem CSHyp.valμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) : valμ U U' β R I ν = valμ U U' β R I μ :=
  tsum_congr fun t => by rw [h.consμ_eq_of_wealth hμ hν hw t]

/-- `U'(cI(p)) = p` for `0 < p ≤ U'(I)`. -/
theorem CSHyp.U'_cI (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hpI : p ≤ U' I) :
    U' (cI U' I p) = p := by
  rcases eq_or_lt_of_le (h.cI_mem hp).1 with he | hgt
  · have := (h.cI_mem hp).2
    rw [← he] at this ⊢
    exact le_antisymm this hpI
  · exact h.cI_eq hp hgt

/-! ### Value, policy and consumption on `ℝ₊` -/

/-- A multiplier of wealth `x ≥ 0`: some `μ ∈ (0, U'(I)]` with `Ξ(μ) = x`. -/
noncomputable def muOf (h : CSHyp U U' β R I) (x : ℝ) : ℝ := by
  classical exact if hx : 0 ≤ x then Classical.choose (h.exists_wealth_eq hx) else U' I

theorem CSHyp.muOf_spec (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    0 < muOf h x ∧ muOf h x ≤ U' I ∧ wealth U' β R I (muOf h x) = x := by
  simp only [muOf, hx, ↓reduceDIte]
  exact Classical.choose_spec (h.exists_wealth_eq hx)

/-- The value function `v`. -/
noncomputable def vR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := valμ U U' β R I (muOf h x)

/-- The policy function `g`. -/
noncomputable def gR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := planμ U' β R I (muOf h x) 1

/-- Initial consumption `c₀(x) = I + x − g(x)/R`. -/
noncomputable def cR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := cI U' I (muOf h x)

theorem CSHyp.vR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    vR h (wealth U' β R I ν) = valμ U U' β R I ν := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  exact h.valμ_eq_of_wealth hν hμ hw.symm

theorem CSHyp.gR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    gR h (wealth U' β R I ν) = wealth U' β R I (ν / (R * β)) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  rw [gR, h.planμ_eq_of_wealth hν hμ hw.symm, planμ, pow_one]

theorem CSHyp.cR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    cR h (wealth U' β R I ν) = cI U' I ν := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  have := h.consμ_eq_of_wealth hν hμ hw.symm 0
  rwa [consμ_zero, consμ_zero] at this

/-- **`v = v*`** on `ℝ₊`. -/
theorem CSHyp.vstar_wealth (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    vstar (csΓ R I) (csF U R I) β ⟨x, hx⟩ = (vR h x : EReal) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  have : (⟨x, hx⟩ : CSWealth) = wealthN h hμ := Subtype.ext hw.symm
  rw [this, h.vstar_eq hμ]
  rfl

theorem CSHyp.cR_ge (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : I ≤ cR h x :=
  (h.cI_mem (h.muOf_spec hx).1).1

theorem CSHyp.cR_pos (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : 0 < cR h x :=
  h.hI.trans_le (h.cR_ge hx)

theorem CSHyp.gR_nonneg (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gR h x :=
  h.planμ_nonneg (h.muOf_spec hx).1 1

/-- `g(x) = R(I + x − c₀(x))`. -/
theorem CSHyp.gR_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    gR h x = R * (I + x - cR h x) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  rw [gR, h.planμ_succ hμ 0, planμ_zero, hw, consμ_zero]
  rfl

theorem CSHyp.cR_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    cR h x = I + x - gR h x / R := by
  rw [h.gR_eq hx, mul_div_cancel_left₀ _ h.hR.ne']
  ring

theorem CSHyp.cR_zero (h : CSHyp U U' β R I) : cR h 0 = I := by
  have hU := h.U'_pos h.hI
  have := h.cR_wealth hU
  rwa [h.wealth_of_ge le_rfl, h.cI_of_le le_rfl] at this

/-- Larger wealth has a smaller multiplier, below `U'(I)`. -/
theorem CSHyp.muOf_lt (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    muOf h x' < muOf h x ∧ muOf h x' < U' I := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  obtain ⟨hμ', -, hw'⟩ := h.muOf_spec (hx.trans hxx'.le)
  refine ⟨not_le.1 fun hle => ?_, h.lt_of_wealth_pos (by rw [hw']; linarith)⟩
  have := h.wealth_anti hμ hle
  rw [hw, hw'] at this
  linarith

theorem CSHyp.cR_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (cR h) (Ici 0) := by
  intro x hx x' _ hxx'
  obtain ⟨hlt, hltI⟩ := h.muOf_lt hx hxx'
  exact h.cI_strictAnti (h.muOf_spec (le_trans hx hxx'.le)).1 hlt hltI

/-- `c₀` maps `ℝ₊` onto `[I, ∞)`. -/
theorem CSHyp.cR_surj (h : CSHyp U U' β R I) {c : ℝ} (hc : I ≤ c) :
    ∃ x, 0 ≤ x ∧ cR h x = c := by
  have hp := h.U'_pos (h.hI.trans_le hc)
  exact ⟨_, h.wealth_nonneg hp, by rw [h.cR_wealth hp, h.cI_U' hc]⟩

theorem CSHyp.continuousWithinAt_cR (h : CSHyp U U' β R I) {x₀ : ℝ} (hx₀ : 0 ≤ x₀) :
    ContinuousWithinAt (cR h) (Ici 0) x₀ := by
  have hmono := h.cR_strictMono
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a I with haI | haI
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact haI.trans_le (h.cR_ge hx)
    · obtain ⟨x₁, hx₁, hc₁⟩ := h.cR_surj (c := (a + cR h x₀) / 2) (by linarith)
      have hx₁x₀ : x₁ < x₀ := (hmono.lt_iff_lt hx₁ hx₀).1 (by rw [hc₁]; linarith)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds hx₁x₀)]
        with x hx hxx
      have := hmono hx₁ hx hxx
      linarith
  · obtain ⟨x₂, hx₂, hc₂⟩ := h.cR_surj (c := (cR h x₀ + b) / 2) (by linarith [h.cR_ge hx₀])
    have hx₀x₂ : x₀ < x₂ := (hmono.lt_iff_lt hx₀ hx₂).1 (by rw [hc₂]; linarith)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hx₀x₂)] with x hx hxx
    have := hmono hx hx₂ hxx
    linarith

theorem CSHyp.continuousOn_cR (h : CSHyp U U' β R I) : ContinuousOn (cR h) (Ici 0) :=
  fun _ hx => h.continuousWithinAt_cR hx

theorem CSHyp.continuousOn_gR (h : CSHyp U U' β R I) : ContinuousOn (gR h) (Ici 0) := by
  refine ContinuousOn.congr (f := fun x => R * (I + x - cR h x)) ?_ fun x hx => h.gR_eq hx
  exact continuousOn_const.mul ((continuousOn_const.add continuousOn_id).sub h.continuousOn_cR)

/-- The marginal value `U'(c₀(x))` is continuous on `ℝ₊`. -/
theorem CSHyp.continuousOn_marg (h : CSHyp U U' β R I) :
    ContinuousOn (fun x => U' (cR h x)) (Ici 0) := fun _ hx =>
  (h.hU'c.continuousAt (Ioi_mem_nhds (h.cR_pos hx))).comp_continuousWithinAt
    (h.continuousWithinAt_cR hx)

/-! ### Differentiability, monotonicity and concavity of `v` -/

/-- **The supergradient inequality** `v(z) ≤ v(x) + U'(c₀(x))(z − x)`. -/
theorem CSHyp.vR_le_tangent (h : CSHyp U U' β R I) {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    vR h z ≤ vR h x + U' (cR h x) * (z - x) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  have := h.vstar_le_tangent hμ ⟨z, hz⟩
  rw [h.vstar_wealth hz, hw] at this
  exact EReal.coe_le_coe_iff.1 this

/-- `v` is differentiable on `ℝ₊` (one-sided at `0`) with `v'(x) = U'(c₀(x))`. -/
theorem CSHyp.hasDerivWithinAt_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (vR h) (U' (cR h x)) (Ici 0) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Tendsto (fun z => U' (cR h z)) (𝓝[Ici 0 \ {x}] x) (𝓝 (U' (cR h x))) :=
    (h.continuousOn_marg x hx).tendsto.mono_left (nhdsWithin_mono _ sdiff_subset)
  have hlo : Tendsto (fun z => min (U' (cR h z)) (U' (cR h x))) (𝓝[Ici 0 \ {x}] x)
      (𝓝 (U' (cR h x))) := by
    have := hs.min (tendsto_const_nhds (x := U' (cR h x)))
    rwa [min_self] at this
  have hhi : Tendsto (fun z => max (U' (cR h z)) (U' (cR h x))) (𝓝[Ici 0 \ {x}] x)
      (𝓝 (U' (cR h x))) := by
    have := hs.max (tendsto_const_nhds (x := U' (cR h x)))
    rwa [max_self] at this
  have hbd : ∀ z ∈ Ici (0 : ℝ) \ {x}, min (U' (cR h z)) (U' (cR h x)) ≤ slope (vR h) x z ∧
      slope (vR h) x z ≤ max (U' (cR h z)) (U' (cR h x)) := by
    rintro z ⟨hz, hzx⟩
    have hz1 := h.vR_le_tangent hx hz
    have hz2 := h.vR_le_tangent hz hx
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hzx with hlt | hgt
    · have hneg : z - x < 0 := sub_neg.2 hlt
      exact ⟨(min_le_right _ _).trans ((le_div_iff_of_neg hneg).2 (by linarith)),
        ((div_le_iff_of_neg hneg).2 (by linarith)).trans (le_max_left _ _)⟩
    · have hpos : 0 < z - x := sub_pos.2 hgt
      exact ⟨(min_le_left _ _).trans ((le_div_iff₀ hpos).2 (by linarith)),
        ((div_le_iff₀ hpos).2 (by linarith)).trans (le_max_right _ _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (eventually_nhdsWithin_of_forall fun z hz => (hbd z hz).1)
    (eventually_nhdsWithin_of_forall fun z hz => (hbd z hz).2)

theorem CSHyp.hasDerivAt_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (vR h) (U' (cR h x)) x :=
  (h.hasDerivWithinAt_vR hx.le).hasDerivAt (Ici_mem_nhds hx)

theorem CSHyp.deriv_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 < x) :
    deriv (vR h) x = U' (I + x - gR h x / R) := by
  rw [(h.hasDerivAt_vR hx).deriv, h.cR_eq hx.le]

theorem CSHyp.continuousOn_vR (h : CSHyp U U' β R I) : ContinuousOn (vR h) (Ici 0) :=
  fun _ hx => (h.hasDerivWithinAt_vR hx).continuousWithinAt

theorem CSHyp.vR_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (vR h) (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) h.continuousOn_vR fun x hx => by
    rw [interior_Ici] at hx
    rw [(h.hasDerivAt_vR hx).deriv]
    exact h.U'_pos (h.cR_pos hx.le)

theorem CSHyp.vR_strictConcave (h : CSHyp U U' β R I) : StrictConcaveOn ℝ (Ici 0) (vR h) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) h.continuousOn_vR ?_
  rw [interior_Ici]
  intro a ha b hb hab
  rw [(h.hasDerivAt_vR ha).deriv, (h.hasDerivAt_vR hb).deriv]
  exact h.U'_lt (h.cR_pos (le_of_lt ha)) (h.cR_strictMono (mem_Ici.2 (le_of_lt ha))
    (mem_Ici.2 (le_of_lt hb)) hab)

/-! ### Exercise 5.17b: the interval `[0, m₁]` -/

/-- `m₁`, defined by `U'(I + m₁) = RβU'(I)`. -/
noncomputable def m1 (U' : ℝ → ℝ) (β R I : ℝ) : ℝ := cI U' I (R * β * U' I) - I

theorem CSHyp.rhoU_pos (h : CSHyp U U' β R I) : 0 < R * β * U' I :=
  mul_pos h.rho_pos (h.U'_pos h.hI)

theorem CSHyp.rhoU_lt (h : CSHyp U U' β R I) : R * β * U' I < U' I := by
  have := h.U'_pos h.hI
  nlinarith [h.hRβ]

/-- **Exercise 5.17b.** `m₁ > 0` is well defined: it is the unique `m ≥ 0` with
`U'(I + m) = RβU'(I)`. -/
theorem ex_5_17b_m1 (h : CSHyp U U' β R I) :
    0 < m1 U' β R I ∧ U' (I + m1 U' β R I) = R * β * U' I ∧
      ∀ m, 0 ≤ m → U' (I + m) = R * β * U' I → m = m1 U' β R I := by
  have hgt := h.cI_gt h.rhoU_pos h.rhoU_lt
  have hU : U' (I + m1 U' β R I) = R * β * U' I := by
    rw [m1, add_sub_cancel]; exact h.cI_eq h.rhoU_pos hgt
  refine ⟨by simp only [m1]; linarith, hU, fun m hm hm' => ?_⟩
  have hpos : 0 < I + m := by linarith [h.hI]
  have hpos1 : 0 < I + m1 U' β R I := by simp only [m1]; linarith [h.hI]
  rcases lt_trichotomy m (m1 U' β R I) with hlt | heq | hgt'
  · have := h.U'_lt hpos (by linarith : I + m < I + m1 U' β R I); linarith
  · exact heq
  · have := h.U'_lt hpos1 (by linarith : I + m1 U' β R I < I + m); linarith

theorem CSHyp.m1_pos (h : CSHyp U U' β R I) : 0 < m1 U' β R I := (ex_5_17b_m1 h).1

theorem CSHyp.wealth_rhoU (h : CSHyp U U' β R I) :
    wealth U' β R I (R * β * U' I) = m1 U' β R I := by
  rw [h.wealth_shift h.rhoU_pos, mul_div_cancel_left₀ _ h.rho_pos.ne',
    h.wealth_of_ge le_rfl, mul_zero, add_zero]
  rfl

theorem CSHyp.muOf_ge (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) (hxm : x ≤ m1 U' β R I) :
    R * β * U' I ≤ muOf h x := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  refine not_lt.1 fun hlt => ?_
  have := h.wealth_strictAnti hμ hlt (hlt.trans h.rhoU_lt)
  rw [hw, h.wealth_rhoU] at this
  linarith

theorem CSHyp.gR_eq_zero (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x)
    (hxm : x ≤ m1 U' β R I) : gR h x = 0 := by
  have := h.muOf_ge hx hxm
  rw [gR, planμ, pow_one]
  exact h.wealth_of_ge ((le_div_iff₀ h.rho_pos).2 (by linarith))

theorem CSHyp.gR_pos (h : CSHyp U U' β R I) {x : ℝ} (hxm : m1 U' β R I < x) : 0 < gR h x := by
  have hx : 0 ≤ x := h.m1_pos.le.trans hxm.le
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hlt : muOf h x / (R * β) < U' I := by
    refine not_le.1 fun hle => ?_
    have h1 : R * β * U' I ≤ muOf h x := by
      have := (le_div_iff₀ h.rho_pos).1 hle; linarith
    have h2 := h.cI_anti h.rhoU_pos h1
    have h3 := h.cR_eq hx
    rw [show gR h x = 0 by rw [gR, planμ, pow_one]; exact h.wealth_of_ge hle, zero_div,
      sub_zero] at h3
    have : cR h x ≤ I + m1 U' β R I := by simp only [m1, cR]; linarith
    linarith
  rw [gR, planμ, pow_one]
  exact h.wealth_pos (div_pos hμ h.rho_pos) hlt

/-- On `[0, m₁]`, `v(x) = U(I + x) + βU(I)/(1 − β)`. -/
theorem CSHyp.vR_eq_low (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) (hxm : x ≤ m1 U' β R I) :
    vR h x = U (I + x) + β * U I / (1 - β) := by
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hge := h.muOf_ge hx hxm
  have hc0 : consμ U' β R I (muOf h x) 0 = I + x := by
    rw [consμ_zero, ← cR, h.cR_eq hx, h.gR_eq_zero hx hxm, zero_div, sub_zero]
  have hct : ∀ t : ℕ, consμ U' β R I (muOf h x) (t + 1) = I := fun t => by
    refine h.cI_of_le ?_
    have h1 : U' I ≤ muOf h x / (R * β) := (le_div_iff₀ h.rho_pos).2 (by linarith)
    refine h1.trans ?_
    rw [div_pow_succ]
    exact le_div_self (div_pos hμ h.rho_pos).le (pow_pos h.rho_pos t)
      (pow_le_one₀ h.rho_pos.le h.hRβ.le) |>.trans (le_of_eq (by
        rw [div_div, div_div, mul_comm]))
  rw [vR, valμ, (h.summable_val hμ).tsum_eq_zero_add, pow_zero, one_mul, hc0]
  have e : ∀ t : ℕ, β ^ (t + 1) * U (consμ U' β R I (muOf h x) (t + 1)) = β * U I * β ^ t :=
    fun t => by rw [hct t, pow_succ]; ring
  rw [tsum_congr e, tsum_mul_left, tsum_geometric_of_lt_one h.hβ0.le h.hβ1]
  ring

/-- **Exercise 5.17b.** On `[0, m₁]`: `g = 0`, `v(x) = U(I + x) + βU(I)/(1 − β)`, `v` is
continuous, strictly increasing and strictly concave, and `v'(x) = U'(I + x)` (one-sided at
`0`). -/
theorem ex_5_17b (h : CSHyp U U' β R I) :
    (∀ x ∈ Icc 0 (m1 U' β R I), gR h x = 0 ∧ vR h x = U (I + x) + β * U I / (1 - β) ∧
      HasDerivWithinAt (vR h) (U' (I + x)) (Ici 0) x) ∧
    ContinuousOn (vR h) (Icc 0 (m1 U' β R I)) ∧ StrictMonoOn (vR h) (Icc 0 (m1 U' β R I)) ∧
      StrictConcaveOn ℝ (Icc 0 (m1 U' β R I)) (vR h) := by
  have hsub : Icc 0 (m1 U' β R I) ⊆ Ici 0 := Icc_subset_Ici_self
  refine ⟨fun x hx => ⟨h.gR_eq_zero hx.1 hx.2, h.vR_eq_low hx.1 hx.2, ?_⟩,
    h.continuousOn_vR.mono hsub, h.vR_strictMono.mono hsub,
    h.vR_strictConcave.subset hsub (convex_Icc _ _)⟩
  have := h.hasDerivWithinAt_vR hx.1
  rwa [h.cR_eq hx.1, h.gR_eq_zero hx.1 hx.2, zero_div, sub_zero] at this

/-! ### Exercise 5.17c: the function `h` -/

/-- `h(y) = Ξ(RβU'(c₀(y)))`: the wealth from which the consumer saves `y/R`. -/
noncomputable def hfun (h : CSHyp U U' β R I) (y : ℝ) : ℝ := wealth U' β R I (R * β * U' (cR h y))

/-- The marginal value `U'(c₀(y))` is the multiplier of `y`. -/
theorem CSHyp.U'_cR (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : U' (cR h y) = muOf h y :=
  h.U'_cI (h.muOf_spec hy).1 (h.muOf_spec hy).2.1

theorem CSHyp.gR_def (h : CSHyp U U' β R I) (x : ℝ) :
    gR h x = wealth U' β R I (muOf h x / (R * β)) := by
  rw [gR, planμ, pow_one]

theorem CSHyp.hfun_zero (h : CSHyp U U' β R I) : hfun h 0 = m1 U' β R I := by
  rw [hfun, h.cR_zero, h.wealth_rhoU]

theorem CSHyp.hfun_nonneg (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ hfun h y :=
  h.wealth_nonneg (mul_pos h.rho_pos (h.U'_pos (h.cR_pos hy)))

/-- `g(h(y)) = y`. -/
theorem CSHyp.gR_hfun (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : gR h (hfun h y) = y := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hy
  rw [hfun, h.U'_cR hy, h.gR_wealth (mul_pos h.rho_pos hμ),
    mul_div_cancel_left₀ _ h.rho_pos.ne', hw]

/-- (2): `U'(I + h(y) − y/R) = RβU'(c₀(y))`. -/
theorem CSHyp.euler_hfun (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) :
    U' (I + hfun h y - y / R) = R * β * U' (cR h y) := by
  obtain ⟨hμ, hμI, -⟩ := h.muOf_spec hy
  have hρμ : 0 < R * β * muOf h y := mul_pos h.rho_pos hμ
  have hc := h.cR_eq (h.hfun_nonneg hy)
  rw [h.gR_hfun hy] at hc
  rw [← hc, hfun, h.U'_cR hy, h.cR_wealth hρμ, h.U'_cI hρμ]
  have := h.rhoU_lt
  have : R * β * muOf h y ≤ R * β * U' I := mul_le_mul_of_nonneg_left hμI h.rho_pos.le
  linarith

theorem CSHyp.hfun_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (hfun h) (Ici 0) := by
  intro y hy y' hy' hyy'
  obtain ⟨hlt, hltI⟩ := h.muOf_lt hy hyy'
  have hμ' := (h.muOf_spec hy').1
  rw [hfun, hfun, h.U'_cR hy, h.U'_cR hy']
  refine h.wealth_strictAnti (mul_pos h.rho_pos hμ')
    (mul_lt_mul_of_pos_left hlt h.rho_pos) ?_
  have := h.rhoU_lt
  have : R * β * muOf h y' < R * β * U' I := mul_lt_mul_of_pos_left hltI h.rho_pos
  linarith

theorem CSHyp.continuousOn_hfun (h : CSHyp U U' β R I) : ContinuousOn (hfun h) (Ici 0) :=
  fun y hy => by
    have hc : ContinuousWithinAt (fun x => R * β * U' (cR h x)) (Ici 0) y :=
      continuousWithinAt_const.mul (h.continuousOn_marg y hy)
    change ContinuousWithinAt (wealth U' β R I ∘ fun x => R * β * U' (cR h x)) (Ici 0) y
    exact ContinuousAt.comp_continuousWithinAt (g := wealth U' β R I)
      (h.continuousAt_wealth (mul_pos h.rho_pos (h.U'_pos (h.cR_pos hy)))) hc

/-- **Exercise 5.17c.** `h` is continuous and strictly increasing, `h(y) → m₁` as `y ↓ 0`, and
for `y > 0`, `h(y)` solves (2), `U'(I + h(y) − y/R) = Rβv'(y)`, and is the wealth from which the
consumer saves `y/R`. -/
theorem ex_5_17c (h : CSHyp U U' β R I) :
    ContinuousOn (hfun h) (Ici 0) ∧ StrictMonoOn (hfun h) (Ici 0) ∧
      Tendsto (hfun h) (𝓝[>] 0) (𝓝 (m1 U' β R I)) ∧
      ∀ y, 0 < y → U' (I + hfun h y - y / R) = R * β * deriv (vR h) y ∧ gR h (hfun h y) = y := by
  refine ⟨h.continuousOn_hfun, h.hfun_strictMono, ?_, fun y hy => ⟨?_, h.gR_hfun hy.le⟩⟩
  · have := (h.continuousOn_hfun 0 (mem_Ici.2 le_rfl)).tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
    rwa [h.hfun_zero] at this
  · rw [h.euler_hfun hy.le, (h.hasDerivAt_vR hy).deriv]

/-! ### Exercises 5.17d–e: the interval `(m₁, m₂]` -/

/-- `g` is nondecreasing on `ℝ₊`. -/
theorem CSHyp.gR_mono (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') :
    gR h x ≤ gR h x' := by
  rcases eq_or_lt_of_le hxx' with rfl | hlt
  · exact le_rfl
  · rw [h.gR_def, h.gR_def]
    exact h.wealth_anti (div_pos (h.muOf_spec (hx.trans hxx')).1 h.rho_pos)
      (div_le_div_of_nonneg_right (h.muOf_lt hx hlt).1.le h.rho_pos.le)

/-- `g` is strictly increasing on `[m₁, ∞)`. -/
theorem CSHyp.gR_strictMono (h : CSHyp U U' β R I) :
    StrictMonoOn (gR h) (Ici (m1 U' β R I)) := by
  intro x hx x' _ hxx'
  have hx0 : 0 ≤ x := h.m1_pos.le.trans hx
  have hpos := h.gR_pos (lt_of_le_of_lt hx hxx')
  rw [h.gR_def] at hpos
  rw [h.gR_def, h.gR_def]
  exact h.wealth_strictAnti (div_pos (h.muOf_spec (hx0.trans hxx'.le)).1 h.rho_pos)
    (div_lt_div_of_pos_right (h.muOf_lt hx0 hxx').1 h.rho_pos) (h.lt_of_wealth_pos hpos)

/-- `m₂ = h(m₁)`. -/
noncomputable def m2 (h : CSHyp U U' β R I) : ℝ := hfun h (m1 U' β R I)

/-- `v'(x) = U'(I + x − g(x)/R)` is continuous on `ℝ₊`. -/
theorem CSHyp.continuousOn_vR' (h : CSHyp U U' β R I) :
    ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ici 0) :=
  h.continuousOn_marg.congr fun x hx => by simp only [h.cR_eq hx]

/-- **Exercise 5.17d.** `m₂ > m₁`; on `[m₁, m₂]`, `g` is continuous (in particular at `m₁`)
and strictly increasing, and `v` is continuous, strictly increasing and strictly concave; on
`(m₁, m₂)`, `v` is continuously differentiable with `v'(x) = U'(I + x − g(x)/R)` (5). -/
theorem ex_5_17d (h : CSHyp U U' β R I) :
    m1 U' β R I < m2 h ∧ ContinuousOn (gR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictMonoOn (gR h) (Icc (m1 U' β R I) (m2 h)) ∧
      ContinuousOn (vR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictMonoOn (vR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictConcaveOn ℝ (Icc (m1 U' β R I) (m2 h)) (vR h) ∧
      (∀ x ∈ Ioo (m1 U' β R I) (m2 h), HasDerivAt (vR h) (U' (I + x - gR h x / R)) x) ∧
      ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ioo (m1 U' β R I) (m2 h)) := by
  have hm1 := h.m1_pos
  have hsub : Icc (m1 U' β R I) (m2 h) ⊆ Ici 0 := fun x hx => mem_Ici.2 (hm1.le.trans hx.1)
  refine ⟨?_, h.continuousOn_gR.mono hsub, h.gR_strictMono.mono fun x hx => hx.1,
    h.continuousOn_vR.mono hsub, h.vR_strictMono.mono hsub,
    h.vR_strictConcave.subset hsub (convex_Icc _ _), fun x hx => ?_,
    h.continuousOn_vR'.mono fun x hx => mem_Ici.2 (hm1.le.trans hx.1.le)⟩
  · have := h.hfun_strictMono (mem_Ici.2 le_rfl) (mem_Ici.2 hm1.le) hm1
    rwa [h.hfun_zero] at this
  · have := h.hasDerivAt_vR (hm1.trans hx.1)
    rwa [h.cR_eq (hm1.le.trans hx.1.le)] at this

/-- **Exercise 5.17e.** `v` and `v'` are continuous at `m₁`. -/
theorem ex_5_17e (h : CSHyp U U' β R I) :
    ContinuousAt (vR h) (m1 U' β R I) ∧ ContinuousAt (deriv (vR h)) (m1 U' β R I) := by
  have hm1 := h.m1_pos
  refine ⟨(h.hasDerivAt_vR hm1).continuousAt, ?_⟩
  have hev : (fun x => U' (cR h x)) =ᶠ[𝓝 (m1 U' β R I)] deriv (vR h) := by
    filter_upwards [lt_mem_nhds hm1] with x hx
    exact ((h.hasDerivAt_vR hx).deriv).symm
  exact ((h.continuousOn_marg _ (mem_Ici.2 hm1.le)).continuousAt (Ici_mem_nhds hm1)).congr hev

/-! ### Exercise 5.17f: the induction covers `ℝ₊` -/

/-- `m_n = Ξ((Rβ)ⁿU'(I))`: `m₀ = 0`, `m₁`, and `m_{n+1} = h(m_n)`. -/
noncomputable def mSeq (U' : ℝ → ℝ) (β R I : ℝ) (n : ℕ) : ℝ :=
  wealth U' β R I ((R * β) ^ n * U' I)

theorem CSHyp.mSeq_succ (h : CSHyp U U' β R I) (n : ℕ) :
    mSeq U' β R I (n + 1) = hfun h (mSeq U' β R I n) := by
  have hU := h.U'_pos h.hI
  have hp : 0 < (R * β) ^ n * U' I := mul_pos (pow_pos h.rho_pos n) hU
  have hpI : (R * β) ^ n * U' I ≤ U' I :=
    mul_le_of_le_one_left hU.le (pow_le_one₀ h.rho_pos.le h.hRβ.le)
  rw [mSeq, mSeq, hfun, h.cR_wealth hp, h.U'_cI hp hpI, pow_succ']
  ring_nf

theorem CSHyp.mSeq_strictMono (h : CSHyp U U' β R I) : StrictMono (mSeq U' β R I) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hU := h.U'_pos h.hI
  have hρn := pow_pos h.rho_pos n
  have hlt : (R * β) ^ (n + 1) * U' I < (R * β) ^ n * U' I := by
    rw [pow_succ]
    have : (R * β) ^ n * (R * β) < (R * β) ^ n := mul_lt_of_lt_one_right hρn h.hRβ
    exact mul_lt_mul_of_pos_right this hU
  refine h.wealth_strictAnti (mul_pos (pow_pos h.rho_pos _) hU) hlt ?_
  refine lt_of_lt_of_le hlt (mul_le_of_le_one_left hU.le (pow_le_one₀ h.rho_pos.le h.hRβ.le))

theorem CSHyp.tendsto_mSeq (h : CSHyp U U' β R I) :
    Tendsto (mSeq U' β R I) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun B => ?_
  have hU := h.U'_pos h.hI
  have hc : 0 < I + max B 0 := by linarith [h.hI, le_max_right B 0]
  have hUc := h.U'_pos hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hUc hU) h.hRβ
  refine ⟨n, fun m hm => ?_⟩
  have hp : 0 < (R * β) ^ n * U' I := mul_pos (pow_pos h.rho_pos n) hU
  have h1 : I + max B 0 ≤ cI U' I ((R * β) ^ n * U' I) :=
    h.le_cI hp (by rwa [lt_div_iff₀ hU] at hn)
  have h2 := h.wealth_ge hp
  have h3 := h.mSeq_strictMono.monotone hm
  simp only [mSeq] at h3 ⊢
  linarith [le_max_left B 0]

/-- **Exercise 5.17f.** The intervals `(m_n, m_{n+1}]` cover `ℝ₊` (`m₀ = 0`, `m_n ↑ ∞`), and on
all of `ℝ₊`: `g` is continuous, zero on `[0, m₁]` and strictly increasing on `[m₁, ∞)`; `h` is
continuous and strictly increasing; `v` is continuous, strictly increasing and strictly concave,
and continuously differentiable with `v'(x) = U'(I + x − g(x)/R)` (one-sided at `0`). -/
theorem ex_5_17f (h : CSHyp U U' β R I) :
    (mSeq U' β R I 0 = 0 ∧ mSeq U' β R I 1 = m1 U' β R I ∧
      (∀ n, mSeq U' β R I (n + 1) = hfun h (mSeq U' β R I n)) ∧ StrictMono (mSeq U' β R I) ∧
      Tendsto (mSeq U' β R I) atTop atTop) ∧
    (ContinuousOn (gR h) (Ici 0) ∧ (∀ x ∈ Icc 0 (m1 U' β R I), gR h x = 0) ∧
      StrictMonoOn (gR h) (Ici (m1 U' β R I))) ∧
    (ContinuousOn (hfun h) (Ici 0) ∧ StrictMonoOn (hfun h) (Ici 0)) ∧
    (ContinuousOn (vR h) (Ici 0) ∧ StrictMonoOn (vR h) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (vR h) ∧
      (∀ x, 0 ≤ x → HasDerivWithinAt (vR h) (U' (I + x - gR h x / R)) (Ici 0) x) ∧
      ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ici 0)) := by
  refine ⟨⟨?_, ?_, h.mSeq_succ, h.mSeq_strictMono, h.tendsto_mSeq⟩,
    ⟨h.continuousOn_gR, fun x hx => h.gR_eq_zero hx.1 hx.2, h.gR_strictMono⟩,
    ⟨h.continuousOn_hfun, h.hfun_strictMono⟩,
    ⟨h.continuousOn_vR, h.vR_strictMono, h.vR_strictConcave, fun x hx => ?_,
      h.continuousOn_vR'⟩⟩
  · rw [mSeq, pow_zero, one_mul, h.wealth_of_ge le_rfl]
  · rw [mSeq, pow_one, h.wealth_rhoU]
  · have := h.hasDerivWithinAt_vR hx
    rwa [h.cR_eq hx] at this

/-! ### Exercise 5.17g: `v` solves (1) and `v = v*` -/

/-- `v(x) = U(c₀(x)) + βv(g(x))`. -/
theorem CSHyp.vR_attained (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    vR h x = U (I + x - gR h x / R) + β * vR h (gR h x) := by
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hμρ : 0 < muOf h x / (R * β) := div_pos hμ h.rho_pos
  rw [← h.cR_eq hx, h.gR_def, h.vR_wealth hμρ, vR, valμ, valμ,
    (h.summable_val hμ).tsum_eq_zero_add, pow_zero, one_mul, consμ_zero, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun t => ?_
  have := consμ_tail (U' := U') (β := β) (R := R) (I := I) (muOf h x) 1 t
  rw [pow_one] at this
  rw [this, pow_succ]
  ring

/-- **Exercise 5.17g.** `v = v*`, and `v` satisfies (1): `v(x) ≥ U(I + x − y/R) + βv(y)` for
every `y ∈ [0, (I + x)R]`, with equality at `y = g(x) ∈ [0, (I + x)R]`. -/
theorem ex_5_17g (h : CSHyp U U' β R I) :
    (∀ x (hx : 0 ≤ x), vstar (csΓ R I) (csF U R I) β ⟨x, hx⟩ = (vR h x : EReal)) ∧
      ∀ x, 0 ≤ x →
        (∀ y, 0 ≤ y → y ≤ (I + x) * R → U (I + x - y / R) + β * vR h y ≤ vR h x) ∧
        0 ≤ gR h x ∧ gR h x ≤ (I + x) * R ∧
        vR h x = U (I + x - gR h x / R) + β * vR h (gR h x) := by
  refine ⟨fun x hx => h.vstar_wealth hx, fun x hx => ⟨fun y hy hyx => ?_, h.gR_nonneg hx, ?_,
    h.vR_attained hx⟩⟩
  · have hFE := theorem_4_2 h.hβ0.le h.assumption41 h.assumption42 ⟨x, hx⟩
    have hle := le_biSup (fun y' : CSWealth => ((csF U R I ⟨x, hx⟩ y' : ℝ) : EReal) +
      (β : EReal) * vstar (csΓ R I) (csF U R I) β y') (show (⟨y, hy⟩ : CSWealth) ∈ csΓ R I ⟨x, hx⟩
        from hyx)
    rw [← hFE, h.vstar_wealth hx, h.vstar_wealth hy] at hle
    have hc : 0 ≤ I + x - y / R := by
      have := (div_le_iff₀ h.hR).2 hyx
      linarith
    have hF : csF U R I ⟨x, hx⟩ ⟨y, hy⟩ = U (I + x - y / R) := by
      simp only [csF]
      rw [max_eq_left hc]
    rw [hF, ← EReal.coe_mul, ← EReal.coe_add] at hle
    exact EReal.coe_le_coe_iff.1 hle
  · rw [h.gR_eq hx]
    have := h.cR_pos hx
    nlinarith [h.hR]

/-! ### Exercise 5.17h: the optimal plan -/

theorem CSHyp.gR_planμ (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    gR h (planμ U' β R I μ t) = planμ U' β R I μ (t + 1) := by
  rw [planμ, h.gR_wealth (div_pos hμ (pow_pos h.rho_pos t)), planμ, div_pow_succ]

/-- **Exercise 5.17h.** From any `x₀ ≥ 0`, a feasible plan is optimal if and only if it follows
`x_{t+1} = g(x_t)`; so that plan is the unique optimal plan. -/
theorem ex_5_17h_plan (h : CSHyp U U' β R I) (x₀ : CSWealth) {xs : ℕ → CSWealth}
    (hxs : xs ∈ Feasible (csΓ R I) x₀) :
    total (csF U R I) β xs = vstar (csΓ R I) (csF U R I) β x₀ ↔
      ∀ t, (xs (t + 1)).1 = gR h (xs t).1 := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec x₀.2
  have hx₀ : x₀ = wealthN h hμ := Subtype.ext hw.symm
  have hxs' : xs ∈ Feasible (csΓ R I) (wealthN h hμ) := hx₀ ▸ hxs
  rw [show vstar (csΓ R I) (csF U R I) β x₀ = vstar (csΓ R I) (csF U R I) β (wealthN h hμ) from
    congrArg _ hx₀, h.optimal_iff hμ hxs']
  constructor
  · rintro rfl t
    exact (h.gR_planμ hμ t).symm
  · intro hg
    funext t
    refine Subtype.ext ?_
    induction t with
    | zero => rw [hxs.1]; exact hw.symm.trans (planμ_zero _).symm
    | succ t ih => rw [hg t, ih]; exact h.gR_planμ hμ t

/-- **Exercise 5.17h (corrected).** For `0 ≤ x < x'`: `0 ≤ g(x') − g(x) < R(x' − x)`, with
equality on the left only if `g(x) = g(x') = 0`. The book's sharper `g(x') − g(x) < x' − x` holds
when `R ≤ 1` (`ex_5_17h_slope_le_one`), but can fail when `R > 1`. -/
theorem ex_5_17h_slope (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    0 ≤ gR h x' - gR h x ∧ gR h x' - gR h x < R * (x' - x) ∧
      (gR h x' = gR h x → gR h x = 0 ∧ gR h x' = 0) := by
  have hx' : 0 ≤ x' := hx.trans hxx'.le
  refine ⟨sub_nonneg.2 (h.gR_mono hx hxx'.le), ?_, fun heq => ?_⟩
  · rw [h.gR_eq hx, h.gR_eq hx']
    have := h.cR_strictMono (mem_Ici.2 hx) (mem_Ici.2 hx') hxx'
    nlinarith [h.hR]
  · have h0 : gR h x' = 0 := by
      refine le_antisymm (not_lt.1 fun hpos => ?_) (h.gR_nonneg hx')
      rw [h.gR_def] at hpos
      have := h.wealth_strictAnti (div_pos (h.muOf_spec hx').1 h.rho_pos)
        (div_lt_div_of_pos_right (h.muOf_lt hx hxx').1 h.rho_pos) (h.lt_of_wealth_pos hpos)
      rw [← h.gR_def, ← h.gR_def] at this
      linarith
    exact ⟨heq ▸ h0, h0⟩

theorem ex_5_17h_slope_le_one (h : CSHyp U U' β R I) (hR1 : R ≤ 1) {x x' : ℝ} (hx : 0 ≤ x)
    (hxx' : x < x') : gR h x' - gR h x < x' - x := by
  have := (ex_5_17h_slope h hx hxx').2.1
  nlinarith

end StokeyLucasPrescott.DeterministicApplications
