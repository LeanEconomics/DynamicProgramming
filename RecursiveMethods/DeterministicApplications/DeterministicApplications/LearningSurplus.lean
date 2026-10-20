/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.LearningByDoing
import DeterministicApplications.OneSectorGrowth

/-!
# Learning by doing: the monopolist, the planner and the competitive industry

SLP §5.6, pp. 107–109, with the book's assumptions (`LBDModel`): `γ` is strictly decreasing and
convex with `γ(Q) → c ≥ 0`; inverse demand `φ` is strictly decreasing and differentiable, with
strictly decreasing marginal revenue, `φ(0) > γ(0) = c̄` and `φ(q̄) = c`.

* **Exercise 5.6a** (`ex_5_6a`): for the monopolist, `R(q) = qφ(q)`. The general results of
  `LearningByDoing` apply, and at each `Q` the output `q̃` that maximizes current profit is
  unique and interior, and every optimal output exceeds it.
* **Exercise 5.6b** (`ex_5_6b_surplus`, `ex_5_6b`): consumer surplus `S(q) = ∫₀^q φ` is strictly
  increasing, strictly concave and continuously differentiable; for the planner, `R = S`, the
  value `w` is unique, strictly increasing and at most `S(q̄)/(1 − β)`, and every efficient
  output exceeds the output maximizing current surplus.
* **Exercise 5.6c** (`ex_5_6c`, `competitive_path`): competitive output at `Q` solves
  `φ(q) = γ(Q)` (price equals unit cost), which is exactly the current-surplus maximizer; so the
  efficient output exceeds the competitive output at every `Q`. Along the competitive path
  output rises, the price `γ(Q_t)` falls, and the price converges to `c`.
* **Exercise 5.6d** (`ex_5_6d`): for a nonrenewable resource with stock `Q ∈ [0, Q̄]`, extraction
  `Q − y` and `Γ(Q) = [0, Q]`, the functional equation again has a unique bounded continuous
  solution, equal to the supremum function.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- The assumptions of SLP §5.6 on demand `φ` (with derivative `φ'`) and unit cost `γ`. -/
structure LBDModel (φ φ' γ : ℝ → ℝ) (c qbar β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  qbar_pos : 0 < qbar
  φ_cont : ContinuousOn φ (Ici 0)
  φ_deriv : ∀ q, 0 < q → HasDerivAt φ (φ' q) q
  φ'_cont : ContinuousOn φ' (Ici 0)
  φ_anti : StrictAntiOn φ (Ici 0)
  φ_nonneg : ∀ q, 0 ≤ q → 0 ≤ φ q
  mr_anti : StrictAntiOn (fun q => φ q + q * φ' q) (Icc 0 qbar)
  φ_zero : γ 0 < φ 0
  φ_qbar : φ qbar = c
  γ_cont : ContinuousOn γ (Ici 0)
  γ_anti : StrictAntiOn γ (Ici 0)
  γ_convex : ConvexOn ℝ (Ici 0) γ
  γ_lim : Tendsto γ atTop (𝓝 c)

variable {φ φ' γ : ℝ → ℝ} {c qbar β : ℝ}

/-- Unit cost stays above its limit: `γ(Q) > c`. -/
theorem LBDModel.c_lt_γ (h : LBDModel φ φ' γ c qbar β) {Q : ℝ} (hQ : 0 ≤ Q) : c < γ Q := by
  have hlt : γ (Q + 1) < γ Q := h.γ_anti (mem_Ici.2 hQ) (mem_Ici.2 (by linarith)) (by linarith)
  have hle : c ≤ γ (Q + 1) := by
    refine le_of_tendsto h.γ_lim (eventually_atTop.2 ⟨Q + 1, fun x hx => ?_⟩)
    exact h.γ_anti.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hx
  linarith

theorem LBDModel.c_nonneg (h : LBDModel φ φ' γ c qbar β) : 0 ≤ c := by
  rw [← h.φ_qbar]; exact h.φ_nonneg _ h.qbar_pos.le

/-- A decreasing differentiable function has a nonpositive derivative. -/
theorem LBDModel.φ'_nonpos (h : LBDModel φ φ' γ c qbar β) {q : ℝ} (hq : 0 < q) : φ' q ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 (h.φ_deriv q hq)).mono_left
    (nhdsWithin_mono (0 : ℝ) fun t (ht : t ∈ Ioi (0 : ℝ)) => ne_of_gt ht)
  refine le_of_tendsto hs ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have := h.φ_anti (mem_Ici.2 hq.le) (mem_Ici.2 (by linarith)) (by linarith : q < q + t)
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.le) (by linarith)

/-- Near `0`, demand exceeds the highest unit cost: some `q₀ ∈ (0, q̄]` has `φ > γ(0)` on
`[0, q₀]`. -/
theorem LBDModel.exists_small (h : LBDModel φ φ' γ c qbar β) :
    ∃ q₀ ∈ Ioc 0 qbar, ∀ q ∈ Icc 0 q₀, γ 0 < φ q := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
    (h.φ_cont 0 (mem_Ici.2 le_rfl)) (φ 0 - γ 0) (by linarith [h.φ_zero])
  refine ⟨min (δ / 2) qbar, ⟨lt_min (by linarith) h.qbar_pos, min_le_right _ _⟩,
    fun q hq => ?_⟩
  have := hball (mem_Ici.2 hq.1) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.1]
    exact hq.2.trans_lt ((min_le_left _ _).trans_lt (by linarith)))
  rw [Real.dist_eq] at this
  linarith [neg_abs_le (φ q - φ 0)]

/-! ### Exercise 5.6a: the monopolist -/

/-- The monopolist's problem satisfies the hypotheses of `LearningByDoing` with `R(q) = qφ(q)`. -/
theorem monopoly_hyp (h : LBDModel φ φ' γ c qbar β) :
    LBDHyp (fun q => q * φ q) γ qbar β := by
  obtain ⟨q₀, hq₀, hsmall⟩ := h.exists_small
  refine ⟨h.β_pos, h.β_lt, h.qbar_pos,
    continuousOn_id.mul (h.φ_cont.mono fun q hq => mem_Ici.2 hq.1), by simp, h.γ_cont,
    h.γ_anti, fun Q hQ => h.c_nonneg.trans (h.c_lt_γ hQ).le, ⟨q₀, hq₀, ?_⟩⟩
  exact mul_lt_mul_of_pos_left (hsmall q₀ ⟨hq₀.1.le, le_rfl⟩) hq₀.1

/-- **Exercise 5.6a.** There is a unique bounded continuous `v`; it is strictly increasing; and at
every `Q` the profit-maximizing output `q̃` is unique and interior, and every optimal output
exceeds it: `y* ∈ G(Q)` implies `y* − Q > q̃`. -/
theorem ex_5_6a (h : LBDModel φ φ' γ c qbar β) :
    (∃ v : ExpStock →ᵇ ℝ,
      bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) v = v ∧
      ∀ w, bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) w = w →
        w = v) ∧
    ∀ {v : ExpStock →ᵇ ℝ},
      bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) v = v →
      StrictMono v ∧ ∀ Q : ExpStock, ∃ qt ∈ Ioo 0 qbar,
        (∀ q ∈ Icc 0 qbar, q ≠ qt → q * φ q - q * γ Q.1 < qt * φ qt - qt * γ Q.1) ∧
        ∀ y ∈ argmax (obj (lbdF (fun q => q * φ q) γ) β v) (lbdΓ qbar) Q, qt < y.1 - Q.1 := by
  obtain ⟨v, hv, huniq, -⟩ := lbd_exists (monopoly_hyp h)
  refine ⟨⟨v, hv, huniq⟩, fun {v} hv => ⟨lbd_strictMono (monopoly_hyp h) hv, fun Q => ?_⟩⟩
  have hγQ := h.c_lt_γ Q.2.out
  have hγ0 : γ Q.1 ≤ γ 0 := lbd_γ_le (monopoly_hyp h) Q
  -- the current-profit maximizer
  obtain ⟨qt, hqt, -, hmax⟩ := unique_interior_max (ψ := fun q => q * φ q - q * γ Q.1)
    (ψ' := fun q => φ q + q * φ' q - γ Q.1) h.qbar_pos
    ((continuousOn_id.mul (h.φ_cont.mono fun q hq => mem_Ici.2 hq.1)).sub
      (continuousOn_id.mul continuousOn_const))
    (fun q hq => by
      have := ((hasDerivAt_id' q).mul (h.φ_deriv q hq.1)).sub
        ((hasDerivAt_id' q).mul_const (γ Q.1))
      convert this using 1; ring)
    (((h.φ_cont.mono fun q hq => mem_Ici.2 hq.1).add (continuousOn_id.mul
      (h.φ'_cont.mono fun q hq => mem_Ici.2 hq.1))).sub continuousOn_const)
    (fun a ha b hb hab => by have := h.mr_anti ha hb hab; simp only at this ⊢; linarith)
    (by simp only [zero_mul, add_zero]; linarith [h.φ_zero])
    (by
      have := h.φ'_nonpos h.qbar_pos
      have : qbar * φ' qbar ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.qbar_pos.le this
      simp only [h.φ_qbar]; linarith)
  refine ⟨qt, hqt, hmax, fun y hy => ?_⟩
  exact lbd_policy_exceeds (monopoly_hyp h) h.γ_convex hv hqt hmax
    ((hasDerivAt_id' qt).mul (h.φ_deriv qt hqt.1)) hy

/-! ### Exercise 5.6b: consumer surplus and the planner -/

/-- Consumer surplus `S(q) = ∫₀^q φ`. -/
noncomputable def surplus (φ : ℝ → ℝ) (q : ℝ) : ℝ := ∫ z in (0 : ℝ)..q, φ z

theorem surplus_hasDerivAt (h : LBDModel φ φ' γ c qbar β) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (surplus φ) (φ q) q :=
  intervalIntegral.integral_hasDerivAt_right
    ((h.φ_cont.mono fun z hz => by
      rw [uIcc_of_le hq.le] at hz; exact mem_Ici.2 hz.1).intervalIntegrable)
    ((h.φ_cont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi q hq)
    (h.φ_cont.continuousAt (Ici_mem_nhds hq))

theorem surplus_continuousOn (h : LBDModel φ φ' γ c qbar β) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (surplus φ) (Icc 0 b) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
    (a := 0) (b := b) (f := φ)
    ((h.φ_cont.mono fun z hz => by
      rw [uIcc_of_le hb] at hz; exact mem_Ici.2 hz.1).integrableOn_compact isCompact_uIcc)
  rwa [uIcc_of_le hb] at this

theorem surplus_continuousOn_Ici (h : LBDModel φ φ' γ c qbar β) :
    ContinuousOn (surplus φ) (Ici 0) := by
  intro q hq
  have h1 := surplus_continuousOn h (b := q + 1) (by linarith [hq.out])
  have hmem : Icc (0 : ℝ) (q + 1) ∈ 𝓝[Ici 0] q := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h1 q ⟨hq.out, by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Exercise 5.6b.** `S` is strictly increasing, strictly concave and continuously
differentiable (`S' = φ`, continuous). -/
theorem ex_5_6b_surplus (h : LBDModel φ φ' γ c qbar β) :
    StrictMonoOn (surplus φ) (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) (surplus φ) ∧
      (∀ q, 0 < q → HasDerivAt (surplus φ) (φ q) q) ∧ ContinuousOn φ (Ici 0) := by
  have hderiv : ∀ q ∈ interior (Ici (0 : ℝ)), deriv (surplus φ) q = φ q := fun q hq => by
    rw [interior_Ici] at hq
    exact (surplus_hasDerivAt h hq).deriv
  refine ⟨strictMonoOn_of_deriv_pos (convex_Ici 0) (surplus_continuousOn_Ici h)
    fun q hq => ?_, StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
    (surplus_continuousOn_Ici h) fun a ha b hb hab => ?_,
    fun q hq => surplus_hasDerivAt h hq, h.φ_cont⟩
  · rw [hderiv q hq]
    rw [interior_Ici] at hq
    have hq' : (0 : ℝ) < q := hq
    have := h.φ_anti (mem_Ici.2 hq'.le) (mem_Ici.2 (by linarith)) (by linarith : q < q + 1)
    linarith [h.φ_nonneg (q + 1) (by linarith)]
  · rw [hderiv a ha, hderiv b hb]
    rw [interior_Ici] at ha hb
    exact h.φ_anti (mem_Ici.2 (le_of_lt ha)) (mem_Ici.2 (le_of_lt hb)) hab

/-- The planner's problem satisfies the hypotheses of `LearningByDoing` with `R = S`. -/
theorem planner_hyp (h : LBDModel φ φ' γ c qbar β) : LBDHyp (surplus φ) γ qbar β := by
  obtain ⟨q₀, hq₀, hsmall⟩ := h.exists_small
  refine ⟨h.β_pos, h.β_lt, h.qbar_pos, surplus_continuousOn h h.qbar_pos.le,
    by simp [surplus], h.γ_cont, h.γ_anti, fun Q hQ => h.c_nonneg.trans (h.c_lt_γ hQ).le,
    ⟨q₀, hq₀, ?_⟩⟩
  -- the mean value theorem: `S(q₀) = φ(ξ)q₀` with `φ(ξ) > γ(0)`
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (surplus φ) φ hq₀.1
    (surplus_continuousOn h hq₀.1.le) fun x hx => surplus_hasDerivAt h hx.1
  have h0 : surplus φ 0 = 0 := by simp [surplus]
  rw [h0, sub_zero, sub_zero, eq_div_iff hq₀.1.ne'] at hslope
  rw [← hslope]
  have := hsmall ξ ⟨hξ.1.le, hξ.2.le⟩
  nlinarith [hq₀.1]

/-- A fixed point is bounded by `M/(1 − β)` when the return is bounded by `M`. -/
theorem lbd_value_le {R : ℝ → ℝ} (h : LBDHyp R γ qbar β) {v : ExpStock →ᵇ ℝ}
    (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v) {M : ℝ}
    (hM : ∀ p ∈ graph (lbdΓ qbar), lbdF R γ p ≤ M) (Q : ExpStock) :
    v Q ≤ M / (1 - β) := by
  have hbdd : BddAbove (range v) := ⟨‖v‖, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (v.norm_coe_le_norm x))⟩
  have hs : ∀ x, v x ≤ M + β * ⨆ z, v z := fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) v x
    rw [hv] at hval
    rw [hval]
    exact add_le_add (hM (x, y) hy) (mul_le_mul_of_nonneg_left (le_ciSup hbdd y) h.β_pos.le)
  have : Nonempty ExpStock := ⟨⟨0, mem_Ici.2 le_rfl⟩⟩
  have hsup : (⨆ z, v z) ≤ M + β * ⨆ z, v z := ciSup_le hs
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  rw [le_div_iff₀ h1β]
  have := le_ciSup hbdd Q
  nlinarith [h.β_pos]

/-- **Exercise 5.6b.** For the planner: `w` is unique, strictly increasing and at most
`S(q̄)/(1 − β)`; the current-surplus maximizer `q̃` is unique and interior, solves
`φ(q̃) = γ(Q)`, and every efficient output exceeds it. -/
theorem ex_5_6b (h : LBDModel φ φ' γ c qbar β) {w : ExpStock →ᵇ ℝ}
    (hw : bellman (lbd_assumption43 (planner_hyp h)) (lbd_assumption44 (planner_hyp h)) w = w) :
    StrictMono w ∧ (∀ Q, w Q ≤ surplus φ qbar / (1 - β)) ∧
      ∀ Q : ExpStock, ∃ qt ∈ Ioo 0 qbar, φ qt = γ Q.1 ∧
        (∀ q ∈ Icc 0 qbar, q ≠ qt →
          surplus φ q - q * γ Q.1 < surplus φ qt - qt * γ Q.1) ∧
        ∀ y ∈ argmax (obj (lbdF (surplus φ) γ) β w) (lbdΓ qbar) Q, qt < y.1 - Q.1 := by
  have hS := ex_5_6b_surplus h
  refine ⟨lbd_strictMono (planner_hyp h) hw, lbd_value_le (planner_hyp h) hw fun p hp => ?_,
    fun Q => ?_⟩
  · -- `S(q) − qγ(Q) ≤ S(q) ≤ S(q̄)`
    have hq : p.2.1 - p.1.1 ∈ Icc 0 qbar := ⟨sub_nonneg.2 hp.1, by linarith [hp.2]⟩
    have h1 := hS.1.monotoneOn (mem_Ici.2 hq.1) (mem_Ici.2 h.qbar_pos.le) hq.2
    have h2 : 0 ≤ (p.2.1 - p.1.1) * γ p.1.1 :=
      mul_nonneg hq.1 (h.c_nonneg.trans (h.c_lt_γ p.1.2.out).le)
    simp only [lbdF]
    linarith
  · have hγQ := h.c_lt_γ Q.2.out
    have hγ0 : γ Q.1 ≤ γ 0 := lbd_γ_le (planner_hyp h) Q
    obtain ⟨qt, hqt, hzero, hmax⟩ := unique_interior_max
      (ψ := fun q => surplus φ q - q * γ Q.1) (ψ' := fun q => φ q - γ Q.1) h.qbar_pos
      ((surplus_continuousOn h h.qbar_pos.le).sub (continuousOn_id.mul continuousOn_const))
      (fun q hq => by
        have := (surplus_hasDerivAt h hq.1).sub ((hasDerivAt_id' q).mul_const (γ Q.1))
        rwa [one_mul] at this)
      ((h.φ_cont.mono fun q hq => mem_Ici.2 hq.1).sub continuousOn_const)
      (fun a ha b hb hab => by
        have := h.φ_anti (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
        change φ b - γ Q.1 < φ a - γ Q.1
        linarith)
      (show 0 < φ 0 - γ Q.1 by linarith [h.φ_zero])
      (show φ qbar - γ Q.1 < 0 by rw [h.φ_qbar]; linarith)
    refine ⟨qt, hqt, sub_eq_zero.1 hzero, hmax, fun y hy => ?_⟩
    exact lbd_policy_exceeds (planner_hyp h) h.γ_convex hw hqt hmax
      (surplus_hasDerivAt h hqt.1) hy

/-! ### Exercise 5.6c: the competitive industry -/

/-- **Exercise 5.6c.** Competitive output at `Q` solves `φ(q) = γ(Q)`: price equals unit cost.
Every efficient output exceeds it, so competition produces too little. -/
theorem ex_5_6c (h : LBDModel φ φ' γ c qbar β) {w : ExpStock →ᵇ ℝ}
    (hw : bellman (lbd_assumption43 (planner_hyp h)) (lbd_assumption44 (planner_hyp h)) w = w)
    (Q : ExpStock) {qc : ℝ} (hqc0 : 0 ≤ qc) (hqc : φ qc = γ Q.1)
    {y : ExpStock} (hy : y ∈ argmax (obj (lbdF (surplus φ) γ) β w) (lbdΓ qbar) Q) :
    qc < y.1 - Q.1 := by
  obtain ⟨-, -, hQ⟩ := ex_5_6b h hw
  obtain ⟨qt, hqt, hφ, -, hexc⟩ := hQ Q
  have : qc = qt := h.φ_anti.injOn (mem_Ici.2 hqc0) (mem_Ici.2 hqt.1.le) (by rw [hqc, hφ])
  rw [this]
  exact hexc y hy

/-- Competitive output rises with experience. -/
theorem competitive_output_mono (h : LBDModel φ φ' γ c qbar β) {Q Q' q q' : ℝ} (hQ : 0 ≤ Q)
    (hQQ' : Q < Q') (hq : 0 ≤ q) (hq' : 0 ≤ q') (hφ : φ q = γ Q) (hφ' : φ q' = γ Q') :
    q < q' := by
  by_contra hle
  push Not at hle
  have h1 := h.φ_anti.antitoneOn (mem_Ici.2 hq') (mem_Ici.2 hq) hle
  have h2 := h.γ_anti (mem_Ici.2 hQ) (mem_Ici.2 (by linarith)) hQQ'
  linarith

/-- **Exercise 5.6c.** Along a competitive path `Q_{t+1} = Q_t + q_t` with `φ(q_t) = γ(Q_t)`,
output rises, the price `p_t = γ(Q_t)` falls, and the price converges to `c`. -/
theorem competitive_path (h : LBDModel φ φ' γ c qbar β) {Qs qs : ℕ → ℝ} (hQ0 : 0 ≤ Qs 0)
    (hstep : ∀ t, Qs (t + 1) = Qs t + qs t) (hq : ∀ t, 0 ≤ qs t)
    (hφ : ∀ t, φ (qs t) = γ (Qs t)) :
    StrictMono qs ∧ StrictAnti (fun t => γ (Qs t)) ∧
      Tendsto (fun t => γ (Qs t)) atTop (𝓝 c) := by
  have hQnn : ∀ t, 0 ≤ Qs t := fun t => by
    induction t with
    | zero => exact hQ0
    | succ t ih => rw [hstep]; linarith [hq t]
  -- output is positive, since `φ(0) > γ(0) ≥ γ(Q_t)`
  have hqpos : ∀ t, 0 < qs t := fun t => by
    refine lt_of_le_of_ne (hq t) fun he => ?_
    have h1 := hφ t
    rw [← he] at h1
    have h2 := h.γ_anti.antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 (hQnn t)) (hQnn t)
    linarith [h.φ_zero]
  have hQmono : StrictMono Qs := strictMono_nat_of_lt_succ fun t => by
    rw [hstep]; linarith [hqpos t]
  have hqmono : StrictMono qs := strictMono_nat_of_lt_succ fun t =>
    competitive_output_mono h (hQnn t) (hQmono (Nat.lt_succ_self t)) (hq t) (hq (t + 1))
      (hφ t) (hφ (t + 1))
  refine ⟨hqmono, fun s t hst => h.γ_anti (mem_Ici.2 (hQnn s)) (mem_Ici.2 (hQnn t))
    (hQmono hst), h.γ_lim.comp ?_⟩
  -- `Q_t ≥ Q_0 + t q_0 → ∞`
  have hlow : ∀ t : ℕ, Qs 0 + t * qs 0 ≤ Qs t := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hstep]
      have := (hqmono.monotone (Nat.zero_le t))
      push_cast
      linarith
  refine tendsto_atTop_mono hlow (tendsto_atTop_add_const_left _ _ ?_)
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (hqpos 0)

/-! ### Exercise 5.6d: a nonrenewable resource -/

/-- The resource problem: stock `Q ∈ [0, Q̄]`, `Γ(Q) = [0, Q]`, extraction `Q − y`, return
`S(Q − y) − (Q − y)γ(Q)`. -/
def resourceF (R γ : ℝ → ℝ) (Qbar : ℝ) (p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar) : ℝ :=
  R (p.1.1 - p.2.1) - (p.1.1 - p.2.1) * γ p.1.1

/-- `Γ(Q) = [0, Q]` on `[0, Q̄]` is the growth correspondence with `f = id`. -/
theorem resource_hyp {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Qbar) :
    GrowthHyp id id β Qbar :=
  ⟨hβ0, hβ1, continuousOn_id, strictMono_id.strictMonoOn _, continuousOn_id, rfl, hQ,
    fun _ hx => ⟨le_rfl, hx.2⟩, strictMono_id.strictMonoOn _⟩

/-- Assumption 4.4 for the resource problem. -/
theorem resource_assumption44 {R : ℝ → ℝ} {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hR : ContinuousOn R (Icc 0 Qbar)) (hγ : ContinuousOn γ (Icc 0 Qbar)) :
    Assumption44 (growthΓ id Qbar) (resourceF R γ Qbar) β := by
  have hq : ∀ p ∈ graph (growthΓ id Qbar), p.1.1 - p.2.1 ∈ Icc 0 Qbar := fun p hp =>
    ⟨sub_nonneg.2 hp, by linarith [p.1.2.2, p.2.2.1]⟩
  have hγc : Continuous fun p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar => γ p.1.1 :=
    hγ.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2
  have hqc : Continuous fun p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar => p.1.1 - p.2.1 :=
    (continuous_subtype_val.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ
  refine ⟨(hR.comp hqc.continuousOn hq).sub (hqc.mul hγc).continuousOn,
    ⟨B + Qbar * C, fun p hp => ?_⟩, hβ0, hβ1⟩
  have h1 := hB _ (hq p hp)
  have h2 := hC _ p.1.2
  rw [Real.norm_eq_abs] at h1 h2
  have hq' := hq p hp
  have h3 : |(p.1.1 - p.2.1) * γ p.1.1| ≤ Qbar * C := by
    rw [abs_mul, abs_of_nonneg hq'.1]
    exact mul_le_mul hq'.2 h2 (abs_nonneg _) (hq'.1.trans hq'.2)
  simp only [resourceF]
  exact (abs_sub _ _).trans (add_le_add h1 h3)

/-- **Exercise 5.6d.** For a nonrenewable resource the analysis carries over: with `R = S`
continuous and `γ` continuous on `[0, Q̄]`, there is a unique bounded continuous solution of
`w(Q) = max_{0 ≤ y ≤ Q} {S(Q − y) − (Q − y)γ(Q) + βw(y)}`, it is the supremum function, and the
policy correspondence is nonempty and u.h.c. -/
theorem ex_5_6d {R : ℝ → ℝ} {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Qbar)
    (hR : ContinuousOn R (Icc 0 Qbar)) (hγ : ContinuousOn γ (Icc 0 Qbar)) :
    ∃ w : Icc (0 : ℝ) Qbar →ᵇ ℝ,
      bellman (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
        (resource_assumption44 hβ0 hβ1 hR hγ) w = w ∧
      (∀ w', bellman (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
        (resource_assumption44 hβ0 hβ1 hR hγ) w' = w' → w' = w) ∧
      (fun x => (w x : EReal)) = vstar (growthΓ id Qbar) (curryF (resourceF R γ Qbar)) β ∧
      ∀ x, (argmax (obj (resourceF R γ Qbar) β w) (growthΓ id Qbar) x).Nonempty ∧
        IsUHC (argmax (obj (resourceF R γ Qbar) β w) (growthΓ id Qbar)) x := by
  have : Nonempty (Icc (0 : ℝ) Qbar) := ⟨⟨0, le_rfl, hQ.le⟩⟩
  obtain ⟨w, hw, huniq, -, hG⟩ := theorem_4_6 (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
    (resource_assumption44 hβ0 hβ1 hR hγ)
  exact ⟨w, hw, huniq, fixedPoint_eq_vstar _ _ hw, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

end StokeyLucasPrescott.DeterministicApplications
