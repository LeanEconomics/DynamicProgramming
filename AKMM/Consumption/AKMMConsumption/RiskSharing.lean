/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.CompleteMarkets
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Consumption under autarky and full insurance

AKMM, §11.2–11.2.1, (11.1)–(11.5) and footnote 1, pp. 288–290.

The event tree, the Arrow–Debreu equilibrium (`definition_13`) and the first-order condition
`βᵗπ(ωᵗ)u′(cᵢ) = λᵢp(ωᵗ)` (`eq_7_20`) come from AKMM Chapter 7 (`AKMM.Uncertainty`) on Miao's
`BPTree`. Here:

* **(11.1)** under autarky (perishable endowment, no trade) the household eats its income
  (`eq_11_1`); footnote 1's endowments (`footnote_1`).
* **(11.3)** in an Arrow–Debreu equilibrium with positive prices there are positive multipliers
  with `u′(cᵢ)/u′(cⱼ) = λᵢ/λⱼ` at every history (`eq_11_3`).
* **CRRA** (`u′(c) = c^{−σ}`): consumption ratios are constant (`rs_crra_ratio`), and **(11.4)**
  `cⱼ = λⱼ^{−1/σ}/(Σᵢ wᵢλᵢ^{−1/σ}) · C` with population weights `wᵢ` (`eq_11_4`); in equilibrium
  every household consumes a history-independent share of the aggregate endowment
  (`rs_crra_share_eqm`).
* **(11.5)** with `u′ᵢ(c) = c^{−σᵢ}` and two households, `λ₂c^{−σ₁} = λ₁(Y − c)^{−σ₂}` has exactly
  one root in `(0, Y)` (`eq_11_5`); when the endowment rises both consumptions rise and
  `σ₁Δlog c₁ = σ₂Δlog c₂`, so the less risk-averse household's consumption rises
  proportionally more (`rs_less_risk_averse_absorbs`).

Departures: the book's measure-one continuum of households is a finite set `ι` (the book itself
sums over `i = 1, …, I` before writing the integral); (11.4) is stated with arbitrary
nonnegative population weights, which covers the integral against any finitely supported
population. The claim about Figure 11.1 is proved as an exact discrete comparative static
(two endowment levels) instead of being read off the figure.
-/

namespace AKMM.Consumption

open Miao.CompleteMarkets AKMM.Uncertainty Filter Topology

/-! ### Autarky -/

/-- **AKMM, (11.1), p. 289.** Under autarky the budget is `c ≤ y` at every history (the endowment
is perishable and cannot be traded); with `u` strictly increasing, consumption `c = y` is the
unique maximiser of `u(c)` over the budget, history by history. -/
theorem eq_11_1 {u : ℝ → ℝ} (hu : StrictMono u) (y c : ℝ) (hc : c ≤ y) :
    u c ≤ u y ∧ (u c = u y → c = y) :=
  ⟨hu.monotone hc, fun h => hu.injective h⟩

/-- **AKMM, fn. 1, p. 289.** With `Y(ω_L) = 2`, `Y(ω_H) = 4`, `y₁(ω_L) = 2`, `y₂(ω_L) = 0`,
`y₁(ω_H) = 1`, `y₂(ω_H) = 3`: the endowments add up, the aggregate is larger in `H`, but type 1
has more in `L` and type 2 more in `H`. -/
theorem footnote_1 :
    let y₁ : Bool → ℝ := fun ω => if ω then 1 else 2
    let y₂ : Bool → ℝ := fun ω => if ω then 3 else 0
    let Y : Bool → ℝ := fun ω => if ω then 4 else 2
    (∀ ω, y₁ ω + y₂ ω = Y ω) ∧ Y false < Y true ∧ y₁ true < y₁ false ∧ y₂ false < y₂ true := by
  refine ⟨fun ω => ?_, ?_, ?_, ?_⟩ <;> (try cases ω) <;> norm_num

/-! ### Complete markets: (11.3) -/

variable {S : Type*} [Fintype S]

/-- **AKMM, (11.3), p. 289.** In an Arrow–Debreu equilibrium (`definition_13`) with positive
prices and `u′ > 0`, there are positive multipliers `λᵢ` (one per household, independent of the
history) such that `u′(cᵢ,ₜ(ωᵗ))/u′(cⱼ,ₜ(ωᵗ)) = λᵢ/λⱼ` at every history `ωᵗ`. -/
theorem eq_11_3 {ι : Type*} [Fintype ι] (T : BPTree S) {β : ℝ} (hβ : 0 < β) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) (hdu : ∀ c, 0 < c → 0 < du c)
    {p : List S → ℝ} {y c : ι → List S → ℝ} (heq : definition_13 T β u p y c)
    (hp : ∀ h, 0 < p h) :
    ∃ lam : ι → ℝ, (∀ i, 0 < lam i) ∧
      (∀ i h, β ^ h.length * T.pr h * du (c i h) = lam i * p h) ∧
      ∀ i j h, du (c i h) / du (c j h) = lam i / lam j := by
  choose lam hlam using fun i => eq_7_20 T hu (heq.1 i) hp
  have hpos : ∀ i, 0 < lam i := fun i => by
    have e := hlam i []
    simp only [List.length_nil, pow_zero, T.pr_nil, one_mul] at e
    have h1 := hdu _ ((heq.1 i).1 [])
    have h2 := hp []
    by_contra hn
    push Not at hn
    nlinarith
  exact ⟨lam, hpos, hlam, fun i j h =>
    cm_risk_sharing T hβ (hlam i) (hlam j) (fun h => (hdu _ ((heq.1 j).1 h)).ne') h⟩

/-! ### CRRA: constant consumption shares, (11.4) -/

/-- Inverting the CRRA first-order condition: if `c^{−σ} = λm` with `c, λ, m > 0`, then
`c = λ^{−1/σ}m^{−1/σ}`. -/
theorem rs_crra_invert {σ c lam m : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hlam : 0 < lam) (hm : 0 < m)
    (hfoc : c ^ (-σ) = lam * m) : c = lam ^ (-1 / σ) * m ^ (-1 / σ) := by
  have h1 : c = (c ^ (-σ)) ^ (-1 / σ) := by
    rw [← Real.rpow_mul hc.le]
    have : -σ * (-1 / σ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [h1, hfoc, Real.mul_rpow hlam.le hm.le]

/-- **AKMM, p. 290.** With CRRA marginal utility `u′(c) = c^{−σ}`, (11.3) gives a constant ratio
of consumptions: `cᵢ/cⱼ = (λᵢ/λⱼ)^{−1/σ}`. -/
theorem rs_crra_ratio {σ ci cj li lj : ℝ} (hσ : 0 < σ) (hci : 0 < ci) (hcj : 0 < cj)
    (hli : 0 < li) (hlj : 0 < lj) (h : ci ^ (-σ) / cj ^ (-σ) = li / lj) :
    ci / cj = (li / lj) ^ (-1 / σ) := by
  have hpos : 0 < cj ^ (-σ) := Real.rpow_pos_of_pos hcj _
  have hfoc : ci ^ (-σ) = li * (cj ^ (-σ) / lj) := by
    field_simp at h ⊢; linarith
  have hm : 0 < cj ^ (-σ) / lj := div_pos hpos hlj
  have e1 := rs_crra_invert hσ hci hli hm hfoc
  have hfj : cj ^ (-σ) = lj * (cj ^ (-σ) / lj) := by field_simp
  have e2 := rs_crra_invert hσ hcj hlj hm hfj
  have hmpos : 0 < (cj ^ (-σ) / lj) ^ (-1 / σ) := Real.rpow_pos_of_pos hm _
  generalize (cj ^ (-σ) / lj) ^ (-1 / σ) = M at e1 e2 hmpos
  rw [e1, e2, Real.div_rpow hli.le hlj.le]
  have : 0 < lj ^ (-1 / σ) := Real.rpow_pos_of_pos hlj _
  field_simp

/-- **AKMM, (11.4), p. 290.** CRRA first-order conditions `cᵢ^{−σ} = λᵢm` (a common history
factor `m > 0`) and population weights `wᵢ ≥ 0`, not all zero: individual consumption is
proportional to aggregate consumption `C = Σᵢ wᵢcᵢ`,
`cⱼ = λⱼ^{−1/σ}/(Σᵢ wᵢλᵢ^{−1/σ}) · C`. -/
theorem eq_11_4 {ι : Type*} [Fintype ι] {σ m : ℝ} (hσ : 0 < σ) (hm : 0 < m) {c lam w : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hlam : ∀ i, 0 < lam i) (hw : ∀ i, 0 ≤ w i) (hw0 : ∃ i, 0 < w i)
    (hfoc : ∀ i, c i ^ (-σ) = lam i * m) (j : ι) :
    c j = lam j ^ (-1 / σ) / (∑ i, w i * lam i ^ (-1 / σ)) * ∑ i, w i * c i := by
  have hci : ∀ i, c i = lam i ^ (-1 / σ) * m ^ (-1 / σ) := fun i =>
    rs_crra_invert hσ (hc i) (hlam i) hm (hfoc i)
  have hS : 0 < ∑ i, w i * lam i ^ (-1 / σ) := by
    obtain ⟨i₀, hi₀⟩ := hw0
    exact lt_of_lt_of_le (mul_pos hi₀ (Real.rpow_pos_of_pos (hlam i₀) _))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (Real.rpow_pos_of_pos (hlam i) _).le)
        (Finset.mem_univ i₀))
  have hsum : ∑ i, w i * c i = m ^ (-1 / σ) * ∑ i, w i * lam i ^ (-1 / σ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hci i]; ring
  rw [hsum, hci j, div_mul_eq_mul_div, eq_div_iff hS.ne']
  ring

/-- **AKMM, p. 290: "individual consumption is proportional to aggregate consumption … independent
of the realization of the individual endowment".** In an Arrow–Debreu equilibrium with positive
prices and CRRA marginal utility `u′(c) = c^{−σ}`, there are shares `θⱼ = λⱼ^{−1/σ}/Σᵢλᵢ^{−1/σ}`,
the same at every history, with `cⱼ,ₜ(ωᵗ) = θⱼ Yₜ(ωᵗ)`, `Y = Σᵢ yᵢ` the aggregate endowment. -/
theorem rs_crra_share_eqm {ι : Type*} [Fintype ι] [Nonempty ι] (T : BPTree S) {β σ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) {u : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-σ)) c)
    {p : List S → ℝ} {y c : ι → List S → ℝ} (heq : definition_13 T β u p y c)
    (hp : ∀ h, 0 < p h) :
    ∃ θ : ι → ℝ, (∀ j, 0 < θ j) ∧ ∑ j, θ j = 1 ∧ ∀ j h, c j h = θ j * ∑ i, y i h := by
  obtain ⟨lam, hlam, hfoc, -⟩ := eq_11_3 T hβ hu (fun c hc => Real.rpow_pos_of_pos hc _) heq hp
  set D := ∑ i, lam i ^ (-1 / σ) with hD
  have hDpos : 0 < D := Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hlam i) _)
    Finset.univ_nonempty
  refine ⟨fun j => lam j ^ (-1 / σ) / D, fun j => div_pos (Real.rpow_pos_of_pos (hlam j) _) hDpos,
    ?_, fun j h => ?_⟩
  · rw [← Finset.sum_div, ← hD, div_self hDpos.ne']
  · have hb : 0 < β ^ h.length * T.pr h := mul_pos (pow_pos hβ _) (T.pr_pos h)
    have hm : 0 < p h / (β ^ h.length * T.pr h) := div_pos (hp h) hb
    have hf : ∀ i, c i h ^ (-σ) = lam i * (p h / (β ^ h.length * T.pr h)) := fun i => by
      have := hfoc i h
      rw [← mul_div_assoc, eq_div_iff hb.ne', ← this]
      ring
    have e := eq_11_4 hσ hm (fun i => (heq.1 i).1 h) hlam (fun _ => zero_le_one)
      ⟨Classical.arbitrary ι, one_pos⟩ hf j
    simp only [one_mul] at e
    rw [e, heq.2 h]

/-! ### Heterogeneous risk aversion: (11.5) -/

/-- The left side `λ₂c^{−σ₁}` of (11.5) is strictly decreasing on `(0, ∞)`. -/
theorem rs_lhs_strictAnti {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) :
    StrictAntiOn (fun c : ℝ => lam * c ^ (-σ)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy (by linarith)) hlam

/-- **AKMM, (11.5), p. 290: the two curves cross only once.** With `u′ᵢ(c) = c^{−σᵢ}`
(`σᵢ > 0`), positive multipliers and aggregate endowment `Y > 0`, the equation
`λ₂c^{−σ₁} = λ₁(Y − c)^{−σ₂}` has exactly one root `c₁ ∈ (0, Y)`. -/
theorem eq_11_5 {σ₁ σ₂ l₁ l₂ Y : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (hY : 0 < Y) :
    ∃! c, c ∈ Set.Ioo 0 Y ∧ l₂ * c ^ (-σ₁) = l₁ * (Y - c) ^ (-σ₂) := by
  set f : ℝ → ℝ := fun c => l₂ * c ^ (-σ₁) - l₁ * (Y - c) ^ (-σ₂) with hf
  have hanti : StrictAntiOn f (Set.Ioo 0 Y) := by
    intro x hx y hy hxy
    have h1 := rs_lhs_strictAnti hσ₁ hl₂ hx.1 hy.1 hxy
    have h2 : l₁ * (Y - x) ^ (-σ₂) < l₁ * (Y - y) ^ (-σ₂) :=
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg (by linarith [hy.2]) (by linarith)
        (by linarith)) hl₁
    simp only [hf]
    linarith
  have hcont : ContinuousOn f (Set.Ioo 0 Y) := by
    refine ContinuousOn.sub (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
    · exact continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne'
    · exact (continuousOn_const.sub continuousOn_id).rpow_const fun x hx =>
        Or.inl (sub_pos.2 hx.2).ne'
  -- `f → +∞` at `0⁺` and `f → −∞` at `Y⁻`
  have hlim0 : Tendsto f (𝓝[>] 0) atTop := by
    have hA : Tendsto (fun c : ℝ => l₂ * c ^ (-σ₁)) (𝓝[>] 0) atTop :=
      (tendsto_rpow_neg_nhdsGT_zero (by linarith : -σ₁ < 0)).const_mul_atTop hl₂
    have hcY : ContinuousAt (fun c : ℝ => (Y - c) ^ (-σ₂)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left
      simp [hY.ne']
    have hB : Tendsto (fun c : ℝ => l₁ * (Y - c) ^ (-σ₂)) (𝓝[>] 0)
        (𝓝 (l₁ * (Y - 0) ^ (-σ₂))) :=
      (hcY.const_mul l₁).tendsto.mono_left nhdsWithin_le_nhds
    exact (hA.atTop_add hB.neg).congr fun c => by simp only [hf]; ring
  have hlimY : Tendsto f (𝓝[<] Y) atBot := by
    have hsub : Tendsto (fun c : ℝ => Y - c) (𝓝[<] Y) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun c : ℝ => Y - c) (𝓝 Y) (𝓝 (Y - Y)) :=
          (continuous_const.sub continuous_id).tendsto _
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with c hc
        exact sub_pos.2 (Set.mem_Iio.1 hc)
    have hB : Tendsto (fun c : ℝ => l₁ * (Y - c) ^ (-σ₂)) (𝓝[<] Y) atTop :=
      ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -σ₂ < 0)).comp hsub).const_mul_atTop hl₁
    have hA : Tendsto (fun c : ℝ => l₂ * c ^ (-σ₁)) (𝓝[<] Y) (𝓝 (l₂ * Y ^ (-σ₁))) :=
      Tendsto.mono_left ((continuous_id.continuousAt.rpow_const (Or.inl hY.ne')).const_mul l₂)
        nhdsWithin_le_nhds
    refine (hA.add_atBot (tendsto_neg_atTop_atBot.comp hB)).congr fun c => ?_
    simp only [hf, Function.comp]
    ring
  obtain ⟨a, ha0, ha⟩ := ((hlim0.eventually (eventually_gt_atTop 0)).and
    (Ioo_mem_nhdsGT hY)).exists
  obtain ⟨b, hb0, hb⟩ := ((hlimY.eventually (eventually_lt_atBot 0)).and
    (Ioo_mem_nhdsLT hY)).exists
  have hab : a < b := by
    by_contra hn
    push Not at hn
    rcases hn.lt_or_eq with h | h
    · have := hanti ⟨hb.1, hb.2⟩ ⟨ha.1, ha.2⟩ h
      linarith
    · rw [h] at hb0; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 Y := fun x hx => ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab.le (hcont.mono hsub)
    (⟨hb0.le, ha0.le⟩ : (0 : ℝ) ∈ Set.Icc (f b) (f a))
  refine ⟨c, ⟨hsub hc, by simp only [hf] at hc0; linarith⟩, ?_⟩
  rintro c' ⟨hc', he⟩
  have hfc' : f c' = 0 := by simp only [hf]; linarith
  exact hanti.injOn hc' (hsub hc) (hfc'.trans hc0.symm)

/-- **AKMM, p. 290 and Figure 11.1: "it is efficient for the planner to have the consumption of
the least risk-averse households fluctuate more in response to aggregate shocks".** Let
`(c₁, c₂)` and `(c₁′, c₂′)` be positive allocations satisfying the first-order condition
`λ₂c₁^{−σ₁} = λ₁c₂^{−σ₂}` at the endowments `Y = c₁ + c₂ < Y′ = c₁′ + c₂′`, with
`0 < σ₁ < σ₂`. Then both consumptions rise, `σ₁(log c₁′ − log c₁) = σ₂(log c₂′ − log c₂)`, and
the consumption of the less risk-averse household 1 rises proportionally more:
`log c₁′ − log c₁ > log c₂′ − log c₂ > 0`. -/
theorem rs_less_risk_averse_absorbs {σ₁ σ₂ l₁ l₂ c₁ c₂ c₁' c₂' : ℝ} (hσ₁ : 0 < σ₁)
    (hσ : σ₁ < σ₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁' : 0 < c₁')
    (hc₂' : 0 < c₂') (hfoc : l₂ * c₁ ^ (-σ₁) = l₁ * c₂ ^ (-σ₂))
    (hfoc' : l₂ * c₁' ^ (-σ₁) = l₁ * c₂' ^ (-σ₂)) (hY : c₁ + c₂ < c₁' + c₂') :
    c₁ < c₁' ∧ c₂ < c₂' ∧
      σ₁ * (Real.log c₁' - Real.log c₁) = σ₂ * (Real.log c₂' - Real.log c₂) ∧
      0 < Real.log c₂' - Real.log c₂ ∧
      Real.log c₂' - Real.log c₂ < Real.log c₁' - Real.log c₁ := by
  have hσ₂ : 0 < σ₂ := hσ₁.trans hσ
  -- take logs of the first-order conditions
  have hlog : ∀ {a b : ℝ}, 0 < a → 0 < b → l₂ * a ^ (-σ₁) = l₁ * b ^ (-σ₂) →
      Real.log l₂ - σ₁ * Real.log a = Real.log l₁ - σ₂ * Real.log b := by
    intro a b ha hb h
    have := congrArg Real.log h
    rw [Real.log_mul hl₂.ne' (Real.rpow_pos_of_pos ha _).ne',
      Real.log_mul hl₁.ne' (Real.rpow_pos_of_pos hb _).ne', Real.log_rpow ha,
      Real.log_rpow hb] at this
    linarith
  have e := hlog hc₁ hc₂ hfoc
  have e' := hlog hc₁' hc₂' hfoc'
  have hkey : σ₁ * (Real.log c₁' - Real.log c₁) = σ₂ * (Real.log c₂' - Real.log c₂) := by
    linarith
  -- the two consumptions move together
  have hmono : c₁ < c₁' ↔ c₂ < c₂' := by
    rw [← Real.log_lt_log_iff hc₁ hc₁', ← Real.log_lt_log_iff hc₂ hc₂']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have h1 : c₁ < c₁' := by
    by_contra hn
    push Not at hn
    have h2 : c₂' ≤ c₂ := by
      by_contra hn2
      push Not at hn2
      have := hmono.2 hn2
      linarith
    linarith
  have h2 := hmono.1 h1
  have hd2 : 0 < Real.log c₂' - Real.log c₂ := sub_pos.2 (Real.log_lt_log hc₂ h2)
  refine ⟨h1, h2, hkey, hd2, ?_⟩
  by_contra hn
  push Not at hn
  nlinarith

end AKMM.Consumption
