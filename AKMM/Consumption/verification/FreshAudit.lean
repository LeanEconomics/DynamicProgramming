import AKMMUncertainty.CompleteMarkets
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import AKMMCompetitiveEquilibrium.ADConsumer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RationalExpectations.Basics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import IncompleteMarkets.SIBounded
import IncompleteMarkets.BWExamples
import IncompleteMarkets.AYExistence
import IncompleteMarkets.AYIncomeFluct
import WeakConvergence.Parameters
import LeanEconomics.Analysis.PowerMean
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Compact
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The bond economy and the deterministic income fluctuation problem

AKMM, §11.2.3 (the bond economy, (11.8)–(11.11)) and §11.3.1, (11.12)–(11.16), footnotes 12–13
and 15, pp. 294–297.

* **(11.11)** from (11.8) with the constant bond price `q = 1/(1 + r)` (`eq_11_11`); **(11.10)**:
  the no-Ponzi condition and the transversality condition together give `lim = 0`
  (`eq_11_10`).
* The flow budget iterated `T` periods (`cd_budget_iter`) and, with (11.10), the intertemporal
  budget `Σⱼ R⁻ʲcₜ₊ⱼ = aₜ + Σⱼ R⁻ʲyₜ₊ⱼ` of p. 296 (`cd_intertemporal_budget`); the present value
  of a positive consumption plan converges automatically (`cd_summable_pv_cons`).
* The problem (11.12) (`cd_Plan`, `cd_Optimal`); **(11.13)** `u′(cₜ) = βRu′(cₜ₊₁)` at every
  optimum, from optimality by a two-period perturbation (`eq_11_13`); **(11.14)** for CRRA
  (`eq_11_14`); sufficiency of the Euler equation and (11.10) for concave `u`
  (`cd_optimal_of_euler`), with the log plan `cₜ = (1 − β)aₜ` as a concrete optimum
  (`cd_log_optimal`).
* **(11.15)** the linear consumption function (`eq_11_15`, from optimality
  `cd_optimal_eq_11_15`), **(11.16)** the MPC (`eq_11_16`); a transitory change in `yₜ` acts as
  a change in `aₜ` (`cd_transitory_eq_wealth`); `βR = 1` gives `MPC = 1 − β = ρ/(1 + ρ)` and
  `0 ≤ ρ − MPC ≤ ρ²` (`cd_mpc_betaR_one`, `cd_mpc_approx_rho`); the MPC out of a permanent change
  in income is `1` when `βR = 1` (`cd_mpc_permanent`); footnote 15, the annuity value keeps assets
  constant (`footnote_15`).
* **Correction** (p. 297, log utility "`MPC ≃ r`"): with `σ = 1`, `MPC = 1 − β` whatever `r`
  (`cd_mpc_log`), it equals `r/(1 + r)` only when `βR = 1` (`cd_mpc_log_eq_r_iff`), and with
  `β = 1/2`, `r = 1/100` it is `1/2` (`cd_mpc_log_printed_counterexample`).

Departures: (11.10) is imposed as `aₜ/Rᵗ → 0`, and the optimum is taken over positive consumption
plans with summable discounted utility.
-/

namespace AKMM.Consumption

open Filter Topology AKMM.CompetitiveEquilibrium

/-! ### The bond economy -/

/-- **AKMM, (11.11), p. 295.** With no aggregate risk the bond price is a constant `q`, and with
`r = 1/q − 1` the budget (11.8) `c + qa′ = y + a` is `a′ = (1 + r)(y + a − c)`. -/
theorem eq_11_11 {q r y a c a' : ℝ} (hq : 0 < q) (hr : r = 1 / q - 1) (h : c + q * a' = y + a) :
    a' = (1 + r) * (y + a - c) := by
  subst hr
  field_simp
  linarith

/-- **AKMM, (11.9)–(11.10), p. 294.** If the discounted debt satisfies the no-Ponzi condition
(eventually `≥ −ε` for every `ε > 0`) and the transversality condition (eventually `≤ ε`), then
it converges to `0`. -/
theorem eq_11_10 {x : ℕ → ℝ} (hnpg : ∀ ε > 0, ∀ᶠ t in atTop, -ε ≤ x t)
    (htvc : ∀ ε > 0, ∀ᶠ t in atTop, x t ≤ ε) : Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, h₁⟩ := eventually_atTop.1 (hnpg (ε / 2) (half_pos hε))
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (htvc (ε / 2) (half_pos hε))
  refine ⟨max N₁ N₂, fun t ht => ?_⟩
  have a := h₁ t (le_of_max_le_left ht)
  have b := h₂ t (le_of_max_le_right ht)
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-! ### Budgets -/

/-- AKMM, p. 296: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)` iterated `T` periods:
`Σ_{j<T} R⁻ʲcₜ₊ⱼ = aₜ + Σ_{j<T} R⁻ʲyₜ₊ⱼ − R⁻ᵀaₜ₊ᵀ`. -/
theorem cd_budget_iter {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (t T : ℕ) :
    ∑ j ∈ Finset.range T, R⁻¹ ^ j * c (t + j) =
      a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) - R⁻¹ ^ T * a (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, show t + (T + 1) = t + T + 1 by ring,
      hb (t + T), pow_succ]
    field_simp
    ring

/-- AKMM, p. 296: the present value of a positive consumption plan converges whenever the
present value of income converges and `R⁻ᵀaₜ₊ᵀ → 0`: its partial sums are bounded. -/
theorem cd_summable_pv_cons {R : ℝ} (hR : 0 < R) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (htvc : Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0))
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    Summable fun j => R⁻¹ ^ j * c (t + j) := by
  have hnn : ∀ j, 0 ≤ R⁻¹ ^ j * c (t + j) := fun j =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hR.le) j) (hc _)
  have hlim : Tendsto (fun T => a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) -
      R⁻¹ ^ T * a (t + T)) atTop (𝓝 (a t + ∑' j, R⁻¹ ^ j * y (t + j) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  refine summable_of_sum_range_le (c := B) hnn fun T => ?_
  rw [cd_budget_iter hR.ne' hb]
  exact hB ⟨T, rfl⟩

/-- AKMM, p. 296: iterating the budget and imposing (11.10) gives the intertemporal budget
`Σⱼ R⁻ʲcₜ₊ⱼ = aₜ + Σⱼ R⁻ʲyₜ₊ⱼ`. -/
theorem cd_intertemporal_budget {R : ℝ} (hR : 0 < R) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (t : ℕ)
    (htvc : Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0))
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j))
    (hc : Summable fun j => R⁻¹ ^ j * c (t + j)) :
    ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j) := by
  have hlim : Tendsto (fun T => a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) -
      R⁻¹ ^ T * a (t + T)) atTop (𝓝 (a t + ∑' j, R⁻¹ ^ j * y (t + j) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  have h2 := hc.hasSum.tendsto_sum_nat
  simp_rw [cd_budget_iter hR.ne' hb t] at h2
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique h2 hlim

/-- (11.10) for the plan, `aₜ/Rᵗ → 0`, gives `R⁻ᵀaₜ₊ᵀ → 0` from every date `t`. -/
theorem cd_tvc_shift {R : ℝ} (hR : 0 < R) {a : ℕ → ℝ}
    (htvc : Tendsto (fun t => a t / R ^ t) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0) := by
  have h := (htvc.comp (tendsto_add_atTop_iff_nat t |>.2 tendsto_id)).const_mul (R ^ t)
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  simp only [Function.comp, id]
  rw [show T + t = t + T by ring, pow_add, inv_pow]
  field_simp

/-! ### The problem (11.12) and the Euler equation (11.13) -/

/-- AKMM, (11.12), p. 295: a feasible plan from `a₀`: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)`,
positive consumption and condition (11.10), in the form `aₜ/Rᵗ → 0`. -/
def cd_Plan (R a₀ : ℝ) (y c a : ℕ → ℝ) : Prop :=
  a 0 = a₀ ∧ (∀ t, a (t + 1) = R * (y t + a t - c t)) ∧ (∀ t, 0 < c t) ∧
    Tendsto (fun t => a t / R ^ t) atTop (𝓝 0)

/-- AKMM, (11.12), p. 295: `(c, a)` solves the problem: it is feasible with summable discounted
utility, and no feasible plan with summable utility does better. -/
def cd_Optimal (β R a₀ : ℝ) (u : ℝ → ℝ) (y c a : ℕ → ℝ) : Prop :=
  cd_Plan R a₀ y c a ∧ Summable (fun t => β ^ t * u (c t)) ∧
    ∀ c' a', cd_Plan R a₀ y c' a' → Summable (fun t => β ^ t * u (c' t)) →
      ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t)

/-- **AKMM, (11.13), p. 296.** At an optimum of (11.12) with `R > 0` and differentiable `u`,
`u′(cₜ) = βRu′(cₜ₊₁)`, i.e. `u′(cₜ)/(βu′(cₜ₊₁)) = 1 + r`. Proved from optimality: shifting `ε`
units of consumption from `t` to `t + 1` (as `Rε`) is feasible and changes only two terms. -/
theorem eq_11_13 {β R a₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {y c a : ℕ → ℝ}
    (hopt : cd_Optimal β R a₀ u y c a) (t : ℕ) : du (c t) = β * R * du (c (t + 1)) := by
  obtain ⟨⟨ha0, hb, hc, htvc⟩, hsum, hle⟩ := hopt
  classical
  set c' : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - ε else if n = t + 1 then c (t + 1) + R * ε else c n with hc'
  set a' : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + R * ε else a n with ha'
  have hplan : ∀ ε, |ε| < min (c t) (c (t + 1) / R) → cd_Plan R a₀ y (c' ε) (a' ε) := by
    intro ε hε
    have h1 : ε < c t := (le_abs_self ε).trans_lt (hε.trans_le (min_le_left _ _))
    have h2 : -ε < c (t + 1) / R := (neg_le_abs ε).trans_lt (hε.trans_le (min_le_right _ _))
    have h2' : 0 < c (t + 1) + R * ε := by
      rw [lt_div_iff₀ hR] at h2; linarith
    refine ⟨?_, fun n => ?_, fun n => ?_, ?_⟩
    · simp only [ha', show (0 : ℕ) ≠ t + 1 by omega, ↓reduceIte, ha0]
    · by_cases hn : n = t
      · subst hn
        simp only [ha', hc', ↓reduceIte, show n ≠ n + 1 by omega]
        rw [hb n]; ring
      · by_cases hn1 : n = t + 1
        · subst hn1
          simp only [ha', hc', show t + 1 + 1 ≠ t + 1 by omega, show t + 1 ≠ t by omega,
            ↓reduceIte]
          rw [hb (t + 1)]; ring
        · simp only [ha', hc', show n + 1 ≠ t + 1 by omega, hn, hn1, ↓reduceIte]
          exact hb n
    · simp only [hc']
      split_ifs
      · linarith
      · exact h2'
      · exact hc n
    · refine htvc.congr' ?_
      filter_upwards [eventually_gt_atTop (t + 1)] with n hn
      simp only [ha', show n ≠ t + 1 by omega, ↓reduceIte]
  have hmin : 0 < min (c t) (c (t + 1) / R) := lt_min (hc t) (div_pos (hc _) hR)
  set f : ℕ → ℝ := fun n => β ^ n * u (c n)
  set g : ℝ → ℕ → ℝ := fun ε n => β ^ n * u (c' ε n)
  have hs : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), g ε n = f n := by
    intro ε n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [g, f, hc', hn.1, hn.2, ↓reduceIte]
  have h0 : ∀ n, g 0 n = f n := by
    intro n
    simp only [g, f, hc', sub_zero, mul_zero, add_zero]
    split_ifs <;> subst_vars <;> rfl
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), Summable (g ε) → ∑' n, g ε n ≤ ∑' n, f n := by
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < min (c t) (c (t + 1) / R) := by
      have hc0 : Continuous fun ε : ℝ => |ε| := continuous_abs
      exact hc0.continuousAt.eventually_lt continuousAt_const (by simpa using hmin)
    filter_upwards [this] with ε hε hsg
    exact hle _ _ (hplan ε hε) hsg
  have hd : HasDerivAt (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), g ε n)
      (β ^ t * (du (c t) * (-1)) + β ^ (t + 1) * (du (c (t + 1)) * (R * 1))) 0 := by
    have ht : t ∉ ({t + 1} : Finset ℕ) := by simp
    have hfun : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), g ε n) =
        fun ε => β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + R * ε) := by
      funext ε
      rw [Finset.sum_insert ht, Finset.sum_singleton]
      simp only [g, hc', ↓reduceIte, show t + 1 ≠ t by omega]
    rw [hfun]
    have e1 : HasDerivAt (fun ε => c t - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c t)
    have e2 : HasDerivAt (fun ε => c (t + 1) + R * ε) (R * 1) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add _
    have u1 := hu (c t) (hc t)
    have u2 := hu (c (t + 1)) (hc _)
    have u1' : HasDerivAt u (du (c t)) (c t - 0) := by simpa using u1
    have u2' : HasDerivAt u (du (c (t + 1))) (c (t + 1) + R * 0) := by simpa using u2
    exact ((u1'.comp 0 e1).const_mul _).add ((u2'.comp 0 e2).const_mul _)
  have := ce_foc_of_perturb {t, t + 1} hsum hs h0 hev hd
  have hβt : β ^ t ≠ 0 := pow_ne_zero _ hβ.ne'
  rw [pow_succ] at this
  have : β ^ t * (β * R * du (c (t + 1)) - du (c t)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hβt
  · linarith

/-- **AKMM, (11.14), p. 296.** With CRRA marginal utility `u′(c) = c^{−σ}`, the Euler equation
(11.13) is `cₜ₊₁/cₜ = (βR)^{1/σ}`. -/
theorem eq_11_14 {β R σ ct ct1 : ℝ} (hσ : 0 < σ) (hβR : 0 < β * R) (hct : 0 < ct)
    (hct1 : 0 < ct1) (h : ct ^ (-σ) = β * R * ct1 ^ (-σ)) : ct1 / ct = (β * R) ^ (1 / σ) := by
  have hf : ct1 ^ (-σ) = (β * R)⁻¹ * ct ^ (-σ) := by
    rw [h, ← mul_assoc, inv_mul_cancel₀ hβR.ne', one_mul]
  have e := rs_crra_invert hσ hct1 (inv_pos.2 hβR) (Real.rpow_pos_of_pos hct _) hf
  have h1 : (ct ^ (-σ)) ^ (-1 / σ) = ct := by
    rw [← Real.rpow_mul hct.le, show -σ * (-1 / σ) = 1 by field_simp, Real.rpow_one]
  have h2 : ((β * R)⁻¹) ^ (-1 / σ) = (β * R) ^ (1 / σ) := by
    rw [Real.inv_rpow hβR.le, neg_div, Real.rpow_neg hβR.le, inv_inv]
  rw [e, h1, h2]
  field_simp

/-- With (11.14) at every date, `cₜ₊ⱼ = gʲcₜ` for `g = (βR)^{1/σ}`. -/
theorem cd_growth {g : ℝ} {c : ℕ → ℝ} (hg : ∀ t, c (t + 1) = g * c t) (t j : ℕ) :
    c (t + j) = g ^ j * c t := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, hg, ih, pow_succ]; ring

/-! ### Sufficiency and a concrete optimum -/

/-- AKMM, p. 296 (the Euler equation and (11.10) characterise the optimum). For `u` with the
tangent-line inequality `u(x) ≤ u(z) + u′(z)(x − z)` (concavity), a feasible plan satisfying the
Euler equation (11.13) at every date, with summable utility and a convergent present value of
income, solves (11.12). -/
theorem cd_optimal_of_euler {β R a₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) {u du : ℝ → ℝ}
    (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) {y c a : ℕ → ℝ}
    (hplan : cd_Plan R a₀ y c a) (heuler : ∀ t, du (c t) = β * R * du (c (t + 1)))
    (hu : Summable fun t => β ^ t * u (c t)) (hy : Summable fun j => R⁻¹ ^ j * y j) :
    cd_Optimal β R a₀ u y c a := by
  refine ⟨hplan, hu, fun c' a' hplan' hu' => ?_⟩
  obtain ⟨ha0, hb, hc, htvc⟩ := hplan
  obtain ⟨ha0', hb', hc', htvc'⟩ := hplan'
  have hdisc : ∀ t, β ^ t * du (c t) = R⁻¹ ^ t * du (c 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e := heuler t
      rw [pow_succ, pow_succ, show β ^ t * β * du (c (t + 1)) = β ^ t * (β * du (c (t + 1)))
        by ring, show β * du (c (t + 1)) = R⁻¹ * du (c t) by rw [e]; field_simp]
      rw [show β ^ t * (R⁻¹ * du (c t)) = R⁻¹ * (β ^ t * du (c t)) by ring, ih]
      ring
  have hy0 : Summable fun j => R⁻¹ ^ j * y (0 + j) := by simpa using hy
  have hpv := cd_summable_pv_cons hR hb (fun t => (hc t).le) 0 (cd_tvc_shift hR htvc 0) hy0
  have hpv' := cd_summable_pv_cons hR hb' (fun t => (hc' t).le) 0 (cd_tvc_shift hR htvc' 0) hy0
  have hib := cd_intertemporal_budget hR hb 0 (cd_tvc_shift hR htvc 0) hy0 hpv
  have hib' := cd_intertemporal_budget hR hb' 0 (cd_tvc_shift hR htvc' 0) hy0 hpv'
  simp only [zero_add] at hpv hpv' hib hib'
  have hpt : ∀ t, β ^ t * u (c' t) ≤
      β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t) := by
    intro t
    have h1 := htan (c' t) (c t) (hc' t) (hc t)
    have h2 : β ^ t * u (c' t) ≤ β ^ t * (u (c t) + du (c t) * (c' t - c t)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ.le t)
    have h3 : β ^ t * (u (c t) + du (c t) * (c' t - c t)) =
        β ^ t * u (c t) + (β ^ t * du (c t)) * (c' t - c t) := by ring
    rw [h3, hdisc t] at h2
    linarith
  have hsr : Summable fun t => β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t) :=
    hu.add ((hpv'.sub hpv).mul_left _)
  calc ∑' t, β ^ t * u (c' t)
      ≤ ∑' t, (β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t)) :=
        Summable.tsum_le_tsum hpt hu' hsr
    _ = ∑' t, β ^ t * u (c t) + du (c 0) * (∑' t, R⁻¹ ^ t * c' t - ∑' t, R⁻¹ ^ t * c t) := by
        rw [hu.tsum_add ((hpv'.sub hpv).mul_left _), tsum_mul_left, hpv'.tsum_sub hpv]
    _ = ∑' t, β ^ t * u (c t) := by rw [hib, hib', ha0, ha0']; ring

/-- A concrete optimum of (11.12) (the problem's hypotheses are not vacuous): log utility, no
income, `0 < β < 1`, `R > 0`, `a₀ > 0`. The plan `aₜ = (βR)ᵗa₀`, `cₜ = (1 − β)aₜ` is optimal. -/
theorem cd_log_optimal {β R a₀ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (ha₀ : 0 < a₀) :
    cd_Optimal β R a₀ Real.log (fun _ => 0) (fun t => (1 - β) * ((β * R) ^ t * a₀))
      (fun t => (β * R) ^ t * a₀) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hcpos : ∀ t, 0 < (1 - β) * ((β * R) ^ t * a₀) := fun t =>
    mul_pos (by linarith) (mul_pos (pow_pos hβR t) ha₀)
  refine cd_optimal_of_euler hβ hR (du := fun x => x⁻¹) (fun x z hx hz => ?_) ⟨by simp,
    fun t => by beta_reduce; ring, hcpos, ?_⟩ (fun t => ?_) ?_ (by simp)
  · have := Real.log_le_sub_one_of_pos (div_pos hx hz)
    rw [Real.log_div hx.ne' hz.ne'] at this
    have e : z⁻¹ * (x - z) = x / z - 1 := by field_simp
    linarith
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const a₀
    rw [zero_mul] at h
    refine h.congr fun t => ?_
    beta_reduce
    rw [mul_pow]
    field_simp
  · show ((1 - β) * ((β * R) ^ t * a₀))⁻¹ = β * R * ((1 - β) * ((β * R) ^ (t + 1) * a₀))⁻¹
    rw [pow_succ]
    have := pow_pos hβR t
    field_simp
  · have hlog : ∀ t : ℕ, β ^ t * Real.log ((1 - β) * ((β * R) ^ t * a₀)) =
        Real.log ((1 - β) * a₀) * β ^ t + Real.log (β * R) * ((t : ℝ) ^ 1 * β ^ t) := by
      intro t
      rw [show (1 - β) * ((β * R) ^ t * a₀) = (1 - β) * a₀ * (β * R) ^ t by ring,
        Real.log_mul (mul_pos (by linarith) ha₀).ne' (pow_pos hβR t).ne', Real.log_pow]
      ring
    simp_rw [hlog]
    have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ]; exact hβ1
    exact ((summable_geometric_of_lt_one hβ.le hβ1).mul_left _).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left _)

/-! ### The consumption function (11.15) and the MPC (11.16) -/

/-- The MPC of (11.16), `1 − R⁻¹(βR)^{1/σ}`. -/
noncomputable def cd_mpc (β R σ : ℝ) : ℝ := 1 - R⁻¹ * (β * R) ^ (1 / σ)

/-- AKMM, p. 297: consumption growing at the rate `g < R` and the intertemporal budget give
`cₜ = (1 − R⁻¹g)(aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`. -/
theorem cd_rule_of_growth {R g : ℝ} (hR : 0 < R) (hg0 : 0 ≤ g) (hgR : g < R) {y c a : ℕ → ℝ}
    (t : ℕ) (hgrow : ∀ j, c (t + j) = g ^ j * c t)
    (hbud : ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j)) :
    c t = (1 - R⁻¹ * g) * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hq0 : 0 ≤ R⁻¹ * g := mul_nonneg (inv_nonneg.2 hR.le) hg0
  have hq1 : R⁻¹ * g < 1 := by rw [inv_mul_lt_iff₀ hR]; linarith
  have hsum : ∑' j, R⁻¹ ^ j * c (t + j) = c t * (1 - R⁻¹ * g)⁻¹ := by
    simp_rw [hgrow, show ∀ j : ℕ, R⁻¹ ^ j * (g ^ j * c t) = c t * (R⁻¹ * g) ^ j from
      fun j => by rw [mul_pow]; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [← hbud, hsum]
  have : 0 < 1 - R⁻¹ * g := by linarith
  rw [mul_comm (c t), ← mul_assoc, mul_inv_cancel₀ this.ne', one_mul]

/-- **AKMM, (11.15), p. 297.** With CRRA utility, the Euler equation (11.14) at every date, the
intertemporal budget from `t`, and `(βR)^{1/σ} < R`: `cₜ = [1 − R⁻¹(βR)^{1/σ}](aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`,
consumption is a constant fraction of total (financial plus human) wealth. -/
theorem eq_11_15 {β R σ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hgR : (β * R) ^ (1 / σ) < R) {y c a : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (heuler : ∀ t, c t ^ (-σ) = β * R * c (t + 1) ^ (-σ)) (t : ℕ)
    (hbud : ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j)) :
    c t = cd_mpc β R σ * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hg : ∀ s, c (s + 1) = (β * R) ^ (1 / σ) * c s := fun s => by
    have := eq_11_14 hσ hβR (hc s) (hc (s + 1)) (heuler s)
    rw [div_eq_iff (hc s).ne'] at this
    exact this
  exact cd_rule_of_growth hR (Real.rpow_nonneg hβR.le _) hgR t (cd_growth hg t) hbud

/-- **AKMM, (11.15), p. 297, from optimality.** At an optimum of (11.12) with CRRA marginal
utility `u′(c) = c^{−σ}` and `(βR)^{1/σ} < R`, if the present value of income from `t`
converges, `cₜ = MPC · (aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`. -/
theorem cd_optimal_eq_11_15 {β R σ a₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hgR : (β * R) ^ (1 / σ) < R) {u : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-σ)) c)
    {y c a : ℕ → ℝ} (hopt : cd_Optimal β R a₀ u y c a) (t : ℕ)
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    c t = cd_mpc β R σ * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have he := fun s => eq_11_13 (du := fun x => x ^ (-σ)) hβ hR hu hopt s
  obtain ⟨⟨-, hb, hc, htvc⟩, -⟩ := hopt
  have hpv := cd_summable_pv_cons hR hb (fun s => (hc s).le) t (cd_tvc_shift hR htvc t) hy
  exact eq_11_15 hσ hβ hR hgR hc he t
    (cd_intertemporal_budget hR hb t (cd_tvc_shift hR htvc t) hy hpv)

/-- **AKMM, (11.16), p. 297.** Differentiating (11.15): `∂cₜ/∂aₜ = MPC = 1 − R⁻¹(βR)^{1/σ}`. -/
theorem eq_11_16 (β R σ H a : ℝ) :
    HasDerivAt (fun x => cd_mpc β R σ * (x + H)) (cd_mpc β R σ) a := by
  simpa using ((hasDerivAt_id a).add_const H).const_mul (cd_mpc β R σ)

/-- AKMM, p. 297 and fn. 12: a transitory change `δ` in `yₜ` (leaving `yₜ₊ⱼ`, `j > 0`,
unchanged) moves consumption exactly as a change `δ` in `aₜ`. -/
theorem cd_transitory_eq_wealth {R : ℝ} (y : ℕ → ℝ) (m a δ : ℝ) (t : ℕ)
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    m * (a + ∑' j, R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0)) =
      m * ((a + δ) + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hδ : Summable fun j : ℕ => R⁻¹ ^ j * (if j = 0 then δ else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsplit : ∑' j, R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0) =
      ∑' j, R⁻¹ ^ j * y (t + j) + δ := by
    rw [show (fun j => R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0)) =
      fun j => R⁻¹ ^ j * y (t + j) + R⁻¹ ^ j * (if j = 0 then δ else 0) from
      funext fun j => mul_add _ _ _, hy.tsum_add hδ,
      tsum_eq_single (f := fun j : ℕ => R⁻¹ ^ j * if j = 0 then δ else 0) 0
        (fun j hj => by simp [hj])]
    simp
  rw [hsplit]
  ring

/-- AKMM, p. 297: when `βR = 1`, `MPC = 1 − R⁻¹ = 1 − β`, and with `β = 1/(1 + ρ)` this is
`ρ/(1 + ρ)`. -/
theorem cd_mpc_betaR_one {β R σ ρ : ℝ} (hR : 0 < R) (hβR : β * R = 1)
    (hρ : β = 1 / (1 + ρ)) (hρ1 : 0 < 1 + ρ) :
    cd_mpc β R σ = 1 - R⁻¹ ∧ cd_mpc β R σ = 1 - β ∧ cd_mpc β R σ = ρ / (1 + ρ) := by
  have hβ : β = R⁻¹ := by field_simp; linarith
  have h1 : cd_mpc β R σ = 1 - R⁻¹ := by simp [cd_mpc, hβR]
  refine ⟨h1, by rw [h1, hβ], ?_⟩
  rw [h1, ← hβ, hρ]
  field_simp
  ring

/-- AKMM, p. 297 and fn. 13: "since `ρ` is small relative to 1, `MPC ≃ ρ`". Exactly:
`0 ≤ ρ − ρ/(1 + ρ) ≤ ρ²` for `ρ ≥ 0`. -/
theorem cd_mpc_approx_rho {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ ρ - ρ / (1 + ρ) ∧ ρ - ρ / (1 + ρ) ≤ ρ ^ 2 := by
  have h : ρ - ρ / (1 + ρ) = ρ ^ 2 / (1 + ρ) := by field_simp; ring
  rw [h]
  exact ⟨by positivity, div_le_self (sq_nonneg ρ) (by linarith)⟩

/-- AKMM, p. 297: with `βR = 1` a permanent change of one unit in income (`yₜ₊ⱼ + 1` for all
`j ≥ 0`) raises human wealth by `1/(1 − R⁻¹)` and consumption by exactly one unit: the MPC out of
permanent income is `1`. -/
theorem cd_mpc_permanent {β R σ : ℝ} (hR : 1 < R) (hβR : β * R = 1) (y : ℕ → ℝ) (a : ℝ)
    (t : ℕ) (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    ∑' j, R⁻¹ ^ j * (y (t + j) + 1) = ∑' j, R⁻¹ ^ j * y (t + j) + 1 / (1 - R⁻¹) ∧
    cd_mpc β R σ * (a + ∑' j, R⁻¹ ^ j * (y (t + j) + 1)) =
      cd_mpc β R σ * (a + ∑' j, R⁻¹ ^ j * y (t + j)) + 1 := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hq1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hg := summable_geometric_of_lt_one hq0 hq1
  have h1 : ∑' j, R⁻¹ ^ j * (y (t + j) + 1) = ∑' j, R⁻¹ ^ j * y (t + j) + 1 / (1 - R⁻¹) := by
    simp_rw [mul_add, mul_one]
    rw [hy.tsum_add hg, tsum_geometric_of_lt_one hq0 hq1, one_div]
  refine ⟨h1, ?_⟩
  rw [h1, (cd_mpc_betaR_one (σ := σ) (ρ := R - 1) hR0 hβR
    (by rw [show 1 + (R - 1) = R by ring, eq_div_iff hR0.ne']; exact hβR) (by linarith)).1]
  have : 0 < 1 - R⁻¹ := by linarith
  generalize ∑' j, R⁻¹ ^ j * y (t + j) = H
  have hR1 : R - 1 ≠ 0 := by linarith
  have e : 1 / (1 - R⁻¹) = R / (R - 1) := by field_simp
  rw [e]
  field_simp
  ring

/-- **AKMM, fn. 15, p. 298.** The annuity value: consuming `r/(1 + r)` of wealth (no income)
keeps assets constant, `(1 + r)(a − ra/(1 + r)) = a`. -/
theorem footnote_15 {r a : ℝ} (hr : 0 < 1 + r) : (1 + r) * (a - r / (1 + r) * a) = a := by
  field_simp
  ring

/-- **Correction to AKMM, p. 297** ("assuming log-utility (`σ = 1`) … without imposing `βR = 1`
… one obtains `MPC ≃ r`"). With `σ = 1`, (11.16) gives `MPC = 1 − β` for every `R > 0`: the MPC
does not depend on the interest rate. -/
theorem cd_mpc_log {β R : ℝ} (hR : 0 < R) : cd_mpc β R 1 = 1 - β := by
  simp only [cd_mpc, div_one, Real.rpow_one]
  field_simp

/-- With `σ = 1`, the MPC equals `r/(1 + r)` (the PIH value, `≃ r`) iff `βR = 1`. -/
theorem cd_mpc_log_eq_r_iff {β r : ℝ} (hr : 0 < 1 + r) :
    cd_mpc β (1 + r) 1 = r / (1 + r) ↔ β * (1 + r) = 1 := by
  rw [cd_mpc_log hr]
  constructor
  · intro h; field_simp at h; linarith
  · intro h
    have : β = 1 / (1 + r) := by field_simp; linarith
    rw [this]; field_simp; ring

/-- Counterexample to "`MPC ≃ r`" with log utility: `β = 1/2`, `r = 1/100` give `MPC = 1/2`,
fifty times `r`. -/
theorem cd_mpc_log_printed_counterexample :
    cd_mpc (1 / 2) (1 + 1 / 100) 1 = 1 / 2 ∧ cd_mpc (1 / 2) (1 + 1 / 100) 1 = 50 * (1 / 100) := by
  rw [cd_mpc_log (by norm_num)]
  constructor <;> norm_num

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The permanent income hypothesis

AKMM, §11.3.2, (11.17)–(11.29), fn. 14–15, pp. 297–301, and the PIH part of §11.3.3,
(11.30), p. 302.

Random variables live in a real normed space `V` with Miao's conditional expectations
`E : CondExpSystem ℝ V` (linear, contractive, iterated expectations); Mathlib's conditional
expectations on `L¹(Ω, F, Pr)` given a filtration are an instance (`condExpSystemL1_real`), and so
is the identity (`pih_detSystem`), which is the deterministic case. Processes are `ℕ → V`. The
gross rate is `R = 1 + r` and `q = (1 + r)⁻¹`.

* **(11.18)** quadratic utility `u′(c) = b₁ − b₂c` and `βR = 1` turn the Euler equation into
  Hall's martingale `cₜ = Eₜcₜ₊₁` (`eq_11_18`); **(11.19)** `Eₜcₜ₊ⱼ = cₜ` (`eq_11_19`).
* The budget iterated `J` periods and conditioned on `Eₜ` (`pih_budget_iter`,
  `pih_budget_condexp`); **(11.20)** with (11.10) in expectation, `cₜ = (r/(1 + r))[aₜ +
  Σⱼ qʲEₜyₜ₊ⱼ]` (`eq_11_20`); **(11.21)** the deterministic case (`eq_11_21`) and certainty
  equivalence: (11.20) is (11.21)'s rule `pih_rule` applied to the forecasts
  (`pih_certainty_equivalence`).
* **(11.22)–(11.24)** consumption changes by the annuity value of the news in total wealth
  (`eq_11_22`, `eq_11_23`, `eq_11_24`).
* **(11.25)–(11.27)** permanent and transitory income: (11.26) (`eq_11_26`), the news
  `(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ = vₜ₊₁ + [j = 0]uₜ₊₁` (`pih_news_perm_trans`) and
  `Δcₜ₊₁ = (r/(1 + r))uₜ₊₁ + vₜ₊₁` (`eq_11_27`).
* **(11.29)** saving for a rainy day: `sₜ = yₜ − (r/(1 + r))Σⱼ qʲEₜyₜ₊ⱼ` and
  `sₜ = −Σ_{j≥1} qʲEₜΔyₜ₊ⱼ` (`eq_11_29`, `pih_rainy_day`).
* **§11.3.3** a random walk income gives `cₜ = (r/(1 + r))aₜ + yₜ` and `aₜ₊₁ = aₜ`
  (`pih_random_walk`); i.i.d. income with mean `ȳ` gives **(11.30)** and
  `aₜ₊₁ = aₜ + yₜ − ȳ` (`eq_11_30`).

Departures: the Euler equation behind (11.18) is a hypothesis (the book states it); the
transversality condition (11.10) is used in expectation, `qᴶEₜaₜ₊ᴶ → 0`; the constant `1` of
`V` is a vector `one` with `Eₜ one = one`. Dates are written `t + 1` and `t` instead of `t` and
`t − 1`.
-/

namespace AKMM.Consumption

open Filter Topology Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The deterministic case: `Eₜ = id` is a system of conditional expectations. -/
def pih_detSystem (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : CondExpSystem ℝ V where
  E := fun _ => ContinuousLinearMap.id ℝ V
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

/-- `1 − (1 + r)⁻¹ = r/(1 + r)`. -/
theorem pih_one_sub_q {r : ℝ} (hr : 0 < r) : 1 - (1 + r)⁻¹ = r / (1 + r) := by
  have : (1 + r) ≠ 0 := by linarith
  field_simp
  ring

/-- `(r/(1 + r))(1 − (1 + r)⁻¹)⁻¹ = 1`: the annuity factor inverts the geometric sum. -/
theorem pih_annuity_inv {r : ℝ} (hr : 0 < r) : r / (1 + r) * (1 - (1 + r)⁻¹)⁻¹ = 1 := by
  rw [pih_one_sub_q hr, mul_inv_cancel₀ (div_pos hr (by linarith)).ne']

/-! ### Hall's martingale -/

/-- **AKMM, (11.18), p. 298 (Hall 1978).** With quadratic utility, `u′(c) = b₁ − b₂c` (`b₂ ≠ 0`),
and `βR = 1`, the Euler equation `u′(cₜ) = βREₜu′(cₜ₊₁)` gives `cₜ = Eₜcₜ₊₁`: consumption is a
martingale. -/
theorem eq_11_18 (E : CondExpSystem ℝ V) {β R b₁ b₂ : ℝ} (hb₂ : b₂ ≠ 0) (hβR : β * R = 1)
    {one : V} (hone : ∀ t, E.E t one = one) {c : ℕ → V}
    (heuler : ∀ t, b₁ • one - b₂ • c t = (β * R) • E.E t (b₁ • one - b₂ • c (t + 1))) (t : ℕ) :
    c t = E.E t (c (t + 1)) := by
  have h := heuler t
  rw [hβR, one_smul, map_sub, map_smul, map_smul, hone] at h
  have h2 : b₂ • c t = b₂ • E.E t (c (t + 1)) := by
    have := congrArg (fun x => b₁ • one - x) h
    simpa using this
  exact smul_right_injective V hb₂ h2

/-- **AKMM, (11.19), p. 298.** From the martingale property and the law of iterated expectations,
`Eₜcₜ₊ⱼ = cₜ` for every `j ≥ 0`. -/
theorem eq_11_19 (E : CondExpSystem ℝ V) {c : ℕ → V} (hmart : ∀ t, c t = E.E t (c (t + 1)))
    (t j : ℕ) : E.E t (c (t + j)) = c t := by
  induction j with
  | zero =>
    rw [add_zero]
    conv_lhs => rw [hmart t]
    rw [E.idem, ← hmart t]
  | succ j ih =>
    rw [← add_assoc, ← E.tower_le_apply (Nat.le_add_right t j) (c (t + j + 1)), ← hmart (t + j), ih]

/-! ### The annuity rule (11.20) -/

/-- AKMM, p. 298: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)` iterated `J` periods, in `V`. -/
theorem pih_budget_iter {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → V}
    (hb : ∀ t, a (t + 1) = R • (y t + a t - c t)) (t J : ℕ) :
    ∑ j ∈ Finset.range J, R⁻¹ ^ j • c (t + j) =
      a t + ∑ j ∈ Finset.range J, R⁻¹ ^ j • y (t + j) - R⁻¹ ^ J • a (t + J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, show t + (J + 1) = t + J + 1 by ring,
      hb (t + J), smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hR, mul_one]
    simp only [smul_sub, smul_add]
    abel

/-- AKMM, p. 298: the iterated budget conditioned on `Eₜ`,
`Σ_{j≤J} R⁻ʲEₜcₜ₊ⱼ = aₜ + Σ_{j≤J} R⁻ʲEₜyₜ₊ⱼ − R^{−(J+1)}Eₜaₜ₊ⱼ₊₁` (`aₜ` known at `t`). -/
theorem pih_budget_condexp (E : CondExpSystem ℝ V) {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → V}
    (hb : ∀ t, a (t + 1) = R • (y t + a t - c t)) (t : ℕ) (ha : E.E t (a t) = a t) (J : ℕ) :
    ∑ j ∈ Finset.range J, R⁻¹ ^ j • E.E t (c (t + j)) =
      a t + ∑ j ∈ Finset.range J, R⁻¹ ^ j • E.E t (y (t + j)) -
        R⁻¹ ^ J • E.E t (a (t + J)) := by
  have h := congrArg (E.E t) (pih_budget_iter hR hb t J)
  simp only [map_sub, map_add, map_sum, map_smul, ha] at h
  exact h

/-- The rule of (11.20)–(11.21): `(r/(1 + r))[a + Σⱼ (1 + r)⁻ʲzⱼ]` applied to forecasts `z`. -/
noncomputable def pih_rule (r : ℝ) (a : V) (z : ℕ → V) : V :=
  (r / (1 + r)) • (a + ∑' j, ((1 + r)⁻¹) ^ j • z j)

/-- **AKMM, (11.20), p. 298: the stochastic permanent income hypothesis.** With `r > 0`, the
martingale property (11.18), the budget, `aₜ` known at `t`, a convergent present value of
expected income and (11.10) in expectation (`(1 + r)^{−J}Eₜaₜ₊ᴶ → 0`):
`cₜ = (r/(1 + r))[aₜ + Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ]`, the annuity value of total wealth. -/
theorem eq_11_20 (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (hb : ∀ t, a (t + 1) = (1 + r) • (y t + a t - c t))
    (t : ℕ) (ha : E.E t (a t) = a t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j)))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J • E.E t (a (t + J))) atTop (𝓝 0)) :
    c t = pih_rule r (a t) fun j => E.E t (y (t + j)) := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hiter := pih_budget_condexp E (show (1 + r) ≠ 0 by linarith) hb t ha
  simp_rw [eq_11_19 E hmart t, ← Finset.sum_smul] at hiter
  have hL : Tendsto (fun J => (∑ j ∈ Finset.range J, q ^ j) • c t) atTop
      (𝓝 ((1 - q)⁻¹ • c t)) :=
    (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat.smul_const _
  have hR : Tendsto (fun J => a t + ∑ j ∈ Finset.range J, q ^ j • E.E t (y (t + j)) -
      q ^ J • E.E t (a (t + J))) atTop (𝓝 (a t + ∑' j, q ^ j • E.E t (y (t + j)) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  have heq : (1 - q)⁻¹ • c t = a t + ∑' j, q ^ j • E.E t (y (t + j)) := by
    rw [← sub_zero (a t + _)]
    exact tendsto_nhds_unique (hL.congr fun J => hiter J) hR
  have h1q : 1 - q = r / (1 + r) := by rw [hq]; field_simp; ring
  have hne : (1 - q) ≠ 0 := by linarith
  unfold pih_rule
  rw [← hq, ← heq, smul_smul, ← h1q, mul_inv_cancel₀ hne, one_smul]

/-- **AKMM, (11.21), p. 298.** Deterministic income (`Eₜ = id`), quadratic utility and
`βR = 1`: the Euler equation gives `cₜ₊₁ = cₜ` and
`cₜ = (r/(1 + r))[aₜ + Σⱼ (1 + r)⁻ʲyₜ₊ⱼ]`. -/
theorem eq_11_21 {r : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ} (hconst : ∀ t, c (t + 1) = c t)
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (t : ℕ)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + j))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J * a (t + J)) atTop (𝓝 0)) :
    c t = r / (1 + r) * (a t + ∑' j, ((1 + r)⁻¹) ^ j * y (t + j)) := by
  have := eq_11_20 (pih_detSystem ℝ) hr (y := y) (c := c) (a := a)
    (fun s => (hconst s).symm) (fun s => by rw [hb s, smul_eq_mul]) t rfl
    (by simpa [pih_detSystem] using hy) (by simpa [pih_detSystem] using htvc)
  simpa [pih_rule, pih_detSystem] using this

/-- **AKMM, p. 298: certainty equivalence.** The stochastic rule (11.20) is the deterministic
rule (11.21) with the conditional expectations `Eₜyₜ₊ⱼ` in place of the incomes: the two
solutions are `pih_rule` applied to the realised and to the forecast income paths. -/
theorem pih_certainty_equivalence (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (hb : ∀ t, a (t + 1) = (1 + r) • (y t + a t - c t))
    (t : ℕ) (ha : E.E t (a t) = a t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j)))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J • E.E t (a (t + J))) atTop (𝓝 0))
    {yd cd ad : ℕ → V} (hconst : ∀ s, cd (s + 1) = cd s)
    (hbd : ∀ s, ad (s + 1) = (1 + r) • (yd s + ad s - cd s))
    (hyd : Summable fun j => ((1 + r)⁻¹) ^ j • yd (t + j))
    (htvcd : Tendsto (fun J => ((1 + r)⁻¹) ^ J • ad (t + J)) atTop (𝓝 0)) :
    c t = pih_rule r (a t) (fun j => E.E t (y (t + j))) ∧
      cd t = pih_rule r (ad t) (fun j => yd (t + j)) :=
  ⟨eq_11_20 E hr hmart hb t ha hy htvc,
    eq_11_20 (pih_detSystem V) hr (fun s => (hconst s).symm) hbd t rfl hyd htvcd⟩

/-! ### News: (11.22)–(11.24) -/

/-- Total wealth `ϖₜ = aₜ + Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ`. -/
noncomputable def pih_wealth (E : CondExpSystem ℝ V) (r : ℝ) (y a : ℕ → V) (t : ℕ) : V :=
  a t + ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + j))

/-- **AKMM, (11.22), p. 299.** If (11.20) holds at `t + 1` and consumption is a martingale,
`Δcₜ₊₁ = cₜ₊₁ − Eₜcₜ₊₁ = (r/(1 + r))[ϖₜ₊₁ − Eₜϖₜ₊₁]`. -/
theorem eq_11_22 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1)) :
    c (t + 1) - c t = c (t + 1) - E.E t (c (t + 1)) ∧
      c (t + 1) - c t = (r / (1 + r)) • (pih_wealth E r y a (t + 1) -
        E.E t (pih_wealth E r y a (t + 1))) := by
  refine ⟨by rw [← hmart t], ?_⟩
  rw [hmart t, h20, map_smul, smul_sub]

/-- **AKMM, (11.23), p. 299.** If `aₜ₊₁` is known at `t` (`Eₜaₜ₊₁ = aₜ₊₁`) and the present value
of expected income at `t + 1` converges, the innovation in total wealth is the discounted sum of
the revisions in expected income: `ϖₜ₊₁ − Eₜϖₜ₊₁ = Σⱼ (1 + r)⁻ʲ(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ`. -/
theorem eq_11_23 (E : CondExpSystem ℝ V) {r : ℝ} {y a : ℕ → V} (t : ℕ)
    (ha : E.E t (a (t + 1)) = a (t + 1))
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) :
    pih_wealth E r y a (t + 1) - E.E t (pih_wealth E r y a (t + 1)) =
      ∑' j, ((1 + r)⁻¹) ^ j • (E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j))) := by
  have hmap : E.E t (∑' j, ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) =
      ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + 1 + j)) := by
    rw [(E.E t).map_tsum hy]
    simp only [map_smul, E.tower_le_apply (Nat.le_succ t)]
  have hy' : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + 1 + j)) := by
    have := (E.E t).summable hy
    simpa only [Function.comp_def, map_smul, E.tower_le_apply (Nat.le_succ t)] using this
  unfold pih_wealth
  rw [map_add, ha, hmap]
  simp_rw [smul_sub]
  rw [hy.tsum_sub hy']
  abel

/-- **AKMM, (11.24), p. 299.** Combining (11.22) and (11.23): under the PIH the change in
consumption is the annuity value of the news,
`Δcₜ₊₁ = (r/(1 + r))Σⱼ (1 + r)⁻ʲ(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ`. -/
theorem eq_11_24 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1))
    (ha : E.E t (a (t + 1)) = a (t + 1))
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) :
    c (t + 1) - c t = (r / (1 + r)) •
      ∑' j, ((1 + r)⁻¹) ^ j • (E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j))) := by
  rw [(eq_11_22 E hmart t h20).2, eq_11_23 E t ha hy]

/-! ### Permanent and transitory shocks: (11.25)–(11.27) -/

omit [NormedSpace ℝ V] in
/-- **AKMM, (11.26), p. 299.** From (11.25), `yₜ₊₁ = yₜ + uₜ₊₁ − uₜ + vₜ₊₁`. -/
theorem eq_11_26 {y yp u v : ℕ → V} (hy : ∀ t, y t = yp t + u t)
    (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1)) (t : ℕ) :
    y (t + 1) = y t + u (t + 1) - u t + v (t + 1) := by
  rw [hy, hy, hyp]; abel

/-- AKMM, p. 299: the permanent component is a martingale, `Eₛypₛ₊ₖ = ypₛ`, when `ypₛ` is known
at `s` and future permanent shocks have conditional mean zero. -/
theorem pih_perm_martingale (E : CondExpSystem ℝ V) {yp v : ℕ → V}
    (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1)) (hypm : ∀ s, E.E s (yp s) = yp s)
    (hv : ∀ s τ, s < τ → E.E s (v τ) = 0) (s k : ℕ) : E.E s (yp (s + k)) = yp s := by
  induction k with
  | zero => simpa using hypm s
  | succ k ih => rw [← add_assoc, hyp, map_add, ih, hv s _ (by omega), add_zero]

/-- AKMM, p. 300 ("after some algebra"): under (11.25), with `Eₛxτ = xτ` for `τ ≤ s` and
`Eₛxτ = 0` for `τ > s` (`x = u, v`) and `ypₛ` known at `s`, the revision in expected income is
`(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ = vₜ₊₁ + [j = 0]uₜ₊₁`. -/
theorem pih_news_perm_trans (E : CondExpSystem ℝ V) {y yp u v : ℕ → V}
    (hy : ∀ t, y t = yp t + u t) (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1))
    (hypm : ∀ s, E.E s (yp s) = yp s) (hu0 : ∀ s, E.E s (u s) = u s)
    (hu : ∀ s τ, s < τ → E.E s (u τ) = 0) (hv : ∀ s τ, s < τ → E.E s (v τ) = 0) (t j : ℕ) :
    E.E (t + 1) (y (t + 1 + j)) = yp (t + 1) + (if j = 0 then u (t + 1) else 0) ∧
      E.E t (y (t + 1 + j)) = yp t ∧
      E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j)) =
        v (t + 1) + (if j = 0 then u (t + 1) else 0) := by
  have h1 : E.E (t + 1) (y (t + 1 + j)) = yp (t + 1) + (if j = 0 then u (t + 1) else 0) := by
    rw [hy, map_add, pih_perm_martingale E hyp hypm hv]
    split_ifs with hj
    · subst hj; rw [add_zero, hu0]
    · rw [hu _ _ (by omega)]
  have h2 : E.E t (y (t + 1 + j)) = yp t := by
    rw [hy, map_add, show t + 1 + j = t + (1 + j) by ring, pih_perm_martingale E hyp hypm hv,
      hu _ _ (by omega), add_zero]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, hyp]
  abel

/-- **AKMM, (11.27), p. 300.** Under the PIH ((11.20) at `t + 1`, `aₜ₊₁` known at `t`, `r > 0`)
and the income process (11.25), `Δcₜ₊₁ = (r/(1 + r))uₜ₊₁ + vₜ₊₁`: the annuity value of the
transitory shock and the full permanent shock. -/
theorem eq_11_27 (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y yp u v c a : ℕ → V}
    (hy : ∀ t, y t = yp t + u t) (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1))
    (hypm : ∀ s, E.E s (yp s) = yp s) (hu0 : ∀ s, E.E s (u s) = u s)
    (hu : ∀ s τ, s < τ → E.E s (u τ) = 0) (hv : ∀ s τ, s < τ → E.E s (v τ) = 0)
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1))
    (ha : E.E t (a (t + 1)) = a (t + 1)) :
    c (t + 1) - c t = (r / (1 + r)) • u (t + 1) + v (t + 1) := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hnews := pih_news_perm_trans E hy hyp hypm hu0 hu hv t
  have hδ : Summable fun j : ℕ => q ^ j • (if j = 0 then u (t + 1) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsy : Summable fun j => q ^ j • E.E (t + 1) (y (t + 1 + j)) := by
    simp_rw [(hnews _).1, smul_add]
    exact (hg.smul_const _).add hδ
  rw [eq_11_24 E hmart t h20 ha hsy]
  simp_rw [(hnews _).2.2, smul_add]
  rw [(hg.smul_const _).tsum_add hδ, hg.tsum_smul_const _, tsum_geometric_of_lt_one hq0 hq1,
    tsum_eq_single (f := fun j : ℕ => q ^ j • (if j = 0 then u (t + 1) else 0)) 0
      (fun j hj => by simp [hj])]
  simp only [pow_zero, ↓reduceIte, one_smul, smul_add, smul_smul]
  rw [hq, pih_annuity_inv hr, one_smul]
  abel

/-! ### Saving for a rainy day (11.29) -/

/-- **AKMM, (11.29), p. 301.** Saving `sₜ = (r/(1 + r))aₜ + yₜ − cₜ`, with consumption from
(11.20), is `yₜ − (r/(1 + r))Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ`. -/
theorem eq_11_29 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V} (t : ℕ)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j))) :
    (r / (1 + r)) • a t + y t - c t =
      y t - (r / (1 + r)) • ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + j)) := by
  rw [h20, pih_rule, smul_add]
  abel

/-- **AKMM, p. 301: saving for the rainy day (Campbell 1987).** With (11.20), `yₜ` known at `t`
and a convergent present value of expected income, `r > 0`:
`sₜ = −Σ_{j≥1} (1 + r)⁻ʲEₜΔyₜ₊ⱼ`, the discounted sum of expected declines in income. -/
theorem pih_rainy_day (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V} (t : ℕ)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j))) (hyt : E.E t (y t) = y t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j))) :
    (r / (1 + r)) • a t + y t - c t =
      -∑' j, ((1 + r)⁻¹) ^ (j + 1) • (E.E t (y (t + (j + 1))) - E.E t (y (t + j))) := by
  rw [eq_11_29 E t h20]
  set q := (1 + r)⁻¹ with hq
  set Y : ℕ → V := fun j => E.E t (y (t + j)) with hY
  have hs1 : Summable fun j => q ^ (j + 1) • Y (j + 1) := (summable_nat_add_iff 1).2 hy
  have hs2 : Summable fun j => q ^ (j + 1) • Y j := by
    simp_rw [pow_succ, mul_comm _ q, ← smul_smul]; exact hy.const_smul q
  have h0 : ∑' j, q ^ j • Y j = q ^ 0 • Y 0 + ∑' j, q ^ (j + 1) • Y (j + 1) :=
    hy.tsum_eq_zero_add
  have h2 : ∑' j, q ^ (j + 1) • Y j = q • ∑' j, q ^ j • Y j := by
    rw [← hy.tsum_const_smul q]
    simp_rw [smul_smul, ← pow_succ']
    rfl
  have hsplit : ∑' j, q ^ (j + 1) • (Y (j + 1) - Y j) =
      (∑' j, q ^ j • Y j - Y 0) - q • ∑' j, q ^ j • Y j := by
    simp_rw [smul_sub]
    rw [hs1.tsum_sub hs2, h2, h0, pow_zero, one_smul]
    abel
  change y t - (r / (1 + r)) • ∑' j, q ^ j • Y j = -∑' j, q ^ (j + 1) • (Y (j + 1) - Y j)
  rw [hsplit]
  have hY0 : Y 0 = y t := by simp [hY, hyt]
  have h1q : r / (1 + r) = 1 - q := by rw [hq]; field_simp; ring
  rw [hY0, h1q, sub_smul, one_smul]
  abel

/-! ### Borrowing constraints in the PIH: random walk and i.i.d. income -/

/-- **AKMM, p. 302: random-walk income.** If `Eₜyₜ₊ⱼ = yₜ` for all `j`, (11.20) gives
`cₜ = (r/(1 + r))aₜ + yₜ`, and the budget gives `aₜ₊₁ = aₜ`: wealth is constant, so the zero
debt limit never binds from positive wealth. -/
theorem pih_random_walk (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V} (t : ℕ)
    (hrw : ∀ j, E.E t (y (t + j)) = y t)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j)))
    (hb : a (t + 1) = (1 + r) • (y t + a t - c t)) :
    c t = (r / (1 + r)) • a t + y t ∧ a (t + 1) = a t := by
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hc : c t = (r / (1 + r)) • a t + y t := by
    rw [h20, pih_rule]
    simp_rw [hrw]
    rw [((summable_geometric_of_lt_one hq0 hq1)).tsum_smul_const _,
      tsum_geometric_of_lt_one hq0 hq1, smul_add, smul_smul]
    rw [pih_annuity_inv hr, one_smul]
  refine ⟨hc, ?_⟩
  rw [hb, hc]
  have hr1 : (1 + r) ≠ 0 := by linarith
  simp only [smul_sub, smul_add, smul_smul]
  rw [show (1 + r) * (r / (1 + r)) = r by field_simp]
  module

/-- **AKMM, (11.30), p. 302: i.i.d. income.** If `yₜ` is known at `t` and `Eₜyₜ₊ⱼ = ȳ` for
`j ≥ 1` (a constant `ȳ · one`), (11.20) gives `cₜ = ȳ/(1 + r) + (r/(1 + r))(aₜ + yₜ)`, and the
budget gives `aₜ₊₁ = aₜ + yₜ − ȳ`: wealth is a random walk without drift. -/
theorem eq_11_30 (E : CondExpSystem ℝ V) {r ybar : ℝ} (hr : 0 < r) {one : V} {y c a : ℕ → V}
    (t : ℕ) (hyt : E.E t (y t) = y t) (hiid : ∀ j, E.E t (y (t + (j + 1))) = ybar • one)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j)))
    (hb : a (t + 1) = (1 + r) • (y t + a t - c t)) :
    c t = (ybar / (1 + r)) • one + (r / (1 + r)) • (a t + y t) ∧
      a (t + 1) = a t + y t - ybar • one := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hsum : ∑' j, q ^ j • E.E t (y (t + j)) = y t + (q * (1 - q)⁻¹ * ybar) • one := by
    have hs : Summable fun j => q ^ j • E.E t (y (t + j)) := by
      rw [← summable_nat_add_iff 1]
      simp_rw [hiid]
      exact (hg.comp_injective (add_left_injective 1)).smul_const _
    rw [hs.tsum_eq_zero_add]
    simp_rw [hiid]
    rw [(((summable_nat_add_iff 1).2 hg)).tsum_smul_const _]
    simp only [pow_zero, one_smul, add_zero, hyt]
    congr 1
    rw [smul_smul]
    congr 1
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hc : c t = (ybar / (1 + r)) • one + (r / (1 + r)) • (a t + y t) := by
    rw [h20, pih_rule, hsum, smul_add, smul_add, smul_smul]
    have : r / (1 + r) * (q * (1 - q)⁻¹ * ybar) = ybar / (1 + r) := by
      rw [mul_comm q, ← mul_assoc, ← mul_assoc, pih_annuity_inv hr, one_mul, hq]
      field_simp
    rw [this]
    module
  refine ⟨hc, ?_⟩
  rw [hb, hc]
  simp only [smul_sub, smul_add, smul_smul]
  rw [show (1 + r) * (ybar / (1 + r)) = ybar by field_simp,
    show (1 + r) * (r / (1 + r)) = r by field_simp]
  module

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Blundell and Preston: inequality in consumption and income

AKMM, §11.3.2, box "Using the PIH to learn about the nature of the rise in inequality",
(11.28), p. 300.

Within a cohort, income and consumption evolve as
`yₜ₊₁ = yₜ + uₜ₊₁ − uₜ + vₜ₊₁` and `cₜ₊₁ = cₜ + kuₜ₊₁ + vₜ₊₁` with `k = r/(1 + r)` ((11.26)
and (11.27)). The cross-sectional covariance is any symmetric bilinear form `B` on the space `V`
of random variables (the population covariance on `L²`, or a finite cross-section's covariance),
and the shocks of date `t + 1` are orthogonal to everything dated `t` and to each other.

* The exact laws of motion: `ΔVar(c) = k²Var(uₜ₊₁) + Var(vₜ₊₁)` (`bp_var_cons`) and
  `ΔCov(c, y) = k(Var(uₜ₊₁) − Var(uₜ)) + Var(vₜ₊₁)` (`bp_cov_cons_income`), using
  `Cov(cₜ, uₜ) = kVar(uₜ)` (`bp_cov_cons_trans`).
* **(11.28)** at `r = 0` (`k = 0`), `ΔVar(c) = ΔCov(c, y) = Var(v)` exactly (`eq_11_28`); with a
  stationary transitory variance, `ΔCov(c, y) = Var(v)` for every `r`
  (`bp_cov_stationary`).

Departure: the book's "`r ≃ 0`, … `≃ Var(v)`" becomes the exact statement at `r = 0`, together
with the exact error terms for `r ≠ 0`.
-/

namespace AKMM.Consumption

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- AKMM, p. 300: `Cov(cₜ, uₜ) = kVar(uₜ)` when `cₜ = cₜ₋₁ + kuₜ + vₜ` and `uₜ` is orthogonal
to `cₜ₋₁` and `vₜ`. -/
theorem bp_cov_cons_trans (B : LinearMap.BilinForm ℝ V) {k : ℝ}
    {c₀ c u v : V} (hc : c = c₀ + k • u + v) (h1 : B c₀ u = 0) (h2 : B v u = 0) :
    B c u = k * B u u := by
  subst hc
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- AKMM, p. 300: the cross-sectional variance of consumption under (11.27),
`Var(cₜ₊₁) = Var(cₜ) + k²Var(uₜ₊₁) + Var(vₜ₊₁)`. -/
theorem bp_var_cons (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c c' u' v' : V} (hc : c' = c + k • u' + v') (h1 : B c u' = 0) (h2 : B c v' = 0)
    (h3 : B u' v' = 0) : B c' c' - B c c = k ^ 2 * B u' u' + B v' v' := by
  subst hc
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hB u' c, hB v' c, hB v' u', h1, h2, h3]
  ring

/-- AKMM, p. 300: the cross-sectional covariance of consumption and income under (11.26) and
(11.27): `ΔCov(c, y) = k(Var(uₜ₊₁) − Var(uₜ)) + Var(vₜ₊₁)`, when the date-`t + 1` shocks are
orthogonal to `cₜ, yₜ, uₜ` and to each other, and `Cov(cₜ, uₜ) = kVar(uₜ)`. -/
theorem bp_cov_cons_income (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c y u c' y' u' v' : V} (hc : c' = c + k • u' + v') (hy : y' = y + u' - u + v')
    (hcu : B c u = k * B u u) (h1 : B c u' = 0) (h2 : B c v' = 0) (h3 : B y u' = 0)
    (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0) :
    B c' y' - B c y = k * (B u' u' - B u u) + B v' v' := by
  subst hc hy
  simp only [map_add, map_sub, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hB u' y, hB u' u, hB v' y, hB v' u, hB v' u', hcu, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- **AKMM, (11.28), p. 300 (Blundell and Preston 1998).** At `r = 0` the PIH laws of motion
(11.26)–(11.27) (`cₜ₊₁ = cₜ + vₜ₊₁`, since `k = r/(1 + r) = 0`) give
`ΔVar(c) = ΔCov(c, y) = Var(v)` exactly. -/
theorem eq_11_28 (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {c y u c' y' u' v' : V} (hc : c' = c + (0 / (1 + 0) : ℝ) • u' + v')
    (hy : y' = y + u' - u + v') (hcu : B c u = 0) (h1 : B c u' = 0) (h2 : B c v' = 0)
    (h3 : B y u' = 0) (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0) :
    B c' c' - B c c = B v' v' ∧ B c' y' - B c y = B v' v' := by
  have hk : (0 / (1 + 0) : ℝ) = 0 := by norm_num
  rw [hk] at hc
  refine ⟨by simpa using bp_var_cons B hB hc h1 h2 h7, ?_⟩
  have := bp_cov_cons_income B hB hc hy (by rw [hcu, zero_mul]) h1 h2 h3 h4 h5 h6 h7
  simpa using this

/-- AKMM, p. 300: if the transitory variance is the same at `t` and `t + 1`, the covariance
identity `ΔCov(c, y) = Var(v)` holds for every `r`, and the variance identity holds up to
`k²Var(u)`. -/
theorem bp_cov_stationary (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c y u c' y' u' v' : V} (hc : c' = c + k • u' + v') (hy : y' = y + u' - u + v')
    (hcu : B c u = k * B u u) (h1 : B c u' = 0) (h2 : B c v' = 0) (h3 : B y u' = 0)
    (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0)
    (hstat : B u' u' = B u u) :
    B c' y' - B c y = B v' v' ∧ B c' c' - B c c = k ^ 2 * B u u + B v' v' := by
  refine ⟨?_, by rw [bp_var_cons B hB hc h1 h2 h7, hstat]⟩
  rw [bp_cov_cons_income B hB hc hy hcu h1 h2 h3 h4 h5 h6 h7, hstat]
  ring

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Borrowing constraints and the natural borrowing limit

AKMM, §11.3.3, (11.31)–(11.32) and the natural borrowing limit, pp. 302–304, and the
borrowing-constraint part of §11.3.4, (11.33), pp. 304–305.

* **p. 302, the i.i.d. case.** Along the unconstrained PIH path of (11.30),
  `aₜ₊₁ = aₜ + yₜ − ȳ`: the book's example `yₜ < (1 − r)ȳ`, `aₜ < rȳ` gives `aₜ₊₁ < 0`
  (`bc_iid_example`); from any wealth, a run of `n` low incomes `y_lo < ȳ` (probability
  `pⁿ > 0`) takes wealth below zero in finite time (`bc_iid_hits`).
* **(11.32)** the modified Euler equation `u′(cₜ) = βREₜu′(cₜ₊₁) + λₜ`, `λₜ ≥ 0`, gives `≥`, strict
  iff the constraint binds (`eq_11_32`); at a binding constraint the household eats its cash in
  hand, with MPC `1` (`bc_binding_cons`).
* **The natural borrowing limit** (p. 303): nonnegative consumption and the no-Ponzi condition
  give `aₜ₊₁ ≥ −Σⱼ (1 + r)⁻ʲyₜ₊₁₊ⱼ` (`bc_natural_limit_det`); if income can stay at `y_min`
  forever, `aₜ₊₁ ≥ −(1 + r)y_min/r` (`bc_natural_limit`); borrowing up to the limit and drawing
  `y_min` forces `cₜ ≤ 0` (`bc_natural_limit_cons_nonpos`); with `y_min = 0` the limit is `0`
  (`bc_natural_limit_zero`).
* **(11.33)** with quadratic utility and `βR = 1`, `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}`
  (`eq_11_33`); below the kink the consumption function has slope `1` (`bc_slope_one`).

Departures: the "positive probability of hitting the limit" is proved for a run of identical low
draws whose probability is `pⁿ`; the stochastic natural limit is proved along the income path
that stays at `y_min` (the event the book uses).
-/

namespace AKMM.Consumption

open Filter Topology

/-- **AKMM, p. 302.** On the unconstrained i.i.d. path `aₜ₊₁ = aₜ + yₜ − ȳ`, if
`yₜ < (1 − r)ȳ` and `aₜ < rȳ` then `aₜ₊₁ < 0`: the no-borrowing limit would be violated. -/
theorem bc_iid_example {r ybar at' yt at1 : ℝ} (hdyn : at1 = at' + yt - ybar)
    (hy : yt < (1 - r) * ybar) (ha : at' < r * ybar) : at1 < 0 := by
  rw [hdyn]; nlinarith

/-- **AKMM, p. 302: "starting from any initial level of wealth there is always a positive
probability that … the household will hit the borrowing limit in finite time".** On the
unconstrained path `aₜ₊₁ = aₜ + yₜ − ȳ`, if income takes a value `y_lo < ȳ` with probability
`p > 0`, then from any `a₀` there is `n` such that `n` consecutive draws of `y_lo`, an event of
probability `pⁿ > 0`, give `aₙ < 0`. -/
theorem bc_iid_hits {ybar ylo p : ℝ} (hlo : ylo < ybar) (hp : 0 < p) (a₀ : ℝ) :
    ∃ n : ℕ, 0 < p ^ n ∧ ∀ a y : ℕ → ℝ, a 0 = a₀ → (∀ t, a (t + 1) = a t + y t - ybar) →
      (∀ t, t < n → y t = ylo) → a n < 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a₀ / (ybar - ylo))
  refine ⟨n, pow_pos hp n, fun a y ha0 hdyn hlow => ?_⟩
  have hk : ∀ k, k ≤ n → a k = a₀ - k * (ybar - ylo) := by
    intro k
    induction k with
    | zero => intro _; simp [ha0]
    | succ k ih =>
      intro hk
      rw [hdyn, ih (by omega), hlow k (by omega)]
      push_cast; ring
  rw [hk n le_rfl]
  have hd : 0 < ybar - ylo := by linarith
  rw [div_lt_iff₀ hd] at hn
  linarith

/-- **AKMM, (11.32), p. 303.** The first-order condition `u′(cₜ) = βREₜu′(cₜ₊₁) + λₜ` with
`λₜ ≥ 0` gives `u′(cₜ) ≥ βREₜu′(cₜ₊₁)`, with strict inequality exactly when `λₜ > 0` (the
constraint binds). -/
theorem eq_11_32 {mu emu βR lam : ℝ} (hfoc : mu = βR * emu + lam) (hlam : 0 ≤ lam) :
    βR * emu ≤ mu ∧ (βR * emu < mu ↔ 0 < lam) := by
  subst hfoc
  exact ⟨by linarith, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- AKMM, p. 303: at a binding constraint `aₜ₊₁ = 0` the budget gives `cₜ = aₜ + yₜ`, so the
marginal propensity to consume out of current income (transitory or permanent) is `1`. -/
theorem bc_binding_cons {R a y c : ℝ} (hR : R ≠ 0) (hbud : 0 = R * (a + y - c)) :
    c = a + y ∧ HasDerivAt (fun y' : ℝ => a + y') 1 y := by
  refine ⟨?_, by simpa using (hasDerivAt_id y).const_add a⟩
  rcases mul_eq_zero.1 hbud.symm with h | h
  · exact absurd h hR
  · linarith

/-- **AKMM, p. 303: the natural borrowing limit, deterministic income.** With `r > 0`, the budget,
nonnegative consumption, a convergent present value of income from `t + 1` and the no-Ponzi
condition (`(1 + r)^{−T}aₜ₊₁₊ᵀ` eventually above `−ε` for every `ε > 0`),
`aₜ₊₁ ≥ −Σⱼ (1 + r)⁻ʲyₜ₊₁₊ⱼ`. -/
theorem bc_natural_limit_det {r : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + 1 + j))
    (hnpg : ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ ((1 + r)⁻¹) ^ T * a (t + 1 + T)) :
    -∑' j, ((1 + r)⁻¹) ^ j * y (t + 1 + j) ≤ a (t + 1) := by
  have hR : (1 + r) ≠ 0 := by linarith
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  -- `Σ_{j<T} q^j y ≤ a + (stuff)`, from the iterated budget and `c ≥ 0`
  have hfin : ∀ T, ((1 + r)⁻¹) ^ T * a (t + 1 + T) - a (t + 1) ≤
      ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * y (t + 1 + j) := by
    intro T
    have h := cd_budget_iter hR hb (t + 1) T
    have hnn : 0 ≤ ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * c (t + 1 + j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hq0 j) (hc _)
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := hy.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ T in atTop, ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * y (t + 1 + j) <
      ∑' j, ((1 + r)⁻¹) ^ j * y (t + 1 + j) + ε / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, h1, h2⟩ := (hev.and (hnpg (ε / 2) (half_pos hε))).exists
  have := hfin T
  linarith

/-- **AKMM, p. 303: the natural borrowing limit** `aₜ₊₁ ≥ −(1 + r)y_min/r`. If income stays at
its lowest value `y_min` from `t + 1` on (an event the household must survive with nonnegative
consumption), the deterministic limit is `−Σⱼ (1 + r)⁻ʲy_min = −(1 + r)y_min/r`. -/
theorem bc_natural_limit {r ymin : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (hmin : ∀ j, y (t + 1 + j) = ymin)
    (hnpg : ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ ((1 + r)⁻¹) ^ T * a (t + 1 + T)) :
    -((1 + r) / r * ymin) ≤ a (t + 1) := by
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + 1 + j) := by
    simp_rw [hmin]; exact hg.mul_right _
  have h := bc_natural_limit_det hr hb hc t hy hnpg
  simp_rw [hmin] at h
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1] at h
  have e : (1 - (1 + r)⁻¹)⁻¹ * ymin = (1 + r) / r * ymin := by
    congr 1
    have : (1 + r) ≠ 0 := by linarith
    rw [show 1 - (1 + r)⁻¹ = r / (1 + r) by field_simp; ring, inv_div]
  linarith

/-- **AKMM, p. 304.** A household that has borrowed up to the natural limit,
`aₜ = −(1 + r)y_min/r`, and draws `yₜ = y_min` has `cₜ = aₜ + y_min − aₜ₊₁/(1 + r) ≤ 0` whenever
`aₜ₊₁` respects the limit. -/
theorem bc_natural_limit_cons_nonpos {r ymin at' at1 c : ℝ} (hr : 0 < r)
    (hat : at' = -((1 + r) / r * ymin)) (hlim : -((1 + r) / r * ymin) ≤ at1)
    (hbud : at1 = (1 + r) * (ymin + at' - c)) : c ≤ 0 := by
  have hR : 0 < 1 + r := by linarith
  have hc : c = at' + ymin - at1 / (1 + r) := by
    rw [hbud]; field_simp; ring
  have h1 : -((1 + r) / r * ymin) / (1 + r) ≤ at1 / (1 + r) := div_le_div_of_nonneg_right hlim hR.le
  have h2 : -((1 + r) / r * ymin) / (1 + r) = -(ymin / r) := by field_simp
  have h3 : -((1 + r) / r * ymin) + ymin = -(ymin / r) := by field_simp; ring
  rw [hc, hat]
  linarith

/-- AKMM, p. 304: if `y_min = 0` the natural borrowing limit is the no-borrowing constraint. -/
theorem bc_natural_limit_zero (r : ℝ) : -((1 + r) / r * 0) = 0 := by simp

/-- **AKMM, (11.33), p. 305.** Quadratic utility and `βR = 1` with the limit `aₜ₊₁ ≥ −a`: the
Euler inequality gives `cₜ ≤ Eₜcₜ₊₁`, with equality when the limit does not bind, and the budget
`aₜ₊₁ = R(yₜ + aₜ − cₜ)`. Then `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}`. -/
theorem eq_11_33 {R y a c a' abar ec : ℝ} (hR : 0 < R) (hbud : a' = R * (y + a - c))
    (hlim : -abar ≤ a') (heul : c ≤ ec) (hslack : -abar < a' → c = ec) :
    c = min (y + a + abar / R) ec := by
  have hc : c ≤ y + a + abar / R := by
    have h1 : -abar ≤ R * (y + a - c) := hbud ▸ hlim
    have h2 : c - y - a ≤ abar / R := by rw [le_div_iff₀ hR]; nlinarith
    linarith
  rcases hlim.lt_or_eq with h | h
  · rw [hslack h] at hc ⊢; exact (min_eq_right hc).symm
  · have hc' : c = y + a + abar / R := by
      rw [← h] at hbud
      field_simp
      linarith
    rw [← hc']
    exact (min_eq_left heul).symm

/-- AKMM, p. 305 and Figure 11.2: where the constraint binds, `c(a) = a + y + a/R`, so the
consumption function has slope `1` in wealth. -/
theorem bc_slope_one (y abar R a : ℝ) :
    HasDerivAt (fun x : ℝ => x + y + abar / R) 1 a := by
  simpa using ((hasDerivAt_id a).add_const y).add_const (abar / R)

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Precautionary saving

AKMM, §11.3.4, pp. 304–309: the precautionary motive with borrowing constraints, (11.34), and
with prudence, (11.35)–(11.40), with footnotes 17–19.

A mean-preserving spread is stated as the **convex order** (`pr_ConvexOrderOn Y μ ν`: both laws
live on `Y` and `∫φ dμ ≤ ∫φ dν` for every `φ` convex on `Y` that both integrate). By
Rothschild–Stiglitz (the book's fn. 17) this is the MPS order for distributions with the same
mean; the characterisation itself is not proved. Two-point spreads are an instance
(`pr_two_point_spread`), and the convex order preserves the mean (`pr_convexOrder_mean`).

* **(11.34)** a spread in next-period income lowers `Eₜ min{yₜ₊₁ + aₜ₊₁ + a/R, Eₜ₊₁cₜ₊₂}`
  (`eq_11_34_spread`).
* **(11.35)** the Euler equation `u′(y₀ − a₁) = βRE₀u′(Ra₁ + y₁)` has at most one root
  (`eq_11_35_unique`); the comparative-statics step (`pr_root_mono`); with `u′` convex, a
  mean-preserving spread of `y₁` raises saving (`pr_spread_raises_saving`); for a two-point
  spread saving rises iff `u′` is midpoint convex at the old `c₁` (`pr_two_point_iff`); with
  quadratic utility a spread leaves the Euler equation unchanged (`pr_quadratic_no_precaution`).
* **DARA ⇒ prudence** (p. 307): `α′ = (−u‴u′ + (u″)²)/(u′)²` (`pr_ara_deriv`), and `α′ < 0`
  gives `u‴ > (u″)²/u′ > 0` (`pr_dara_prudent`).
* **(11.36)** (Blanchard–Mankiw) holds exactly when `u′` is quadratic on the support, with
  `r − ρ` replaced by `(r − ρ)/(1 + r) = 1 − (βR)⁻¹` (`eq_11_36_exact`, `pr_betaR_inv`).
* **(11.37)–(11.40)** differentiating the envelope condition: `c′ = V″/u″ > 0` (`eq_11_38`),
  `c″` (`eq_11_39`), and `c″ ≤ 0` iff `V‴V′/(V″)² ≥ u‴u′/(u″)²` (`eq_11_40`).
* **Footnote 19, HARA:** the risk tolerance `T = −u′/u″` has `T′ = κ − 1`, `κ = u‴u′/(u″)²`
  (`pr_tolerance_deriv`), so `T` affine gives `κ` constant (`pr_hara_kappa_const`); quadratic
  `κ = 0`, CARA `κ = 1`, CRRA `κ = (σ + 1)/σ > 1` (`pr_kappa_quadratic`, `pr_kappa_cara`,
  `pr_kappa_crra`). **Correction:** `κ ≥ 0` needs prudence: the HARA marginal utility
  `√(1 − 2c)` has `κ = −1` (`pr_hara_kappa_neg`).
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology

/-! ### The convex order -/

/-- AKMM, p. 306 and fn. 17: `ν` is a mean-preserving spread of `μ` on `Y`, as the convex order:
both laws live on `Y`, and `∫φ dμ ≤ ∫φ dν` for every `φ` convex on `Y` integrable under both. -/
def pr_ConvexOrderOn (Y : Set ℝ) (μ ν : Measure ℝ) : Prop :=
  (∀ᵐ y ∂μ, y ∈ Y) ∧ (∀ᵐ y ∂ν, y ∈ Y) ∧
    ∀ φ : ℝ → ℝ, ConvexOn ℝ Y φ → Integrable φ μ → Integrable φ ν → ∫ y, φ y ∂μ ≤ ∫ y, φ y ∂ν

/-- The convex order preserves the mean (apply it to `y` and `−y`). -/
theorem pr_convexOrder_mean {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ}
    (h : pr_ConvexOrderOn Y μ ν) (hμ : Integrable (fun y => y) μ)
    (hν : Integrable (fun y => y) ν) : ∫ y, y ∂μ = ∫ y, y ∂ν := by
  have h1 := h.2.2 (fun y => y) (convexOn_id hY) hμ hν
  have h2 := h.2.2 (fun y => -y) (concaveOn_id hY).neg hμ.neg hν.neg
  rw [integral_neg, integral_neg] at h2
  linarith

/-- A two-point mean-preserving spread: `δₘ` is below `½δ_{m−h} + ½δ_{m+h}` in the convex order on
any convex `Y` containing `m ± h` (Jensen). This is the instance behind fn. 17. -/
theorem pr_two_point_spread {Y : Set ℝ} {m h : ℝ} (hY : Convex ℝ Y) (h1 : m - h ∈ Y)
    (h2 : m + h ∈ Y) :
    pr_ConvexOrderOn Y (Measure.dirac m)
      ((1 / 2 : ENNReal) • Measure.dirac (m - h) + (1 / 2 : ENNReal) • Measure.dirac (m + h)) := by
  have hm : m ∈ Y := by
    have := hY h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1; ring
  refine ⟨by rw [ae_dirac_eq]; exact hm, ?_, fun φ hφ _ hν => ?_⟩
  · rw [ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h1) _,
      Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h2) _⟩
  · rw [integral_add_measure (hν.mono_measure (Measure.le_add_right le_rfl))
      (hν.mono_measure (Measure.le_add_left le_rfl)), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, integral_dirac]
    have := hφ.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • (m - h) + (1 / 2 : ℝ) • (m + h) = m := by simp only [smul_eq_mul]; ring
    rw [e] at this
    simp only [smul_eq_mul] at this ⊢
    norm_num at this ⊢
    linarith

/-! ### Borrowing constraints: (11.34) -/

/-- **AKMM, (11.34), p. 305.** `y ↦ min{y + A, K}` is concave, so a mean-preserving spread of
next-period income lowers `E min{yₜ₊₁ + aₜ₊₁ + a/R, Eₜ₊₁cₜ₊₂}` (with `A = aₜ₊₁ + a/R` and
`K = Eₜ₊₁cₜ₊₂` held fixed): consumption today falls and saving rises. -/
theorem eq_11_34_spread {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ}
    (h : pr_ConvexOrderOn Y μ ν) (A K : ℝ) (hμ : Integrable (fun y => min (y + A) K) μ)
    (hν : Integrable (fun y => min (y + A) K) ν) :
    ∫ y, min (y + A) K ∂ν ≤ ∫ y, min (y + A) K ∂μ := by
  have hconc : ConcaveOn ℝ Y fun y => min (y + A) K :=
    ((concaveOn_id hY).add_const A).inf (concaveOn_const K hY)
  have := h.2.2 _ hconc.neg hμ.neg hν.neg
  simp only [Pi.neg_apply] at this
  rw [integral_neg, integral_neg] at this
  linarith

/-! ### Prudence: the two-period problem (11.35) -/

/-- **AKMM, (11.35), p. 306: "the solution for `a₁` is uniquely determined".** If the left side
`F` is strictly increasing and the right side `G` antitone (on a set `S`), the Euler equation
`F(a₁) = G(a₁)` has at most one root in `S`. -/
theorem eq_11_35_unique {S : Set ℝ} {F G : ℝ → ℝ} (hF : StrictMonoOn F S) (hG : AntitoneOn G S)
    {a a' : ℝ} (ha : a ∈ S) (ha' : a' ∈ S) (h : F a = G a) (h' : F a' = G a') : a = a' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hF ha ha' hlt; have := hG ha ha' hlt.le; linarith
  · have := hF ha' ha hlt; have := hG ha' ha hlt.le; linarith

/-- AKMM, p. 306 (Figure 11.3): the comparative statics of (11.35). The left side `F` is strictly
increasing; the new right side `G₂` is antitone and lies above the old one at the old root `a₁`.
Then the new root `a₂` is at least `a₁`. -/
theorem pr_root_mono {F G₁ G₂ : ℝ → ℝ} {a₁ a₂ : ℝ}
    (hG₂ : a₂ < a₁ → G₂ a₁ ≤ G₂ a₂) (h₁ : F a₁ = G₁ a₁) (h₂ : F a₂ = G₂ a₂)
    (hup : G₁ a₁ ≤ G₂ a₁) (hFmono : a₂ < a₁ → F a₂ < F a₁) : a₁ ≤ a₂ := by
  by_contra hlt
  push Not at hlt
  have := hFmono hlt
  have := hG₂ hlt
  linarith

/-- The right side of (11.35), `βRE u′(Ra₁ + y₁)` under the law `μ` of `y₁`. -/
noncomputable def pr_rhs (du : ℝ → ℝ) (β R : ℝ) (μ : Measure ℝ) (a : ℝ) : ℝ :=
  β * R * ∫ y, du (R * a + y) ∂μ

/-- **AKMM, p. 306: prudence and precautionary saving.** Let `u′` be strictly decreasing and
convex on `(0, ∞)`, `β, R > 0`, and let the law `ν` of `y₁` be a mean-preserving spread of `μ`
on the convex set `Y` (convex order). If `a₁` solves (11.35) under `μ`, `a₂` solves it under `ν`,
and both plans have positive consumption (`y₀ − aᵢ > 0`, `Raᵢ + y > 0` on `Y`), then `a₂ ≥ a₁`:
the spread raises saving. -/
theorem pr_spread_raises_saving {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0))
    (hconv : ConvexOn ℝ (Set.Ioi 0) du) {β R y₀ a₁ a₂ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ} (hspread : pr_ConvexOrderOn Y μ ν)
    (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂) (hc₁ : ∀ y ∈ Y, 0 < R * a₁ + y)
    (hc₂ : ∀ y ∈ Y, 0 < R * a₂ + y)
    (hμ₁ : Integrable (fun y => du (R * a₁ + y)) μ) (hν₁ : Integrable (fun y => du (R * a₁ + y)) ν)
    (hν₂ : Integrable (fun y => du (R * a₂ + y)) ν)
    (h₁ : du (y₀ - a₁) = pr_rhs du β R μ a₁) (h₂ : du (y₀ - a₂) = pr_rhs du β R ν a₂) :
    a₁ ≤ a₂ := by
  -- `y ↦ u′(Ra₁ + y)` is convex on `Y`
  have hφ : ConvexOn ℝ Y fun y => du (R * a₁ + y) := by
    refine ⟨hY, fun x hx z hz s t hs ht hst => ?_⟩
    have e : R * a₁ + (s • x + t • z) = s • (R * a₁ + x) + t • (R * a₁ + z) := by
      simp only [smul_eq_mul]
      linear_combination (-(R * a₁)) * hst
    simp only [e]
    exact hconv.2 (hc₁ x hx) (hc₁ z hz) hs ht hst
  have hup : pr_rhs du β R μ a₁ ≤ pr_rhs du β R ν a₁ := by
    unfold pr_rhs
    exact mul_le_mul_of_nonneg_left (hspread.2.2 _ hφ hμ₁ hν₁) (mul_pos hβ hR).le
  by_contra hlt
  push Not at hlt
  -- the left side is strictly increasing in `a`
  have hF : du (y₀ - a₂) < du (y₀ - a₁) :=
    hdu hc₀₁ hc₀₂ (by linarith)
  -- the right side under `ν` is antitone in `a`
  have hG : pr_rhs du β R ν a₁ ≤ pr_rhs du β R ν a₂ := by
    unfold pr_rhs
    refine mul_le_mul_of_nonneg_left (integral_mono_ae hν₁ hν₂ ?_) (mul_pos hβ hR).le
    filter_upwards [hspread.2.1] with y hy
    exact (hdu.antitoneOn (hc₂ y hy) (hc₁ y hy) (by nlinarith))
  linarith

/-- **AKMM, p. 306: "if `u′` is convex then … the right-hand side will increase", and
conversely.** For the two-point spread of a sure income `m` into `m ± h`, with roots `a₁` (sure
income) and `a₂` (spread) of (11.35) and positive consumption in both plans: saving weakly rises
iff `u′` is midpoint convex at the old second-period consumption `x = Ra₁ + m`,
`u′(x) ≤ (u′(x − h) + u′(x + h))/2`. -/
theorem pr_two_point_iff {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0)) {β R y₀ m h a₁ a₂ : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂)
    (hlo₁ : 0 < R * a₁ + (m - h)) (hlo₂ : 0 < R * a₂ + (m - h)) (hh : 0 ≤ h)
    (h₁ : du (y₀ - a₁) = β * R * du (R * a₁ + m))
    (h₂ : du (y₀ - a₂) = β * R * ((du (R * a₂ + (m - h)) + du (R * a₂ + (m + h))) / 2)) :
    a₁ ≤ a₂ ↔ du (R * a₁ + m) ≤ (du (R * a₁ + m - h) + du (R * a₁ + m + h)) / 2 := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hG : ∀ {a a' : ℝ}, 0 < R * a + (m - h) → a ≤ a' →
      (du (R * a' + (m - h)) + du (R * a' + (m + h))) / 2 ≤
        (du (R * a + (m - h)) + du (R * a + (m + h))) / 2 := by
    intro a a' ha haa
    have h1 : du (R * a' + (m - h)) ≤ du (R * a + (m - h)) :=
      hdu.antitoneOn (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (by nlinarith)) (by nlinarith)
    have h2 : du (R * a' + (m + h)) ≤ du (R * a + (m + h)) :=
      hdu.antitoneOn (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by nlinarith)) (by nlinarith)
    linarith
  have e1 : R * a₁ + m - h = R * a₁ + (m - h) := by ring
  have e2 : R * a₁ + m + h = R * a₁ + (m + h) := by ring
  rw [e1, e2]
  constructor
  · intro hle
    -- `F(a₁) ≤ F(a₂) = G₂(a₂) ≤ G₂(a₁)`
    have hF : du (y₀ - a₁) ≤ du (y₀ - a₂) :=
      hdu.antitoneOn (Set.mem_Ioi.2 hc₀₂) (Set.mem_Ioi.2 hc₀₁) (by linarith)
    have := hG hlo₁ hle
    have : β * R * du (R * a₁ + m) ≤
        β * R * ((du (R * a₁ + (m - h)) + du (R * a₁ + (m + h))) / 2) := by
      rw [← h₁]; calc du (y₀ - a₁) ≤ du (y₀ - a₂) := hF
        _ = _ := h₂
        _ ≤ _ := mul_le_mul_of_nonneg_left this hβR.le
    exact le_of_mul_le_mul_left this hβR
  · intro hconv
    by_contra hlt
    push Not at hlt
    have hF : du (y₀ - a₂) < du (y₀ - a₁) := hdu (Set.mem_Ioi.2 hc₀₁) (Set.mem_Ioi.2 hc₀₂)
      (by linarith)
    have := hG hlo₂ hlt.le
    have := mul_le_mul_of_nonneg_left hconv hβR.le
    have := mul_le_mul_of_nonneg_left (hG hlo₂ hlt.le) hβR.le
    linarith

/-- **AKMM, p. 304: no precautionary saving with quadratic utility.** If `u′(c) = b₁ − b₂c`, the
right side of (11.35) depends on the law of `y₁` only through its mean, so a mean-preserving
spread (convex order) leaves the Euler equation, and hence saving, unchanged. -/
theorem pr_quadratic_no_precaution {b₁ b₂ β R a : ℝ} {Y : Set ℝ} (hY : Convex ℝ Y)
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hspread : pr_ConvexOrderOn Y μ ν) (hμ : Integrable (fun y => y) μ)
    (hν : Integrable (fun y => y) ν) :
    pr_rhs (fun c => b₁ - b₂ * c) β R μ a = pr_rhs (fun c => b₁ - b₂ * c) β R ν a := by
  have hm := pr_convexOrder_mean hY hspread hμ hν
  unfold pr_rhs
  have hint : ∀ ρ : Measure ℝ, [IsProbabilityMeasure ρ] → Integrable (fun y => y) ρ →
      ∫ y, b₁ - b₂ * (R * a + y) ∂ρ = b₁ - b₂ * (R * a + ∫ y, y ∂ρ) := by
    intro ρ _ hρ
    have h1 : Integrable (fun y => b₂ * (R * a + y)) ρ :=
      ((integrable_const (R * a)).add hρ).const_mul b₂
    rw [integral_sub (integrable_const b₁) h1, integral_const, integral_const_mul,
      integral_add (integrable_const _) hρ, integral_const]
    simp
  rw [hint μ hμ, hint ν hν, hm]

/-! ### DARA implies prudence -/

/-- **AKMM, p. 307.** The coefficient of absolute risk aversion `α = −u″/u′` has derivative
`α′ = (−u‴u′ + (u″)²)/(u′)²`. -/
theorem pr_ara_deriv {u1 u2 : ℝ → ℝ} {c u3c : ℝ} (h1 : HasDerivAt u1 (u2 c) c)
    (h2 : HasDerivAt u2 u3c c) (hne : u1 c ≠ 0) :
    HasDerivAt (fun x => -u2 x / u1 x) ((-u3c * u1 c + u2 c ^ 2) / u1 c ^ 2) c := by
  have := h2.neg.div h1 hne
  convert this using 1
  simp only [Pi.neg_apply]
  ring

/-- **AKMM, p. 307: DARA implies prudence.** If `u′ > 0`, `u″ ≠ 0` and absolute risk aversion is
strictly decreasing at `c` (`α′(c) < 0`), then `u‴(c) > (u″(c))²/u′(c) > 0`. -/
theorem pr_dara_prudent {u1c u2c u3c : ℝ} (h1 : 0 < u1c) (h2 : u2c ≠ 0)
    (hdara : (-u3c * u1c + u2c ^ 2) / u1c ^ 2 < 0) : u2c ^ 2 / u1c < u3c ∧ 0 < u2c ^ 2 / u1c := by
  have hpos : 0 < u1c ^ 2 := by positivity
  rw [div_lt_iff₀ hpos, zero_mul] at hdara
  refine ⟨?_, div_pos (by positivity) h1⟩
  rw [div_lt_iff₀ h1]
  linarith

/-! ### Blanchard–Mankiw (11.36) -/

/-- AKMM, p. 308: with `β = 1/(1 + ρ)`, `1 − (βR)⁻¹ = (r − ρ)/(1 + r)` exactly; the book uses
`(βR)⁻¹ ≃ 1 + ρ − r`. -/
theorem pr_betaR_inv {r ρ : ℝ} (hr : 0 < 1 + r) :
    1 - (1 / (1 + ρ) * (1 + r))⁻¹ = (r - ρ) / (1 + r) := by
  field_simp
  ring

/-- **AKMM, (11.36), p. 308 (Blanchard and Mankiw 1988), exact version.** Let next-period
consumption take the values `c′ₖ` with probabilities `pₖ` (summing to `1`), and let `u′` be
quadratic on the support: `u′(c′ₖ) = u′(c) + u″(c)(c′ₖ − c) + ½u‴(c)(c′ₖ − c)²` (cubic `u`).
Then the Euler equation `u′(c) = βREu′(c′)` gives
`E[(c′ − c)/c] = EIS(c)(1 − (βR)⁻¹) + ½P(c)E[((c′ − c)/c)²]` with `EIS = −u′/(cu″)` and
`P = −u‴c/u″`. -/
theorem eq_11_36_exact {ι : Type*} [Fintype ι] {p c' : ι → ℝ} (hp : ∑ k, p k = 1)
    {c u1c u2c u3c βR : ℝ} (hc : 0 < c) (hu2 : u2c ≠ 0) (hβR : 0 < βR) {du : ℝ → ℝ}
    (htaylor : ∀ k, du (c' k) = u1c + u2c * (c' k - c) + 1 / 2 * u3c * (c' k - c) ^ 2)
    (heuler : u1c = βR * ∑ k, p k * du (c' k)) :
    ∑ k, p k * ((c' k - c) / c) =
      (-u1c / (c * u2c)) * (1 - βR⁻¹) +
        1 / 2 * (-u3c * c / u2c) * ∑ k, p k * ((c' k - c) / c) ^ 2 := by
  have hm1 : ∑ k, p k * ((c' k - c) / c) = (∑ k, p k * c' k - c) / c := by
    rw [eq_div_iff hc.ne', Finset.sum_mul]
    have : ∀ k, p k * ((c' k - c) / c) * c = p k * c' k - p k * c := fun k => by
      field_simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  have hm2 : ∑ k, p k * ((c' k - c) / c) ^ 2 = (∑ k, p k * (c' k - c) ^ 2) / c ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by rw [div_pow]; ring
  have hEdu : ∑ k, p k * du (c' k) = u1c + u2c * (∑ k, p k * c' k - c) +
      1 / 2 * u3c * ∑ k, p k * (c' k - c) ^ 2 := by
    simp_rw [htaylor]
    have : ∀ k, p k * (u1c + u2c * (c' k - c) + 1 / 2 * u3c * (c' k - c) ^ 2) =
        u1c * p k + u2c * (p k * c' k) - u2c * c * p k + 1 / 2 * u3c * (p k * (c' k - c) ^ 2) :=
      fun k => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hp]
    ring
  rw [hm1, hm2]
  rw [hEdu] at heuler
  generalize ∑ k, p k * c' k = m1 at heuler ⊢
  generalize ∑ k, p k * (c' k - c) ^ 2 = M2 at heuler ⊢
  have hm : m1 - c = (u1c * βR⁻¹ - u1c - 1 / 2 * u3c * M2) / u2c := by
    rw [eq_div_iff hu2]
    have : u1c * βR⁻¹ = u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2 :=
      calc u1c * βR⁻¹ = βR * (u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2) * βR⁻¹ := by
            rw [← heuler]
        _ = u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2 := by field_simp
    linarith
  rw [hm]
  field_simp
  ring

/-! ### Concavity of the consumption function: (11.37)–(11.40) -/

/-- **AKMM, (11.38), p. 308.** If the envelope condition (11.37) `u′(c(a)) = V′(a)` holds near
`a`, `c` is differentiable at `a`, `u′` has derivative `u″` at `c(a)` and `V′` has derivative
`V″(a)`, then `c′(a) = V″(a)/u″(c(a))`; with `V″ < 0` and `u″ < 0`, `c′(a) > 0`. -/
theorem eq_11_38 {u1 V1 c : ℝ → ℝ} {a c1 u2c V2a : ℝ}
    (henv : ∀ᶠ x in 𝓝 a, u1 (c x) = V1 x) (hc : HasDerivAt c c1 a)
    (hu : HasDerivAt u1 u2c (c a)) (hV : HasDerivAt V1 V2a a) (hu2 : u2c < 0) (hV2 : V2a < 0) :
    c1 = V2a / u2c ∧ 0 < c1 := by
  have h1 : HasDerivAt (fun x => u1 (c x)) (u2c * c1) a := hu.comp a hc
  have h2 : HasDerivAt (fun x => u1 (c x)) V2a a := hV.congr_of_eventuallyEq henv
  have e := h1.unique h2
  have hc1 : c1 = V2a / u2c := by rw [eq_div_iff hu2.ne]; linarith
  exact ⟨hc1, by rw [hc1]; exact div_pos_of_neg_of_neg hV2 hu2⟩

/-- **AKMM, (11.39), p. 308.** Differentiating `c′(a) = V″(a)/u″(c(a))`:
`c″(a) = (V‴(a)u″(c(a)) − V″(a)u‴(c(a))c′(a))/[u″(c(a))]²`. -/
theorem eq_11_39 {u2 V2 c : ℝ → ℝ} {a c1 u3c V3a : ℝ} (hc : HasDerivAt c c1 a)
    (hu : HasDerivAt u2 u3c (c a)) (hV : HasDerivAt V2 V3a a) (hne : u2 (c a) ≠ 0) :
    HasDerivAt (fun x => V2 x / u2 (c x))
      ((V3a * u2 (c a) - V2 a * (u3c * c1)) / u2 (c a) ^ 2) a :=
  hV.div (hu.comp a hc) hne

/-- **AKMM, (11.40), p. 309 (Carroll and Kimball 1996, Lemma 2).** With the envelope condition
`V′(a) = u′(c(a)) > 0`, `c′ = V″/u″`, `u″ < 0` and `V″ ≠ 0`: the expression (11.39) for `c″` is
`≤ 0` iff `V‴V′/(V″)² ≥ u‴u′/(u″)²`. -/
theorem eq_11_40 {V1a V2a V3a u1c u2c u3c c1 : ℝ} (henv : V1a = u1c) (hu1 : 0 < u1c)
    (hu2 : u2c < 0) (hV2 : V2a ≠ 0) (hc1 : c1 = V2a / u2c) :
    (V3a * u2c - V2a * (u3c * c1)) / u2c ^ 2 ≤ 0 ↔
      u3c * u1c / u2c ^ 2 ≤ V3a * V1a / V2a ^ 2 := by
  subst henv hc1
  have hu2sq : 0 < u2c ^ 2 := by nlinarith
  have hV2sq : 0 < V2a ^ 2 := by positivity
  have h3 : u2c ^ 3 < 0 := Odd.pow_neg (by decide) hu2
  have e : (V3a * u2c - V2a * (u3c * (V2a / u2c))) / u2c ^ 2 =
      (V3a * u2c ^ 2 - u3c * V2a ^ 2) / u2c ^ 3 := by
    field_simp
  rw [e, div_nonpos_iff, div_le_div_iff₀ hu2sq hV2sq]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · nlinarith [mul_nonneg hu1.le h1]
    · exact absurd h2 (not_le.2 h3)
  · intro h
    left
    refine ⟨?_, h3.le⟩
    by_contra hD
    push Not at hD
    nlinarith [mul_neg_of_pos_of_neg hu1 hD]

/-! ### HARA and footnote 19 -/

/-- The index `κ = u‴u′/(u″)²` of (11.40) (prudence relative to risk aversion). -/
noncomputable def pr_kappa (u1c u2c u3c : ℝ) : ℝ := u3c * u1c / u2c ^ 2

/-- AKMM, p. 308 and fn. 18–19: the absolute risk tolerance `T = −u′/u″` has derivative
`T′ = κ − 1`. -/
theorem pr_tolerance_deriv {u1 u2 : ℝ → ℝ} {c u3c : ℝ} (h1 : HasDerivAt u1 (u2 c) c)
    (h2 : HasDerivAt u2 u3c c) (hne : u2 c ≠ 0) :
    HasDerivAt (fun x => -u1 x / u2 x) (pr_kappa (u1 c) (u2 c) u3c - 1) c := by
  have := h1.neg.div h2 hne
  convert this using 1
  simp only [Pi.neg_apply]
  unfold pr_kappa
  field_simp
  ring

/-- **AKMM, p. 309, fn. 18: HARA gives a constant `κ`.** If the risk tolerance is affine,
`−u′(c)/u″(c) = η + sc` on an open set `S`, then `κ = 1 + s` on `S`. -/
theorem pr_hara_kappa_const {u1 u2 u3 : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) {η s : ℝ}
    (h1 : ∀ c ∈ S, HasDerivAt u1 (u2 c) c) (h2 : ∀ c ∈ S, HasDerivAt u2 (u3 c) c)
    (hne : ∀ c ∈ S, u2 c ≠ 0) (hT : ∀ c ∈ S, -u1 c / u2 c = η + s * c) :
    ∀ c ∈ S, pr_kappa (u1 c) (u2 c) (u3 c) = 1 + s := by
  intro c hc
  have hd := pr_tolerance_deriv (h1 c hc) (h2 c hc) (hne c hc)
  have hT' : HasDerivAt (fun x => -u1 x / u2 x) s c := by
    have : HasDerivAt (fun x => η + s * x) s c := by
      simpa using ((hasDerivAt_id c).const_mul s).const_add η
    exact this.congr_of_eventuallyEq (Filter.eventually_of_mem (hS.mem_nhds hc) hT)
  have := hd.unique hT'
  linarith

/-- **AKMM, fn. 19: quadratic utility has `κ = 0`** (`u′ = b₁ − b₂c`, `u″ = −b₂`, `u‴ = 0`). -/
theorem pr_kappa_quadratic (b₁ b₂ c : ℝ) : pr_kappa (b₁ - b₂ * c) (-b₂) 0 = 0 := by
  simp [pr_kappa]

/-- **AKMM, fn. 19: CARA utility has `κ = 1`** (`u′ = e^{−θc}`, `u″ = −θe^{−θc}`,
`u‴ = θ²e^{−θc}`, `θ ≠ 0`). -/
theorem pr_kappa_cara {θ : ℝ} (hθ : θ ≠ 0) (c : ℝ) :
    pr_kappa (Real.exp (-θ * c)) (-θ * Real.exp (-θ * c)) (θ ^ 2 * Real.exp (-θ * c)) = 1 := by
  unfold pr_kappa
  have := Real.exp_pos (-θ * c)
  field_simp

/-- **AKMM, fn. 19: CRRA utility has `κ = (σ + 1)/σ > 1`** (`u′ = c^{−σ}`, `u″ = −σc^{−σ−1}`,
`u‴ = σ(σ + 1)c^{−σ−2}`, `c, σ > 0`). -/
theorem pr_kappa_crra {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    pr_kappa (c ^ (-σ)) (-σ * c ^ (-σ - 1)) (σ * (σ + 1) * c ^ (-σ - 2)) = (σ + 1) / σ ∧
      1 < (σ + 1) / σ := by
  refine ⟨?_, by rw [lt_div_iff₀ hσ]; linarith⟩
  unfold pr_kappa
  have e1 : c ^ (-σ - 2) * c ^ (-σ) = (c ^ (-σ - 1)) ^ 2 := by
    rw [← Real.rpow_add hc, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num; ring_nf
  have hp : 0 < c ^ (-σ - 1) := Real.rpow_pos_of_pos hc _
  rw [mul_assoc, e1, mul_pow, neg_sq]
  field_simp

/-- The derivatives of the HARA marginal utility `u′(c) = (1 − 2c)^{1/2}` on `c < 1/2`
(risk tolerance `−u′/u″ = 1 − 2c`, slope `s = −2`). -/
theorem pr_hara_neg_derivs {c : ℝ} (hc : c < 1 / 2) :
    HasDerivAt (fun x : ℝ => (1 - 2 * x) ^ (1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-1 / 2 : ℝ)) c ∧
      HasDerivAt (fun x : ℝ => -(1 - 2 * x) ^ (-1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-3 / 2 : ℝ)) c := by
  have hpos : 0 < 1 - 2 * c := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) c := by
    simpa using ((hasDerivAt_id c).const_mul 2).const_sub 1
  constructor
  · have := hlin.rpow_const (p := 1 / 2) (Or.inl hpos.ne')
    convert this using 1
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]; ring
  · have := (hlin.rpow_const (p := -1 / 2) (Or.inl hpos.ne')).neg
    convert this using 1
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num]; ring

/-- **Correction to AKMM, p. 309** ("if `u` belongs to the HARA class, then … the right hand side
of (11.40) is equal to a constant `κ ≥ 0`"). Without prudence `κ` can be negative: the HARA
marginal utility `u′(c) = (1 − 2c)^{1/2}` (`u′ > 0`, `u″ < 0` on `c < 1/2`) has `κ = −1`. -/
theorem pr_hara_kappa_neg {c : ℝ} (hc : c < 1 / 2) :
    0 < (1 - 2 * c) ^ (1 / 2 : ℝ) ∧ -(1 - 2 * c) ^ (-1 / 2 : ℝ) < 0 ∧
      pr_kappa ((1 - 2 * c) ^ (1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-1 / 2 : ℝ))
        (-(1 - 2 * c) ^ (-3 / 2 : ℝ)) = -1 := by
  have hpos : 0 < 1 - 2 * c := by linarith
  refine ⟨Real.rpow_pos_of_pos hpos _, neg_neg_of_pos (Real.rpow_pos_of_pos hpos _), ?_⟩
  unfold pr_kappa
  have e : (1 - 2 * c) ^ (-3 / 2 : ℝ) * (1 - 2 * c) ^ (1 / 2 : ℝ) =
      ((1 - 2 * c) ^ (-1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hp : 0 < (1 - 2 * c) ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  rw [neg_mul, e, neg_sq]
  field_simp

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Capital income uncertainty

AKMM, §11.3.4, box "Capital income uncertainty", pp. 309–310.

With `y₀ = c₀ + a₁` and `c₁ = Ra₁` for a random gross return `R > 0`, the Euler equation is
`u′(y₀ − a₁) = βE[Ru′(Ra₁)]`. The box claims that "under prudence … the right-hand side is still
a convex function of `r` (it is the product of a linear and a convex function)", so that saving
rises with a mean-preserving spread of the return. This is false.

* `d²/dR²[Ru′(Ra)] = a[2u″(c) + cu‴(c)]`, `c = Ra` (`cr_deriv`, `cr_second_deriv`), which is
  `≥ 0` iff relative prudence `−cu‴(c)/u″(c) ≥ 2` (`cr_second_deriv_nonneg_iff`).
* **Corrected claim:** if relative prudence is at least `2`, `R ↦ Ru′(Ra)` is convex
  (`cr_convex_of_rel_prudence`) and a mean-preserving spread of the return raises saving
  (`cr_spread_raises_saving`). For CRRA (relative prudence `σ + 1`) this is `σ ≥ 1`.
* **Counterexamples:** with log utility (`σ = 1`, prudent) return risk has no effect on saving
  (`cr_log_return_risk_neutral`); with `σ = 1/2` (prudent, `u‴ > 0`) the two-point spread of
  `R = 1` into `R = 1/2, 3/2` (a convex-order spread, `cr_return_spread_instance`) strictly
  lowers saving (`cr_printed_counterexample`).
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology

/-- AKMM, p. 309: the first derivative of `R ↦ Ru′(Ra)`, `u′(Ra) + Rau″(Ra)`. -/
theorem cr_deriv {u1 u2 : ℝ → ℝ} {a R : ℝ} (h1 : HasDerivAt u1 (u2 (R * a)) (R * a)) :
    HasDerivAt (fun x => x * u1 (x * a)) (u1 (R * a) + R * a * u2 (R * a)) R := by
  have hl : HasDerivAt (fun x : ℝ => x * a) a R := by simpa using (hasDerivAt_id R).mul_const a
  have := (hasDerivAt_id R).mul (h1.comp R hl)
  exact this.congr_deriv (by simp only [id, Function.comp_apply]; ring)

/-- AKMM, p. 309: the second derivative of `R ↦ Ru′(Ra)` is `a[2u″(c) + cu‴(c)]`, `c = Ra`. -/
theorem cr_second_deriv {u1 u2 u3 : ℝ → ℝ} {a R : ℝ} (h1 : HasDerivAt u1 (u2 (R * a)) (R * a))
    (h2 : HasDerivAt u2 (u3 (R * a)) (R * a)) :
    HasDerivAt (fun x => u1 (x * a) + x * a * u2 (x * a))
      (a * (2 * u2 (R * a) + R * a * u3 (R * a))) R := by
  have hl : HasDerivAt (fun x : ℝ => x * a) a R := by simpa using (hasDerivAt_id R).mul_const a
  have := (h1.comp R hl).add (hl.mul (h2.comp R hl))
  exact this.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- **AKMM, p. 309, corrected.** With `a > 0`, `c = Ra > 0` and `u″(c) < 0`, the second
derivative `a[2u″(c) + cu‴(c)]` is nonnegative iff relative prudence `−cu‴(c)/u″(c) ≥ 2`. -/
theorem cr_second_deriv_nonneg_iff {a c u2c u3c : ℝ} (ha : 0 < a) (hu2 : u2c < 0) :
    0 ≤ a * (2 * u2c + c * u3c) ↔ 2 ≤ -c * u3c / u2c := by
  rw [le_div_iff_of_neg hu2]
  constructor
  · intro h
    have := nonneg_of_mul_nonneg_right (by linarith [h] : 0 ≤ a * (2 * u2c + c * u3c)) ha
    linarith
  · intro h
    exact mul_nonneg ha.le (by linarith)

/-- **AKMM, p. 310, corrected.** If `u″ < 0` and relative prudence is at least `2` on `(0, ∞)`,
then for `a > 0` the return function `R ↦ Ru′(Ra)` is convex on `(0, ∞)`. -/
theorem cr_convex_of_rel_prudence {u1 u2 u3 : ℝ → ℝ} (h1 : ∀ c, 0 < c → HasDerivAt u1 (u2 c) c)
    (h2 : ∀ c, 0 < c → HasDerivAt u2 (u3 c) c) (hu2 : ∀ c, 0 < c → u2 c < 0)
    (hrp : ∀ c, 0 < c → 2 ≤ -c * u3 c / u2 c) {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Set.Ioi 0) fun R => R * u1 (R * a) := by
  have hpos : ∀ R ∈ Set.Ioi (0 : ℝ), 0 < R * a := fun R hR => mul_pos hR ha
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (f' := fun R => u1 (R * a) + R * a * u2 (R * a))
    (f'' := fun R => a * (2 * u2 (R * a) + R * a * u3 (R * a))) ?_ ?_ ?_ ?_
  · exact fun R hR => (cr_deriv (h1 _ (hpos R hR))).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_deriv (h1 _ (hpos R hR))).hasDerivWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_second_deriv (h1 _ (hpos R hR)) (h2 _ (hpos R hR))).hasDerivWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_second_deriv_nonneg_iff ha (hu2 _ (hpos R hR))).2 (hrp _ (hpos R hR))

/-- **AKMM, p. 310, corrected: return risk raises saving when relative prudence is at least 2.**
Let `u′` be strictly decreasing on `(0, ∞)`, `R ↦ Ru′(Ra₁)` convex on `Y ⊆ (0, ∞)` (by
`cr_convex_of_rel_prudence`), and let the law `ν` of the return be a mean-preserving spread of `μ`
on `Y`. If `a₁ > 0` solves `u′(y₀ − a) = βE_μ[Ru′(Ra)]` and `a₂ > 0` solves it under `ν`, with
positive first-period consumption, then `a₁ ≤ a₂`. -/
theorem cr_spread_raises_saving {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0)) {β y₀ a₁ a₂ : ℝ}
    (hβ : 0 < β) {Y : Set ℝ} (hYpos : Y ⊆ Set.Ioi 0) {μ ν : Measure ℝ}
    (hspread : pr_ConvexOrderOn Y μ ν) (hconv : ConvexOn ℝ Y fun R => R * du (R * a₁))
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂)
    (hμ₁ : Integrable (fun R => R * du (R * a₁)) μ) (hν₁ : Integrable (fun R => R * du (R * a₁)) ν)
    (hν₂ : Integrable (fun R => R * du (R * a₂)) ν)
    (h₁ : du (y₀ - a₁) = β * ∫ R, R * du (R * a₁) ∂μ)
    (h₂ : du (y₀ - a₂) = β * ∫ R, R * du (R * a₂) ∂ν) : a₁ ≤ a₂ := by
  have hup : ∫ R, R * du (R * a₁) ∂μ ≤ ∫ R, R * du (R * a₁) ∂ν :=
    hspread.2.2 _ hconv hμ₁ hν₁
  by_contra hlt
  push Not at hlt
  have hF : du (y₀ - a₂) < du (y₀ - a₁) := hdu hc₀₁ hc₀₂ (by linarith)
  have hG : ∫ R, R * du (R * a₁) ∂ν ≤ ∫ R, R * du (R * a₂) ∂ν := by
    refine integral_mono_ae hν₁ hν₂ ?_
    filter_upwards [hspread.2.1] with R hR
    have hR0 : 0 < R := hYpos hR
    exact mul_le_mul_of_nonneg_left (hdu.antitoneOn (Set.mem_Ioi.2 (mul_pos hR0 ha₂))
      (Set.mem_Ioi.2 (mul_pos hR0 ha₁)) (by nlinarith)) hR0.le
  have := mul_le_mul_of_nonneg_left hup hβ.le
  have := mul_le_mul_of_nonneg_left hG hβ.le
  linarith

/-- **Counterexample to AKMM, p. 310, log utility.** With `u′(c) = 1/c` (prudent:
`u‴ = 2/c³ > 0`), `Ru′(Ra) = 1/a` does not depend on `R`: for every law of the return on
`(0, ∞)` the right side of the Euler equation is `β/a`, so return risk does not change saving. -/
theorem cr_log_return_risk_neutral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ R ∂μ, 0 < R) {a : ℝ} (ha : 0 < a) : ∫ R, R * (R * a)⁻¹ ∂μ = a⁻¹ := by
  have : ∫ R, R * (R * a)⁻¹ ∂μ = ∫ _R, a⁻¹ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ] with R hR
    field_simp
  rw [this, integral_const]
  simp

/-- The two-point return spread of the counterexample is a convex-order spread: `δ₁` is below
`½δ_{1/2} + ½δ_{3/2}` on `(0, ∞)`. -/
theorem cr_return_spread_instance :
    pr_ConvexOrderOn (Set.Ioi 0) (Measure.dirac 1)
      ((1 / 2 : ENNReal) • Measure.dirac (1 - 1 / 2) +
        (1 / 2 : ENNReal) • Measure.dirac (1 + 1 / 2)) :=
  pr_two_point_spread (convex_Ioi 0) (by norm_num) (by norm_num)

/-- **Counterexample to AKMM, p. 310** ("under prudence … the right-hand side is still a convex
function of `r` … precautionary saving behavior emerges even in the face of higher volatility of
returns"). CRRA with `σ = 1/2`, `u′(c) = 1/√c`, is prudent (`u‴(c) = (3/4)c^{−5/2} > 0`). Let
`a₁ ∈ (0, y₀)` solve the Euler equation with the sure return `R = 1` and `a₂ ∈ (0, y₀)` solve it
when `R` is `1/2` or `3/2` with probability `1/2` each (a mean-preserving spread,
`cr_return_spread_instance`). Then `a₂ < a₁`: return risk strictly lowers saving. -/
theorem cr_printed_counterexample {β y₀ a₁ a₂ : ℝ} (hβ : 0 < β) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hc₂ : 0 < y₀ - a₂)
    (h₁ : (Real.sqrt (y₀ - a₁))⁻¹ = β * (1 * (Real.sqrt (1 * a₁))⁻¹))
    (h₂ : (Real.sqrt (y₀ - a₂))⁻¹ = β * (1 / 2 * ((1 / 2) * (Real.sqrt ((1 / 2) * a₂))⁻¹) +
      1 / 2 * ((3 / 2) * (Real.sqrt ((3 / 2) * a₂))⁻¹))) :
    a₂ < a₁ ∧ ∀ c : ℝ, 0 < c → 0 < 1 / 2 * (1 / 2 + 1) * c ^ (-(1 / 2 : ℝ) - 2) := by
  refine ⟨?_, fun c hc => by positivity⟩
  -- the spread multiplies the right side by `m = (√(1/2) + √(3/2))/2 < 1`
  have hs1 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hp1 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hp2 : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hm : (Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2 < 1 := by
    have hprod : Real.sqrt (1 / 2) * Real.sqrt (3 / 2) < 1 := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (1 / 2 : ℝ) * (3 / 2) = 3 / 4 by norm_num, Real.sqrt_lt' one_pos]
      norm_num
    nlinarith
  have hsq : ∀ R : ℝ, 0 < R → R * (Real.sqrt (R * a₂))⁻¹ = Real.sqrt R * (Real.sqrt a₂)⁻¹ := by
    intro R hR
    rw [Real.sqrt_mul hR.le]
    have := Real.sqrt_pos.2 hR
    have := Real.sqrt_pos.2 ha₂
    field_simp
    rw [Real.sq_sqrt hR.le]
  rw [hsq (1 / 2) (by norm_num), hsq (3 / 2) (by norm_num)] at h₂
  simp only [one_mul] at h₁
  have hrhs₂ : (Real.sqrt (y₀ - a₂))⁻¹ =
      β * ((Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2) * (Real.sqrt a₂)⁻¹ := by
    rw [h₂]; ring
  by_contra hle
  push Not at hle
  -- `F(a₁) ≤ F(a₂) = βm/√a₂ < β/√a₂ ≤ β/√a₁ = F(a₁)`
  have hF : (Real.sqrt (y₀ - a₁))⁻¹ ≤ (Real.sqrt (y₀ - a₂))⁻¹ := by
    apply inv_anti₀ (Real.sqrt_pos.2 hc₂)
    exact Real.sqrt_le_sqrt (by linarith)
  have hG : (Real.sqrt a₂)⁻¹ ≤ (Real.sqrt a₁)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 ha₁) (Real.sqrt_le_sqrt hle)
  have hpa : 0 < (Real.sqrt a₂)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ha₂)
  have h3 : β * ((Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2) * (Real.sqrt a₂)⁻¹ <
      β * (Real.sqrt a₂)⁻¹ := by
    rw [mul_assoc]
    apply mul_lt_mul_of_pos_left _ hβ
    nlinarith
  have h4 : β * (Real.sqrt a₂)⁻¹ ≤ β * (Real.sqrt a₁)⁻¹ := mul_le_mul_of_nonneg_left hG hβ.le
  linarith

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The lognormal Euler equation: buffer stock (11.41) and Zeldes

AKMM, §11.3.4, (11.41), p. 310, and the box "Excess sensitivity and liquidity constraints",
p. 311.

With CRRA utility, `u′(cₜ₊₁)/u′(cₜ) = exp(−σΔlog cₜ₊₁)`, and the Euler equation (with a
borrowing-constraint multiplier `λ ≥ 0`, `λ = 0` when the constraint is slack) is
`1 = (1 + λ)βR E exp(−σΔlog cₜ₊₁)`. If `Δlog cₜ₊₁` is Gaussian with mean `m` and variance `v`,
the moment generating function `E e^{tX} = exp(mt + vt²/2)` (Mathlib's `mgf_gaussianReal`) solves
this exactly:

* `m = (log(1 + r) − log(1 + ρ))/σ + (σ/2)v + log(1 + λ)/σ` (`cs_lognormal_euler`), so
  **(11.41), corrected**: `E Δlog c = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog c)`
  (`eq_11_41`), and the Zeldes equation with the coefficient `σ/2` and `ρ` (`cs_zeldes_euler`).
* The printed coefficient `(σ + 1)/2` is wrong whenever `Var > 0` (`eq_11_41_printed_false`):
  it is the coefficient of the uncentred second moment of the growth *rate* in (11.36), where
  relative prudence is `σ + 1`.

Departure: the book's `≃` (and `r`, `ρ` for `log(1 + r)`, `log(1 + ρ)`) becomes the exact identity
under joint lognormality.
-/

namespace AKMM.Consumption

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, pp. 310–311: the lognormal Euler equation, exactly. If `X = Δlog cₜ₊₁` has law
`N(m, v)` and `1 = (1 + λ)βR E exp(−σX)` with `β = 1/(1 + ρ)`, `R = 1 + r`, `σ > 0`, then
`m = (log(1 + r) − log(1 + ρ))/σ + (σ/2)v + log(1 + λ)/σ`. -/
theorem cs_lognormal_euler {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) {σ r ρ lam : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hρ : 0 < 1 + ρ) (hlam : 0 < 1 + lam)
    (heuler : 1 = (1 + lam) * (1 / (1 + ρ)) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    m = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * (v : ℝ) +
      Real.log (1 + lam) / σ := by
  have hmgf := mgf_gaussianReal hX (-σ)
  rw [mgf] at hmgf
  rw [hmgf] at heuler
  have hpos : 0 < (1 + lam) * (1 / (1 + ρ)) * (1 + r) := by positivity
  have hlog := congrArg Real.log heuler
  rw [Real.log_one, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) hr.ne', Real.log_mul hlam.ne' (by positivity), one_div,
    Real.log_inv] at hlog
  field_simp
  nlinarith [hlog]

/-- **AKMM, (11.41), p. 310, corrected.** With CRRA utility, an interior Euler equation
`1 = βR E exp(−σΔlog cₜ₊₁)` and `Δlog cₜ₊₁ ~ N(m, v)`:
`E Δlog cₜ₊₁ = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog cₜ₊₁)`. -/
theorem eq_11_41 {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) {σ r ρ : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hρ : 0 < 1 + ρ)
    (heuler : 1 = 1 / (1 + ρ) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * Var[X; P] := by
  have h := cs_lognormal_euler hX (lam := 0) hσ hr hρ (by norm_num) (by simpa using heuler)
  rw [hX.integral_eq, integral_id_gaussianReal, hX.variance_eq, variance_id_gaussianReal, h]
  simp

/-- **AKMM, p. 311, the Zeldes (1989) Euler equation, corrected.** With the multiplier `λ ≥ 0`,
`1 = (1 + λ)βR E exp(−σΔlog cₜ₊₁)` and `Δlog cₜ₊₁ ~ N(m, v)`:
`E Δlog cₜ₊₁ = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog cₜ₊₁) + log(1 + λ)/σ`; the
coefficient on `log(1 + λ)` is `1/σ > 0`, as printed, and on the variance `σ/2`. -/
theorem cs_zeldes_euler {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ}
    {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) {σ r ρ lam : ℝ} (hσ : 0 < σ)
    (hr : 0 < 1 + r) (hρ : 0 < 1 + ρ) (hlam : 0 ≤ lam)
    (heuler : 1 = (1 + lam) * (1 / (1 + ρ)) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * Var[X; P] +
      Real.log (1 + lam) / σ ∧ 0 < 1 / σ := by
  have h := cs_lognormal_euler hX hσ hr hρ (by linarith) heuler
  rw [hX.integral_eq, integral_id_gaussianReal, hX.variance_eq, variance_id_gaussianReal, h]
  exact ⟨rfl, by positivity⟩

/-- **Correction to AKMM, (11.41), p. 310** (and the Zeldes equation, p. 311), which print the
coefficient `(σ + 1)/2` on `Var(Δlog c)`. Under the exact lognormal Euler equation the printed
formula fails whenever the variance is positive: it overstates the mean by `v/2`. -/
theorem eq_11_41_printed_false {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ}
    {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) {σ r ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < 1 + r) (hρ : 0 < 1 + ρ)
    (heuler : 1 = 1 / (1 + ρ) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P ≠ (Real.log (1 + r) - Real.log (1 + ρ)) / σ + (σ + 1) / 2 * Var[X; P] := by
  rw [eq_11_41 hX hσ hr hρ heuler, hX.variance_eq, variance_id_gaussianReal]
  have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  intro h
  nlinarith

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounds on wealth accumulation

AKMM, §11.3.5, (11.42)–(11.46), fn. 23–25, pp. 312–314.

The book's informal proof (after Schechtman and Escudero 1977) is formalised in two layers.

* **The book's argument, given (11.44).** From the Euler equation (11.42) and the identity
  (11.43), if `E u′(c(x′))/u′(c(x̄′)) → 1` as `x → ∞` and `βR < 1`, then `x̄′(x) < x` for all large
  `x`: the highest next-period cash in hand is below today's (`eq_11_43`,
  `bw_bounded_of_ratio`); and `x̄′ − x′ = ȳ − y′` (`bw_cash_gap`, the step of (11.45)).
* **The theorem.** The Taylor step from (11.46) to (11.44) is replaced by Miao's proof of
  Schechtman–Escudero (`Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_3_all`, reused): with
  `βR < 1` and relative risk aversion eventually below some `γ`, there is `x*` with `x′ < x` for
  every income realisation once `x > x*` (`bw_bounded_wealth`); CRRA qualifies
  (`bw_crra_rra`, `bw_bounded_wealth_crra`), and CRRA has `α(c) = σ/c → 0`, (11.46)
  (`bw_crra_ara_tendsto`).
* **Correction** (p. 314: "(11.46) requires … that `u` belongs to the DARA class … under DARA
  the condition `βR < 1` is sufficient"). DARA does not give (11.46): `u′(c) = e^{−c}/c` has
  strictly decreasing absolute risk aversion `α(c) = 1 + 1/c`, which tends to `1`
  (`bw_dara_not_ara_zero`). The sufficient condition the proof uses is `α → 0`, delivered for
  instance by bounded relative risk aversion.
-/

namespace AKMM.Consumption

open Filter Topology

/-- **AKMM, (11.42)–(11.43), p. 313.** If `u′(c(x)) = βRD(x)` with `D(x) = E u′(c(x′))` and
`u′(c(x̄′)) ≠ 0`, then `u′(c(x)) = βR(D(x)/u′(c(x̄′)))u′(c(x̄′))`. -/
theorem eq_11_43 {mx D mbar βR : ℝ} (h : mx = βR * D) (hm : mbar ≠ 0) :
    mx = βR * (D / mbar) * mbar := by
  rw [h]; field_simp

/-- AKMM, p. 314, (11.45): `x′ = Ra′ + y′` and `x̄′ = Ra′ + ȳ`, so `x̄′ − x′ = ȳ − y′`. -/
theorem bw_cash_gap (R a' y' ybar : ℝ) : (R * a' + ybar) - (R * a' + y') = ybar - y' := by ring

/-- **AKMM, p. 313: the bounded-wealth argument given (11.44).** Let `u′` be strictly decreasing
on `(0, ∞)`, consumption `c` positive and strictly increasing, `βR < 1` (`βR > 0`), and let the
Euler equation (11.42) `u′(c(x)) = βRD(x)` hold with `D(x) = E u′(c(x′))`. If (11.44)
`D(x)/u′(c(x̄′(x))) → 1` as `x → ∞`, then for all large `x`, `x̄′(x) < x`: cash in hand does not
increase forever. -/
theorem bw_bounded_of_ratio {du cons xbar D : ℝ → ℝ} {βR : ℝ} (hβR0 : 0 < βR) (hβR : βR < 1)
    (hdu : StrictAntiOn du (Set.Ioi 0)) (hdupos : ∀ c, 0 < c → 0 < du c)
    (hc : StrictMono cons) (hcpos : ∀ x, 0 < cons x) (heuler : ∀ x, du (cons x) = βR * D x)
    (h44 : Tendsto (fun x => D x / du (cons (xbar x))) atTop (𝓝 1)) :
    ∀ᶠ x in atTop, xbar x < x := by
  have hlt : ∀ᶠ x in atTop, D x / du (cons (xbar x)) < 1 / βR :=
    h44.eventually (gt_mem_nhds (by rw [lt_div_iff₀ hβR0]; linarith))
  filter_upwards [hlt] with x hx
  have hm := hdupos _ (hcpos (xbar x))
  have h1 : du (cons x) < du (cons (xbar x)) := by
    rw [eq_11_43 (heuler x) hm.ne']
    have : βR * (D x / du (cons (xbar x))) < 1 := by
      rw [lt_div_iff₀ hβR0] at hx; linarith
    nlinarith
  by_contra hle
  push Not at hle
  have := hdu.antitoneOn (hcpos _) (hcpos _) (hc.monotone hle)
  linarith

/-- **AKMM, p. 313: `βR < 1` bounds wealth** (Schechtman and Escudero 1977, Clarida 1987, Huggett
1997; the proof is Miao's Lemma 8.3.3). In Miao's i.i.d. income fluctuation problem, if `βR < 1`
and relative risk aversion is eventually below some `γ > 0`, there is `x*` such that
`x′ = Râ(x) + y − rb < x` for every income `y ≤ y_max` whenever `x > x*`. -/
theorem bw_bounded_wealth {M : Miao.IncompleteMarkets.SIModel} (S : M.Solution)
    (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x :=
  S.lemma_8_3_3_all hβR hddu hγ0 hγ

/-- CRRA marginal utility `u′(c) = c^{−σ}` has constant relative risk aversion `σ`. -/
theorem bw_crra_rra {σ c : ℝ} (hc : 0 < c) :
    -c * (-σ * c ^ (-σ - 1)) / c ^ (-σ) = σ := by
  have hp : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have e : c ^ (-σ - 1) = c ^ (-σ) * c⁻¹ := by
    rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
  rw [e]
  field_simp

/-- **AKMM, p. 314 with CRRA.** In Miao's income fluctuation problem with CRRA marginal utility
`u′(c) = c^{−σ}` and `βR < 1`, wealth is bounded: there is `x*` with `x′ < x` for every income
once `x > x*`. -/
theorem bw_bounded_wealth_crra {M : Miao.IncompleteMarkets.SIModel} (S : M.Solution) {σ : ℝ}
    (hσ : 0 < σ) (hdu : ∀ c, 0 < c → M.du c = c ^ (-σ)) (hβR : M.β * M.R < 1) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x := by
  have hddu : ∀ c, 0 < c → HasDerivAt M.du (-σ * c ^ (-σ - 1)) c := by
    intro c hc
    have h := Real.hasDerivAt_rpow_const (x := c) (p := -σ) (Or.inl hc.ne')
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hc] with x hx
    exact hdu x hx
  refine bw_bounded_wealth S hβR hddu (γ := σ + 1) (by linarith) ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [hdu c hc, bw_crra_rra hc]
  linarith

/-- **AKMM, (11.46), p. 314, for CRRA.** Absolute risk aversion `α(c) = σ/c → 0` as `c → ∞`. -/
theorem bw_crra_ara_tendsto (σ : ℝ) : Tendsto (fun c : ℝ => σ / c) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- **Correction to AKMM, p. 314** ("Condition (11.46) requires … that `u` belongs to the DARA
class"; "under DARA the condition `βR < 1` is sufficient"). DARA does not give (11.46): the
marginal utility `u′(c) = e^{−c}/c` is positive and strictly decreasing on `(0, ∞)`, its absolute
risk aversion `α(c) = −u″(c)/u′(c) = 1 + 1/c` is strictly decreasing (DARA), and `α(c) → 1 ≠ 0`. -/
theorem bw_dara_not_ara_zero :
    (∀ c : ℝ, 0 < c → HasDerivAt (fun x => Real.exp (-x) / x)
        (-(Real.exp (-c) / c) - Real.exp (-c) / c ^ 2) c) ∧
      (∀ c : ℝ, 0 < c → 0 < Real.exp (-c) / c) ∧
      (∀ c : ℝ, 0 < c →
        -(-(Real.exp (-c) / c) - Real.exp (-c) / c ^ 2) / (Real.exp (-c) / c) = 1 + 1 / c) ∧
      StrictAntiOn (fun c : ℝ => 1 + 1 / c) (Set.Ioi 0) ∧
      Tendsto (fun c : ℝ => 1 + 1 / c) atTop (𝓝 1) := by
  refine ⟨fun c hc => ?_, fun c hc => div_pos (Real.exp_pos _) hc, fun c hc => ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-c)) c := by
      simpa using (hasDerivAt_neg c).exp
    have := h1.div (hasDerivAt_id c) hc.ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  · have := Real.exp_pos (-c)
    field_simp
    ring
  · intro x hx y hy hxy
    have : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
    simp only
    linarith
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The endowment economy: Huggett and Bewley

AKMM, §11.4.1, (11.47)–(11.50), pp. 315–320.

The household problem (11.47), the transition (11.48)–(11.49) and stationarity are Miao's
(`Miao.IncompleteMarkets`): `BWEconomy.Bellman r φ y V g` (the Bellman equation with rate `r`,
debt limit `φ = a`, endowment `y`, maximum attained by `g`), `BWEconomy.Stationary g λ` (the fixed
point of (11.49) on measurable rectangles), `BWHuggettEqm` (Definition 17.2.1) and
`definition_17_2_1` (`r` is an equilibrium rate iff `0 ∈ Ea(r)`).

* **The stationary equilibrium** (p. 316) with bond supply `B` and lump-sum tax `T`
  (`hg_IsStationaryEqm`): `B = T = 0` is Huggett's definition, `B > 0` with (11.50) is Bewley's.
  Stationarity makes mean assets equal mean saving (`hg_mean_assets_eq_mean_policy`), so mean
  consumption is `∫y + rB − T` (`hg_mean_consumption`): with zero net supply the goods market
  clears automatically (`hg_goods_clear_zero_supply`, so AKMM's definition is Miao's
  Definition 17.2.1, `hg_eqm_iff_miao`), and with positive supply it clears iff **(11.50)**
  `rB = T` (`eq_11_50`). Concrete equilibria: Miao's cycle economy (`hg_cycle_eqm`,
  `hg_cycle_huggett`).
* **Existence** (p. 318): at `r = −1` every household borrows to the limit, so `A(−1) = −a`
  (`hg_policy_at_minus_one`, `hg_A_at_minus_one`); continuity of `A`, `A(r) → ∞` as `r ↑ 1/β − 1`
  and `−a < B` give an equilibrium rate in `(−1, 1/β − 1)` (`hg_existence`, by Miao's crossing
  argument), for zero supply a stationary equilibrium (`hg_existence_eqm`).
* **`r* < 1/β − 1`** (p. 318): every stationary distribution of the income fluctuation problem
  with nondegenerate income has `βR < 1` (Miao's `ay_beta_R_lt_one`, `ay_r_lt_rho`;
  `hg_rate_below_cm`).
* **Uniqueness** (p. 318): a strictly increasing `A` crosses `B` once (`hg_unique_of_strictMono`).
  **Correction:** "the smaller is `σ` the larger is the income effect" — in the two-period CRRA
  problem saving rises with `R` iff `σ < 1`, where the *substitution* effect dominates
  (`hg_saving_ratio_crra`, `hg_saving_increasing_iff`).

Departures: `A(r)` is a function given as a hypothesis (the book asserts its continuity, by SLP
Theorems 12.12–12.13, and the limit at `1/β − 1`); Miao's `EaSet` handles a possibly
set-valued `A`. The ACHLLM uniqueness theorem (continuous time, `σ < 1`) is not formalised.
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology ProbabilityTheory Miao.IncompleteMarkets

variable {E : Type*} [MeasurableSpace E]

/-! ### The stationary equilibrium -/

/-- **AKMM, p. 316 (zero supply) and pp. 319–320 (positive supply).** A recursive stationary
competitive equilibrium of the endowment economy with debt limit `φ`, bond supply `B` and lump-sum
tax `T`: `V, g` solve (11.47) with income `y − T`, `λ` is a stationary probability measure on
`[−φ, ∞) × E`, the asset market clears, `∫g dλ = B`, and the goods market clears,
`∫c dλ = ∫y dλ` with `c = (1 + r)a + y − T − g`. -/
def hg_IsStationaryEqm (H : BWEconomy E) (φ B T r : ℝ) (V g : ℝ → E → ℝ)
    (lam : Measure (ℝ × E)) : Prop :=
  IsProbabilityMeasure lam ∧ lam {p | p.1 < -φ} = 0 ∧
    H.Bellman r φ (fun s => H.e s - T) V g ∧ H.Stationary g lam ∧
    Integrable (fun p => g p.1 p.2) lam ∧ ∫ p, g p.1 p.2 ∂lam = B ∧
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam

/-- AKMM, p. 317: stationarity (11.49) with a Markov kernel makes the asset marginal of `λ` the
image of `λ` under the policy: `λ(A × E) = λ{g ∈ A}`. -/
theorem hg_map_fst_eq (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hgm : AEMeasurable (fun p : ℝ × E => g p.1 p.2) lam) :
    lam.map Prod.fst = lam.map (fun p => g p.1 p.2) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.map_apply_of_aemeasurable hgm hA]
  have h := hst A Set.univ hA MeasurableSet.univ
  simp only [measure_univ, mul_one] at h
  rw [show Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set E) by ext; simp, h]
  have : (fun p : ℝ × E => A.indicator (1 : ℝ → ENNReal) (g p.1 p.2)) =
      ((fun p : ℝ × E => g p.1 p.2) ⁻¹' A).indicator 1 := by
    ext p; simp only [Set.indicator, Pi.one_apply]; rfl
  rw [this, lintegral_indicator_one₀ (hgm.nullMeasurableSet_preimage hA)]

/-- Under a stationary distribution, assets are integrable when saving is. -/
theorem hg_integrable_assets (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) : Integrable (fun p : ℝ × E => p.1) lam := by
  have hi : Integrable (fun x : ℝ => x) (lam.map fun p => g p.1 p.2) :=
    (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).2 hg
  rw [← hg_map_fst_eq H hst hg.aemeasurable] at hi
  exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 hi

/-- AKMM, p. 317: under a stationary distribution, mean assets equal mean saving,
`∫a dλ = ∫g dλ`. -/
theorem hg_mean_assets_eq_mean_policy (H : BWEconomy E) [IsMarkovKernel H.Q]
    {g : ℝ → E → ℝ} {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) :
    ∫ p, p.1 ∂lam = ∫ p, g p.1 p.2 ∂lam := by
  have h1 : ∫ p, p.1 ∂lam = ∫ x, x ∂(lam.map Prod.fst) :=
    (integral_map measurable_fst.aemeasurable aestronglyMeasurable_id).symm
  have h2 : ∫ p, g p.1 p.2 ∂lam = ∫ x, x ∂(lam.map fun p => g p.1 p.2) :=
    (integral_map hg.aemeasurable aestronglyMeasurable_id).symm
  rw [h1, h2, hg_map_fst_eq H hst hg.aemeasurable]

/-- AKMM, pp. 316 and 319: mean consumption in a stationary distribution. With mean saving `B`,
`∫[(1 + r)a + y − T − g] dλ = ∫y dλ + rB − T`. -/
theorem hg_mean_consumption (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r T B : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hB : ∫ p, g p.1 p.2 ∂lam = B) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam + r * B - T := by
  have hma := hg_mean_assets_eq_mean_policy H hst hg
  have i1 : Integrable (fun p : ℝ × E => (1 + r) * p.1 + H.e p.2) lam := (ha.const_mul _).add he
  have i2 : Integrable (fun p : ℝ × E => (1 + r) * p.1 + H.e p.2 - T) lam :=
    i1.sub (integrable_const T)
  have e1 : ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam =
      ∫ p, ((1 + r) * p.1 + H.e p.2 - T) ∂lam - ∫ p, g p.1 p.2 ∂lam := integral_sub i2 hg
  have e2 : ∫ p, ((1 + r) * p.1 + H.e p.2 - T) ∂lam =
      ∫ p, ((1 + r) * p.1 + H.e p.2) ∂lam - T := by
    rw [integral_sub i1 (integrable_const T), integral_const]; simp
  have e3 : ∫ p, ((1 + r) * p.1 + H.e p.2) ∂lam = (1 + r) * ∫ p, p.1 ∂lam + ∫ p, H.e p.2 ∂lam := by
    rw [integral_add (ha.const_mul _) he, integral_const_mul]
  rw [e1, e2, e3, hma, hB]
  ring

/-- **AKMM, p. 316: with zero net supply the goods market clears.** If the asset market clears,
`∫g dλ = 0`, and `T = 0`, then mean consumption equals the mean endowment. -/
theorem hg_goods_clear_zero_supply (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hclear : ∫ p, g p.1 p.2 ∂lam = 0) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - 0 - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam := by
  rw [hg_mean_consumption H hst hg ha he hclear]
  ring

/-- **AKMM, p. 316 and Miao's Definition 17.2.1.** With zero supply and no taxes, AKMM's
stationary equilibrium is Miao's (`BWHuggettEqm`): the goods-market condition is implied
(given integrable assets and endowments under `λ`). -/
theorem hg_eqm_iff_miao (H : BWEconomy E) [IsMarkovKernel H.Q] (φ r : ℝ) (V g : ℝ → E → ℝ)
    (lam : Measure (ℝ × E)) [IsProbabilityMeasure lam]
    (ha : Integrable (fun p : ℝ × E => p.1) lam) (he : Integrable (fun p : ℝ × E => H.e p.2) lam) :
    hg_IsStationaryEqm H φ 0 0 r V g lam ↔
      lam {p | p.1 < -φ} = 0 ∧ H.Bellman r φ H.e V g ∧ H.Stationary g lam ∧
        Integrable (fun p => g p.1 p.2) lam ∧ ∫ p, g p.1 p.2 ∂lam = 0 := by
  have hy : (fun s => H.e s - 0) = H.e := by funext s; ring
  unfold hg_IsStationaryEqm
  rw [hy]
  constructor
  · rintro ⟨-, h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨inferInstance, h1, h2, h3, h4, h5, hg_goods_clear_zero_supply H h3 h4 ha he h5⟩

/-- **AKMM, (11.50), p. 319: assets in positive supply.** In a stationary distribution with
`∫g dλ = B`, the goods market clears iff the government budget `rB = T` holds. -/
theorem eq_11_50 (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r T B : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hB : ∫ p, g p.1 p.2 ∂lam = B) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam ↔ r * B = T := by
  rw [hg_mean_consumption H hst hg ha he hB]
  constructor <;> intro h <;> linarith

/-- Miao's cycle economy has a Markov (deterministic) transition kernel. -/
theorem hg_cycle_markov : IsMarkovKernel bw_cycle.Q := by
  change IsMarkovKernel (Kernel.deterministic (fun s : Bool => !s) Measurable.of_discrete)
  infer_instance

/-- Integrability against Miao's cycle distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}`. -/
theorem hg_cycle_integrable (f : ℝ × Bool → ℝ) : Integrable f bw_cycleLam :=
  ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

/-- **The definition is not vacuous (positive supply).** Miao's cycle economy at `r = 0`, with no
borrowing, bond supply `B = 1/4` and `T = rB = 0`, is a stationary equilibrium. -/
theorem hg_cycle_eqm :
    hg_IsStationaryEqm bw_cycle 0 (1 / 4) 0 0 bw_cycleV bw_cycleG bw_cycleLam := by
  have hP := bw_cycleLam_isProb
  have := hg_cycle_markov
  have hy : (fun s => bw_cycle.e s - 0) = bw_cycle.e := by funext s; ring
  refine ⟨hP, bw_cycleLam_supp, by rw [hy]; exact bw_cycle_bellman, bw_cycle_stationary,
    bw_cycle_integrable, bw_cycle_mean, ?_⟩
  exact (eq_11_50 bw_cycle bw_cycle_stationary bw_cycle_integrable (hg_cycle_integrable _)
    (hg_cycle_integrable _) bw_cycle_mean).2 (by ring)

/-- **The definition is not vacuous (zero supply).** The cycle economy with debt limit `1/4` has a
Huggett stationary equilibrium in AKMM's sense (Miao's `bw_cycle_huggett`). -/
theorem hg_cycle_huggett : ∃ (V g : ℝ → Bool → ℝ) (lam : Measure (ℝ × Bool)),
    hg_IsStationaryEqm bw_cycle (1 / 4) 0 0 0 V g lam := by
  obtain ⟨eqm, hr⟩ := bw_cycle_huggett
  have hP := eqm.isProb
  have := hg_cycle_markov
  refine ⟨eqm.V, eqm.g, eqm.lam, ?_⟩
  have ha := hg_integrable_assets bw_cycle eqm.stationary eqm.integrable
  have he : Integrable (fun p : ℝ × Bool => bw_cycle.e p.2) eqm.lam := by
    refine Integrable.of_bound (C := 2) ?_ (Eventually.of_forall fun p => ?_)
    · exact (Measurable.of_discrete.comp measurable_snd).aestronglyMeasurable
    · simp only [bw_cycle]
      split_ifs <;> norm_num
  have := (hg_eqm_iff_miao bw_cycle (1 / 4) eqm.r eqm.V eqm.g eqm.lam ha he).2
    ⟨eqm.supp, eqm.bellman, eqm.stationary, eqm.integrable, eqm.clear⟩
  rwa [hr] at this

/-! ### Existence -/

/-- **AKMM, p. 318: "if `r = −1`, it is optimal to borrow up to the limit since one would never
have to repay".** With `r = −1` and `u` strictly increasing on `[0, ∞)`, every solution of (11.47)
has `g(a, s) = −a` (the debt limit) at every state. -/
theorem hg_policy_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0))
    {φ : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ} (hB : H.Bellman (-1) φ y V g) :
    ∀ a s, -φ ≤ a → g a s = -φ := by
  have h0 : ∀ x : ℝ, (1 + -1) * x = 0 := fun x => by ring
  -- the value does not depend on assets: the budget does not
  have hV : ∀ x s', -φ ≤ x → V x s' = V (-φ) s' := by
    intro x s' hx
    obtain ⟨hg1, -, he1, hle1⟩ := hB x s' hx
    obtain ⟨hg2, -, he2, hle2⟩ := hB (-φ) s' le_rfl
    rw [h0, zero_add] at hg1 hg2 he1 he2 hle1 hle2
    apply le_antisymm
    · rw [he1]; exact hle2 _ hg1
    · rw [he2]; exact hle1 _ hg2
  intro a s ha
  obtain ⟨hg, -, he, hle⟩ := hB a s ha
  rw [h0, zero_add] at hg he hle
  have hI : ∫ s', V (g a s) s' ∂(H.Q s) = ∫ s', V (-φ) s' ∂(H.Q s) :=
    integral_congr_ae (Eventually.of_forall fun s' => hV _ s' hg.1)
  have hfeas : -φ ∈ Set.Icc (-φ) (y s) := ⟨le_rfl, hg.1.trans hg.2⟩
  have h := hle _ hfeas
  rw [he, hI] at h
  have hu' : H.u (y s - -φ) ≤ H.u (y s - g a s) := by linarith
  have h1 : (0 : ℝ) ≤ y s - -φ := by linarith [hg.1, hg.2]
  have h2 : (0 : ℝ) ≤ y s - g a s := by linarith [hg.2]
  have := (hu.le_iff_le h1 h2).1 hu'
  linarith [hg.1]

/-- **AKMM, p. 318: `A(−1) = −a`.** At `r = −1`, mean saving under any distribution on
`[−φ, ∞) × E` is the debt limit `−φ`. -/
theorem hg_A_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0)) {φ : ℝ}
    {y : E → ℝ} {V g : ℝ → E → ℝ} (hB : H.Bellman (-1) φ y V g) {lam : Measure (ℝ × E)}
    [IsProbabilityMeasure lam] (hsupp : lam {p | p.1 < -φ} = 0) :
    ∫ p, g p.1 p.2 ∂lam = -φ := by
  have hae : ∀ᵐ p ∂lam, -φ ≤ p.1 := by
    rw [ae_iff]
    simpa only [not_le] using hsupp
  have : ∫ p, g p.1 p.2 ∂lam = ∫ _p, -φ ∂lam :=
    integral_congr_ae (hae.mono fun p hp => hg_policy_at_minus_one H hu hB p.1 p.2 hp)
  rw [this, integral_const]
  simp

/-- AKMM, p. 318, in Miao's set-valued form: `Ea(−1) ⊆ {−φ}`. -/
theorem hg_EaSet_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0)) (φ : ℝ)
    (y : E → ℝ) : H.EaSet (-1) φ y ⊆ {-φ} := by
  rintro m ⟨V, g, lam, hP, hsupp, hB, -, -, rfl⟩
  exact hg_A_at_minus_one H hu hB hsupp

/-- **AKMM, p. 318 (Figures 11.6–11.7): existence.** If the aggregate asset demand `A` is
continuous on `[−1, 1/β − 1)`, `A(−1) = −a`, `A(r) → ∞` as `r ↑ 1/β − 1`, and the bond supply
satisfies `−a < B`, then `A(r*) = B` for some `r* ∈ (−1, 1/β − 1)` (Miao's crossing argument). -/
theorem hg_existence {A : ℝ → ℝ} {β φ B : ℝ} (hβ : 0 < β)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / β - 1)) atTop) (hA1 : A (-1) = -φ) (hB : -φ < B) :
    ∃ r ∈ Set.Ioo (-1) (1 / β - 1), A r = B := by
  have hr0 : (-1 : ℝ) < 1 / β - 1 := by have := one_div_pos.2 hβ; linarith
  exact ay_existence (Kd := fun _ => B) hr0 hA continuousOn_const hlim (by rw [hA1]; exact hB)

/-- **AKMM, p. 318: a Huggett equilibrium exists.** If `A(r) ∈ Ea(r)` (a selection of Miao's
long-run asset holdings) satisfies the hypotheses of `hg_existence` with `a > 0`, there is a
stationary equilibrium (Definition 17.2.1) with rate in `(−1, 1/β − 1)`. -/
theorem hg_existence_eqm (H : BWEconomy E) {A : ℝ → ℝ} {φ : ℝ} (hβ : 0 < H.β) (hφ : 0 < φ)
    (hsel : ∀ r ∈ Set.Ico (-1) (1 / H.β - 1), A r ∈ H.EaSet r φ H.e)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / H.β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / H.β - 1)) atTop) (hA1 : A (-1) = -φ) :
    ∃ eqm : BWHuggettEqm H φ, eqm.r ∈ Set.Ioo (-1) (1 / H.β - 1) := by
  obtain ⟨r, hr, hAr⟩ := hg_existence hβ hA hlim hA1 (by linarith : -φ < 0)
  have h0 : (0 : ℝ) ∈ H.EaSet r φ H.e := hAr ▸ hsel r ⟨hr.1.le, hr.2⟩
  obtain ⟨eqm, he⟩ := (definition_17_2_1 H φ r).2 h0
  exact ⟨eqm, he ▸ hr⟩

/-- **AKMM, p. 318: "the equilibrium interest rate `r*` will always lie below its complete market
counterpart `1/β − 1`", so `βR* < 1`.** In Miao's income fluctuation problem, every stationary
distribution of cash on hand with nondegenerate income has `βR < 1` and `r < 1/β − 1` (Miao's
`ay_beta_R_lt_one`, `ay_r_lt_rho`, by an Euler-equation variance argument). -/
theorem hg_rate_below_cm {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.β * M.R < 1 ∧ M.r < 1 / M.β - 1 :=
  ⟨ay_beta_R_lt_one S hst hnd, ay_r_lt_rho S hst hnd⟩

/-! ### Uniqueness -/

/-- **AKMM, p. 318: "uniqueness is guaranteed if `A(r)` is monotonically increasing".** A strictly
increasing `A` meets the supply `B` at most once. -/
theorem hg_unique_of_strictMono {A : ℝ → ℝ} {S : Set ℝ} (hA : StrictMonoOn A S) {B r r' : ℝ}
    (hr : r ∈ S) (hr' : r' ∈ S) (h : A r = B) (h' : A r' = B) : r = r' :=
  hA.injOn hr hr' (h.trans h'.symm)

/-- AKMM, p. 318: in the two-period CRRA problem with no second-period income, the Euler
equation `(y₀ − a)^{−σ} = βR(Ra)^{−σ}` gives the saving ratio `a/(y₀ − a) = β^{1/σ}R^{1/σ − 1}`. -/
theorem hg_saving_ratio_crra {σ β R y₀ a : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (ha : 0 < a) (hc : 0 < y₀ - a) (h : (y₀ - a) ^ (-σ) = β * R * (R * a) ^ (-σ)) :
    a / (y₀ - a) = β ^ (1 / σ) * R ^ (1 / σ - 1) := by
  have e := eq_11_14 hσ (mul_pos hβ hR) hc (mul_pos hR ha) h
  rw [Real.mul_rpow hβ.le hR.le] at e
  rw [Real.rpow_sub_one hR.ne', ← mul_div_assoc, ← e]
  field_simp

/-- **Correction to AKMM, p. 318** ("the smaller is `σ` the larger is the income effect and a
higher `r` increases savings"). In the two-period CRRA problem the saving ratio
`β^{1/σ}R^{1/σ − 1}` is strictly increasing in `R` iff `σ < 1`: saving rises with the interest
rate when the elasticity of substitution `1/σ` exceeds one, i.e. when the *substitution* effect
dominates. -/
theorem hg_saving_increasing_iff {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    StrictMonoOn (fun R : ℝ => β ^ (1 / σ) * R ^ (1 / σ - 1)) (Set.Ioi 0) ↔ σ < 1 := by
  have hk : 0 < β ^ (1 / σ) := Real.rpow_pos_of_pos hβ _
  constructor
  · intro hmono
    by_contra hge
    push Not at hge
    have hexp : 1 / σ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hσ]; exact hge
    have := hmono (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos) one_lt_two
    simp only [Real.one_rpow, mul_one] at this
    have h2 : (2 : ℝ) ^ (1 / σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two hexp
    nlinarith
  · intro hlt R hR R' _ hRR
    have hexp : 0 < 1 / σ - 1 := by rw [sub_pos, lt_div_iff₀ hσ]; linarith
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hR) hRR hexp) hk

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuity of aggregate asset demand

AKMM, §11.4.1, "Existence", p. 317: "`A(r) = ∫a′(a, y; r)dλ*_r` … `A(r)` is continuous if both
`a′` and `λ*_r` are, in turn, continuous in `r`", with the continuity of `λ*_r` from Stokey,
Lucas and Prescott, Theorems 12.12–12.13.

On a compact metric state space `S` with Markov kernels `P_r` that are jointly continuous in
`(s, r)` and have unique invariant probability measures `μ_r`, SLP Theorem 12.13 (reused,
`StokeyLucasPrescott.WeakConvergence.theorem_12_13`) makes `r ↦ μ_r` weakly continuous. If the
policy `a′(·; r)` is a bounded continuous function of the state that depends continuously on `r`
in the sup norm (the theorem of the maximum), then `A(r) = ∫a′(·; r)dμ_r` is (sequentially)
continuous (`hg_A_continuous`), and so continuous on any metric parameter space
(`hg_A_continuousOn`).
-/

namespace AKMM.Consumption

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
  StokeyLucasPrescott.WeakConvergence

variable {S Θ : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MetricSpace Θ]

/-- **AKMM, p. 317: `A(r)` is continuous.** Let `S` be compact, the transitions `P_θ` Markov and
jointly continuous (`P_{θₙ}(sₙ) → P_{θ₀}(s₀)` weakly), `μ_θ` the unique invariant probability
measure of `P_θ`, and the policies `f_θ ∈ C_b(S)` continuous in `θ` in the sup norm. Then
`θₙ → θ₀` implies `∫f_{θₙ}dμ_{θₙ} → ∫f_{θ₀}dμ_{θ₀}`. -/
theorem hg_A_continuous [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    (f : Θ → S →ᵇ ℝ) (hf : Continuous f) {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    Tendsto (fun n => ∫ s, f (θ n) s ∂μ (θ n)) atTop (𝓝 (∫ s, f θ₀ s ∂μ θ₀)) := by
  have hw := theorem_12_13 P hcont μ hfix huniq hθ
  have h2 := hw (f θ₀)
  -- `|∫(fₙ − f₀)dμₙ| ≤ ‖fₙ − f₀‖ → 0`
  have hfn : Tendsto (fun n => f (θ n)) atTop (𝓝 (f θ₀)) := (hf.tendsto θ₀).comp hθ
  have h1 : Tendsto (fun n => ∫ s, (f (θ n) - f θ₀) s ∂μ (θ n)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => ‖f (θ n) - f θ₀‖) atTop (𝓝 0) := by
      have := (continuous_norm.tendsto 0).comp (tendsto_sub_nhds_zero_iff.2 hfn)
      rw [norm_zero] at this
      exact this
    refine squeeze_zero_norm (fun n => ?_) hn
    calc ‖∫ s, (f (θ n) - f θ₀) s ∂μ (θ n)‖ ≤ ‖f (θ n) - f θ₀‖ * (μ (θ n)).real Set.univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun s =>
            BoundedContinuousFunction.norm_coe_le_norm _ s)
      _ = ‖f (θ n) - f θ₀‖ := by simp
  have := h1.add h2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  rw [integral_sub ((f (θ n)).integrable _) ((f θ₀).integrable _)]
  ring

/-- AKMM, p. 317: under the hypotheses of `hg_A_continuous`, `A(θ) = ∫f_θdμ_θ` is continuous. -/
theorem hg_A_continuousOn [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    (f : Θ → S →ᵇ ℝ) (hf : Continuous f) : Continuous fun θ => ∫ s, f θ s ∂μ θ := by
  rw [continuous_iff_seqContinuous]
  intro θ θ₀ hθ
  exact hg_A_continuous P hcont μ hfix huniq f hf hθ

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The production economy: Aiyagari

AKMM, §11.4.2, pp. 320–323, with footnote 27 and the box "The marginal propensity to consume:
models vs data".

The equilibrium of the production economy is Miao's Definition 17.1.1 (`AYStationaryEqm`,
`definition_17_1_1`, reused), with the redundancy of the goods-market condition under constant
returns (`ay_resource_redundant`) and a concrete equilibrium (`ay_example_exists`). The
Cobb–Douglas capital demand is Miao's `ay_Kd A α δ L r = L(αA/(r + δ))^{1/(1−α)}`.

* **Footnote 27, corrected:** with `F = K^αL^{1−α}`, `K(r) = L(α/(δ + r))^{1/(1−α)}` solves
  `F_K = r + δ` (`footnote_27`); the printed `(αL/(δ + r))^{1/(1−α)}` is right only for `L = 1`
  (`footnote_27_printed_false`).
* **`K(r)`** (p. 321) is continuous and strictly decreasing on `(−δ, ∞)`, `K → ∞` as `r ↓ −δ`
  (Miao) and `K → 0` as `r → ∞` (`ai_capital_demand_props`, `ai_Kd_tendsto_zero`).
* **Existence** (p. 321) by the crossing argument (`ai_existence`, Miao's `ay_existence_cd`).
* **Precautionary wealth** (Figure 11.8, p. 322): at any stationary distribution of the household
  problem the rate is below `1/β − 1`, so `K* > K^{CM}` (`ai_precautionary_wealth`).
* **MPC box** (p. 323): in the representative-agent equilibrium `βR* = 1`,
  `MPC = r/(1 + r)`, within `r²` of `r` (`ai_mpc_representative`).
-/

namespace AKMM.Consumption

open Filter Topology Miao.IncompleteMarkets

/-- **AKMM, fn. 27, p. 321, corrected.** With `F(K, L) = K^αL^{1−α}` (`0 < α < 1`, `L > 0`) and
`r > −δ`, the capital demand `K(r) = L(α/(δ + r))^{1/(1−α)}` solves the first-order condition
`F_K(K, L) = r + δ`, and it is the only positive solution. -/
theorem footnote_27 {α δ L r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) (hr : -δ < r) :
    ay_cdFK 1 α (L * (α / (δ + r)) ^ (1 / (1 - α))) L = r + δ ∧
      ∀ K, 0 < K → ay_cdFK 1 α K L = r + δ → K = L * (α / (δ + r)) ^ (1 / (1 - α)) := by
  have e : L * (α / (δ + r)) ^ (1 / (1 - α)) = ay_Kd 1 α δ L r := by
    rw [ay_Kd, mul_one, add_comm δ r]
  rw [e]
  exact ⟨ay_Kd_foc one_pos hα0 hα1 hL hr, fun K hK h => ay_Kd_unique one_pos hα0 hα1 hL hr hK h⟩

/-- **Correction to AKMM, fn. 27, p. 321** ("if `F(K, L) = K^αL^{1−α}`, then
`K(r) = (αL/(δ + r))^{1/(1−α)}`"). With `α = 1/2`, `L = 2`, `δ + r = 1/2` the printed formula gives
`K = 4`, where `F_K = (1/2)(4/2)^{−1/2} ≠ 1/2 = r + δ`; the correct demand is `K = 2`. -/
theorem footnote_27_printed_false :
    ((1 / 2 : ℝ) * 2 / (1 / 4 + 1 / 4)) ^ (1 / (1 - 1 / 2 : ℝ)) = 4 ∧
      ay_cdFK 1 (1 / 2) 4 2 ≠ 1 / 4 + 1 / 4 ∧
      (2 : ℝ) * ((1 / 2) / (1 / 4 + 1 / 4)) ^ (1 / (1 - 1 / 2 : ℝ)) = 2 := by
  have h2 : (1 / (1 - 1 / 2 : ℝ)) = 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; norm_num
  · rw [ay_cdFK]
    intro h
    have hlt : ((4 : ℝ) / 2) ^ ((1 / 2 : ℝ) - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    norm_num at h hlt
    linarith
  · rw [h2]; norm_num

/-- **AKMM, p. 321: capital demand.** For `A > 0`, `0 < α < 1`, `L > 0`, `K(r)` is continuous and
strictly decreasing on `(−δ, ∞)` and `K(r) → ∞` as `r ↓ −δ` (Miao's `ay_Kd_continuousOn`,
`ay_Kd_strictAnti`, `ay_Kd_tendsto`). -/
theorem ai_capital_demand_props {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) :
    ContinuousOn (ay_Kd A α δ L) (Set.Ioi (-δ)) ∧ StrictAntiOn (ay_Kd A α δ L) (Set.Ioi (-δ)) ∧
      Tendsto (ay_Kd A α δ L) (𝓝[>] (-δ)) atTop :=
  ⟨ay_Kd_continuousOn hA hα0, ay_Kd_strictAnti hA hα0 hα1 hL, ay_Kd_tendsto hA hα0 hα1 hL⟩

/-- **AKMM, p. 321: "for `r → +∞`, `K → 0`".** -/
theorem ai_Kd_tendsto_zero {A α δ L : ℝ} (hα1 : α < 1) :
    Tendsto (ay_Kd A α δ L) atTop (𝓝 0) := by
  have hp : 0 < 1 / (1 - α) := by rw [one_div_pos]; linarith
  have h1 : Tendsto (fun r : ℝ => α * A / (r + δ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ δ tendsto_id)
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (1 - α))) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (1 - α)) (Or.inr hp.le)).tendsto
    rwa [Real.zero_rpow hp.ne'] at this
  have := (h2.comp h1).const_mul L
  rw [mul_zero] at this
  exact this

/-- **AKMM, p. 321: "existence follows from the same conditions".** If the household capital
supply `Ea` is continuous on `(−δ, 1/β − 1)`, bounded above near `−δ`, and tends to `∞` as
`r ↑ 1/β − 1`, it meets the Cobb–Douglas demand at some `r* ∈ (−δ, 1/β − 1)` (Miao's
`ay_existence_cd`). -/
theorem ai_existence {A α δ L β : ℝ} {Ea : ℝ → ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hEa : ContinuousOn Ea (Set.Ioo (-δ) (ay_rho β)))
    (hlim : Tendsto Ea (𝓝[<] ay_rho β) atTop)
    (hbdd : ∃ r' ∈ Set.Ioo (-δ) (ay_rho β), ∃ B, ∀ r ∈ Set.Ioc (-δ) r', Ea r ≤ B) :
    ∃ r ∈ Set.Ioo (-δ) (ay_rho β), Ea r = ay_Kd A α δ L r :=
  ay_existence_cd hA hα0 hα1 hL hEa hlim hbdd

/-- **AKMM, p. 322 and Figure 11.8: precautionary wealth.** Let the rate `r = R − 1 > −δ` of
Miao's income fluctuation problem admit a stationary distribution of cash on hand, with
nondegenerate income. Then `r < 1/β − 1`, and the capital demanded at `r` exceeds the
complete-markets stock `K^{CM} = K(1/β − 1)`: `K* − K^{CM} > 0` is the precautionary wealth. -/
theorem ai_precautionary_wealth {M : SIModel} (S : M.Solution) {lam : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α)
    (hα1 : α < 1) (hL : 0 < L) (hδ : 0 < δ) (hr : -δ < M.r) :
    M.r < 1 / M.β - 1 ∧ ay_Kd A α δ L (1 / M.β - 1) < ay_Kd A α δ L M.r := by
  have h := (hg_rate_below_cm S hst hnd).2
  exact ⟨h, (ay_overaccumulation hA hα0 hα1 hL hδ hr h).1⟩

/-- **AKMM, p. 323 (MPC box).** In the representative-agent equilibrium `βR* = 1`, the MPC
`1 − R⁻¹(βR)^{1/σ}` of (11.16) is `r/(1 + r)`, and `0 ≤ r − r/(1 + r) ≤ r²` for `r ≥ 0`: the MPC
"roughly equals the real interest rate". -/
theorem ai_mpc_representative {β r σ : ℝ} (hr : 0 ≤ r) (hβR : β * (1 + r) = 1) :
    cd_mpc β (1 + r) σ = r / (1 + r) ∧ 0 ≤ r - r / (1 + r) ∧ r - r / (1 + r) ≤ r ^ 2 := by
  have hR : 0 < 1 + r := by linarith
  have hβ : β = 1 / (1 + r) := by rw [eq_div_iff hR.ne']; exact hβR
  exact ⟨(cd_mpc_betaR_one hR hβR hβ hR).2.2, cd_mpc_approx_rho hr⟩

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The shape of the consumption function under a borrowing limit (Figure 11.2)

AKMM, §11.3.4, pp. 304–306, Figure 11.2: with a borrowing limit `aₜ₊₁ ≥ −a` the consumption
function has slope `1` below the kink `a*` where the limit stops binding, is concave above it,
its slope tends to `r/(1 + r)` as wealth grows and lies between `r/(1 + r)` and `1`, and a
tighter limit `a₂ < a₁` makes the household constrained on a wider range, lowers consumption,
raises the MPC, and leaves consumption unchanged at high wealth.

## The model

Income is i.i.d. with finitely many values `yᵢ ≥ d + a > 0` (`d > 0`), so the state is cash in
hand `x = aₜ + yₜ ≥ d` and the budget is `c + aₜ₊₁/R = x`, `aₜ₊₁ ≥ −a`. The household lives
`n` more periods and eats its cash in the last (`cfn_cons 0 = id`). With `n + 1` periods left its
consumption `c` at `x` solves the Kuhn–Tucker conditions of (11.32)–(11.33),

  `c ≤ x + a/R`,  `c ≤ θ·M(cₙ(R(x − c) + yᵢ))`,  with equality in the second if `c < x + a/R`,

where `M` is the certainty equivalent of the Euler equation (`CfnHousehold.KKT`). For quadratic
utility with `βR = 1`, the book's case, `M` is the expectation and `θ = 1`, and the conditions
are exactly (11.33), `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}` (`cfn_kkt_iff_min`, `cfn_quadratic_kkt_iff`);
for CRRA utility `M` is the power mean with exponent `−σ` and `θ = (βR)^{−1/σ}`, and the second
condition is the Euler inequality `u′(c) ≥ βREu′(cₙ)` (`cfn_crra_euler_iff`). All that is used
of `M` is that it is monotone, normalised, concave and continuous on positive vectors
(`cfn_IsMean`; `cfn_isMean_expect`, `cfn_isMean_powerMean`, the latter from LeanEconomics'
Carroll–Kimball power mean).

## Results

* The Kuhn–Tucker conditions have exactly one solution at every `x ≥ d` (`cfn_kkt_exists`,
  `cfn_kkt_unique`), so the consumption functions `cfn_cons n` are well defined (`cfn_cons_kkt`).
* **Figure 11.2, shape.** Every `cfn_cons n` is concave (`cfn_cons_concave`), nondecreasing with
  slopes in `[κₙ, 1]` (`cfn_cons_slope_bounds`), the constraint binds on an initial interval of
  cash in hand where the slope is exactly `1` (`cfn_binding_initial`), and
  `κₙx ≤ cₙ(x) ≤ κₙ(x + hₙ)` (`cfn_cons_good`), where `κₙ` is the perfect-foresight MPC with `n`
  periods left (`cfn_kappa`).
* **The slope tends to `κₙ`** as wealth grows (`cfn_slope_tendsto`), and `κₙ → 1 − 1/(θR)` as the
  horizon grows (`cfn_kappa_tendsto`); for `βR = 1` this is `r/(1 + r)` (`cfn_kappa_tendsto_r`,
  `cfn_fig_11_2_slope`), and for CRRA it is the MPC (11.16) `1 − R⁻¹(βR)^{1/σ}`
  (`cfn_crra_kappa_limit`).
* **A tighter limit** `a₂ ≤ a₁` (with `r ≥ 0`): consumption is lower everywhere
  (`cfn_tight_le`), the household is constrained wherever the loose one is (`cfn_tight_binds`),
  the two consumption functions coincide for large wealth (`cfn_tight_eventually_eq`), and one
  period before the end the tight MPC is at least the loose MPC on every interval
  (`cfn_tight_mpc_last`).

Departures: the book's household lives for ever; here the horizon is finite and the infinite
horizon is reached only through `κₙ → r/(1 + r)`. Consumption functions are defined by the
Kuhn–Tucker conditions (as the book does with (11.33)); their sufficiency for optimality is not
re-proved. Concavity is proved weakly; "strictly concave" in the intermediate range is not. The
MPC comparison for a tighter limit is proved pointwise only one period before the end; with
more periods left the proved statements are the three above (lower consumption, wider
constrained range, coincidence at high wealth).
-/

namespace AKMM.Consumption

open Filter Topology

/-! ### The certainty equivalent -/

/-- The properties of the Euler equation's certainty equivalent `M` that the argument uses, on
vectors of positive next-period consumptions: monotone, normalised (`M` of a constant is the
constant), concave, continuous. The expectation (quadratic utility) and the power mean with a
negative exponent (CRRA) are instances. -/
def cfn_IsMean {ι : Type*} (M : (ι → ℝ) → ℝ) : Prop :=
  (∀ z z' : ι → ℝ, (∀ i, 0 < z i) → (∀ i, z i ≤ z' i) → M z ≤ M z') ∧
  (∀ k : ℝ, 0 < k → M (fun _ => k) = k) ∧
  (∀ z z' : ι → ℝ, (∀ i, 0 < z i) → (∀ i, 0 < z' i) → ∀ μ ν : ℝ, 0 ≤ μ → 0 ≤ ν → μ + ν = 1 →
    μ * M z + ν * M z' ≤ M (fun i => μ * z i + ν * z' i)) ∧
  (∀ z : ι → ℝ, (∀ i, 0 < z i) → ContinuousAt M z)

/-- A monotone, normalised `M` is at least `k` on vectors bounded below by `k > 0`. -/
theorem cfn_mean_ge {ι : Type*} {M : (ι → ℝ) → ℝ} (hM : cfn_IsMean M) {k : ℝ} (hk : 0 < k)
    {z : ι → ℝ} (hz : ∀ i, k ≤ z i) : k ≤ M z := by
  have h := hM.1 (fun _ => k) z (fun _ => hk) hz
  rwa [hM.2.1 k hk] at h

/-- A monotone, normalised `M` is at most `k` on positive vectors bounded above by `k`. -/
theorem cfn_mean_le {ι : Type*} {M : (ι → ℝ) → ℝ} (hM : cfn_IsMean M) {k : ℝ}
    {z : ι → ℝ} (hz0 : ∀ i, 0 < z i) (hz : ∀ i, z i ≤ k) [Nonempty ι] : M z ≤ k := by
  have hk : 0 < k := lt_of_lt_of_le (hz0 (Classical.arbitrary ι)) (hz _)
  have h := hM.1 z (fun _ => k) hz0 hz
  rwa [hM.2.1 k hk] at h

/-- **The expectation is a certainty equivalent** (quadratic utility). -/
theorem cfn_isMean_expect {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : cfn_IsMean (fun z : ι → ℝ => ∑ i, w i * z i) := by
  refine ⟨fun z z' _ hzz => Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hzz i) (hw i),
    fun k _ => by
      change ∑ i, w i * k = k
      rw [← Finset.sum_mul, hw1, one_mul], fun z z' _ _ μ ν _ _ _ => ?_,
    fun z _ => ?_⟩
  · simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    exact le_of_eq (by congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring)
  · exact (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).continuousAt

/-- **The power mean with a negative exponent is a certainty equivalent** (CRRA utility), by
LeanEconomics' Carroll–Kimball power-mean concavity (`powerMean_concave`). -/
theorem cfn_isMean_powerMean {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {p : ℝ} (hp : p < 0) :
    cfn_IsMean (LeanEconomics.powerMean w p) := by
  refine ⟨fun z z' hz hzz => LeanEconomics.powerMean_mono hp hw hw1 hz
      (fun i => lt_of_lt_of_le (hz i) (hzz i)) hzz, fun k hk => ?_,
    fun z z' hz hz' μ ν hμ hν hμν => LeanEconomics.powerMean_concave hp hw hw1 hz hz' hμ hν hμν,
    fun z hz => ?_⟩
  · have hs : ∑ i, w i * k ^ p = k ^ p := by rw [← Finset.sum_mul, hw1, one_mul]
    simp only [LeanEconomics.powerMean, hs]
    rw [← Real.rpow_mul hk.le, mul_one_div_cancel hp.ne, Real.rpow_one]
  · have hS : 0 < ∑ i, w i * z i ^ p := LeanEconomics.sum_rpow_pos hw hw1 hz
    have hi : ∀ i, ContinuousAt (fun z : ι → ℝ => w i * z i ^ p) z := fun i =>
      continuousAt_const.mul ((continuous_apply i).continuousAt.rpow_const (Or.inl (hz i).ne'))
    have hsum : ContinuousAt (fun z : ι → ℝ => ∑ i, w i * z i ^ p) z :=
      tendsto_finsetSum _ (fun i _ => hi i)
    exact hsum.rpow_const (Or.inl hS.ne')

/-! ### The household -/

/-- AKMM, pp. 304–306: the household of Figure 11.2. `M` and `θ` are the Euler equation's
certainty equivalent and its factor, `R = 1 + r`, `b` the borrowing limit `a`, `d` the lowest
cash in hand, `y` the i.i.d. income values with probabilities `w` and upper bound `ymax`. -/
structure CfnHousehold (ι : Type*) where
  M : (ι → ℝ) → ℝ
  θ : ℝ
  R : ℝ
  b : ℝ
  d : ℝ
  y : ι → ℝ
  ymax : ℝ
  w : ι → ℝ

namespace CfnHousehold

variable {ι : Type*} (H : CfnHousehold ι)

/-- The standing assumptions: `M` a certainty equivalent, `θ > 0`, `R ≥ 1` (`r ≥ 0`), `a ≥ 0`,
`d > 0`, `d + a ≤ yᵢ ≤ ymax`, and `w` a probability vector. -/
def Valid [Fintype ι] : Prop :=
  cfn_IsMean H.M ∧ 0 < H.θ ∧ 1 ≤ H.R ∧ 0 ≤ H.b ∧ 0 < H.d ∧ (∀ i, H.d + H.b ≤ H.y i) ∧
    (∀ i, H.y i ≤ H.ymax) ∧ (∀ i, 0 ≤ H.w i) ∧ ∑ i, H.w i = 1

/-- The right-hand side of the Euler condition at end-of-period saving `s = aₜ₊₁/R`, given next
period's consumption function `cn`: `θ·M(cn(Rs + yᵢ))`. -/
noncomputable def cont (cn : ℝ → ℝ) (s : ℝ) : ℝ := H.θ * H.M (fun i => cn (H.R * s + H.y i))

/-- **AKMM, (11.32)–(11.33).** The Kuhn–Tucker conditions for consumption `c` at cash in hand
`x`: the borrowing limit `c ≤ x + a/R`, the Euler inequality, and the Euler equation where the
limit is slack. -/
def KKT (cn : ℝ → ℝ) (x c : ℝ) : Prop :=
  c ≤ x + H.b / H.R ∧ c ≤ H.cont cn (x - c) ∧ (c < x + H.b / H.R → c = H.cont cn (x - c))

/-- One step of backward induction: the solution of the Kuhn–Tucker conditions. -/
noncomputable def step (cn : ℝ → ℝ) (x : ℝ) : ℝ := Classical.epsilon (fun c => H.KKT cn x c)

/-- The consumption function with `n` periods left after this one; in the last period the
household eats its cash in hand. -/
noncomputable def cons : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => H.step (cons n)

/-- The perfect-foresight MPC with `n` periods left: `κ₀ = 1`, `κₙ₊₁ = θRκₙ/(1 + θRκₙ)`. -/
noncomputable def kappa : ℕ → ℝ
  | 0 => 1
  | n + 1 => H.θ * H.R * kappa n / (1 + H.θ * H.R * kappa n)

/-- Human wealth at the highest income with `n` periods left: `h₀ = 0`, `hₙ₊₁ = (ymax + hₙ)/R`. -/
noncomputable def hw : ℕ → ℝ
  | 0 => 0
  | n + 1 => (H.ymax + hw n) / H.R

/-- The properties carried along the induction: positive, nondecreasing, slopes at most `1`,
concave, and between the lines `κx` and `κ(x + h)`. -/
def Good (κ h : ℝ) (cn : ℝ → ℝ) : Prop :=
  (∀ x, H.d ≤ x → 0 < cn x) ∧ MonotoneOn cn (Set.Ici H.d) ∧
  (∀ x x', H.d ≤ x → x ≤ x' → cn x' - cn x ≤ x' - x) ∧ ConcaveOn ℝ (Set.Ici H.d) cn ∧
  (∀ x, H.d ≤ x → κ * x ≤ cn x ∧ cn x ≤ κ * (x + h))

end CfnHousehold

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- Saving at least `−a/R` keeps next period's cash in hand above `d`. -/
theorem cfn_arg_ge (hV : H.Valid) {s : ℝ} (hs : -(H.b / H.R) ≤ s) (i : ι) :
    H.d ≤ H.R * s + H.y i := by
  obtain ⟨-, -, hR, -, -, hy, -⟩ := hV
  have hR0 : 0 < H.R := by linarith
  have h1 : -H.b ≤ H.R * s := by
    have := mul_le_mul_of_nonneg_left hs hR0.le
    rwa [mul_neg, mul_div_cancel₀ _ hR0.ne'] at this
  linarith [hy i]

omit [Fintype ι] in
/-- A good function is continuous on `[d, ∞)`: it is `1`-Lipschitz. -/
theorem cfn_good_continuousOn {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) :
    ContinuousOn cn (Set.Ici H.d) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx x' hx' => ?_).continuousOn
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x x' with hxx | hxx
  · have h1 := hg.2.2.1 x x' hx hxx
    have h2 := hg.2.1 hx hx' hxx
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := hg.2.2.1 x' x hx' hxx
    have h2 := hg.2.1 hx' hx hxx
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1

/-- The Euler right-hand side is nondecreasing in saving. -/
theorem cfn_cont_mono (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {s₁ s₂ : ℝ}
    (hs₁ : -(H.b / H.R) ≤ s₁) (h12 : s₁ ≤ s₂) : H.cont cn s₁ ≤ H.cont cn s₂ := by
  have hR : 0 ≤ H.R := by linarith [hV.2.2.1]
  have hs₂ : -(H.b / H.R) ≤ s₂ := le_trans hs₁ h12
  refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => hg.1 _ (cfn_arg_ge hV hs₁ i))
    (fun i => hg.2.1 (cfn_arg_ge hV hs₁ i) (cfn_arg_ge hV hs₂ i) ?_)) hV.2.1.le
  nlinarith

/-- The Euler right-hand side is concave in saving (Carroll–Kimball). -/
theorem cfn_cont_concave (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s₁ s₂ μ ν : ℝ} (hs₁ : -(H.b / H.R) ≤ s₁) (hs₂ : -(H.b / H.R) ≤ s₂) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hμν : μ + ν = 1) :
    μ * H.cont cn s₁ + ν * H.cont cn s₂ ≤ H.cont cn (μ * s₁ + ν * s₂) := by
  have hm : -(H.b / H.R) ≤ μ * s₁ + ν * s₂ := by
    have e1 := mul_le_mul_of_nonneg_left hs₁ hμ
    have e2 := mul_le_mul_of_nonneg_left hs₂ hν
    have e3 : -(H.b / H.R) = μ * -(H.b / H.R) + ν * -(H.b / H.R) := by
      linear_combination (H.b / H.R) * hμν
    linarith
  have hpos : ∀ s, -(H.b / H.R) ≤ s → ∀ i, 0 < cn (H.R * s + H.y i) :=
    fun s hs i => hg.1 _ (cfn_arg_ge hV hs i)
  have hconc : ∀ i, μ * cn (H.R * s₁ + H.y i) + ν * cn (H.R * s₂ + H.y i)
      ≤ cn (H.R * (μ * s₁ + ν * s₂) + H.y i) := by
    intro i
    have := hg.2.2.2.1.2 (Set.mem_Ici.2 (cfn_arg_ge hV hs₁ i))
      (Set.mem_Ici.2 (cfn_arg_ge hV hs₂ i)) hμ hν hμν
    simp only [smul_eq_mul] at this
    have he : μ * (H.R * s₁ + H.y i) + ν * (H.R * s₂ + H.y i)
        = H.R * (μ * s₁ + ν * s₂) + H.y i := by linear_combination H.y i * hμν
    rwa [he] at this
  have hcomb := hV.1.2.2.1 _ _ (hpos s₁ hs₁) (hpos s₂ hs₂) μ ν hμ hν hμν
  have hmono := hV.1.1 _ _ (fun i => by
      have := hpos s₁ hs₁ i; have := hpos s₂ hs₂ i
      rcases eq_or_lt_of_le hμ with h0 | h0
      · have : ν = 1 := by linarith
        subst h0; simp only [zero_mul, zero_add, this, one_mul]; linarith
      · positivity) hconc
  simp only [cont]
  have hθ := hV.2.1
  nlinarith [mul_le_mul_of_nonneg_left (le_trans hcomb hmono) hθ.le]

/-- The lower bound of the Euler right-hand side from a linear lower bound on `cn`. -/
theorem cfn_cont_ge (hV : H.Valid) {κ h : ℝ} (hκ : 0 < κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s : ℝ} (hs : 0 < s) : H.θ * κ * H.R * s ≤ H.cont cn s := by
  obtain ⟨hM, hθ, hR, hb, hd, hy, -⟩ := id hV
  have hR0 : 0 < H.R := by linarith
  have hbR : -(H.b / H.R) ≤ s := by
    have : 0 ≤ H.b / H.R := div_nonneg hb hR0.le
    linarith
  have hk : 0 < κ * H.R * s := by positivity
  have hz : ∀ i, κ * H.R * s ≤ cn (H.R * s + H.y i) := by
    intro i
    have h1 := (hg.2.2.2.2 _ (cfn_arg_ge hV hbR i)).1
    have hyi : 0 ≤ H.y i := by linarith [hy i]
    nlinarith
  have := cfn_mean_ge hM hk hz
  simp only [cont]
  nlinarith

/-- The upper bound of the Euler right-hand side from `cn ≤ κ(x + h)`. -/
theorem cfn_cont_le (hV : H.Valid) {κ h : ℝ} (hκ0 : 0 ≤ κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s : ℝ} (hs : -(H.b / H.R) ≤ s) : H.cont cn s ≤ H.θ * (κ * (H.R * s + H.ymax + h)) := by
  have hz : ∀ i, cn (H.R * s + H.y i) ≤ κ * (H.R * s + H.ymax + h) := by
    intro i
    have h1 := (hg.2.2.2.2 _ (cfn_arg_ge hV hs i)).2
    have := hV.2.2.2.2.2.2.1 i
    nlinarith
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := hV.1.2.1 1 one_pos
    have h2 := hV.1.2.1 2 two_pos
    have : (fun _ : ι => (1 : ℝ)) = fun _ => 2 := funext fun i => isEmptyElim i
    rw [this] at h1
    linarith
  exact mul_le_mul_of_nonneg_left
    (cfn_mean_le hV.1 (fun i => hg.1 _ (cfn_arg_ge hV hs i)) hz) hV.2.1.le

omit [Fintype ι] in
/-- Unfolding `R(x − c) ≥ −a` from `c ≤ x + a/R`. -/
theorem cfn_save_ge {x c : ℝ} (hc : c ≤ x + H.b / H.R) :
    -(H.b / H.R) ≤ x - c := by linarith

/-- **The Kuhn–Tucker conditions have a solution** at every `x ≥ d`, by the intermediate value
theorem: the Euler gap `c − θM(cn(R(x − c) + yᵢ))` is continuous and negative at small `c`. -/
theorem cfn_kkt_exists (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) (x : ℝ) :
    ∃ c, H.KKT cn x c := by
  set top := x + H.b / H.R with htop
  by_cases hF : top ≤ H.cont cn (x - top)
  · exact ⟨top, le_rfl, hF, fun h => absurd h (lt_irrefl _)⟩
  push Not at hF
  have hd := hV.2.2.2.2.1
  set c₀ := min top (H.θ * cn H.d) with hc₀
  have hc₀top : c₀ ≤ top := min_le_left _ _
  -- the Euler right-hand side is at least `θ·cn(d)`
  have hlow : ∀ c, c ≤ top → H.θ * cn H.d ≤ H.cont cn (x - c) := by
    intro c hc
    have hs := cfn_save_ge hc
    have h1 : cn H.d ≤ H.M (fun i => cn (H.R * (x - c) + H.y i)) :=
      cfn_mean_ge hV.1 (hg.1 _ le_rfl) fun i => hg.2.1 (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 (cfn_arg_ge hV hs i)) (cfn_arg_ge hV hs i)
    exact mul_le_mul_of_nonneg_left h1 hV.2.1.le
  have hF0 : c₀ - H.cont cn (x - c₀) ≤ 0 := by
    have := hlow c₀ hc₀top
    have : c₀ ≤ H.θ * cn H.d := min_le_right _ _
    linarith
  -- continuity of the Euler gap on `[c₀, top]`
  have hcont : ContinuousOn (fun c => c - H.cont cn (x - c)) (Set.Icc c₀ top) := by
    have hcn := cfn_good_continuousOn hg
    have hv : ContinuousOn (fun c => fun i => cn (H.R * (x - c) + H.y i)) (Set.Icc c₀ top) := by
      refine continuousOn_pi.2 fun i => ?_
      refine hcn.comp (f := fun c => H.R * (x - c) + H.y i) (by fun_prop) fun c hc => ?_
      exact Set.mem_Ici.2 (cfn_arg_ge hV (cfn_save_ge hc.2) i)
    refine continuousOn_id.sub (continuousOn_const.mul fun c hc => ?_)
    exact (hV.1.2.2.2 _ fun i => hg.1 _ (cfn_arg_ge hV (cfn_save_ge hc.2) i)
      ).comp_continuousWithinAt (hv c hc)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hc₀top hcont
    ⟨hF0, by linarith⟩
  have hceq : c = H.cont cn (x - c) := by linarith
  exact ⟨c, hc.2, le_of_eq hceq, fun _ => hceq⟩

/-- **The Kuhn–Tucker conditions have at most one solution.** -/
theorem cfn_kkt_unique (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c c' : ℝ}
    (hc : H.KKT cn x c) (hc' : H.KKT cn x c') : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hint : c < x + H.b / H.R := lt_of_lt_of_le hlt hc'.1
    have := hc.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge hc'.1) (by linarith : x - c' ≤ x - c)
    linarith [hc'.2.1]
  · have hint : c' < x + H.b / H.R := lt_of_lt_of_le hlt hc.1
    have := hc'.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge hc.1) (by linarith : x - c ≤ x - c')
    linarith [hc.2.1]

/-- The step function solves the Kuhn–Tucker conditions. -/
theorem cfn_step_kkt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) (x : ℝ) :
    H.KKT cn x (H.step cn x) :=
  Classical.epsilon_spec (cfn_kkt_exists hV hg x)

/-- Any solution of the Kuhn–Tucker conditions is the step function's value. -/
theorem cfn_step_eq_of_kkt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (hc : H.KKT cn x c) : H.step cn x = c :=
  cfn_kkt_unique hV hg (cfn_step_kkt hV hg x) hc

/-- **Consumption and saving are both nondecreasing in cash in hand** under any rule solving the
Kuhn–Tucker conditions. -/
theorem cfn_kkt_mono (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x₁ x₂ c₁ c₂ : ℝ}
    (h₁ : H.KKT cn x₁ c₁) (h₂ : H.KKT cn x₂ c₂) (hx : x₁ ≤ x₂) : c₁ ≤ c₂ ∧ x₁ - c₁ ≤ x₂ - c₂ := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hint : c₂ < x₂ + H.b / H.R := by linarith [h₁.1]
    have := h₂.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge h₁.1) (by linarith : x₁ - c₁ ≤ x₂ - c₂)
    linarith [h₁.2.1]
  · by_contra hlt
    push Not at hlt
    have hint : c₁ < x₁ + H.b / H.R := by linarith [h₂.1]
    have := h₁.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge h₂.1) hlt.le
    linarith [h₂.2.1]

/-- **The induction step.** If next period's consumption function is good with `(κ, h)`, this
period's is good with `(θRκ/(1 + θRκ), (ymax + h)/R)`. -/
theorem cfn_step_good (hV : H.Valid) {κ h : ℝ} (hκ : 0 < κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn) :
    H.Good (H.θ * H.R * κ / (1 + H.θ * H.R * κ)) ((H.ymax + h) / H.R) (H.step cn) := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hθ := hV.2.1
  have hd := hV.2.2.2.2.1
  have hb := hV.2.2.2.1
  set q := H.θ * H.R * κ with hq
  have hq0 : 0 < q := by positivity
  have hK := fun x (_ : H.d ≤ x) => cfn_step_kkt hV hg x
  have hκ1 : q / (1 + q) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- the sandwich
  have hsand : ∀ x, H.d ≤ x → q / (1 + q) * x ≤ H.step cn x ∧
      H.step cn x ≤ q / (1 + q) * (x + (H.ymax + h) / H.R) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hK x hx
    constructor
    · rcases le_or_gt (x - H.step cn x) 0 with hs | hs
      · have : q / (1 + q) * x ≤ x := by
          have := mul_le_mul_of_nonneg_right hκ1 (by linarith : 0 ≤ x); linarith
        linarith
      · have hint : H.step cn x < x + H.b / H.R := by
          have : 0 ≤ H.b / H.R := div_nonneg hb hR0.le
          linarith
        have he := h3 hint
        have hge := cfn_cont_ge hV hκ hg hs
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        rw [← he] at hge
        nlinarith
    · have hle := cfn_cont_le hV hκ.le hg (cfn_save_ge h1)
      have hc := le_trans h2 hle
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have he : H.θ * (κ * (H.R * (x - H.step cn x) + H.ymax + h))
          = q * (x - H.step cn x + (H.ymax + h) / H.R) := by
        rw [hq]; field_simp; ring
      rw [he] at hc
      nlinarith
  refine ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun x x' hx hxx => ?_, ?_, hsand⟩
  · have := (hsand x hx).1
    have : 0 < q / (1 + q) * x := mul_pos (div_pos hq0 (by linarith)) (by linarith)
    linarith
  · exact (cfn_kkt_mono hV hg (hK x hx) (hK x' hx') hxx).1
  · have := (cfn_kkt_mono hV hg (hK x hx) (hK x' (le_trans hx hxx)) hxx).2
    linarith
  · refine ⟨convex_Ici _, fun x hx x' hx' μ ν hμ hν hμν => ?_⟩
    simp only [smul_eq_mul]
    have hx0 : H.d ≤ x := hx
    have hx0' : H.d ≤ x' := hx'
    have hm : H.d ≤ μ * x + ν * x' := by nlinarith
    obtain ⟨a1, a2, -⟩ := hK x hx0
    obtain ⟨b1, b2, -⟩ := hK x' hx0'
    obtain ⟨m1, -, m3⟩ := hK _ hm
    by_contra hlt
    push Not at hlt
    have hsa := cfn_save_ge a1
    have hsb := cfn_save_ge b1
    have hsm : μ * (x - H.step cn x) + ν * (x' - H.step cn x')
        < μ * x + ν * x' - H.step cn (μ * x + ν * x') := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hsa hμ
    have e2 := mul_le_mul_of_nonneg_left hsb hν
    have e3 : -(H.b / H.R) = μ * -(H.b / H.R) + ν * -(H.b / H.R) := by
      linear_combination (H.b / H.R) * hμν
    have hint : H.step cn (μ * x + ν * x') < μ * x + ν * x' + H.b / H.R := by linarith
    have he := m3 hint
    have hconc := cfn_cont_concave hV hg hsa hsb hμ hν hμν
    have hmono := cfn_cont_mono hV hg (by linarith) hsm.le
    nlinarith

/-- `0 < κₙ ≤ 1`. -/
theorem cfn_kappa_pos (hV : H.Valid) (n : ℕ) : 0 < H.kappa n ∧ H.kappa n ≤ 1 := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hθ := hV.2.1
  induction n with
  | zero => simp only [kappa]; norm_num
  | succ n ih =>
    simp only [kappa]
    have hq : 0 < H.θ * H.R * H.kappa n := by have := ih.1; positivity
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩

/-- **Every consumption function is good**: positive, nondecreasing, slopes at most `1`, concave,
and `κₙx ≤ cₙ(x) ≤ κₙ(x + hₙ)`. -/
theorem cfn_cons_good (hV : H.Valid) (n : ℕ) : H.Good (H.kappa n) (H.hw n) (H.cons n) := by
  induction n with
  | zero =>
    have hd := hV.2.2.2.2.1
    refine ⟨fun x hx => by simp only [cons]; linarith, fun x _ x' _ h => h,
      fun x x' _ _ => by simp only [cons]; linarith, ?_, fun x _ => ?_⟩
    · exact (LinearMap.id : ℝ →ₗ[ℝ] ℝ).concaveOn (convex_Ici _)
    · simp only [cons, kappa, hw]; constructor <;> linarith
  | succ n ih =>
    simp only [cons, kappa, hw]
    exact cfn_step_good hV (cfn_kappa_pos hV n).1 ih

/-- `cₙ₊₁` solves the Kuhn–Tucker conditions (11.32)–(11.33) given `cₙ`. -/
theorem cfn_cons_kkt (hV : H.Valid) (n : ℕ) (x : ℝ) :
    H.KKT (H.cons n) x (H.cons (n + 1) x) :=
  cfn_step_kkt hV (cfn_cons_good hV n) x

/-- The borrowing limit: `cₙ(x) ≤ x + a/R`. -/
theorem cfn_cons_le (hV : H.Valid) (n : ℕ) (x : ℝ) :
    H.cons n x ≤ x + H.b / H.R := by
  cases n with
  | zero =>
    simp only [cons]
    have : 0 ≤ H.b / H.R := div_nonneg hV.2.2.2.1 (by linarith [hV.2.2.1])
    linarith
  | succ n => exact (cfn_cons_kkt hV n x).1

/-- **Figure 11.2: the consumption function is concave** in cash in hand (Carroll–Kimball). -/
theorem cfn_cons_concave (hV : H.Valid) (n : ℕ) : ConcaveOn ℝ (Set.Ici H.d) (H.cons n) :=
  (cfn_cons_good hV n).2.2.2.1

/-! ### Slopes -/

/-- A concave function above the line `κx` has every slope at least `κ`. -/
theorem cfn_slope_ge_of_concave {f : ℝ → ℝ} {d κ : ℝ} (hf : ConcaveOn ℝ (Set.Ici d) f)
    (hlow : ∀ x, d ≤ x → κ * x ≤ f x) {x x' : ℝ} (hx : d ≤ x) (hxx : x < x') :
    κ ≤ (f x' - f x) / (x' - x) := by
  by_contra hlt
  push Not at hlt
  set σ := (f x' - f x) / (x' - x) with hσ
  set z := max (x' + 1) ((f x' - σ * x' + 1) / (κ - σ)) with hz
  have hz1 : x' < z := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hκσ : 0 < κ - σ := by linarith
  have hslope := hf.slope_anti_adjacent (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (by linarith : d ≤ z)) hxx hz1
  rw [← hσ, div_le_iff₀ (by linarith)] at hslope
  have hfz := hlow z (by linarith)
  have hz2 : (f x' - σ * x' + 1) / (κ - σ) ≤ z := le_max_right _ _
  rw [div_le_iff₀ hκσ] at hz2
  nlinarith

/-- A concave function below the line `κ(x + K)` has slopes eventually at most `κ + ε`. -/
theorem cfn_slope_le_eventually {f : ℝ → ℝ} {d κ K : ℝ} (hf : ConcaveOn ℝ (Set.Ici d) f)
    (hup : ∀ x, d ≤ x → f x ≤ κ * (x + K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ X, ∀ x x', X ≤ x → x < x' → (f x' - f x) / (x' - x) ≤ κ + ε := by
  set C := κ * (K + d) - f d with hC
  refine ⟨d + 1 + |C| / ε, fun x x' hx hxx => ?_⟩
  have hCε : 0 ≤ |C| / ε := div_nonneg (abs_nonneg _) hε.le
  have hdx : d < x := by linarith
  have hslope := hf.slope_anti_adjacent (Set.mem_Ici.2 le_rfl)
    (Set.mem_Ici.2 (by linarith : d ≤ x')) hdx hxx
  refine le_trans hslope ?_
  rw [div_le_iff₀ (by linarith)]
  have hfx := hup x hdx.le
  have h1 : |C| ≤ ε * (x - d - 1) := by
    have : |C| / ε ≤ x - d - 1 := by linarith
    rw [div_le_iff₀ hε] at this; linarith
  have h2 : C ≤ |C| := le_abs_self C
  nlinarith

/-- **Figure 11.2: the MPC lies between `κₙ` and `1`.** Every slope of the consumption function
on `[d, ∞)` is at least the perfect-foresight MPC `κₙ` and at most `1`. -/
theorem cfn_cons_slope_bounds (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x < x') :
    H.kappa n ≤ (H.cons n x' - H.cons n x) / (x' - x) ∧
      (H.cons n x' - H.cons n x) / (x' - x) ≤ 1 := by
  have hg := cfn_cons_good hV n
  refine ⟨cfn_slope_ge_of_concave hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).1) hx hxx, ?_⟩
  rw [div_le_one (by linarith)]
  exact hg.2.2.1 x x' hx hxx.le

/-- **Figure 11.2: the slope tends to `κₙ` as wealth grows.** For every `ε > 0` all slopes of
`cₙ` beyond some wealth level are within `ε` of the perfect-foresight MPC `κₙ`. -/
theorem cfn_slope_tendsto (hV : H.Valid) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X, ∀ x x', X ≤ x → x < x' →
      |(H.cons n x' - H.cons n x) / (x' - x) - H.kappa n| ≤ ε := by
  have hg := cfn_cons_good hV n
  obtain ⟨X, hX⟩ := cfn_slope_le_eventually hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).2) hε
  refine ⟨max X H.d, fun x x' hx hxx => ?_⟩
  have h1 := hX x x' (le_trans (le_max_left _ _) hx) hxx
  have h2 := cfn_slope_ge_of_concave hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).1)
    (le_trans (le_max_right _ _) hx) hxx
  rw [abs_le]; constructor <;> linarith

/-- **Figure 11.2: the binding region is an initial interval**, on which the slope is `1`. If the
borrowing limit binds at `x'` (`c = x' + a/R`) it binds at every `x ∈ [d, x']`. -/
theorem cfn_binding_initial (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hxx : x ≤ x')
    (hbind : H.cons (n + 1) x' = x' + H.b / H.R) :
    H.cons (n + 1) x = x + H.b / H.R ∧ H.cons (n + 1) x' - H.cons (n + 1) x = x' - x := by
  have h1 := cfn_kkt_mono hV (cfn_cons_good hV n) (cfn_cons_kkt hV n x)
    (cfn_cons_kkt hV n _) hxx
  have h2 := (cfn_cons_kkt hV n x).1
  have h3 : H.cons (n + 1) x = x + H.b / H.R := by linarith [h1.2]
  exact ⟨h3, by rw [h3, hbind]; ring⟩

/-! ### The perfect-foresight MPC and the infinite horizon -/

omit [Fintype ι] in
/-- The closed form `κₙ = (1 − ρ)/(1 − ρⁿ⁺¹)`, `ρ = 1/(θR) < 1`. -/
theorem cfn_kappa_eq (hθR : 1 < H.θ * H.R) (n : ℕ) :
    H.kappa n = (1 - 1 / (H.θ * H.R)) / (1 - (1 / (H.θ * H.R)) ^ (n + 1)) := by
  set ρ := 1 / (H.θ * H.R) with hρ
  have hθR0 : 0 < H.θ * H.R := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hθR0]; exact hθR
  have hpow : ∀ k : ℕ, ρ ^ (k + 1) < 1 := fun k => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hθR : H.θ * H.R = 1 / ρ := by rw [hρ, one_div_one_div]
  induction n with
  | zero => simp only [kappa, zero_add, pow_one]; rw [div_self (by linarith)]
  | succ n ih =>
    simp only [kappa]
    rw [ih, hθR]
    have h1 := hpow n
    have h2 := hpow (n + 1)
    have h3 : 0 < 1 - ρ ^ (n + 1) := by linarith
    have h4 : 0 < 1 - ρ ^ (n + 1 + 1) := by linarith
    have hA : 0 < 1 - ρ := by linarith
    have h5 : 0 < 1 / ρ * ((1 - ρ) / (1 - ρ ^ (n + 1))) :=
      mul_pos (by positivity) (div_pos hA h3)
    rw [div_eq_div_iff (by linarith) h4.ne']
    field_simp
    ring

omit [Fintype ι] in
/-- **As the horizon grows the perfect-foresight MPC tends to `1 − 1/(θR)`.** -/
theorem cfn_kappa_tendsto (hθR : 1 < H.θ * H.R) :
    Tendsto H.kappa atTop (𝓝 (1 - 1 / (H.θ * H.R))) := by
  have hθR0 : 0 < H.θ * H.R := by linarith
  have hρ0 : 0 ≤ 1 / (H.θ * H.R) := by positivity
  have hρ1 : 1 / (H.θ * H.R) < 1 := by rw [div_lt_one hθR0]; exact hθR
  have hp : Tendsto (fun n : ℕ => (1 / (H.θ * H.R)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x := 1 - 1 / (H.θ * H.R))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp) (by norm_num)
  simp only [sub_zero, div_one] at h
  exact h.congr fun n => (cfn_kappa_eq hθR n).symm

omit [Fintype ι] in
/-- **AKMM, p. 305 (`βR = 1`): the limiting MPC is `r/(1 + r)`.** With `θ = 1` and `R = 1 + r`,
`r > 0`, `κₙ → r/(1 + r)`. -/
theorem cfn_kappa_tendsto_r (hθ : H.θ = 1) {r : ℝ} (hr : 0 < r)
    (hR : H.R = 1 + r) : Tendsto H.kappa atTop (𝓝 (r / (1 + r))) := by
  have h := cfn_kappa_tendsto (by rw [hθ, hR]; linarith)
  have he : 1 - 1 / (H.θ * H.R) = r / (1 + r) := by
    rw [hθ, hR, one_mul]; field_simp; ring
  rwa [he] at h

/-- **Figure 11.2 (`βR = 1`): for large wealth and a long horizon the slope is `r/(1 + r)`.**
For every `ε > 0` there is a horizon `N` such that for every `n ≥ N`, all slopes of `cₙ` beyond
some wealth level are within `ε` of `r/(1 + r)`. -/
theorem cfn_fig_11_2_slope (hV : H.Valid) (hθ : H.θ = 1) {r : ℝ} (hr : 0 < r) (hR : H.R = 1 + r)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∃ X, ∀ x x', X ≤ x → x < x' →
      |(H.cons n x' - H.cons n x) / (x' - x) - r / (1 + r)| ≤ ε := by
  have h := cfn_kappa_tendsto_r hθ hr hR
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨X, hX⟩ := cfn_slope_tendsto hV n (by linarith : 0 < ε / 2)
  refine ⟨X, fun x x' hx hxx => ?_⟩
  have h1 := hX x x' hx hxx
  have h2 := hN n hn
  rw [Real.dist_eq] at h2
  calc |(H.cons n x' - H.cons n x) / (x' - x) - r / (1 + r)|
      ≤ |(H.cons n x' - H.cons n x) / (x' - x) - H.kappa n| + |H.kappa n - r / (1 + r)| :=
        abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- The perfect-foresight MPC stays above its limit: `1 − 1/(θR) < κₙ`. -/
theorem cfn_kappa_gt (hV : H.Valid) (n : ℕ) : 1 - 1 / (H.θ * H.R) < H.kappa n := by
  have hθR0 : 0 < H.θ * H.R := mul_pos hV.2.1 (by linarith [hV.2.2.1])
  induction n with
  | zero =>
    simp only [kappa]
    have : 0 < 1 / (H.θ * H.R) := by positivity
    linarith
  | succ n ih =>
    simp only [kappa]
    have hq : H.θ * H.R - 1 < H.θ * H.R * H.kappa n := by
      have := mul_lt_mul_of_pos_left ih hθR0
      rw [mul_sub, mul_one, mul_one_div_cancel hθR0.ne'] at this
      exact this
    have hq0 : 0 < 1 + H.θ * H.R * H.kappa n := by
      have := (cfn_kappa_pos hV n).1; positivity
    rw [show 1 - 1 / (H.θ * H.R) = (H.θ * H.R - 1) / (H.θ * H.R) by
        rw [sub_div, div_self hθR0.ne'],
      div_lt_div_iff₀ hθR0 hq0]
    nlinarith

/-- **The impatience condition for a target** (`θ ≥ 1`, i.e. `βR ≤ 1`): `R(1 − κₙ) < 1`. -/
theorem cfn_R_one_sub_kappa_lt (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (n : ℕ) :
    H.R * (1 - H.kappa n) < 1 := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  cases n with
  | zero => simp only [kappa]; norm_num
  | succ n =>
    have hgt := cfn_kappa_gt hV n
    have hθR0 : 0 < H.θ * H.R := mul_pos hV.2.1 hR0
    have hk0 := (cfn_kappa_pos hV n).1
    simp only [kappa]
    have hq0 : 0 < 1 + H.θ * H.R * H.kappa n := by positivity
    have h1 : 1 - H.θ * H.R * H.kappa n / (1 + H.θ * H.R * H.kappa n)
        = 1 / (1 + H.θ * H.R * H.kappa n) := by field_simp; ring
    rw [h1, mul_one_div, div_lt_one hq0]
    have h2 : H.θ * H.R - 1 < H.θ * H.R * H.kappa n := by
      have := mul_lt_mul_of_pos_left hgt hθR0
      rw [mul_sub, mul_one, mul_one_div_cancel hθR0.ne'] at this
      exact this
    nlinarith

/-! ### A tighter borrowing limit -/

/-- The household with the tighter borrowing limit `a₂`. -/
def CfnHousehold.tighten (H : CfnHousehold ι) (b₂ : ℝ) : CfnHousehold ι := { H with b := b₂ }

/-- The tighter household satisfies the standing assumptions. -/
theorem cfn_tighten_valid (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) :
    (H.tighten b₂).Valid := by
  obtain ⟨hM, hθ, hR, -, hd, hy, hymax, hw, hw1⟩ := hV
  exact ⟨hM, hθ, hR, hb₂, hd, fun i => by simp only [CfnHousehold.tighten]; linarith [hy i],
    hymax, hw, hw1⟩

/-- **AKMM, p. 306: a tighter limit lowers consumption everywhere.** -/
theorem cfn_tight_le (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : (H.tighten b₂).cons n x ≤ H.cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  induction n generalizing x with
  | zero => simp only [cons]; rfl
  | succ n ih =>
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n x
    have hg := cfn_cons_good hV n
    have hR0 : 0 < H.R := by linarith [hV.2.2.1]
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) x
    have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
    have hs₂ : -(H.b / H.R) ≤ x - c₂ := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this; linarith
    have hint : c < x + H.b / H.R := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this; linarith
    have he := hK.2.2 hint
    have hm := cfn_cont_mono hV hg hs₂ (by linarith : x - c₂ ≤ x - c)
    -- next period the tight household consumes less
    have hle : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - c₂)
        ≤ H.cont (H.cons n) (x - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => ?_) fun i => ih ?_) hV.2.1.le
      · exact (cfn_cons_good hV₂ n).1 _ (cfn_arg_ge hV₂ (by
          have := hK₂.1; simp only [CfnHousehold.tighten] at this ⊢; linarith) i)
      · exact cfn_arg_ge hV hs₂ i
    linarith [hK₂.2.1]

/-- **The shift bound.** With `Δ = a₁ − a₂` more cash the tight household consumes at least as
much as the loose one (`r ≥ 0`). -/
theorem cfn_tight_shift (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : H.cons n x ≤ (H.tighten b₂).cons n (x + (H.b - b₂)) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    set Δ := H.b - b₂ with hΔ
    have hΔ0 : 0 ≤ Δ := by linarith
    have hxΔ : H.d ≤ x + Δ := by linarith
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + Δ)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) (x + Δ)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    -- the tight household saves more than the loose one plus `Δ`, hence is unconstrained
    have hΔR : Δ / H.R ≤ Δ := div_le_self hΔ0 hR1
    have hbR : H.b / H.R = b₂ / H.R + Δ / H.R := by rw [hΔ]; ring
    have hK1 := hK.1
    have hint : c₂ < x + Δ + (H.tighten b₂).b / H.R := by
      simp only [CfnHousehold.tighten]; linarith
    have he := hK₂.2.2 hint
    -- compare the Euler right-hand sides
    have hge : H.cont (H.cons n) (x - c) ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n)
        (x + Δ - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
        (cfn_arg_ge hV hs i)) fun i => ?_) hV.2.1.le
      have hsi := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      refine le_trans (ih hsi) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 ?_) ?_)
      · have : H.R * (x - c) + Δ ≤ H.R * (x + Δ - c₂) := by nlinarith
        rw [htd]; linarith
      · have : H.R * (x - c) + Δ ≤ H.R * (x + Δ - c₂) := by nlinarith
        linarith
    linarith [hK.2.1]

/-- **AKMM, p. 306: with a tighter limit the household is constrained on a wider range.** Wherever
the loose limit binds, so does the tight one. -/
theorem cfn_tight_binds (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) (x : ℝ)
    (hbind : H.cons (n + 1) x = x + H.b / H.R) :
    (H.tighten b₂).cons (n + 1) x = x + b₂ / H.R := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hK := (cfn_cons_kkt hV n x).2.1
  rw [hbind, show x - (x + H.b / H.R) = -(H.b / H.R) by ring] at hK
  -- the corner Euler inequality carries over through the shift bound
  have hcorner : H.cont (H.cons n) (-(H.b / H.R)) ≤ (H.tighten b₂).cont
      ((H.tighten b₂).cons n) (-(b₂ / H.R)) := by
    simp only [cont, CfnHousehold.tighten]
    refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
      (cfn_arg_ge hV le_rfl i)) fun i => ?_) hV.2.1.le
    have h1 := cfn_tight_shift hV hb₂ hb n (cfn_arg_ge hV le_rfl i)
    have he : H.R * -(H.b / H.R) + H.y i + (H.b - b₂) = H.R * -(b₂ / H.R) + H.y i := by
      field_simp; ring
    rw [he] at h1
    exact h1
  have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
  have he2 : x - (x + (H.tighten b₂).b / (H.tighten b₂).R) = -(b₂ / H.R) := by
    simp only [CfnHousehold.tighten]; ring
  have hkkt : (H.tighten b₂).KKT ((H.tighten b₂).cons n) x
      (x + (H.tighten b₂).b / (H.tighten b₂).R) := by
    refine ⟨le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
    rw [he2]
    have : x + (H.tighten b₂).b / (H.tighten b₂).R = x + b₂ / H.R := rfl
    rw [this]
    linarith
  exact cfn_step_eq_of_kkt hV₂ (cfn_cons_good hV₂ n) hkkt

/-- **AKMM, p. 306: "as wealth keeps growing, the two consumption functions converge".** They
coincide above some wealth level. -/
theorem cfn_tight_eventually_eq (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) :
    ∃ X, H.d ≤ X ∧ ∀ x, X ≤ x → (H.tighten b₂).cons n x = H.cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  induction n with
  | zero => exact ⟨H.d, le_rfl, fun x _ => rfl⟩
  | succ n ih =>
    obtain ⟨X', hX'd, hX'⟩ := ih
    have hg := cfn_cons_good hV (n + 1)
    set κ := H.kappa (n + 1) with hκ
    have hκ1 : κ < 1 := by
      simp only [hκ, kappa]
      have := (cfn_kappa_pos hV n).1
      have : 0 < H.θ * H.R * H.kappa n := mul_pos (mul_pos hV.2.1 hR0) this
      rw [div_lt_one (by linarith)]; linarith
    set h := H.hw (n + 1)
    -- saving exceeds `S` once cash in hand exceeds `X`
    set S := |X'| / H.R + 1 with hS
    set X := max H.d ((S + κ * |h|) / (1 - κ)) with hX
    refine ⟨X, le_max_left _ _, fun x hx => ?_⟩
    have hxd : H.d ≤ x := le_trans (le_max_left _ _) hx
    have hup := (hg.2.2.2.2 x hxd).2
    have hsave : S ≤ x - H.cons (n + 1) x := by
      have h1 : (S + κ * |h|) / (1 - κ) ≤ x := le_trans (le_max_right _ _) hx
      rw [div_le_iff₀ (by linarith)] at h1
      have := (cfn_kappa_pos hV (n + 1)).1
      nlinarith [le_abs_self h, mul_le_mul_of_nonneg_left (le_abs_self h) this.le]
    have hS1 : 1 ≤ S := by
      have : 0 ≤ |X'| / H.R := by positivity
      linarith
    have hK := cfn_cons_kkt hV n x
    have hbR : 0 ≤ b₂ / H.R := div_nonneg hb₂ hR0.le
    have hint : H.cons (n + 1) x < x + b₂ / H.R := by linarith
    have hint₁ : H.cons (n + 1) x < x + H.b / H.R := by
      have : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
      linarith
    have he := hK.2.2 hint₁
    refine cfn_step_eq_of_kkt hV₂ (cfn_cons_good hV₂ n) ⟨?_, ?_, fun _ => ?_⟩
    · simp only [CfnHousehold.tighten]; exact hint.le
    · have : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - H.cons (n + 1) x)
          = H.cont (H.cons n) (x - H.cons (n + 1) x) := by
        simp only [cont, CfnHousehold.tighten]
        congr 2
        funext i
        refine hX' _ ?_
        have : |X'| ≤ H.R * (x - H.cons (n + 1) x) - H.R := by
          have h2 := mul_le_mul_of_nonneg_left hsave hR0.le
          rw [hS, mul_add, mul_div_cancel₀ _ hR0.ne', mul_one] at h2
          linarith
        have hyi : 0 ≤ H.y i := by linarith [hV.2.2.2.2.2.1 i, hV.2.2.2.2.1, hV.2.2.2.1]
        linarith [le_abs_self X']
      rw [this, ← he]
    · have : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - H.cons (n + 1) x)
          = H.cont (H.cons n) (x - H.cons (n + 1) x) := by
        simp only [cont, CfnHousehold.tighten]
        congr 2
        funext i
        refine hX' _ ?_
        have : |X'| ≤ H.R * (x - H.cons (n + 1) x) - H.R := by
          have h2 := mul_le_mul_of_nonneg_left hsave hR0.le
          rw [hS, mul_add, mul_div_cancel₀ _ hR0.ne', mul_one] at h2
          linarith
        have hyi : 0 ≤ H.y i := by linarith [hV.2.2.2.2.2.1 i, hV.2.2.2.2.1, hV.2.2.2.1]
        linarith [le_abs_self X']
      rw [this, ← he]

/-- **AKMM, p. 306: a tighter limit raises the MPC**, one period before the end (the two-period
problem): on every interval of cash in hand the tight household's consumption rises at least as
much as the loose household's. -/
theorem cfn_tight_mpc_last (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) {x x' : ℝ}
    (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons 1 x' - H.cons 1 x ≤ (H.tighten b₂).cons 1 x' - (H.tighten b₂).cons 1 x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hx' : H.d ≤ x' := le_trans hx hxx
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hg := cfn_cons_good hV 0
  have hlip := hg.2.2.1 x x' hx hxx
  have hle := cfn_tight_le hV hb₂ hb 1 hx
  by_cases hbind : (H.tighten b₂).cons 1 x' = x' + b₂ / H.R
  · -- the tight household is constrained at `x'`, hence at `x`
    have h := cfn_binding_initial hV₂ 0 hxx (by simpa only [CfnHousehold.tighten] using hbind)
    have := (cfn_cons_good hV 1).2.2.1 x x' hx hxx
    linarith [h.2]
  · -- the tight household is unconstrained at `x'`, so it consumes as the loose one does
    have hK₂ := cfn_cons_kkt hV₂ 0 x'
    have hint : (H.tighten b₂).cons 1 x' < x' + b₂ / H.R := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this
      exact lt_of_le_of_ne this hbind
    have he := hK₂.2.2 (by simpa only [CfnHousehold.tighten] using hint)
    have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
    have heq : H.cons 1 x' = (H.tighten b₂).cons 1 x' := by
      exact cfn_step_eq_of_kkt hV hg ⟨by linarith, le_of_eq (he.trans rfl),
        fun _ => he.trans rfl⟩
    linarith

/-- **Correction to AKMM, p. 306** ("for unconstrained households, consumption falls across the
board"). One period before the end a tighter limit does not lower the consumption of a household
it leaves unconstrained at all: there the two consumption functions coincide. Together with
`cfn_tight_eventually_eq` (such cash in hand exists) the fall is only weak. -/
theorem cfn_tight_eq_unconstrained_last (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    {x : ℝ} (hint : (H.tighten b₂).cons 1 x < x + b₂ / H.R) :
    (H.tighten b₂).cons 1 x = H.cons 1 x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have he := (cfn_cons_kkt hV₂ 0 x).2.2 (by simpa only [CfnHousehold.tighten] using hint)
  have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
  exact (cfn_step_eq_of_kkt hV (cfn_cons_good hV 0) ⟨by linarith, le_of_eq (he.trans rfl),
    fun _ => he.trans rfl⟩).symm

/-! ### Instances: quadratic and CRRA utility -/

omit [Fintype ι] in
/-- **(11.33) in compound form.** The Kuhn–Tucker conditions say exactly
`c = min{x + a/R, θM(cn(R(x − c) + yᵢ))}`. -/
theorem cfn_kkt_iff_min (H : CfnHousehold ι) (cn : ℝ → ℝ) (x c : ℝ) :
    H.KKT cn x c ↔ c = min (x + H.b / H.R) (H.cont cn (x - c)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_or_eq_of_le h1 with hlt | heq
    · rw [← h3 hlt, min_eq_right (h3 hlt ▸ h1)]
    · rw [min_eq_left (heq ▸ h2), heq]
  · intro h
    refine ⟨(le_of_eq h).trans (min_le_left _ _), (le_of_eq h).trans (min_le_right _ _),
      fun hlt => ?_⟩
    rcases min_choice (x + H.b / H.R) (H.cont cn (x - c)) with hm | hm
    · rw [hm] at h; linarith
    · rw [hm] at h; exact h

/-- The household with quadratic utility and `βR = 1` (the book's case): `M` is the expectation
and `θ = 1`. -/
def cfn_quadratic (w y : ι → ℝ) (R b d ymax : ℝ) : CfnHousehold ι :=
  { M := fun z => ∑ i, w i * z i, θ := 1, R := R, b := b, d := d, y := y, ymax := ymax, w := w }

/-- **AKMM, (11.33), p. 305.** For quadratic utility with `βR = 1` the Kuhn–Tucker conditions are
`cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}` (with `x = yₜ + aₜ`). -/
theorem cfn_quadratic_kkt_iff (w y : ι → ℝ) (R b d ymax : ℝ) (cn : ℝ → ℝ) (x c : ℝ) :
    (cfn_quadratic w y R b d ymax).KKT cn x c ↔
      c = min (x + b / R) (∑ i, w i * cn (R * (x - c) + y i)) := by
  rw [cfn_kkt_iff_min]
  simp only [cont, cfn_quadratic, one_mul]

/-- The quadratic household satisfies the standing assumptions. -/
theorem cfn_quadratic_valid {w y : ι → ℝ} {R b d ymax : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hR : 1 ≤ R) (hb : 0 ≤ b) (hd : 0 < d) (hy : ∀ i, d + b ≤ y i)
    (hymax : ∀ i, y i ≤ ymax) : (cfn_quadratic w y R b d ymax).Valid :=
  ⟨cfn_isMean_expect hw hw1, one_pos, hR, hb, hd, hy, hymax, hw, hw1⟩

/-- The CRRA household: `M` is the power mean with exponent `−σ`, `θ = (βR)^{−1/σ}`. -/
noncomputable def cfn_crra (β σ : ℝ) (w y : ι → ℝ) (R b d ymax : ℝ) : CfnHousehold ι :=
  { M := LeanEconomics.powerMean w (-σ), θ := (β * R) ^ (-(1 / σ)), R := R, b := b, d := d,
    y := y, ymax := ymax, w := w }

/-- The CRRA household satisfies the standing assumptions. -/
theorem cfn_crra_valid {β σ : ℝ} {w y : ι → ℝ} {R b d ymax : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hR : 1 ≤ R) (hb : 0 ≤ b) (hd : 0 < d)
    (hy : ∀ i, d + b ≤ y i) (hymax : ∀ i, y i ≤ ymax) :
    (cfn_crra β σ w y R b d ymax).Valid :=
  ⟨cfn_isMean_powerMean hw hw1 (neg_neg_of_pos hσ),
    Real.rpow_pos_of_pos (mul_pos hβ (by linarith)) _, hR, hb, hd, hy, hymax, hw, hw1⟩

/-- **The CRRA Euler inequality.** For positive `c` and next-period consumptions `zᵢ`,
`c ≤ (βR)^{−1/σ}M₋σ(z)` iff `u′(c) = c^{−σ} ≥ βR Σᵢ wᵢ zᵢ^{−σ} = βR E u′(z)`, with equality iff
equality. -/
theorem cfn_crra_euler_iff {β σ R : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 0 < R) {w z : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hz : ∀ i, 0 < z i) {c : ℝ} (hc : 0 < c) :
    (c ≤ (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z ↔
      β * R * ∑ i, w i * z i ^ (-σ) ≤ c ^ (-σ)) ∧
    (c = (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z ↔
      c ^ (-σ) = β * R * ∑ i, w i * z i ^ (-σ)) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hP := LeanEconomics.powerMean_pos (p := -σ) hw hw1 hz
  have hK : 0 < (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z :=
    mul_pos (Real.rpow_pos_of_pos hβR _) hP
  have hpow : ((β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z) ^ (-σ)
      = β * R * ∑ i, w i * z i ^ (-σ) := by
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hβR _).le hP.le, ← Real.rpow_mul hβR.le,
      LeanEconomics.powerMean_rpow (neg_ne_zero.2 hσ.ne') hw hw1 hz]
    congr 1
    rw [show -(1 / σ) * -σ = 1 by field_simp, Real.rpow_one]
  constructor
  · rw [← hpow, Real.rpow_le_rpow_iff_of_neg hK hc (neg_neg_of_pos hσ)]
  · rw [← hpow]
    constructor
    · intro h; rw [← h]
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := Real.rpow_lt_rpow_of_neg hc hlt (neg_neg_of_pos hσ); linarith
      · have := Real.rpow_lt_rpow_of_neg hK hlt (neg_neg_of_pos hσ); linarith

/-- For CRRA, `θ = (βR)^{−1/σ} ≥ 1` iff `βR ≤ 1` (the discount rate is at least the interest
rate). -/
theorem cfn_crra_theta_ge_one_iff {β σ R : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 0 < R) :
    1 ≤ (β * R) ^ (-(1 / σ)) ↔ β * R ≤ 1 := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hs : -(1 / σ) < 0 := neg_neg_of_pos (by positivity)
  constructor
  · intro h
    by_contra hgt
    push Not at hgt
    have := Real.rpow_lt_one_of_one_lt_of_neg hgt hs
    linarith
  · intro h
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hβR h hs.le

/-- **For CRRA the limiting MPC is (11.16)**: `1 − 1/(θR) = 1 − R⁻¹(βR)^{1/σ}` (`cd_mpc`). -/
theorem cfn_crra_kappa_limit {β σ : ℝ} {w y : ι → ℝ} {R b d ymax : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    1 - 1 / ((cfn_crra β σ w y R b d ymax).θ * (cfn_crra β σ w y R b d ymax).R) =
      cd_mpc β R σ := by
  simp only [cfn_crra, cd_mpc]
  have hβR : 0 < β * R := mul_pos hβ hR
  rw [Real.rpow_neg hβR.le, one_div, mul_inv, inv_inv]
  ring

/-- **A concrete instance**: the quadratic household with income `1` or `3` with equal
probability, `R = 1.02`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions, so every
theorem above applies to it. -/
theorem cfn_example_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The buffer-stock target (Figure 11.4)

AKMM, §11.3.4, "Buffer-stock saving", pp. 310–311, Figure 11.4: when the discount rate exceeds
the interest rate there is a target level `x*` of cash in hand; above it the household
decumulates and below it it accumulates, and `x*` is stable — "wealth converges back toward
`x*`".

The model is the household of `ConsumptionShape` (i.i.d. income, borrowing limit `a`, finite
horizon, CRRA or quadratic utility), with expected next-period cash in hand
`E[xₜ₊₁ | xₜ = x] = R(x − cₙ(x)) + ȳ`, `ȳ = Σᵢ wᵢyᵢ` (`CfnHousehold.nextCash`).

* **The target** (`bsk_target`): if `θ ≥ 1` — for CRRA `βR ≤ 1`, the book's `ρ > r`
  (`cfn_crra_theta_ge_one_iff`) — and `d + a < ȳ`, then at every horizon `n` there is a unique
  `x* > d` with `E[x′ | x*] = x*`, `E[x′ | x] > x` for `d ≤ x < x*` and `E[x′ | x] < x` for
  `x > x*`. The proof: the expected change `R(x − c(x)) + ȳ − x` is convex because the consumption
  function is concave (`cfn_cons_concave`), positive at `d`, and eventually negative because the
  slope of consumption never falls below `κₙ` and `R(1 − κₙ) < 1` (`cfn_R_one_sub_kappa_lt`);
  a convex function with these properties crosses zero once (`bsk_convex_crossing`).
* **Stability** (`bsk_target_stable`): the expected-cash map is nondecreasing, so from below it
  moves up without overshooting `x*` and from above it moves down without undershooting, and its
  iterates converge to `x*` from every starting point (`bsk_iterate_tendsto`).

Departures: the book's model has permanent income shocks (cash in hand normalised by permanent
income) and a probability of zero income that makes the natural borrowing limit zero; here income
is i.i.d. with a positive floor and the borrowing limit `a ≥ 0` is imposed (with `a = 0` the
book's limit). With permanent shocks and growth the condition for a target is Carroll's growth
impatience condition rather than `ρ > r`; that model is not formalised. The target is that of the
`n`-period-ahead consumption function, at every `n`, because the horizon is finite. "Stable" is
read as convergence of the expected-cash dynamics `x ↦ E[x′ | x]`; the stochastic process itself
is not studied, and Figure 11.4's vertical axis (expected consumption growth) is not formalised.
-/

namespace AKMM.Consumption

open Filter Topology CfnHousehold

/-! ### Convex crossing and monotone iteration -/

/-- **A convex function that is positive at `d` and eventually negative crosses zero exactly
once**, from above. -/
theorem bsk_convex_crossing {e : ℝ → ℝ} {d : ℝ} (hconv : ConvexOn ℝ (Set.Ici d) e)
    (hcont : ContinuousOn e (Set.Ici d)) (hd : 0 < e d) {X : ℝ} (hX : ∀ x, X ≤ x → e x < 0) :
    ∃ xs, d < xs ∧ e xs = 0 ∧ (∀ x, d ≤ x → x < xs → 0 < e x) ∧ (∀ x, xs < x → e x < 0) := by
  -- once `e` is nonpositive it stays negative
  have hkey : ∀ z w, d ≤ z → z < w → e z ≤ 0 → e w < 0 := by
    intro z w hz hzw hez
    by_contra hge
    push Not at hge
    set v := max X (w + 1) with hv
    have hwv : w < v := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs := hconv.slope_mono_adjacent (Set.mem_Ici.2 hz) (Set.mem_Ici.2 (by linarith)) hzw hwv
    have h1 : 0 ≤ (e w - e z) / (w - z) := div_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ e v - e w := by
      have := le_trans h1 hs
      rwa [le_div_iff₀ (by linarith), zero_mul] at this
    have := hX v (le_max_left _ _)
    linarith
  set X₀ := max X (d + 1) with hX₀
  have hdX : d ≤ X₀ := le_trans (by linarith) (le_max_right _ _)
  have hneg := hX X₀ (le_max_left _ _)
  obtain ⟨xs, hxs, hexs⟩ := intermediate_value_Icc' hdX (hcont.mono Set.Icc_subset_Ici_self)
    ⟨hneg.le, hd.le⟩
  have hdxs : d < xs := by
    rcases eq_or_lt_of_le hxs.1 with h | h
    · rw [← h] at hexs; linarith
    · exact h
  refine ⟨xs, hdxs, hexs, fun x hx hxx => ?_, fun x hxx => hkey xs x hdxs.le hxx hexs.le⟩
  by_contra hle
  push Not at hle
  have := hkey x xs hx hxx hle
  linarith

/-- **Monotone dynamics converge to the unique fixed point.** If `g` is continuous and
nondecreasing on `[d, ∞)`, maps it into itself, and has a fixed point `x*` with `g x > x` below
and `g x < x` above, then `gᵏ(x₀) → x*` for every `x₀ ≥ d`. -/
theorem bsk_iterate_tendsto {g : ℝ → ℝ} {d xs : ℝ} (hcont : ContinuousOn g (Set.Ici d))
    (hmono : MonotoneOn g (Set.Ici d)) (hmaps : ∀ x, d ≤ x → d ≤ g x) (hxs : d ≤ xs)
    (hfix : g xs = xs) (hbelow : ∀ x, d ≤ x → x < xs → x < g x)
    (habove : ∀ x, xs < x → g x < x) {x₀ : ℝ} (hx₀ : d ≤ x₀) :
    Tendsto (fun k => g^[k] x₀) atTop (𝓝 xs) := by
  set u : ℕ → ℝ := fun k => g^[k] x₀ with hu
  have hsucc : ∀ k, u (k + 1) = g (u k) := fun k => by
    simp only [hu, Function.iterate_succ_apply']
  have hmem : ∀ k, d ≤ u k := by
    intro k
    induction k with
    | zero => simpa [hu] using hx₀
    | succ k ih => rw [hsucc]; exact hmaps _ ih
  -- a limit point in `[d, ∞)` of the orbit is a fixed point
  have hfixL : ∀ L, d ≤ L → Tendsto u atTop (𝓝 L) → g L = L := by
    intro L hL hT
    have h1 : Tendsto (fun k => u (k + 1)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => g (u k)) atTop (𝓝 (g L)) :=
      (hcont L hL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hT, Eventually.of_forall hmem⟩)
    have h3 : (fun k => u (k + 1)) = fun k => g (u k) := funext hsucc
    rw [h3] at h1
    exact tendsto_nhds_unique h2 h1
  rcases le_total x₀ xs with hlo | hhi
  · have hle : ∀ k, u k ≤ xs := by
      intro k
      induction k with
      | zero => simpa [hu] using hlo
      | succ k ih => rw [hsucc, ← hfix]; exact hmono (hmem k) hxs ih
    have hstep : ∀ k, u k ≤ u (k + 1) := by
      intro k
      rw [hsucc]
      rcases eq_or_lt_of_le (hle k) with h | h
      · rw [h, hfix]
      · exact (hbelow _ (hmem k) h).le
    have hbdd : BddAbove (Set.range u) := ⟨xs, by rintro _ ⟨k, rfl⟩; exact hle k⟩
    have hT := tendsto_atTop_ciSup (monotone_nat_of_le_succ hstep) hbdd
    have hLle : (⨆ k, u k) ≤ xs := ciSup_le hle
    have hLge : d ≤ ⨆ k, u k := le_trans (hmem 0) (le_ciSup hbdd 0)
    have hgL := hfixL _ hLge hT
    rcases eq_or_lt_of_le hLle with h | h
    · rwa [h] at hT
    · have := hbelow _ hLge h; linarith
  · have hge : ∀ k, xs ≤ u k := by
      intro k
      induction k with
      | zero => simpa [hu] using hhi
      | succ k ih => rw [hsucc, ← hfix]; exact hmono hxs (hmem k) ih
    have hstep : ∀ k, u (k + 1) ≤ u k := by
      intro k
      rw [hsucc]
      rcases eq_or_lt_of_le (hge k) with h | h
      · rw [← h, hfix]
      · exact (habove _ h).le
    have hbdd : BddBelow (Set.range u) := ⟨xs, by rintro _ ⟨k, rfl⟩; exact hge k⟩
    have hT := tendsto_atTop_ciInf (antitone_nat_of_succ_le hstep) hbdd
    have hLge : xs ≤ ⨅ k, u k := le_ciInf hge
    have hgL := hfixL _ (le_trans hxs hLge) hT
    rcases eq_or_lt_of_le hLge with h | h
    · rwa [← h] at hT
    · have := habove _ h; linarith

/-! ### The target in the household problem -/

/-- **Expected next-period cash in hand**, `E[xₜ₊₁ | xₜ = x] = R(x − cₙ(x)) + ȳ`. -/
noncomputable def CfnHousehold.nextCash {ι : Type*} [Fintype ι] (H : CfnHousehold ι) (n : ℕ)
    (x : ℝ) : ℝ := H.R * (x - H.cons n x) + ∑ i, H.w i * H.y i

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- Expected cash in hand is nondecreasing in current cash in hand. -/
theorem bsk_nextCash_mono (hV : H.Valid) (n : ℕ) : MonotoneOn (H.nextCash n) (Set.Ici H.d) := by
  intro x hx x' hx' hxx
  have h := (cfn_cons_good hV n).2.2.1 x x' hx hxx
  simp only [CfnHousehold.nextCash]
  have hR : 0 ≤ H.R := by linarith [hV.2.2.1]
  nlinarith

/-- Expected cash in hand is continuous on `[d, ∞)`. -/
theorem bsk_nextCash_continuousOn (hV : H.Valid) (n : ℕ) :
    ContinuousOn (H.nextCash n) (Set.Ici H.d) := by
  have hc := cfn_good_continuousOn (cfn_cons_good hV n)
  exact ((continuousOn_const.mul (continuousOn_id.sub hc)).add continuousOn_const)

/-- Expected cash in hand is at least `ȳ − a`. -/
theorem bsk_nextCash_ge (hV : H.Valid) (n : ℕ) (x : ℝ) :
    ∑ i, H.w i * H.y i - H.b ≤ H.nextCash n x := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have h := cfn_cons_le hV n x
  have h2 : -(H.b / H.R) ≤ x - H.cons n x := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hR0.le
  rw [mul_neg, mul_div_cancel₀ _ hR0.ne'] at h3
  simp only [CfnHousehold.nextCash]
  linarith

/-- **Figure 11.4: the buffer-stock target.** If `θ ≥ 1` (for CRRA `βR ≤ 1`: the discount rate is
at least the interest rate) and mean income exceeds `d + a`, then at every horizon there is a
target `x* > d`: expected cash in hand equals `x*` there, exceeds current cash in hand below `x*`
and falls short of it above `x*`; the target is the only fixed point. -/
theorem bsk_target (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (hy : H.d + H.b < ∑ i, H.w i * H.y i)
    (n : ℕ) : ∃ xs, H.d < xs ∧ H.nextCash n xs = xs ∧
      (∀ x, H.d ≤ x → x < xs → x < H.nextCash n x) ∧ (∀ x, xs < x → H.nextCash n x < x) ∧
      (∀ x, H.d ≤ x → H.nextCash n x = x → x = xs) := by
  have hg := cfn_cons_good hV n
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  set ybar := ∑ i, H.w i * H.y i with hybar
  set e : ℝ → ℝ := fun x => H.nextCash n x - x with he
  -- convexity of the expected change, from concavity of consumption
  have hconv : ConvexOn ℝ (Set.Ici H.d) e := by
    refine ⟨convex_Ici _, fun x hx x' hx' μ ν hμ hν hμν => ?_⟩
    have hc := hg.2.2.2.1.2 hx hx' hμ hν hμν
    simp only [smul_eq_mul] at hc ⊢
    simp only [he, CfnHousehold.nextCash]
    have := mul_le_mul_of_nonneg_left hc hR0.le
    have hyb : ybar = μ * ybar + ν * ybar := by linear_combination -ybar * hμν
    nlinarith
  have hcont : ContinuousOn e (Set.Ici H.d) :=
    (bsk_nextCash_continuousOn hV n).sub continuousOn_id
  have hd : 0 < e H.d := by
    have := bsk_nextCash_ge hV n H.d
    simp only [he]
    linarith
  -- eventually negative: the slope of consumption is at least `κₙ` and `R(1 − κₙ) < 1`
  set α := 1 - H.R * (1 - H.kappa n) with hα
  have hα0 : 0 < α := by have := cfn_R_one_sub_kappa_lt hV hθ1 n; linarith
  have hX : ∀ x, max H.d (|ybar| / α + 1) ≤ x → e x < 0 := by
    intro x hx
    have hxd : H.d ≤ x := le_trans (le_max_left _ _) hx
    have hlow := (hg.2.2.2.2 x hxd).1
    have h1 : |ybar| / α + 1 ≤ x := le_trans (le_max_right _ _) hx
    have h2 : |ybar| + α ≤ α * x := by
      have := mul_le_mul_of_nonneg_left h1 hα0.le
      rw [mul_add, mul_div_cancel₀ _ hα0.ne', mul_one] at this
      linarith
    simp only [he, CfnHousehold.nextCash]
    have := mul_le_mul_of_nonneg_left hlow hR0.le
    nlinarith [le_abs_self ybar]
  obtain ⟨xs, hdxs, hexs, hlo, hhi⟩ := bsk_convex_crossing hconv hcont hd hX
  refine ⟨xs, hdxs, by simp only [he] at hexs; linarith, fun x hx hxx => ?_, fun x hxx => ?_,
    fun x hx hfx => ?_⟩
  · have := hlo x hx hxx; simp only [he] at this; linarith
  · have := hhi x hxx; simp only [he] at this; linarith
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hlo x hx h; simp only [he] at this; linarith
    · have := hhi x h; simp only [he] at this; linarith

/-- **Figure 11.4: the target is stable.** Under the assumptions of `bsk_target`, from below the
target expected cash in hand rises without overshooting, from above it falls without
undershooting, and the expected-cash dynamics converge to the target from every `x₀ ≥ d`. -/
theorem bsk_target_stable (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (hy : H.d + H.b < ∑ i, H.w i * H.y i)
    (n : ℕ) : ∃ xs, H.d < xs ∧ H.nextCash n xs = xs ∧
      (∀ x, H.d ≤ x → x < xs → x < H.nextCash n x ∧ H.nextCash n x ≤ xs) ∧
      (∀ x, xs < x → xs ≤ H.nextCash n x ∧ H.nextCash n x < x) ∧
      ∀ x₀, H.d ≤ x₀ → Tendsto (fun k => (H.nextCash n)^[k] x₀) atTop (𝓝 xs) := by
  obtain ⟨xs, hdxs, hfix, hlo, hhi, -⟩ := bsk_target hV hθ1 hy n
  have hmono := bsk_nextCash_mono hV n
  have hmaps : ∀ x, H.d ≤ x → H.d ≤ H.nextCash n x := fun x _ => by
    have := bsk_nextCash_ge hV n x; linarith
  refine ⟨xs, hdxs, hfix, fun x hx hxx => ⟨hlo x hx hxx, ?_⟩, fun x hxx => ⟨?_, hhi x hxx⟩,
    fun x₀ hx₀ => bsk_iterate_tendsto (bsk_nextCash_continuousOn hV n) hmono hmaps hdxs.le hfix
      hlo hhi hx₀⟩
  · rw [← hfix]; exact hmono hx (Set.mem_Ici.2 hdxs.le) hxx.le
  · rw [← hfix]
    exact hmono (Set.mem_Ici.2 hdxs.le) (Set.mem_Ici.2 (by linarith : H.d ≤ x)) hxx.le

/-- **A concrete instance**: the quadratic household of `cfn_example_valid` with `βR = 1` has
mean income `2 > d + a = 1`, so it has a stable buffer-stock target at every horizon. -/
theorem bsk_example_target (n : ℕ) :
    ∃ xs, (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2) 3).d
      < xs ∧ (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2)
        3).nextCash n xs = xs := by
  obtain ⟨xs, h1, h2, -⟩ := bsk_target cfn_example_valid (by simp [cfn_quadratic])
    (by simp [cfn_quadratic, Fin.sum_univ_two]) n
  exact ⟨xs, h1, h2⟩

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# More government debt moves the Bewley economy towards full insurance (Figure 11.7)

AKMM, §11.4.1, "Assets in positive supply", p. 319, Figure 11.7: in Bewley's endowment economy
the government supplies `B` bonds and the equilibrium rate solves `A(r*) = B`; "as `B` increases,
the economy moves closer to the full insurance outcome", i.e. `r*` rises towards the
complete-markets rate `r^{CM} = 1/β − 1`, where the household problem has no precautionary
motive (`hg_rate_below_cm`).

As in `Huggett`, the aggregate asset demand `A` is a function given as a hypothesis, continuous on
`[−1, r^{CM})` with `A(−1) = −a` (`hg_A_at_minus_one`) and `A(r) → ∞` as `r ↑ r^{CM}`; for
every `B > −a` an equilibrium exists (`hg_existence`).

* **Every selection of equilibrium rates tends to `r^{CM}` as `B → ∞`** (`bwy_rate_tendsto_cm`):
  `A` is bounded on each `[−1, r̄]`, `r̄ < r^{CM}`, so a large enough `B` can only be met above
  `r̄`. **Full insurance is not reached at any finite `B`**: `r* < r^{CM}` always
  (`bwy_eqm_exists_below_cm`).
* **The lowest equilibrium rate rises with `B`** (`bwy_lower_eqm`): below every equilibrium rate
  at `B′` there is an equilibrium rate at each `B ∈ (−a, B′)`. If `A` is strictly increasing (as
  drawn) the equilibrium rate is strictly increasing in `B` (`bwy_rate_strictMono`).
* **Taxes.** With `T = rB` the household's income depends on `B`, so in fact `A = A(r, B)`; the
  figure holds `A` fixed. The convergence survives if `A(·, B)` is bounded above on each
  `[−1, r̄]` uniformly in `B` (`bwy_rate_tendsto_cm_dep`, of which `bwy_rate_tendsto_cm` is the
  fixed-`A` case).
* A concrete instance, `A(r) = −1 + (1 + r)/(1 − r)` with `β = 1/2`, `a = 1`: the equilibrium
  rate is `B/(B + 2)`, increasing to `r^{CM} = 1` (`bwy_example`).

Departures: "closer to the full insurance outcome" is read as the equilibrium rate approaching the
complete-markets rate (the content of the figure); consumption dispersion is not formalised.
-/

namespace AKMM.Consumption

open Filter Topology

/-- **Figure 11.7, with `A` depending on `B`.** If `A(·, B)` is bounded above on each
`[−1, r̄]`, `r̄ < r^{CM}`, uniformly in `B`, then any equilibrium rates `r(B) ∈ (−1, r^{CM})`
with `A(r(B), B) = B` (for all large `B`) tend to `r^{CM}` from below as `B → ∞`. -/
theorem bwy_rate_tendsto_cm_dep {A : ℝ → ℝ → ℝ} {rcm : ℝ}
    (hbound : ∀ rbar < rcm, ∃ K, ∀ B r, r ∈ Set.Icc (-1) rbar → A r B ≤ K) {req : ℝ → ℝ}
    (heq : ∀ᶠ B in atTop, req B ∈ Set.Ioo (-1) rcm ∧ A (req B) B = B) :
    Tendsto req atTop (𝓝[<] rcm) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩,
    heq.mono fun B hB => hB.1.2⟩
  · obtain ⟨K, hK⟩ := hbound a ha
    filter_upwards [heq, eventually_gt_atTop K] with B hB hBK
    by_contra hle
    push Not at hle
    have := hK B (req B) ⟨hB.1.1.le, hle⟩
    rw [hB.2] at this
    linarith
  · exact heq.mono fun B hB => lt_trans hB.1.2 ha

/-- **Figure 11.7: more debt moves the economy towards full insurance.** If `A` is continuous on
`[−1, r^{CM})`, any equilibrium rates `r(B) ∈ (−1, r^{CM})` with `A(r(B)) = B` tend to
`r^{CM} = 1/β − 1` from below as `B → ∞`. -/
theorem bwy_rate_tendsto_cm {A : ℝ → ℝ} {β : ℝ} (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    {req : ℝ → ℝ} (heq : ∀ᶠ B in atTop, req B ∈ Set.Ioo (-1) (1 / β - 1) ∧ A (req B) = B) :
    Tendsto req atTop (𝓝[<] (1 / β - 1)) := by
  refine bwy_rate_tendsto_cm_dep (A := fun r _ => A r) (fun rbar hrbar => ?_) heq
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := rbar)).bddAbove_image
    (hA.mono fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hrbar⟩)
  exact ⟨K, fun _ r hr => hK ⟨r, hr, rfl⟩⟩

/-- **AKMM, p. 319: for every bond supply `B > −a` there is an equilibrium, and its rate is below
`r^{CM}`**: full insurance is not reached at any finite `B` (`hg_existence`). -/
theorem bwy_eqm_exists_below_cm {A : ℝ → ℝ} {β φ : ℝ} (hβ : 0 < β)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / β - 1)) atTop) (hA1 : A (-1) = -φ) {B : ℝ} (hB : -φ < B) :
    ∃ r ∈ Set.Ioo (-1) (1 / β - 1), A r = B ∧ r < 1 / β - 1 := by
  obtain ⟨r, hr, hAr⟩ := hg_existence hβ hA hlim hA1 hB
  exact ⟨r, hr, hAr, hr.2⟩

/-- **The lowest equilibrium rate rises with `B`.** If `r′` is an equilibrium rate for supply
`B′` and `−a < B < B′`, there is an equilibrium rate `r < r′` for `B`. -/
theorem bwy_lower_eqm {A : ℝ → ℝ} {rcm φ : ℝ} (hA : ContinuousOn A (Set.Ico (-1) rcm))
    (hA1 : A (-1) = -φ) {B B' r' : ℝ} (hB : -φ < B) (hBB : B < B')
    (hr' : r' ∈ Set.Ioo (-1) rcm) (hAr' : A r' = B') : ∃ r ∈ Set.Ioo (-1) r', A r = B := by
  have hsub : Set.Icc (-1) r' ⊆ Set.Ico (-1) rcm := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hr'.2⟩
  obtain ⟨r, hr, hAr⟩ := intermediate_value_Icc hr'.1.le (hA.mono hsub)
    (show B ∈ Set.Icc (A (-1)) (A r') from ⟨by rw [hA1]; exact hB.le, by rw [hAr']; exact hBB.le⟩)
  refine ⟨r, ⟨?_, ?_⟩, hAr⟩
  · rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h, hA1] at hAr; linarith
    · exact h
  · rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h, hAr'] at hAr; linarith
    · exact h

/-- **With `A` strictly increasing (as drawn in Figure 11.7) the equilibrium rate is strictly
increasing in `B`.** -/
theorem bwy_rate_strictMono {A : ℝ → ℝ} {S : Set ℝ} (hA : StrictMonoOn A S) {B B' r r' : ℝ}
    (hr : r ∈ S) (hr' : r' ∈ S) (hAr : A r = B) (hAr' : A r' = B') (hBB : B < B') : r < r' := by
  by_contra hle
  push Not at hle
  have := hA.monotoneOn hr' hr hle
  linarith

/-- **A concrete instance.** With `β = 1/2` (`r^{CM} = 1`), `a = 1` and
`A(r) = −1 + (1 + r)/(1 − r)`, `A` is continuous on `[−1, 1)`, `A(−1) = −1`, `A → ∞` at `1`; the
equilibrium rate at `B > −1` is `B/(B + 2)`, and it tends to `r^{CM}` as `B → ∞`. -/
theorem bwy_example :
    ContinuousOn (fun r : ℝ => -1 + (1 + r) / (1 - r)) (Set.Ico (-1) (1 / (1 / 2) - 1)) ∧
    (fun r : ℝ => -1 + (1 + r) / (1 - r)) (-1) = -1 ∧
    Tendsto (fun r : ℝ => -1 + (1 + r) / (1 - r)) (𝓝[<] (1 / (1 / 2) - 1)) atTop ∧
    (∀ B : ℝ, -1 < B → B / (B + 2) ∈ Set.Ioo (-1) (1 / (1 / 2) - 1) ∧
      -1 + (1 + B / (B + 2)) / (1 - B / (B + 2)) = B) ∧
    Tendsto (fun B : ℝ => B / (B + 2)) atTop (𝓝[<] (1 / (1 / 2) - 1)) := by
  have hcm : (1 : ℝ) / (1 / 2) - 1 = 1 := by norm_num
  have hcont : ContinuousOn (fun r : ℝ => -1 + (1 + r) / (1 - r)) (Set.Ico (-1) 1) := by
    refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) fun r hr => ?_)
    have := hr.2; linarith
  have heqm : ∀ B : ℝ, -1 < B → B / (B + 2) ∈ Set.Ioo (-1) 1 ∧
      -1 + (1 + B / (B + 2)) / (1 - B / (B + 2)) = B := by
    intro B hB
    have h2 : 0 < B + 2 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ h2]; linarith
    · rw [div_lt_one h2]; linarith
    · have h3 : 1 - B / (B + 2) = 2 / (B + 2) := by field_simp; ring
      rw [h3]
      field_simp
      ring
  rw [hcm]
  refine ⟨hcont, by norm_num, ?_, heqm, ?_⟩
  · -- `(1 + r)/(1 − r) → ∞` as `r ↑ 1`
    have h1 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.2 (Set.mem_Iio.1 hr)
    have h2 : Tendsto (fun r : ℝ => (1 - r)⁻¹) (𝓝[<] 1) atTop :=
      tendsto_inv_nhdsGT_zero.comp h1
    have h3 : Tendsto (fun r : ℝ => 1 + r) (𝓝[<] 1) (𝓝 2) := by
      have : Tendsto (fun r : ℝ => 1 + r) (𝓝 1) (𝓝 (1 + 1)) :=
        (continuous_const.add continuous_id).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun r : ℝ => (1 + r) * (1 - r)⁻¹) (𝓝[<] 1) atTop :=
      Tendsto.pos_mul_atTop (by norm_num) h3 h2
    exact tendsto_atTop_add_const_left _ (-1) (h4.congr fun r => (div_eq_mul_inv _ _).symm)
  · have h := bwy_rate_tendsto_cm (A := fun r : ℝ => -1 + (1 + r) / (1 - r)) (β := 1 / 2)
      (req := fun B : ℝ => B / (B + 2)) (by rw [hcm]; exact hcont)
      (by
        rw [hcm]
        filter_upwards [eventually_gt_atTop (-1 : ℝ)] with B hB using heqm B hB)
    rwa [hcm] at h

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tighter borrowing limit raises the MPC with more periods left (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: when the credit limit tightens from `a₁` to `a₂ < a₁`, "their
marginal propensity to consume (the slope of the consumption function) increases". In the
finite-horizon household of `ConsumptionShape` (`CfnHousehold`) this is the statement that on every
interval of cash in hand the tight household's consumption rises at least as much as the loose
household's, i.e. that the fall in consumption `cₙ(x) − c̃ₙ(x)` is nonincreasing in `x`. The module
`ConsumptionShape` proved it one period before the end (`cfn_tight_mpc_last`). Here:

* **The sharp shift bound** (any certainty equivalent `M`): with `(a₁ − a₂)/R` more cash the tight
  household consumes at least as much as the loose one, `cₙ(x) ≤ c̃ₙ(x + (a₁ − a₂)/R)`
  (`ctl_shift_sharp`), so a tighter limit lowers consumption by at most `(a₁ − a₂)/R`, the amount
  it removes from the budget, at every horizon (`ctl_gap_le`).
* **The induction step** (quadratic utility: `M` the expectation, any `θ`, any `R ≥ 1`). Call
  `(cₙ, c̃ₙ)` *`τ`-dominated* if the tight function shifted left by `τ` rises at least as much as
  the loose one on every interval (`ctl_IncrDom`). If the period-`n` functions are
  `(a₁ − a₂)/R`-dominated, the tight MPC is at least the loose MPC on every interval with `n + 1`
  periods left (`ctl_mpc_step`); and `(a₁ − a₂)`-domination at `n` gives `(a₁ − a₂)/R`-domination
  at `n + 1` (`ctl_incr_step`). The proof follows Carroll–Holm–Kimball's backward induction, with
  the counterconcavity comparison of marginal values replaced by this shifted comparison of
  consumption functions, which is what the Euler equation passes back.
* **Two periods before the end**, for every `R ≥ 1` and `θ > 0` (`ctl_tight_mpc_two`).
* **Every horizon when `r = 0`** (`R = 1`; `ctl_tight_mpc_R_one`), with a concrete instance
  (`ctl_example_R_one_valid`, `ctl_example_mpc`).

What is left: for quadratic utility with `R > 1` and three or more periods left, the domination
step consumes `(a₁ − a₂)`-domination and returns only `(a₁ − a₂)/R`-domination, so the induction
does not close and the comparison is proved at horizons `1` and `2` only. For CRRA (the power mean)
the step's use of the linearity of the expectation (`ctl_cont_incr`) is not available, so beyond
`cfn_tight_mpc_last` nothing is proved. Carroll–Holm–Kimball's concavification theorem adds
constraints one date at a time in reverse chronological order; tightening the same limit at every
date is not of that form, so it does not settle these cases either. The quadratic case at every
horizon is closed in `TighterLimitAllHorizons` (`cta_tight_mpc`), with a level bound added to the
invariant.
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- `(f, g)` is `τ`-dominated on `[d, ∞)`: on every interval `[z, z']` the function `g` shifted
left by `τ` rises at least as much as `f`. With `f` the loose and `g` the tight consumption function
and `τ = 0` this is the MPC comparison of AKMM p. 306. -/
def ctl_IncrDom (f g : ℝ → ℝ) (d τ : ℝ) : Prop :=
  ∀ z z', d ≤ z → z ≤ z' → f z' - f z ≤ g (z' + τ) - g (z + τ)

/-- For a concave function, the rise over `[z, z']` shrinks as the interval is moved to the right:
`g(z' + b) − g(z + b) ≤ g(z' + a) − g(z + a)` for `0 ≤ a ≤ b`. -/
theorem ctl_concave_incr {g : ℝ → ℝ} {d z z' a b : ℝ} (hg : ConcaveOn ℝ (Set.Ici d) g)
    (hz : d ≤ z) (hzz : z ≤ z') (ha : 0 ≤ a) (hab : a ≤ b) :
    g (z' + b) - g (z + b) ≤ g (z' + a) - g (z + a) := by
  set D := (b - a) + (z' - z) with hD
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ D) with h0 | hpos
  · have h1 : b = a := by linarith
    have h2 : z' = z := by linarith
    rw [h1, h2]
  set lam := (z' - z) / D with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hpos.le
  have hl1 : lam ≤ 1 := by rw [div_le_one hpos]; linarith
  have hp : z + a ∈ Set.Ici d := Set.mem_Ici.2 (by linarith)
  have hq : z' + b ∈ Set.Ici d := Set.mem_Ici.2 (by linarith)
  have hc1 := hg.2 hp hq hl0 (by linarith : 0 ≤ 1 - lam) (by ring)
  have hc2 := hg.2 hp hq (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
  simp only [smul_eq_mul] at hc1 hc2
  have e1 : lam * (z + a) + (1 - lam) * (z' + b) = z + b := by
    have : lam * D = z' - z := by rw [hlam]; field_simp
    linear_combination -this
  have e2 : (1 - lam) * (z + a) + lam * (z' + b) = z' + a := by
    have : lam * D = z' - z := by rw [hlam]; field_simp
    linear_combination this
  rw [e1] at hc1
  rw [e2] at hc2
  linarith

/-- Domination at a larger shift gives domination at every smaller nonnegative shift, for a concave
tight function. -/
theorem ctl_incrDom_le {f g : ℝ → ℝ} {d τ a : ℝ} (hg : ConcaveOn ℝ (Set.Ici d) g)
    (hP : ctl_IncrDom f g d τ) (ha : 0 ≤ a) (haτ : a ≤ τ) {z z' : ℝ} (hz : d ≤ z)
    (hzz : z ≤ z') : f z' - f z ≤ g (z' + a) - g (z + a) :=
  le_trans (hP z z' hz hzz) (ctl_concave_incr hg hz hzz ha haτ)

omit [Fintype ι] in
/-- With the expectation as certainty equivalent, the Euler right-hand side passes comparisons of
increments through: if every state's increment of `g` dominates that of `f`, so does the Euler
right-hand side's. -/
theorem ctl_cont_incr (H : CfnHousehold ι) [Fintype ι] (hM : ∀ z, H.M z = ∑ i, H.w i * z i)
    (hθ : 0 ≤ H.θ) (hw : ∀ i, 0 ≤ H.w i) {f g : ℝ → ℝ} {s s' σ σ' : ℝ}
    (h : ∀ i, f (H.R * s' + H.y i) - f (H.R * s + H.y i) ≤
      g (H.R * σ' + H.y i) - g (H.R * σ + H.y i)) :
    H.cont f s' - H.cont f s ≤ H.cont g σ' - H.cont g σ := by
  simp only [cont, hM]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hθ
  rw [← mul_sub, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (h i) (hw i)

/-- **The sharp shift bound.** With `(a₁ − a₂)/R` more cash in hand the tight household consumes
at least as much as the loose one, at every horizon (any certainty equivalent). -/
theorem ctl_shift_sharp (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : H.cons n x ≤ (H.tighten b₂).cons n (x + (H.b - b₂) / H.R) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have he0 : 0 ≤ (H.b - b₂) / H.R := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + (H.b - b₂) / H.R = H.b / H.R := by field_simp; ring
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    set e := (H.b - b₂) / H.R with he
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + e)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) (x + e)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    have hint : c₂ < x + e + b₂ / H.R := by linarith [hK.1]
    have he₂ : c₂ = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + e - c₂) := hK₂.2.2 hint
    have hge : H.cont (H.cons n) (x - c) ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n)
        (x + e - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
        (cfn_arg_ge hV hs i)) fun i => ?_) hV.2.1.le
      have hsi := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x - c) + H.y i + e ≤ H.R * (x + e - c₂) + H.y i := by nlinarith
      refine le_trans (ih hsi) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    linarith [hK.2.1]

/-- **AKMM, p. 306: a tighter limit lowers consumption by at most `(a₁ − a₂)/R`**, the amount it
removes from the current budget, at every horizon: `0 ≤ cₙ(x) − c̃ₙ(x) ≤ (a₁ − a₂)/R`. -/
theorem ctl_gap_le (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : 0 ≤ H.cons n x - (H.tighten b₂).cons n x ∧
      H.cons n x - (H.tighten b₂).cons n x ≤ (H.b - b₂) / H.R := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have he0 : 0 ≤ (H.b - b₂) / H.R := div_nonneg (by linarith) hR0.le
  have h1 := cfn_tight_le hV hb₂ hb n hx
  have h2 := ctl_shift_sharp hV hb₂ hb n hx
  have h3 := (cfn_cons_good hV₂ n).2.2.1 x (x + (H.b - b₂) / H.R) hx (by linarith)
  constructor <;> linarith

omit [Fintype ι] in
/-- In the last period both households eat their cash: the pair `(c₀, c̃₀)` is `τ`-dominated for
every `τ`. -/
theorem ctl_incrDom_zero {b₂ τ : ℝ} :
    ctl_IncrDom (H.cons 0) ((H.tighten b₂).cons 0) H.d τ := by
  intro z z' _ _
  simp only [cons]
  linarith

/-- **The MPC induction step** (quadratic utility). If with `n` periods left the pair of
consumption functions is `(a₁ − a₂)/R`-dominated, then with `n + 1` periods left the tight MPC is at
least the loose MPC on every interval of cash in hand. -/
theorem ctl_mpc_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d ((H.b - b₂) / H.R)) {x x' : ℝ}
    (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons (n + 1) x' - H.cons (n + 1) x ≤
      (H.tighten b₂).cons (n + 1) x' - (H.tighten b₂).cons (n + 1) x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have heR : e / H.R ≤ e := div_le_self he0 hR1
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n x
  have hT' := cfn_cons_kkt hV₂ n x'
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) x
  set k' := (H.tighten b₂).cons (n + 1) x'
  have hk'le : k' ≤ x' + b₂ / H.R := hT'.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x'`, hence at `x`
    have hb' := cfn_binding_initial hV₂ n hxx hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  -- the tight household is unconstrained at `x'`, hence so is the loose one
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' - k') := hT'.2.2 hint'
  have hc'lt : c' < x' + H.b / H.R := by
    by_contra hge
    push Not at hge
    have := cfn_tight_binds hV hb₂ hb n x' (le_antisymm hK'.1 hge)
    linarith
  have hec' : c' = H.cont (H.cons n) (x' - c') := hK'.2.2 hc'lt
  have hs' : -(H.b / H.R) ≤ x' - c' := cfn_save_ge hK'.1
  have hkc' : k' ≤ c' := cfn_tight_le hV hb₂ hb (n + 1) hx'
  -- the gap at `x'` is at most `e/R`
  have hγ' : c' - k' ≤ e / H.R := by
    by_contra hgt
    push Not at hgt
    have hRγ : e ≤ H.R * (c' - k') := by
      have := mul_lt_mul_of_pos_left hgt hR0
      rw [mul_div_cancel₀ _ hR0.ne'] at this; linarith
    have hcmp : H.cont (H.cons n) (x' - c') ≤
        (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' - k') := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => hg.1 _ (cfn_arg_ge hV hs' i))
        fun i => ?_) hV.2.1.le
      have hz := cfn_arg_ge hV hs' i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x' - c') + H.y i + e ≤ H.R * (x' - k') + H.y i := by nlinarith
      exact le_trans (ctl_shift_sharp hV hb₂ hb n hz) (hg₂.2.1
        (Set.mem_Ici.2 (by rw [htd]; linarith)) (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    have : 0 ≤ e / H.R := div_nonneg he0 hR0.le
    linarith
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`, hence so is the tight one: the gap is `e`
    have hk := cfn_tight_binds hV hb₂ hb n x hcb
    have : c - k = e := by
      have hk' : k = x + b₂ / H.R := hk
      rw [hcb, hk']; linarith
    linarith
  -- the loose household is unconstrained at `x`
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  have hkc : k ≤ c := cfn_tight_le hV hb₂ hb (n + 1) hx
  set γ' := c' - k' with hγ'def
  have hγ'0 : 0 ≤ γ' := by linarith
  have hm := cfn_cont_mono hV₂ hg₂ hsk (by linarith : x - k ≤ (x - c) + γ')
  have hRγ0 : 0 ≤ H.R * γ' := mul_nonneg hR0.le hγ'0
  have hRγe : H.R * γ' ≤ e := by
    have := mul_le_mul_of_nonneg_left hγ' hR0.le
    rwa [mul_div_cancel₀ _ hR0.ne'] at this
  have hdiff := ctl_cont_incr (H.tighten b₂) hM hV.2.1.le hV.2.2.2.2.2.2.2.1
    (f := H.cons n) (g := (H.tighten b₂).cons n) (s := x - c) (s' := x' - c')
    (σ := (x - c) + γ') (σ' := (x' - c') + γ') (fun i => by
      have hz := cfn_arg_ge hV hs i
      have h1 := ctl_incrDom_le hg₂.2.2.2.1 hP hRγ0 hRγe hz
        (by nlinarith : H.R * (x - c) + H.y i ≤ H.R * (x' - c') + H.y i)
      have e1 : H.R * (x' - c' + γ') + H.y i = H.R * (x' - c') + H.y i + H.R * γ' := by ring
      have e2 : H.R * (x - c + γ') + H.y i = H.R * (x - c) + H.y i + H.R * γ' := by ring
      change H.cons n _ - H.cons n _ ≤ (H.tighten b₂).cons n _ - (H.tighten b₂).cons n _
      rw [show (H.tighten b₂).R = H.R from rfl, show (H.tighten b₂).y = H.y from rfl, e1, e2]
      exact h1)
  have hx'k' : x' - c' + γ' = x' - k' := by rw [hγ'def]; ring
  rw [hx'k'] at hdiff
  rw [hHT] at hec hec'
  linarith

/-- **The domination step** (quadratic utility): `(a₁ − a₂)`-domination with `n` periods left gives
`(a₁ − a₂)/R`-domination with `n + 1` periods left. -/
theorem ctl_incr_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂)) :
    ctl_IncrDom (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d ((H.b - b₂) / H.R) := by
  intro x x' hx hxx
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have hRe : H.R * e = H.b - b₂ := by rw [he]; field_simp
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hxe : H.d ≤ x + e := by linarith
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n (x + e)
  have hT' := cfn_cons_kkt hV₂ n (x' + e)
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  have hsh := ctl_shift_sharp hV hb₂ hb (n + 1) hx
  have hsh' := ctl_shift_sharp hV hb₂ hb (n + 1) hx'
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) (x + e)
  set k' := (H.tighten b₂).cons (n + 1) (x' + e)
  have hk'le : k' ≤ x' + e + b₂ / H.R := hT'.1
  have hkle1 : k ≤ x + e + b₂ / H.R := hT.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x' + e`, hence at `x + e`
    have hb' := cfn_binding_initial hV₂ n (by linarith : x + e ≤ x' + e) hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' + e - k') := hT'.2.2 hint'
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`: then `c̃(x + e) = c(x)`
    have : k = c := by linarith
    linarith
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hc'le : c' ≤ H.cont (H.cons n) (x' - c') := hK'.2.1
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + e - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x + e - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  -- the saving gap `t` lies in `[0, e]`
  set t := (x + e - k) - (x - c) with ht
  have hkc : k ≤ c + e := by
    have h1 := cfn_tight_le hV hb₂ hb (n + 1) hxe
    have h2 := (cfn_cons_good hV (n + 1)).2.2.1 x (x + e) hx (by linarith)
    linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hte : t ≤ e := by rw [ht]; linarith
  have hRt0 : 0 ≤ H.R * t := mul_nonneg hR0.le ht0
  have hRtΔ : H.R * t ≤ H.b - b₂ := by
    rw [← hRe]; exact mul_le_mul_of_nonneg_left hte hR0.le
  have hm := cfn_cont_mono hV₂ hg₂ (by linarith : -(b₂ / H.R) ≤ (x' - c') + t)
    (by linarith : (x' - c') + t ≤ x' + e - k')
  have hdiff := ctl_cont_incr (H.tighten b₂) hM hV.2.1.le hV.2.2.2.2.2.2.2.1
    (f := H.cons n) (g := (H.tighten b₂).cons n) (s := x - c) (s' := x' - c')
    (σ := (x - c) + t) (σ' := (x' - c') + t) (fun i => by
      have hz := cfn_arg_ge hV hs i
      have h1 := ctl_incrDom_le hg₂.2.2.2.1 hP hRt0 hRtΔ hz
        (by nlinarith : H.R * (x - c) + H.y i ≤ H.R * (x' - c') + H.y i)
      have e1 : H.R * (x' - c' + t) + H.y i = H.R * (x' - c') + H.y i + H.R * t := by ring
      have e2 : H.R * (x - c + t) + H.y i = H.R * (x - c) + H.y i + H.R * t := by ring
      change H.cons n _ - H.cons n _ ≤ (H.tighten b₂).cons n _ - (H.tighten b₂).cons n _
      rw [show (H.tighten b₂).R = H.R from rfl, show (H.tighten b₂).y = H.y from rfl, e1, e2]
      exact h1)
  have hxt : x - c + t = x + e - k := by rw [ht]; ring
  rw [hxt] at hdiff
  rw [hHT] at hec hc'le
  linarith

/-- **AKMM, p. 306: a tighter limit raises the MPC two periods before the end** (quadratic utility,
any `R ≥ 1` and `θ > 0`): on every interval of cash in hand the tight household's consumption rises
at least as much as the loose household's. -/
theorem ctl_tight_mpc_two (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons 2 x' - H.cons 2 x ≤ (H.tighten b₂).cons 2 x' - (H.tighten b₂).cons 2 x :=
  ctl_mpc_step hV hb₂ hb hM 1 (ctl_incr_step hV hb₂ hb hM 0 ctl_incrDom_zero) hx hxx

/-- With `R = 1` the pair of consumption functions is `(a₁ − a₂)`-dominated at every horizon
(quadratic utility). -/
theorem ctl_incrDom_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) :
    ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂) := by
  induction n with
  | zero => exact ctl_incrDom_zero
  | succ n ih =>
    have h := ctl_incr_step hV hb₂ hb hM n ih
    rwa [hR, div_one] at h

/-- **AKMM, p. 306: with `r = 0` a tighter limit raises the MPC at every horizon** (quadratic
utility): for every number of periods left, on every interval of cash in hand the tight household's
consumption rises at least as much as the loose household's. -/
theorem ctl_tight_mpc_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  cases n with
  | zero => simp only [cons]; rfl
  | succ n =>
    have h := ctl_incrDom_R_one hV hb₂ hb hM hR n
    have he : (H.b - b₂) / H.R ≤ H.b - b₂ := by rw [hR, div_one]
    have hR0 : 0 < H.R := by rw [hR]; exact one_pos
    refine ctl_mpc_step hV hb₂ hb hM n (fun z z' hz hzz => ?_) hx hxx
    exact ctl_incrDom_le (cfn_cons_good (cfn_tighten_valid hV hb₂ hb) n).2.2.2.1 h
      (div_nonneg (by linarith) hR0.le) he hz hzz

/-- **The fall in consumption shrinks as wealth grows** (quadratic utility, `r = 0`, every horizon):
`cₙ(x) − c̃ₙ(x)` is nonincreasing — the form in which Figure 11.2 shows the MPC comparison. -/
theorem ctl_gap_antitone_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) :
    AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := ctl_tight_mpc_R_one hV hb₂ hb hM hR n hx hxx
  simp only
  linarith

/-- The quadratic household's certainty equivalent is the expectation, so the theorems above
apply to it. -/
theorem ctl_quadratic_linear (w y : ι → ℝ) (R b d ymax : ℝ) (z : ι → ℝ) :
    (cfn_quadratic w y R b d ymax).M z = ∑ i, (cfn_quadratic w y R b d ymax).w i * z i := rfl

/-- **A concrete instance with `r = 0`**: the quadratic household with income `1` or `3` with equal
probability, `R = 1`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions. -/
theorem ctl_example_R_one_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- **The instance**: for that household, removing the borrowing limit's slack entirely (`a₂ = 0`)
raises the MPC on every interval at every horizon. -/
theorem ctl_example_mpc (n : ℕ) {x x' : ℝ} (hx : 1 / 2 ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).cons n x' -
        (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).cons n x ≤
      ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x' -
        ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x :=
  ctl_tight_mpc_R_one ctl_example_R_one_valid le_rfl (by simp only [cfn_quadratic]; norm_num)
    (ctl_quadratic_linear _ _ _ _ _ _) rfl n hx hxx

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tighter borrowing limit raises the MPC at every horizon (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: when the credit limit tightens from `a₁` to `a₂ < a₁`, "their
marginal propensity to consume (the slope of the consumption function) increases". The module
`TighterLimitMPC` proved this for quadratic utility two periods before the end and, when `r = 0`,
at every horizon; its invariant, domination with shift `(a₁ − a₂)`, came back from one step of
backward induction with the smaller shift `(a₁ − a₂)/R`. Here the induction is closed for every
`R ≥ 1` and every horizon, for the expectation as certainty equivalent with factor `θ ≥ 1`, which
contains the book's quadratic case `βR = 1` (`θ = 1`, `cfn_quadratic`).

Write `Δ = a₁ − a₂`, `cₙ` for the loose and `c̃ₙ` for the tight consumption function. The invariant
is a pair:

* **the level bound** `cₙ(x) + (Δ − Δ/R) ≤ c̃ₙ(x + Δ)` (`cta_shift_full`): with `Δ` more cash the
  tight household consumes at least `(1 − 1/R)Δ` more than the loose one, a strengthening of the
  sharp shift bound `ctl_shift_sharp` (it propagates on its own, using `θ ≥ 1`);
* **`Δ`-domination** (`ctl_IncrDom` with shift `Δ`, `cta_incrDom_full`): the tight function shifted
  left by `Δ` rises at least as much as the loose one on every interval.

The level bound caps the gap between the two households' saving at the points the induction
compares at `Δ/R`, so the shift that the Euler equation passes back is at most `R · Δ/R = Δ`, and
`Δ`-domination returns `Δ`-domination (`cta_incr_step`). By concavity of the tight function,
`Δ`-domination gives domination at shift `0`, which is the MPC comparison at every horizon
(`cta_tight_mpc`) and the monotonicity of the fall in consumption (`cta_gap_antitone`), with a
concrete instance at `r = 1` (`cta_example_valid`, `cta_example_mpc`).

The level bound is the integrated form of an identity found from the infinitesimal problem: with
`η = ∂c/∂a` the derivative of consumption in the limit, `η − c′ + (R − 1)/(Rθ)` is nonpositive and
nonincreasing, because unconstrained it is `(1 − c′)·θE[·]` of its next-period value plus the
constant `(R − 1)(1 − θ)/(Rθ)`.

What is left: the factor `θ < 1` (no counterpart in quadratic utility; there the constant above is
positive and `Δ`-domination fails numerically) and CRRA utility beyond one period before the end.
For CRRA no shift domination can serve: one period before the end both households share the same
strictly concave unconstrained consumption function (when the income values differ), so
`τ`-domination already fails there for every `τ > 0`. Nor does a decomposition into single-date
tightenings, taken in reverse chronological order as in Carroll–Holm–Kimball, give the result link
by link: tightening only the next date's limit can lower today's MPC, for every utility
(`cta_link_mpc_counterexample`, a deterministic household `cta_det`).
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- **The level bound** (expectation, `θ ≥ 1`, every horizon): with `Δ = a₁ − a₂` more cash in hand
the tight household consumes at least `(1 − 1/R)Δ` more than the loose one,
`cₙ(x) + (Δ − Δ/R) ≤ c̃ₙ(x + Δ)`. -/
theorem cta_shift_full (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) {x : ℝ} (hx : H.d ≤ x) :
    H.cons n x + ((H.b - b₂) - (H.b - b₂) / H.R) ≤
      (H.tighten b₂).cons n (x + (H.b - b₂)) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  set Δ := H.b - b₂ with hΔ
  set e := Δ / H.R with he
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
  have he0 : 0 ≤ e := div_nonneg hΔ0 hR0.le
  have heΔ : e ≤ Δ := div_le_self hΔ0 hR1
  have hRe : H.R * e = Δ := by rw [he]; field_simp
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he, hΔ]; field_simp; ring
  have hw1 : ∑ i, H.w i = 1 := hV.2.2.2.2.2.2.2.2
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + Δ)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set k := (H.tighten b₂).cons (n + 1) (x + Δ)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    have hint : k < x + Δ + b₂ / H.R := by
      have : c ≤ x + H.b / H.R := hK.1
      linarith
    have hek : k = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := hK₂.2.2 hint
    have hce : c ≤ H.cont (H.cons n) (x - c) := hK.2.1
    -- the tight household saves more than `e` above the loose one
    have hσ : x - c + e < x + Δ - k := by linarith
    have hge : H.θ * ((∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e)) ≤
        (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := by
      simp only [cont, CfnHousehold.tighten, hM]
      refine mul_le_mul_of_nonneg_left ?_ hV.2.1.le
      have hsplit : (∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e) =
          ∑ i, H.w i * (H.cons n (H.R * (x - c) + H.y i) + (Δ - e)) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [hsplit]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hV.2.2.2.2.2.2.2.1 i)
      have hz := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x - c) + H.y i + Δ ≤ H.R * (x + Δ - k) + H.y i := by
        nlinarith [mul_le_mul_of_nonneg_left hσ.le hR0.le]
      exact le_trans (ih hz) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    have hcont : H.cont (H.cons n) (x - c) =
        H.θ * ∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i) := by
      simp only [cont, hM]
    have hθa : Δ - e ≤ H.θ * (Δ - e) := by nlinarith
    rw [hcont] at hce
    have : H.θ * ((∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e)) =
        H.θ * ∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i) + H.θ * (Δ - e) := by ring
    linarith

/-- **The domination step** (expectation, any `θ > 0`): `Δ`-domination with `n` periods left and
the level bound with `n + 1` periods left give `Δ`-domination with `n + 1` periods left. -/
theorem cta_incr_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂))
    (hS : ∀ x, H.d ≤ x → H.cons (n + 1) x + ((H.b - b₂) - (H.b - b₂) / H.R) ≤
      (H.tighten b₂).cons (n + 1) (x + (H.b - b₂))) :
    ctl_IncrDom (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d (H.b - b₂) := by
  intro x x' hx hxx
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set Δ := H.b - b₂ with hΔ
  set e := Δ / H.R with he
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
  have hRe : H.R * e = Δ := by rw [he]; field_simp
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he, hΔ]; field_simp; ring
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hxΔ : H.d ≤ x + Δ := by linarith
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n (x + Δ)
  have hT' := cfn_cons_kkt hV₂ n (x' + Δ)
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  have hS1 := hS x hx
  have hS2 := hS x' hx'
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) (x + Δ)
  set k' := (H.tighten b₂).cons (n + 1) (x' + Δ)
  have hk'le : k' ≤ x' + Δ + b₂ / H.R := hT'.1
  have hkle1 : k ≤ x + Δ + b₂ / H.R := hT.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`: the level bound is attained there
    have : k = c + (Δ - e) := by linarith
    linarith
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x' + Δ`, hence at `x + Δ`
    have hb' := cfn_binding_initial hV₂ n (by linarith : x + Δ ≤ x' + Δ) hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' + Δ - k') := hT'.2.2 hint'
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hc'le : c' ≤ H.cont (H.cons n) (x' - c') := hK'.2.1
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x + Δ - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  -- the saving gap `t` lies in `[0, e]`, by the level bound
  set t := (x + Δ - k) - (x - c) with ht
  have hkc : k ≤ c + Δ := by
    have h1 := cfn_tight_le hV hb₂ hb (n + 1) hxΔ
    have h2 := (cfn_cons_good hV (n + 1)).2.2.1 x (x + Δ) hx (by linarith)
    linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hte : t ≤ e := by rw [ht]; linarith
  have hRt0 : 0 ≤ H.R * t := mul_nonneg hR0.le ht0
  have hRtΔ : H.R * t ≤ Δ := by
    rw [← hRe]; exact mul_le_mul_of_nonneg_left hte hR0.le
  have hm := cfn_cont_mono hV₂ hg₂ (by linarith : -(b₂ / H.R) ≤ (x' - c') + t)
    (by linarith : (x' - c') + t ≤ x' + Δ - k')
  have hdiff := ctl_cont_incr (H.tighten b₂) hM hV.2.1.le hV.2.2.2.2.2.2.2.1
    (f := H.cons n) (g := (H.tighten b₂).cons n) (s := x - c) (s' := x' - c')
    (σ := (x - c) + t) (σ' := (x' - c') + t) (fun i => by
      have hz := cfn_arg_ge hV hs i
      have h1 := ctl_incrDom_le hg₂.2.2.2.1 hP hRt0 hRtΔ hz
        (by nlinarith : H.R * (x - c) + H.y i ≤ H.R * (x' - c') + H.y i)
      have e1 : H.R * (x' - c' + t) + H.y i = H.R * (x' - c') + H.y i + H.R * t := by ring
      have e2 : H.R * (x - c + t) + H.y i = H.R * (x - c) + H.y i + H.R * t := by ring
      change H.cons n _ - H.cons n _ ≤ (H.tighten b₂).cons n _ - (H.tighten b₂).cons n _
      rw [show (H.tighten b₂).R = H.R from rfl, show (H.tighten b₂).y = H.y from rfl, e1, e2]
      exact h1)
  have hxt : x - c + t = x + Δ - k := by rw [ht]; ring
  rw [hxt] at hdiff
  rw [hHT] at hec hc'le
  linarith

/-- **`Δ`-domination at every horizon** (expectation, `θ ≥ 1`, any `R ≥ 1`). -/
theorem cta_incrDom_full (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) :
    ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂) := by
  induction n with
  | zero => exact ctl_incrDom_zero
  | succ n ih =>
    exact cta_incr_step hV hb₂ hb hM n ih fun x hx => cta_shift_full hV hb₂ hb hM hθ (n + 1) hx

/-- **AKMM, p. 306: a tighter limit raises the MPC at every horizon** (the expectation as certainty
equivalent with `θ ≥ 1`, which contains quadratic utility with `βR = 1`; any `r ≥ 0`): for every
number of periods left, on every interval of cash in hand the tight household's consumption rises
at least as much as the loose household's. -/
theorem cta_tight_mpc (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  have h := ctl_incrDom_le (cfn_cons_good (cfn_tighten_valid hV hb₂ hb) n).2.2.2.1
    (cta_incrDom_full hV hb₂ hb hM hθ n) le_rfl (by linarith : (0 : ℝ) ≤ H.b - b₂) hx hxx
  simpa only [add_zero] using h

/-- **The fall in consumption shrinks as wealth grows** (expectation, `θ ≥ 1`, every horizon, any
`r ≥ 0`): `cₙ(x) − c̃ₙ(x)` is nonincreasing — the form in which Figure 11.2 shows the MPC
comparison. -/
theorem cta_gap_antitone (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) :
    AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := cta_tight_mpc hV hb₂ hb hM hθ n hx hxx
  simp only
  linarith

/-- **AKMM, p. 306, the book's case**: for the quadratic household (`βR = 1`, `M` the expectation,
`θ = 1`) a tighter limit raises the MPC on every interval at every horizon, for every `r ≥ 0`. -/
theorem cta_quadratic_tight_mpc {w y : ι → ℝ} {R b d ymax : ℝ}
    (hV : (cfn_quadratic w y R b d ymax).Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ b) (n : ℕ)
    {x x' : ℝ} (hx : d ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic w y R b d ymax).cons n x' - (cfn_quadratic w y R b d ymax).cons n x ≤
      ((cfn_quadratic w y R b d ymax).tighten b₂).cons n x' -
        ((cfn_quadratic w y R b d ymax).tighten b₂).cons n x :=
  cta_tight_mpc hV hb₂ hb (ctl_quadratic_linear _ _ _ _ _ _) le_rfl n hx hxx

/-- **A concrete instance with `r = 1`**: the quadratic household with income `1` or `3` with equal
probability, `R = 2`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions. -/
theorem cta_example_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- **The instance**: for that household (`R = 2`), removing the borrowing limit's slack entirely
(`a₂ = 0`) raises the MPC on every interval at every horizon. -/
theorem cta_example_mpc (n : ℕ) {x x' : ℝ} (hx : 1 / 2 ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).cons n x' -
        (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).cons n x ≤
      ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x' -
        ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x :=
  cta_quadratic_tight_mpc cta_example_valid le_rfl (by norm_num) n hx hxx

/-- The deterministic household of the single-date counterexample: income `3`, `R = 1`, `a = 1`,
`d = 1/2` (one income state, so every certainty equivalent is the identity). -/
noncomputable def cta_det : CfnHousehold (Fin 1) := cfn_quadratic (fun _ => 1) ![3] 1 1 (1 / 2) 3

/-- The deterministic household satisfies the standing assumptions. -/
theorem cta_det_valid : cta_det.Valid :=
  cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => by simp; norm_num) (fun _ => by simp)

/-- Its Euler right-hand side, under the loose or the tight limit: `cn(s + 3)`. -/
theorem cta_det_cont (b₂ : ℝ) (cn : ℝ → ℝ) (s : ℝ) :
    (cta_det.tighten b₂).cont cn s = cn (s + 3) := by
  simp [cont, cta_det, cfn_quadratic, CfnHousehold.tighten]

/-- The tight household's consumption one period before the end satisfies the induction's
properties, as a continuation for the loose household. -/
theorem cta_det_good_tight : ∃ κ h, cta_det.Good κ h ((cta_det.tighten 0).cons 1) :=
  ⟨_, _, cfn_cons_good (cfn_tighten_valid cta_det_valid le_rfl (by norm_num : (0:ℝ) ≤ 1)) 1⟩

/-- The four consumption values: with two periods left the loose household consumes `2` at
`x = 1` and `5/2` at `x = 3/2`; with the limit tightened to `0` at the next date only it consumes
`2` and `9/4`. -/
theorem cta_det_values :
    cta_det.cons 2 1 = 2 ∧ cta_det.cons 2 (3 / 2) = 5 / 2 ∧
      cta_det.step ((cta_det.tighten 0).cons 1) 1 = 2 ∧
      cta_det.step ((cta_det.tighten 0).cons 1) (3 / 2) = 9 / 4 := by
  have hV := cta_det_valid
  have hV₂ := cfn_tighten_valid hV le_rfl (by norm_num : (0:ℝ) ≤ 1)
  have hc0 : cta_det.cont = (cta_det.tighten 1).cont := rfl
  -- one period before the end
  have hL1 : cta_det.cons 1 2 = 5 / 2 := by
    refine cfn_step_eq_of_kkt hV (cfn_cons_good hV 0) ⟨?_, ?_, fun _ => ?_⟩
    · change (5 / 2 : ℝ) ≤ 2 + 1 / 1; norm_num
    · rw [hc0, cta_det_cont]; simp only [cons]; norm_num
    · rw [hc0, cta_det_cont]; simp only [cons]; norm_num
  have hT1 : ∀ z : ℝ, 3 / 2 ≤ z → z ≤ 3 → (cta_det.tighten 0).cons 1 z = z := by
    intro z hz1 hz3
    refine cfn_step_eq_of_kkt hV₂ (cfn_cons_good hV₂ 0) ⟨?_, ?_, fun h => ?_⟩
    · change z ≤ z + 0 / 1; norm_num
    · rw [cta_det_cont]; simp only [cons]; linarith
    · change z < z + 0 / 1 at h; norm_num at h
  obtain ⟨κ, h, hg⟩ := cta_det_good_tight
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine cfn_step_eq_of_kkt hV (cfn_cons_good hV 1) ⟨?_, ?_, fun h => ?_⟩
    · change (2 : ℝ) ≤ 1 + 1 / 1; norm_num
    · rw [hc0, cta_det_cont, show (1 : ℝ) - 2 + 3 = 2 by norm_num, hL1]; norm_num
    · change (2 : ℝ) < 1 + 1 / 1 at h; norm_num at h
  · refine cfn_step_eq_of_kkt hV (cfn_cons_good hV 1) ⟨?_, ?_, fun h => ?_⟩
    · change (5 / 2 : ℝ) ≤ 3 / 2 + 1 / 1; norm_num
    · rw [hc0, cta_det_cont, show (3 / 2 : ℝ) - 5 / 2 + 3 = 2 by norm_num, hL1]
    · change (5 / 2 : ℝ) < 3 / 2 + 1 / 1 at h; norm_num at h
  · refine cfn_step_eq_of_kkt hV hg ⟨?_, ?_, fun h => ?_⟩
    · change (2 : ℝ) ≤ 1 + 1 / 1; norm_num
    · rw [hc0, cta_det_cont, show (1 : ℝ) - 2 + 3 = 2 by norm_num, hT1 2 (by norm_num)
        (by norm_num)]
    · change (2 : ℝ) < 1 + 1 / 1 at h; norm_num at h
  · refine cfn_step_eq_of_kkt hV hg ⟨?_, ?_, fun _ => ?_⟩
    · change (9 / 4 : ℝ) ≤ 3 / 2 + 1 / 1; norm_num
    · rw [hc0, cta_det_cont, show (3 / 2 : ℝ) - 9 / 4 + 3 = 9 / 4 by norm_num,
        hT1 (9 / 4) (by norm_num) (by norm_num)]
    · rw [hc0, cta_det_cont, show (3 / 2 : ℝ) - 9 / 4 + 3 = 9 / 4 by norm_num,
        hT1 (9 / 4) (by norm_num) (by norm_num)]

/-- **Tightening the limit at the next date alone can lower today's MPC** (the single-date step
of a reverse-chronological decomposition fails). In the deterministic household `cta_det`, with
two periods left and today's limit `a = 1`, tightening only the next date's limit to `0` makes
consumption rise by `1/4` on `[1, 3/2]` instead of `1/2`: the household saves more today, so
today's limit stops binding at lower cash (Carroll–Holm–Kimball's hidden kink). With one income
state every certainty equivalent is the identity, so this holds for every utility, CRRA
included. -/
theorem cta_link_mpc_counterexample :
    cta_det.step ((cta_det.tighten 0).cons 1) (3 / 2) - cta_det.step ((cta_det.tighten 0).cons 1) 1
      < cta_det.cons 2 (3 / 2) - cta_det.cons 2 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := cta_det_values
  rw [h1, h2, h3, h4]; norm_num

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tighter limit raises the MPC without income risk, for every utility (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: "their marginal propensity to consume … increases" when the
credit limit tightens from `a₁` to `a₂`. Here income is deterministic (one income state), the
utility is arbitrary — CRRA with any `σ` and any `β`, so any `θ = (βR)^{−1/σ} > 0` — and the claim
is proved at every horizon and every `r ≥ 0` (`ctp_tight_mpc`, `ctp_gap_antitone`; for CRRA
`ctp_crra_tight_mpc`).

With one income state every certainty equivalent is the identity on positive values
(`ctp_cont_eq`), so the Euler condition is `c = θ·cₙ(R(x − c) + y)`. The invariant is a
comparison at equal consumption: *horizontal domination* (`ctp_Hor`). If the tight household
consumes at least as much at `ζ` as the loose one at `z`, and at most as much at `ζ′` as the loose
one at `z′`, then `ζ′ − ζ ≤ z′ − z`. In words: to raise consumption by a given amount the tight
household needs no more extra cash than the loose one. It holds in the last period
(`ctp_hor_zero`). It propagates because with one state the Euler condition maps equal
consumption today to equal consumption tomorrow (`ctp_hor_step`; where the loose household is
constrained, the sharp shift bound `ctl_shift_sharp` closes the case). Concavity of the tight
function then turns it into the MPC comparison (`ctp_mpc_of_hor`).

This route does not need `θ ≥ 1`, and does not extend to income risk: with several states,
equal consumption today does not give equal consumption tomorrow state by state.
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- `(f, g)` is *horizontally dominated* on `[d, ∞)`: if `g` at `ζ` is at least `f` at `z`, and
`g` at `ζ′` is at most `f` at `z′`, then `ζ′ − ζ ≤ z′ − z`. With `f` the loose and `g` the tight
consumption function: raising consumption by a given amount takes the tight household no more
extra cash than the loose one. -/
def ctp_Hor (f g : ℝ → ℝ) (d : ℝ) : Prop :=
  ∀ z z' ζ ζ', d ≤ z → z ≤ z' → d ≤ ζ → d ≤ ζ' → f z ≤ g ζ → g ζ' ≤ f z' → ζ' - ζ ≤ z' - z

/-- With one income state the Euler right-hand side is `θ·cₙ(Rs + y)` wherever `cₙ` is positive
there: every certainty equivalent is the identity on a single positive value. -/
theorem ctp_cont_eq [Unique ι] (hV : H.Valid) {cn : ℝ → ℝ} {s : ℝ}
    (hpos : 0 < cn (H.R * s + H.y default)) :
    H.cont cn s = H.θ * cn (H.R * s + H.y default) := by
  have hfun : (fun i => cn (H.R * s + H.y i)) = fun _ => cn (H.R * s + H.y default) := by
    funext i
    rw [Subsingleton.elim i default]
  simp only [cont, hfun, hV.1.2.1 _ hpos]

omit [Fintype ι] in
/-- In the last period both households eat their cash: horizontal domination holds. -/
theorem ctp_hor_zero {b₂ : ℝ} : ctp_Hor (H.cons 0) ((H.tighten b₂).cons 0) H.d := by
  intro z z' ζ ζ' _ _ _ _ h1 h2
  simp only [cons] at h1 h2
  linarith

/-- A consumption function rises at rate at least `κₙ > 0`: it is strictly increasing. -/
theorem ctp_cons_strict (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x < x') :
    H.cons n x < H.cons n x' := by
  have h := (cfn_cons_slope_bounds hV n hx hxx).1
  have hκ := (cfn_kappa_pos hV n).1
  have hd : 0 < x' - x := by linarith
  rw [le_div_iff₀ hd] at h
  nlinarith

/-- **The horizontal step** (one income state, any utility, any `θ > 0`): horizontal domination
with `n` periods left gives horizontal domination with `n + 1` periods left. -/
theorem ctp_hor_step [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    (hP : ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d) :
    ctp_Hor (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d := by
  intro x₁ x₂ ξ₁ ξ₂ hx₁ hx₁₂ hξ₁ hξ₂ h1 h2
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hθ := hV.2.1
  have hx₂ : H.d ≤ x₂ := le_trans hx₁ hx₁₂
  set e := (H.b - b₂) / H.R with he
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hK₁ := cfn_cons_kkt hV n x₁
  have hK₂ := cfn_cons_kkt hV n x₂
  have hT₁ := cfn_cons_kkt hV₂ n ξ₁
  have hT₂ := cfn_cons_kkt hV₂ n ξ₂
  have hsh := ctl_shift_sharp hV hb₂ hb (n + 1) hx₂
  set c₁ := H.cons (n + 1) x₁
  set c₂ := H.cons (n + 1) x₂
  set k₁ := (H.tighten b₂).cons (n + 1) ξ₁
  set k₂ := (H.tighten b₂).cons (n + 1) ξ₂
  by_contra hlt
  push Not at hlt
  have hss : x₁ - c₁ ≤ x₂ - c₂ := (cfn_kkt_mono hV hg hK₁ hK₂ hx₁₂).2
  have hs₁ : -(H.b / H.R) ≤ x₁ - c₁ := cfn_save_ge hK₁.1
  have hs₂ : -(H.b / H.R) ≤ x₂ - c₂ := cfn_save_ge hK₂.1
  have hσ₁ : -(b₂ / H.R) ≤ ξ₁ - k₁ := cfn_save_ge hT₁.1
  have hσ₂ : -(b₂ / H.R) ≤ ξ₂ - k₂ := cfn_save_ge hT₂.1
  -- the tight household saves strictly more at `ξ₂` than at `ξ₁`, so it is unconstrained there
  have hgap : (x₂ - c₂) - (x₁ - c₁) < (ξ₂ - k₂) - (ξ₁ - k₁) := by linarith
  have hint : k₂ < ξ₂ + b₂ / H.R := by linarith
  have hek₂ : k₂ = (H.tighten b₂).cont ((H.tighten b₂).cons n) (ξ₂ - k₂) := hT₂.2.2 hint
  rcases eq_or_lt_of_le hK₁.1 with hcb | hclt
  · -- the loose household is constrained at `x₁`: then `ξ₁ ≥ x₁ + e` and `ξ₂ ≤ x₂ + e`
    have hξ₁e : x₁ + e ≤ ξ₁ := by
      have : k₁ ≤ ξ₁ + b₂ / H.R := hT₁.1
      linarith
    have hξ₂e : ξ₂ ≤ x₂ + e := by
      by_contra hgt
      push Not at hgt
      have hx₂e : H.d ≤ x₂ + e := by
        have : 0 ≤ e := div_nonneg (by linarith) hR0.le
        linarith
      have := ctp_cons_strict hV₂ (n + 1) hx₂e hgt
      linarith
    linarith
  -- the loose household is unconstrained at `x₁`: compare one period ahead
  have hec₁ : c₁ = H.cont (H.cons n) (x₁ - c₁) := hK₁.2.2 hclt
  have hc₂ : c₂ ≤ H.cont (H.cons n) (x₂ - c₂) := hK₂.2.1
  have hk₁ : k₁ ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (ξ₁ - k₁) := hT₁.2.1
  have hz₁ := cfn_arg_ge hV hs₁ default
  have hz₂ := cfn_arg_ge hV hs₂ default
  have hζ₁ := cfn_arg_ge hV₂ hσ₁ default
  have hζ₂ := cfn_arg_ge hV₂ hσ₂ default
  have htd : (H.tighten b₂).d = H.d := rfl
  have htR : (H.tighten b₂).R = H.R := rfl
  have hty : (H.tighten b₂).y = H.y := rfl
  rw [htd, htR, hty] at hζ₁ hζ₂
  rw [ctp_cont_eq hV (hg.1 _ hz₁)] at hec₁
  rw [ctp_cont_eq hV (hg.1 _ hz₂)] at hc₂
  rw [ctp_cont_eq hV₂ (by rw [htR, hty]; exact hg₂.1 _ hζ₁), htR, hty] at hk₁
  rw [ctp_cont_eq hV₂ (by rw [htR, hty]; exact hg₂.1 _ hζ₂), htR, hty] at hek₂
  have hθ' : (H.tighten b₂).θ = H.θ := rfl
  rw [hθ'] at hk₁ hek₂
  have hl1 : H.cons n (H.R * (x₁ - c₁) + H.y default) ≤
      (H.tighten b₂).cons n (H.R * (ξ₁ - k₁) + H.y default) := by
    have : H.θ * H.cons n (H.R * (x₁ - c₁) + H.y default) ≤
        H.θ * (H.tighten b₂).cons n (H.R * (ξ₁ - k₁) + H.y default) := by linarith
    exact le_of_mul_le_mul_left this hθ
  have hl2 : (H.tighten b₂).cons n (H.R * (ξ₂ - k₂) + H.y default) ≤
      H.cons n (H.R * (x₂ - c₂) + H.y default) := by
    have : H.θ * (H.tighten b₂).cons n (H.R * (ξ₂ - k₂) + H.y default) ≤
        H.θ * H.cons n (H.R * (x₂ - c₂) + H.y default) := by linarith
    exact le_of_mul_le_mul_left this hθ
  have hzz : H.R * (x₁ - c₁) + H.y default ≤ H.R * (x₂ - c₂) + H.y default := by nlinarith
  have hfin := hP _ _ _ _ hz₁ hzz hζ₁ hζ₂ hl1 hl2
  have : H.R * ((ξ₂ - k₂) - (ξ₁ - k₁)) ≤ H.R * ((x₂ - c₂) - (x₁ - c₁)) := by nlinarith
  have := le_of_mul_le_mul_left this hR0
  linarith

/-- **Horizontal domination at every horizon** (one income state, any utility, any `θ > 0`). -/
theorem ctp_hor_all [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) :
    ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d := by
  induction n with
  | zero => exact ctp_hor_zero
  | succ n ih => exact ctp_hor_step hV hb₂ hb n ih

/-- **Horizontal domination gives the MPC comparison**, by concavity of the tight function and the
sharp shift bound. -/
theorem ctp_mpc_of_hor (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    (hP : ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hg₂ := cfn_cons_good hV₂ n
  have hcont : ContinuousOn ((H.tighten b₂).cons n) (Set.Ici H.d) := cfn_good_continuousOn hg₂
  -- the points where the tight household consumes what the loose one does at `x` and `x'`
  have hfind : ∀ u, H.d ≤ u → ∃ ζ, u ≤ ζ ∧ ζ ≤ u + e ∧
      (H.tighten b₂).cons n ζ = H.cons n u := by
    intro u hu
    have hlo := cfn_tight_le hV hb₂ hb n hu
    have hhi := ctl_shift_sharp hV hb₂ hb n hu
    have hc : ContinuousOn ((H.tighten b₂).cons n) (Set.Icc u (u + e)) :=
      hcont.mono fun t ht => Set.mem_Ici.2 (le_trans hu ht.1)
    obtain ⟨ζ, hζ, hζv⟩ := intermediate_value_Icc (by linarith) hc ⟨hlo, hhi⟩
    exact ⟨ζ, hζ.1, hζ.2, hζv⟩
  obtain ⟨ζ, hζ1, -, hζv⟩ := hfind x hx
  obtain ⟨ζ', hζ'1, -, hζ'v⟩ := hfind x' hx'
  have hd := hP x x' ζ ζ' hx hxx (by linarith) (by linarith) hζv.ge hζ'v.le
  have hmono := cfn_cons_good hV n
  have hLx : H.cons n x ≤ H.cons n x' := hmono.2.1 hx hx' hxx
  have hζζ : ζ ≤ ζ' := by
    by_contra hlt
    push Not at hlt
    have := ctp_cons_strict hV₂ n (by linarith : H.d ≤ ζ') hlt
    linarith
  -- concavity: the rise over `[x, x + (ζ' − ζ)]` is at least that over `[ζ, ζ']`
  have hconc := ctl_concave_incr hg₂.2.2.2.1 hx (by linarith : x ≤ x + (ζ' - ζ)) le_rfl
    (by linarith : (0 : ℝ) ≤ ζ - x)
  have e1 : x + (ζ' - ζ) + (ζ - x) = ζ' := by ring
  have e2 : x + (ζ - x) = ζ := by ring
  rw [e1, e2, add_zero, add_zero] at hconc
  have hmon := hg₂.2.1 (Set.mem_Ici.2 (by linarith : H.d ≤ x + (ζ' - ζ))) (Set.mem_Ici.2 hx')
    (by linarith : x + (ζ' - ζ) ≤ x')
  linarith

/-- **AKMM, p. 306, without income risk: a tighter limit raises the MPC at every horizon** (one
income state, any certainty equivalent — every utility, CRRA with any `σ` and `β` included —
any `r ≥ 0`). -/
theorem ctp_tight_mpc [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    {x x' : ℝ} (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x :=
  ctp_mpc_of_hor hV hb₂ hb n (ctp_hor_all hV hb₂ hb n) hx hxx

/-- **The fall in consumption shrinks as wealth grows** without income risk, at every horizon. -/
theorem ctp_gap_antitone [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (n : ℕ) : AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := ctp_tight_mpc hV hb₂ hb n hx hxx
  simp only
  linarith

/-- **AKMM, p. 306, CRRA without income risk**: for the CRRA household with one income value `y`,
any `β > 0`, `σ > 0` and `R ≥ 1` (so any `θ = (βR)^{−1/σ}`, `βR` above or below `1`), a tighter
limit raises the MPC on every interval of cash in hand at every horizon. -/
theorem ctp_crra_tight_mpc {β σ y R b d : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 1 ≤ R) (hb : 0 ≤ b)
    (hd : 0 < d) (hy : d + b ≤ y) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hbb : b₂ ≤ b) (n : ℕ) {x x' : ℝ}
    (hx : d ≤ x) (hxx : x ≤ x') :
    (cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).cons n x' -
        (cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).cons n x ≤
      ((cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).tighten b₂).cons n x' -
        ((cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).tighten b₂).cons n x :=
  ctp_tight_mpc (cfn_crra_valid hβ hσ (fun _ => zero_le_one) (by simp) hR hb hd (fun _ => hy)
    (fun _ => le_rfl)) hb₂ hbb n hx hxx

end AKMM.Consumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tighter limit can lower the MPC two periods before the end (CRRA with income risk)

AKMM, §11.3.4, p. 306: "their marginal propensity to consume (the slope of the consumption
function) increases" when the credit limit tightens from `a₁` to `a₂`. For the household of
`ConsumptionShape` this is proved one period before the end for every certainty equivalent
(`cfn_tight_mpc_last`), at every horizon for the expectation with `θ ≥ 1` (quadratic utility,
`cta_tight_mpc`) and at every horizon without income risk (`ctp_tight_mpc`). Here it is shown
to be **false** two periods before the end for CRRA utility with income risk.

## The counterexample

Log utility (`σ = 1`, so `M` is the harmonic mean), `β = 1/2`, `R = 1` (so `θ = 2`), loose limit
`a₁ = 2`, tight limit `a₂ = 197/100`, income `2003/1000` with probability `1/3000` and
`5003/1000` otherwise, lowest cash in hand `d = 3/1000` (`ctc_H`, `ctc_valid`). Between cash in
hand `43/4` and `279/25` the loose household's consumption two periods before the end rises by
more than the tight household's (`ctc_counterexample`), by about `2.5·10⁻⁷`; so the fall
`c₂ − c̃₂` is not nonincreasing and the MPC comparison fails (`ctc_not_tight_mpc`).

The four consumption levels are not computed in closed form. Each is bracketed by the sign of
its Euler gap at a rational point (`ctc_lt_step`, `ctc_step_lt`): consumption is the unique zero
of the increasing gap `c − θM(cₙ(R(x − c) + yᵢ))`. Next period's consumption in the low state
is the constrained `z + a` (`ctc_step_top`), and in the high state it is in turn bracketed by
the sign of its own Euler gap. All the checks are rational inequalities (`ctc_cons2_gt`,
`ctc_cons2_lt`).

## Why it fails

In the interval the low income state is constrained next period and the high one is not, for
both households. Differentiating the Euler equation in the limit `a` (not formalised) gives
`∂c₂/∂a = π·(∂c₂/∂x)/R²`, where `π` is the share of the constrained states in
`E|V₁″(Rs + yᵢ)|`, the curvature of next period's value function. As cash rises, the weight of
the high state in `π` falls at the rate of the absolute prudence of `V₁′` there. Just past the
kink that prudence includes the low-income risk two periods ahead and exceeds the prudence
`(1 + σ)/c₁` of the constrained state, so `π` rises. For an impatient enough household (here
`θ = 2`) the fall of the MPC is too small to absorb this, and `∂c₂/∂a` rises with cash in hand.
The same example refutes horizontal domination, the invariant without risk (`ctc_not_hor`).
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-! ### Bracketing consumption by the sign of the Euler gap -/

/-- **A lower bracket.** If `c` is below the borrowing limit and below the Euler right-hand side
at saving `x − c`, then the Kuhn–Tucker consumption at `x` exceeds `c`. -/
theorem ctc_lt_step (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (htop : c < x + H.b / H.R) (heu : c < H.cont cn (x - c)) : c < H.step cn x := by
  have hK := cfn_step_kkt hV hg x
  by_contra hle
  push Not at hle
  have he := hK.2.2 (lt_of_le_of_lt hle htop)
  have hs : -(H.b / H.R) ≤ x - c := by linarith
  have hm := cfn_cont_mono hV hg hs (by linarith : x - c ≤ x - H.step cn x)
  linarith

/-- **An upper bracket.** If `c` exceeds the Euler right-hand side at saving `x − c`, then the
Kuhn–Tucker consumption at `x` is below `c`. -/
theorem ctc_step_lt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (heu : H.cont cn (x - c) < c) : H.step cn x < c := by
  have hK := cfn_step_kkt hV hg x
  by_contra hle
  push Not at hle
  have hs : -(H.b / H.R) ≤ x - H.step cn x := cfn_save_ge hK.1
  have hm := cfn_cont_mono hV hg hs (by linarith : x - H.step cn x ≤ x - c)
  linarith [hK.2.1]

/-- **The constrained branch.** If the borrowing limit is below the Euler right-hand side at the
lowest saving `−a/R`, the household is constrained: it consumes `x + a/R`. -/
theorem ctc_step_top (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x : ℝ}
    (htop : x + H.b / H.R ≤ H.cont cn (-(H.b / H.R))) : H.step cn x = x + H.b / H.R := by
  refine cfn_step_eq_of_kkt hV hg ⟨le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
  rwa [show x - (x + H.b / H.R) = -(H.b / H.R) by ring]

/-! ### The household -/

/-- The counterexample household: log utility (`σ = 1`), `β = 1/2`, `R = 1`, borrowing limit
`a₁ = 2`, income `2003/1000` with probability `1/3000` and `5003/1000` otherwise, `d = 3/1000`. -/
noncomputable def ctc_H : CfnHousehold (Fin 2) :=
  cfn_crra (1 / 2) 1 ![1 / 3000, 2999 / 3000] ![2003 / 1000, 5003 / 1000] 1 2 (3 / 1000)
    (5003 / 1000)

/-- The counterexample household satisfies the standing assumptions. -/
theorem ctc_valid : ctc_H.Valid := by
  refine cfn_crra_valid (by norm_num) one_pos (fun i => ?_) ?_ le_rfl (by norm_num) (by norm_num)
    (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- The household with the tighter limit `a₂ ∈ [0, 2]` satisfies the standing assumptions. -/
theorem ctc_tight_valid {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) : (ctc_H.tighten b₂).Valid :=
  cfn_tighten_valid ctc_valid h0 h2

/-- With log utility, `β = 1/2` and `R = 1` the Euler right-hand side is twice the harmonic mean
of next period's consumptions. -/
theorem ctc_cont (b₂ : ℝ) (cn : ℝ → ℝ) (s : ℝ) :
    (ctc_H.tighten b₂).cont cn s =
      2 / (1 / 3000 / cn (s + 2003 / 1000) + 2999 / 3000 / cn (s + 5003 / 1000)) := by
  simp only [cont, CfnHousehold.tighten, ctc_H, cfn_crra, LeanEconomics.powerMean,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_neg_one, one_mul]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- **A lower bound** on consumption two periods before the end, from a lower bound `ℓ` on next
period's consumption in the high state; next period's low state is constrained. -/
theorem ctc_cons2_gt {b₂ x c ℓ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) (hc : c < x + b₂)
    (hcon : x - c + 2003 / 1000 + b₂ ≤
      2 / (1 / 3000 / (-b₂ + 2003 / 1000) + 2999 / 3000 / (-b₂ + 5003 / 1000)))
    (hℓ0 : 0 < ℓ) (hℓ : ℓ < x - c + 5003 / 1000 + b₂)
    (hℓe : ℓ < 2 / (1 / 3000 / (x - c + 5003 / 1000 - ℓ + 2003 / 1000) +
      2999 / 3000 / (x - c + 5003 / 1000 - ℓ + 5003 / 1000)))
    (hm : c < 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / ℓ)) :
    c < (ctc_H.tighten b₂).cons 2 x := by
  have hV := ctc_tight_valid h0 h2
  have hR : (ctc_H.tighten b₂).R = 1 := rfl
  have hb : (ctc_H.tighten b₂).b = b₂ := rfl
  change c < (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 1) x
  refine ctc_lt_step hV (cfn_cons_good hV 1) (by rw [hR, hb, div_one]; exact hc) ?_
  rw [ctc_cont]
  have e0 : (ctc_H.tighten b₂).cons 1 (x - c + 2003 / 1000) = x - c + 2003 / 1000 + b₂ := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ = _
    rw [ctc_step_top hV (cfn_cons_good hV 0), hR, hb, div_one]
    rw [ctc_cont, hR, hb, div_one]
    simpa only [cons] using hcon
  have e1 : ℓ < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := by
    change ℓ < (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _
    refine ctc_lt_step hV (cfn_cons_good hV 0) (by rw [hR, hb, div_one]; exact hℓ) ?_
    rw [ctc_cont]
    simpa only [cons] using hℓe
  rw [e0]
  have hz : 0 < x - c + 2003 / 1000 + b₂ := by linarith
  have ha : 0 < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := lt_trans hℓ0 e1
  have hle : 2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) ≤ 2999 / 3000 / ℓ :=
    div_le_div_of_nonneg_left (by norm_num) hℓ0 e1.le
  have hp : 0 < 1 / 3000 / (x - c + 2003 / 1000 + b₂) +
      2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := by positivity
  calc c < 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / ℓ) := hm
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hp (by linarith)

/-- **An upper bound** on consumption two periods before the end, from an upper bound `η` on next
period's consumption in the high state; next period's low state is constrained. -/
theorem ctc_cons2_lt {b₂ x c η : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) (hc : c ≤ x + b₂)
    (hcon : x - c + 2003 / 1000 + b₂ ≤
      2 / (1 / 3000 / (-b₂ + 2003 / 1000) + 2999 / 3000 / (-b₂ + 5003 / 1000)))
    (hηe : 2 / (1 / 3000 / (x - c + 5003 / 1000 - η + 2003 / 1000) +
      2999 / 3000 / (x - c + 5003 / 1000 - η + 5003 / 1000)) < η)
    (hm : 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η) < c) :
    (ctc_H.tighten b₂).cons 2 x < c := by
  have hV := ctc_tight_valid h0 h2
  have hR : (ctc_H.tighten b₂).R = 1 := rfl
  have hb : (ctc_H.tighten b₂).b = b₂ := rfl
  have hd : (ctc_H.tighten b₂).d = 3 / 1000 := rfl
  change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 1) x < c
  refine ctc_step_lt hV (cfn_cons_good hV 1) ?_
  rw [ctc_cont]
  have e0 : (ctc_H.tighten b₂).cons 1 (x - c + 2003 / 1000) = x - c + 2003 / 1000 + b₂ := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ = _
    rw [ctc_step_top hV (cfn_cons_good hV 0), hR, hb, div_one]
    rw [ctc_cont, hR, hb, div_one]
    simpa only [cons] using hcon
  have e1 : (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) < η := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ < η
    refine ctc_step_lt hV (cfn_cons_good hV 0) ?_
    rw [ctc_cont]
    simpa only [cons] using hηe
  rw [e0]
  have ha : 0 < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) :=
    (cfn_cons_good hV 1).1 _ (by rw [hd]; linarith)
  have hz : 0 < x - c + 2003 / 1000 + b₂ := by linarith
  have hle : 2999 / 3000 / η ≤ 2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) :=
    div_le_div_of_nonneg_left (by norm_num) ha e1.le
  have hp : 0 < 1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η := by
    have : 0 < η := lt_trans ha e1
    positivity
  calc 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) +
        2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000))
      ≤ 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η) :=
        div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
    _ < c := hm

/-! ### The counterexample -/

/-- The loose household is the tightening to its own limit. -/
theorem ctc_tighten_self : ctc_H.tighten 2 = ctc_H := rfl

/-- **Counterexample to AKMM, p. 306, two periods before the end** (CRRA utility with income
risk). Between cash in hand `43/4` and `279/25` the tight household (`a₂ = 197/100`) raises its
consumption by less than the loose one (`a₁ = 2`). -/
theorem ctc_counterexample :
    (ctc_H.tighten (197 / 100)).cons 2 (279 / 25) - (ctc_H.tighten (197 / 100)).cons 2 (43 / 4)
      < ctc_H.cons 2 (279 / 25) - ctc_H.cons 2 (43 / 4) := by
  have hL1 : ctc_H.cons 2 (43 / 4) < 295299987 / 25000000 := by
    rw [← ctc_tighten_self]
    refine ctc_cons2_lt (η := 590798579987 / 100000000000) (by norm_num) le_rfl ?_ ?_ ?_ ?_ <;>
      norm_num
  have hL2 : 3016612953 / 250000000 < ctc_H.cons 2 (279 / 25) := by
    rw [← ctc_tighten_self]
    refine ctc_cons2_gt (ℓ := 603513439297 / 100000000000) (by norm_num) le_rfl ?_ ?_ ?_ ?_ ?_
      ?_ <;> norm_num
  have hT1 : 1181196963 / 100000000 < (ctc_H.tighten (197 / 100)).cons 2 (43 / 4) := by
    refine ctc_cons2_gt (ℓ := 36925072523 / 6250000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
      ?_ ?_ <;> norm_num
  have hT2 : (ctc_H.tighten (197 / 100)).cons 2 (279 / 25) < 1206642171 / 100000000 := by
    refine ctc_cons2_lt (η := 603515765609 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
      ?_ <;> norm_num
  linarith

/-- **Correction to AKMM, p. 306.** For CRRA utility with income risk a tighter borrowing limit
does not raise the MPC on every interval two periods before the end: the comparison that holds
one period before the end for every certainty equivalent (`cfn_tight_mpc_last`) fails at
`n = 2` for the household `ctc_H` (log utility, `β = 1/2`, `R = 1`) and `a₂ = 197/100`. -/
theorem ctc_not_tight_mpc :
    ¬ ∀ x x', ctc_H.d ≤ x → x ≤ x' →
      ctc_H.cons 2 x' - ctc_H.cons 2 x ≤
        (ctc_H.tighten (197 / 100)).cons 2 x' - (ctc_H.tighten (197 / 100)).cons 2 x := by
  intro h
  have := h (43 / 4) (279 / 25) (by change (3 : ℝ) / 1000 ≤ 43 / 4; norm_num) (by norm_num)
  linarith [ctc_counterexample]

/-- **Horizontal domination fails with income risk.** The invariant that proves the comparison
without risk (`ctp_Hor`, `ctp_tight_mpc`) does not hold two periods before the end for `ctc_H`:
with it, `ctp_mpc_of_hor` would give the comparison that `ctc_not_tight_mpc` refutes. -/
theorem ctc_not_hor :
    ¬ ctp_Hor (ctc_H.cons 2) ((ctc_H.tighten (197 / 100)).cons 2) ctc_H.d := by
  intro hP
  exact ctc_not_tight_mpc fun x x' hx hxx =>
    ctp_mpc_of_hor ctc_valid (by norm_num) (by change (197 : ℝ) / 100 ≤ 2; norm_num) 2 hP hx hxx

end AKMM.Consumption

set_option linter.style.longLine false
#print axioms AKMM.Consumption.eq_11_1
#print axioms AKMM.Consumption.footnote_1
#print axioms AKMM.Consumption.eq_11_3
#print axioms AKMM.Consumption.rs_crra_invert
#print axioms AKMM.Consumption.rs_crra_ratio
#print axioms AKMM.Consumption.eq_11_4
#print axioms AKMM.Consumption.rs_crra_share_eqm
#print axioms AKMM.Consumption.rs_lhs_strictAnti
#print axioms AKMM.Consumption.eq_11_5
#print axioms AKMM.Consumption.rs_less_risk_averse_absorbs
#print axioms AKMM.Consumption.eq_11_11
#print axioms AKMM.Consumption.eq_11_10
#print axioms AKMM.Consumption.cd_budget_iter
#print axioms AKMM.Consumption.cd_summable_pv_cons
#print axioms AKMM.Consumption.cd_intertemporal_budget
#print axioms AKMM.Consumption.cd_tvc_shift
#print axioms AKMM.Consumption.cd_Plan
#print axioms AKMM.Consumption.cd_Optimal
#print axioms AKMM.Consumption.eq_11_13
#print axioms AKMM.Consumption.eq_11_14
#print axioms AKMM.Consumption.cd_growth
#print axioms AKMM.Consumption.cd_optimal_of_euler
#print axioms AKMM.Consumption.cd_log_optimal
#print axioms AKMM.Consumption.cd_mpc
#print axioms AKMM.Consumption.cd_rule_of_growth
#print axioms AKMM.Consumption.eq_11_15
#print axioms AKMM.Consumption.cd_optimal_eq_11_15
#print axioms AKMM.Consumption.eq_11_16
#print axioms AKMM.Consumption.cd_transitory_eq_wealth
#print axioms AKMM.Consumption.cd_mpc_betaR_one
#print axioms AKMM.Consumption.cd_mpc_approx_rho
#print axioms AKMM.Consumption.cd_mpc_permanent
#print axioms AKMM.Consumption.footnote_15
#print axioms AKMM.Consumption.cd_mpc_log
#print axioms AKMM.Consumption.cd_mpc_log_eq_r_iff
#print axioms AKMM.Consumption.cd_mpc_log_printed_counterexample
#print axioms AKMM.Consumption.pih_detSystem
#print axioms AKMM.Consumption.pih_one_sub_q
#print axioms AKMM.Consumption.pih_annuity_inv
#print axioms AKMM.Consumption.eq_11_18
#print axioms AKMM.Consumption.eq_11_19
#print axioms AKMM.Consumption.pih_budget_iter
#print axioms AKMM.Consumption.pih_budget_condexp
#print axioms AKMM.Consumption.pih_rule
#print axioms AKMM.Consumption.eq_11_20
#print axioms AKMM.Consumption.eq_11_21
#print axioms AKMM.Consumption.pih_certainty_equivalence
#print axioms AKMM.Consumption.pih_wealth
#print axioms AKMM.Consumption.eq_11_22
#print axioms AKMM.Consumption.eq_11_23
#print axioms AKMM.Consumption.eq_11_24
#print axioms AKMM.Consumption.eq_11_26
#print axioms AKMM.Consumption.pih_perm_martingale
#print axioms AKMM.Consumption.pih_news_perm_trans
#print axioms AKMM.Consumption.eq_11_27
#print axioms AKMM.Consumption.eq_11_29
#print axioms AKMM.Consumption.pih_rainy_day
#print axioms AKMM.Consumption.pih_random_walk
#print axioms AKMM.Consumption.eq_11_30
#print axioms AKMM.Consumption.bp_cov_cons_trans
#print axioms AKMM.Consumption.bp_var_cons
#print axioms AKMM.Consumption.bp_cov_cons_income
#print axioms AKMM.Consumption.eq_11_28
#print axioms AKMM.Consumption.bp_cov_stationary
#print axioms AKMM.Consumption.bc_iid_example
#print axioms AKMM.Consumption.bc_iid_hits
#print axioms AKMM.Consumption.eq_11_32
#print axioms AKMM.Consumption.bc_binding_cons
#print axioms AKMM.Consumption.bc_natural_limit_det
#print axioms AKMM.Consumption.bc_natural_limit
#print axioms AKMM.Consumption.bc_natural_limit_cons_nonpos
#print axioms AKMM.Consumption.bc_natural_limit_zero
#print axioms AKMM.Consumption.eq_11_33
#print axioms AKMM.Consumption.bc_slope_one
#print axioms AKMM.Consumption.pr_ConvexOrderOn
#print axioms AKMM.Consumption.pr_convexOrder_mean
#print axioms AKMM.Consumption.pr_two_point_spread
#print axioms AKMM.Consumption.eq_11_34_spread
#print axioms AKMM.Consumption.eq_11_35_unique
#print axioms AKMM.Consumption.pr_root_mono
#print axioms AKMM.Consumption.pr_rhs
#print axioms AKMM.Consumption.pr_spread_raises_saving
#print axioms AKMM.Consumption.pr_two_point_iff
#print axioms AKMM.Consumption.pr_quadratic_no_precaution
#print axioms AKMM.Consumption.pr_ara_deriv
#print axioms AKMM.Consumption.pr_dara_prudent
#print axioms AKMM.Consumption.pr_betaR_inv
#print axioms AKMM.Consumption.eq_11_36_exact
#print axioms AKMM.Consumption.eq_11_38
#print axioms AKMM.Consumption.eq_11_39
#print axioms AKMM.Consumption.eq_11_40
#print axioms AKMM.Consumption.pr_kappa
#print axioms AKMM.Consumption.pr_tolerance_deriv
#print axioms AKMM.Consumption.pr_hara_kappa_const
#print axioms AKMM.Consumption.pr_kappa_quadratic
#print axioms AKMM.Consumption.pr_kappa_cara
#print axioms AKMM.Consumption.pr_kappa_crra
#print axioms AKMM.Consumption.pr_hara_neg_derivs
#print axioms AKMM.Consumption.pr_hara_kappa_neg
#print axioms AKMM.Consumption.cr_deriv
#print axioms AKMM.Consumption.cr_second_deriv
#print axioms AKMM.Consumption.cr_second_deriv_nonneg_iff
#print axioms AKMM.Consumption.cr_convex_of_rel_prudence
#print axioms AKMM.Consumption.cr_spread_raises_saving
#print axioms AKMM.Consumption.cr_log_return_risk_neutral
#print axioms AKMM.Consumption.cr_return_spread_instance
#print axioms AKMM.Consumption.cr_printed_counterexample
#print axioms AKMM.Consumption.cs_lognormal_euler
#print axioms AKMM.Consumption.eq_11_41
#print axioms AKMM.Consumption.cs_zeldes_euler
#print axioms AKMM.Consumption.eq_11_41_printed_false
#print axioms AKMM.Consumption.eq_11_43
#print axioms AKMM.Consumption.bw_cash_gap
#print axioms AKMM.Consumption.bw_bounded_of_ratio
#print axioms AKMM.Consumption.bw_bounded_wealth
#print axioms AKMM.Consumption.bw_crra_rra
#print axioms AKMM.Consumption.bw_bounded_wealth_crra
#print axioms AKMM.Consumption.bw_crra_ara_tendsto
#print axioms AKMM.Consumption.bw_dara_not_ara_zero
#print axioms AKMM.Consumption.hg_IsStationaryEqm
#print axioms AKMM.Consumption.hg_map_fst_eq
#print axioms AKMM.Consumption.hg_integrable_assets
#print axioms AKMM.Consumption.hg_mean_assets_eq_mean_policy
#print axioms AKMM.Consumption.hg_mean_consumption
#print axioms AKMM.Consumption.hg_goods_clear_zero_supply
#print axioms AKMM.Consumption.hg_eqm_iff_miao
#print axioms AKMM.Consumption.eq_11_50
#print axioms AKMM.Consumption.hg_cycle_markov
#print axioms AKMM.Consumption.hg_cycle_integrable
#print axioms AKMM.Consumption.hg_cycle_eqm
#print axioms AKMM.Consumption.hg_cycle_huggett
#print axioms AKMM.Consumption.hg_policy_at_minus_one
#print axioms AKMM.Consumption.hg_A_at_minus_one
#print axioms AKMM.Consumption.hg_EaSet_at_minus_one
#print axioms AKMM.Consumption.hg_existence
#print axioms AKMM.Consumption.hg_existence_eqm
#print axioms AKMM.Consumption.hg_rate_below_cm
#print axioms AKMM.Consumption.hg_unique_of_strictMono
#print axioms AKMM.Consumption.hg_saving_ratio_crra
#print axioms AKMM.Consumption.hg_saving_increasing_iff
#print axioms AKMM.Consumption.hg_A_continuous
#print axioms AKMM.Consumption.hg_A_continuousOn
#print axioms AKMM.Consumption.footnote_27
#print axioms AKMM.Consumption.footnote_27_printed_false
#print axioms AKMM.Consumption.ai_capital_demand_props
#print axioms AKMM.Consumption.ai_Kd_tendsto_zero
#print axioms AKMM.Consumption.ai_existence
#print axioms AKMM.Consumption.ai_precautionary_wealth
#print axioms AKMM.Consumption.ai_mpc_representative
#print axioms AKMM.Consumption.cfn_IsMean
#print axioms AKMM.Consumption.cfn_mean_ge
#print axioms AKMM.Consumption.cfn_mean_le
#print axioms AKMM.Consumption.cfn_isMean_expect
#print axioms AKMM.Consumption.cfn_isMean_powerMean
#print axioms AKMM.Consumption.CfnHousehold
#print axioms AKMM.Consumption.CfnHousehold.mk
#print axioms AKMM.Consumption.CfnHousehold.M
#print axioms AKMM.Consumption.CfnHousehold.θ
#print axioms AKMM.Consumption.CfnHousehold.R
#print axioms AKMM.Consumption.CfnHousehold.b
#print axioms AKMM.Consumption.CfnHousehold.d
#print axioms AKMM.Consumption.CfnHousehold.y
#print axioms AKMM.Consumption.CfnHousehold.ymax
#print axioms AKMM.Consumption.CfnHousehold.w
#print axioms AKMM.Consumption.CfnHousehold.Valid
#print axioms AKMM.Consumption.CfnHousehold.cont
#print axioms AKMM.Consumption.CfnHousehold.KKT
#print axioms AKMM.Consumption.CfnHousehold.step
#print axioms AKMM.Consumption.CfnHousehold.cons
#print axioms AKMM.Consumption.CfnHousehold.kappa
#print axioms AKMM.Consumption.CfnHousehold.hw
#print axioms AKMM.Consumption.CfnHousehold.Good
#print axioms AKMM.Consumption.cfn_arg_ge
#print axioms AKMM.Consumption.cfn_good_continuousOn
#print axioms AKMM.Consumption.cfn_cont_mono
#print axioms AKMM.Consumption.cfn_cont_concave
#print axioms AKMM.Consumption.cfn_cont_ge
#print axioms AKMM.Consumption.cfn_cont_le
#print axioms AKMM.Consumption.cfn_save_ge
#print axioms AKMM.Consumption.cfn_kkt_exists
#print axioms AKMM.Consumption.cfn_kkt_unique
#print axioms AKMM.Consumption.cfn_step_kkt
#print axioms AKMM.Consumption.cfn_step_eq_of_kkt
#print axioms AKMM.Consumption.cfn_kkt_mono
#print axioms AKMM.Consumption.cfn_step_good
#print axioms AKMM.Consumption.cfn_kappa_pos
#print axioms AKMM.Consumption.cfn_cons_good
#print axioms AKMM.Consumption.cfn_cons_kkt
#print axioms AKMM.Consumption.cfn_cons_le
#print axioms AKMM.Consumption.cfn_cons_concave
#print axioms AKMM.Consumption.cfn_slope_ge_of_concave
#print axioms AKMM.Consumption.cfn_slope_le_eventually
#print axioms AKMM.Consumption.cfn_cons_slope_bounds
#print axioms AKMM.Consumption.cfn_slope_tendsto
#print axioms AKMM.Consumption.cfn_binding_initial
#print axioms AKMM.Consumption.cfn_kappa_eq
#print axioms AKMM.Consumption.cfn_kappa_tendsto
#print axioms AKMM.Consumption.cfn_kappa_tendsto_r
#print axioms AKMM.Consumption.cfn_fig_11_2_slope
#print axioms AKMM.Consumption.cfn_kappa_gt
#print axioms AKMM.Consumption.cfn_R_one_sub_kappa_lt
#print axioms AKMM.Consumption.CfnHousehold.tighten
#print axioms AKMM.Consumption.cfn_tighten_valid
#print axioms AKMM.Consumption.cfn_tight_le
#print axioms AKMM.Consumption.cfn_tight_shift
#print axioms AKMM.Consumption.cfn_tight_binds
#print axioms AKMM.Consumption.cfn_tight_eventually_eq
#print axioms AKMM.Consumption.cfn_tight_mpc_last
#print axioms AKMM.Consumption.cfn_tight_eq_unconstrained_last
#print axioms AKMM.Consumption.cfn_kkt_iff_min
#print axioms AKMM.Consumption.cfn_quadratic
#print axioms AKMM.Consumption.cfn_quadratic_kkt_iff
#print axioms AKMM.Consumption.cfn_quadratic_valid
#print axioms AKMM.Consumption.cfn_crra
#print axioms AKMM.Consumption.cfn_crra_valid
#print axioms AKMM.Consumption.cfn_crra_euler_iff
#print axioms AKMM.Consumption.cfn_crra_theta_ge_one_iff
#print axioms AKMM.Consumption.cfn_crra_kappa_limit
#print axioms AKMM.Consumption.cfn_example_valid
#print axioms AKMM.Consumption.bsk_convex_crossing
#print axioms AKMM.Consumption.bsk_iterate_tendsto
#print axioms AKMM.Consumption.CfnHousehold.nextCash
#print axioms AKMM.Consumption.bsk_nextCash_mono
#print axioms AKMM.Consumption.bsk_nextCash_continuousOn
#print axioms AKMM.Consumption.bsk_nextCash_ge
#print axioms AKMM.Consumption.bsk_target
#print axioms AKMM.Consumption.bsk_target_stable
#print axioms AKMM.Consumption.bsk_example_target
#print axioms AKMM.Consumption.bwy_rate_tendsto_cm_dep
#print axioms AKMM.Consumption.bwy_rate_tendsto_cm
#print axioms AKMM.Consumption.bwy_eqm_exists_below_cm
#print axioms AKMM.Consumption.bwy_lower_eqm
#print axioms AKMM.Consumption.bwy_rate_strictMono
#print axioms AKMM.Consumption.bwy_example
#print axioms AKMM.Consumption.ctl_IncrDom
#print axioms AKMM.Consumption.ctl_concave_incr
#print axioms AKMM.Consumption.ctl_incrDom_le
#print axioms AKMM.Consumption.ctl_cont_incr
#print axioms AKMM.Consumption.ctl_shift_sharp
#print axioms AKMM.Consumption.ctl_gap_le
#print axioms AKMM.Consumption.ctl_incrDom_zero
#print axioms AKMM.Consumption.ctl_mpc_step
#print axioms AKMM.Consumption.ctl_incr_step
#print axioms AKMM.Consumption.ctl_tight_mpc_two
#print axioms AKMM.Consumption.ctl_incrDom_R_one
#print axioms AKMM.Consumption.ctl_tight_mpc_R_one
#print axioms AKMM.Consumption.ctl_gap_antitone_R_one
#print axioms AKMM.Consumption.ctl_quadratic_linear
#print axioms AKMM.Consumption.ctl_example_R_one_valid
#print axioms AKMM.Consumption.ctl_example_mpc
#print axioms AKMM.Consumption.cta_shift_full
#print axioms AKMM.Consumption.cta_incr_step
#print axioms AKMM.Consumption.cta_incrDom_full
#print axioms AKMM.Consumption.cta_tight_mpc
#print axioms AKMM.Consumption.cta_gap_antitone
#print axioms AKMM.Consumption.cta_quadratic_tight_mpc
#print axioms AKMM.Consumption.cta_example_valid
#print axioms AKMM.Consumption.cta_example_mpc
#print axioms AKMM.Consumption.cta_det
#print axioms AKMM.Consumption.cta_det_valid
#print axioms AKMM.Consumption.cta_det_cont
#print axioms AKMM.Consumption.cta_det_good_tight
#print axioms AKMM.Consumption.cta_det_values
#print axioms AKMM.Consumption.cta_link_mpc_counterexample
#print axioms AKMM.Consumption.ctp_Hor
#print axioms AKMM.Consumption.ctp_cont_eq
#print axioms AKMM.Consumption.ctp_hor_zero
#print axioms AKMM.Consumption.ctp_cons_strict
#print axioms AKMM.Consumption.ctp_hor_step
#print axioms AKMM.Consumption.ctp_hor_all
#print axioms AKMM.Consumption.ctp_mpc_of_hor
#print axioms AKMM.Consumption.ctp_tight_mpc
#print axioms AKMM.Consumption.ctp_gap_antitone
#print axioms AKMM.Consumption.ctp_crra_tight_mpc
#print axioms AKMM.Consumption.ctc_lt_step
#print axioms AKMM.Consumption.ctc_step_lt
#print axioms AKMM.Consumption.ctc_step_top
#print axioms AKMM.Consumption.ctc_H
#print axioms AKMM.Consumption.ctc_valid
#print axioms AKMM.Consumption.ctc_tight_valid
#print axioms AKMM.Consumption.ctc_cont
#print axioms AKMM.Consumption.ctc_cons2_gt
#print axioms AKMM.Consumption.ctc_cons2_lt
#print axioms AKMM.Consumption.ctc_tighten_self
#print axioms AKMM.Consumption.ctc_counterexample
#print axioms AKMM.Consumption.ctc_not_tight_mpc
#print axioms AKMM.Consumption.ctc_not_hor
