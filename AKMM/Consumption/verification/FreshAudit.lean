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
