/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYFirm
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# §17.1.3: existence of a stationary equilibrium by the crossing argument (Figure 17.1)

Miao, §17.1.3, pp. 563–564, and §17.1.4, p. 568. The aggregate capital supply `Ea(r)` (the
long-run average assets) is continuous, tends to infinity as `r ↑ ρ = 1/β − 1` and lies below
the capital demand `K^d(r)` for `r` near `−δ`; by the Intermediate Value Theorem the curves
cross.

* `ay_rho`, `ay_complete_markets_rate`: under complete markets (constant consumption satisfying
  the Euler equation `u′(c) = β(1 + r)u′(c)`) the interest rate is `ρ = 1/β − 1`.
* `ay_existence`: the abstract crossing argument: `Ea` continuous on `[r₀, ρ)`, `Ea → ∞` as
  `r ↑ ρ`, `K^d` continuous on `[r₀, ρ]`, `Ea(r₀) < K^d(r₀)` ⇒ `Ea(r*) = K^d(r*)` for some
  `r* ∈ (r₀, ρ)`; in particular `r* < ρ`.
* `ay_existence_cd`: with the Cobb–Douglas capital demand `K^d(r) = F_K^{-1}(r + δ)`, `Ea`
  continuous on `(−δ, ρ)`, bounded above near `−δ` (the book's "when `r < 0`, `Ea(r)`
  approaches `−b`") and tending to infinity at `ρ`: there is an equilibrium `r* ∈ (−δ, ρ)`.
* `ay_overaccumulation`: at any crossing `r* < ρ`, capital exceeds the complete-markets level
  `K^d(ρ)` (where `F_K = ρ + δ`), and the saving rate `δα/(r* + δ)` exceeds the complete-markets
  saving rate `δα/(ρ + δ)` (§17.1.4: precautionary saving).
* `ay_existence_example`: the hypotheses of `ay_existence_cd` hold for a concrete supply curve
  (`Ea(r) = 1/(1 − r)`, `β = 1/2`, `δ = 1/8`, `A = L = 1`, `α = 1/2`), so the theorem is not
  vacuous.

**Departures.** The continuity of `Ea` in `r` (via continuity of the policy and of the
stationary distribution in `r`), its divergence as `r ↑ ρ`, and its behaviour as `r ↓ −δ` are
asserted, not proved, in the book ("we can show"); they are hypotheses of `ay_existence` and
`ay_existence_cd` (the Chapter 8 project likewise leaves the continuity of the stationary
distribution in `R` unformalised). The book's possible multiplicity of crossings and "this case
seldom happens" carry no precise claim and are not formalised. That `r < ρ` holds at every
stationary distribution (not only at the crossing constructed here) is `ay_r_lt_rho`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, p. 564: `ρ = 1/β − 1`, the equilibrium interest rate under complete markets. -/
noncomputable def ay_rho (β : ℝ) : ℝ := 1 / β - 1

/-- Miao, p. 564: under complete markets consumption is constant at `c` and the Euler equation
`u′(c) = β(1 + r)u′(c)` with `u′(c) > 0` forces `r = ρ = 1/β − 1`. -/
theorem ay_complete_markets_rate {β r duc : ℝ} (hβ : 0 < β) (hdu : 0 < duc)
    (heul : duc = β * (1 + r) * duc) : r = ay_rho β := by
  have h1 : β * (1 + r) = 1 := by
    have := mul_right_cancel₀ hdu.ne' (heul.symm.trans (one_mul duc).symm)
    exact this
  rw [ay_rho]
  field_simp
  linarith

/-- Miao, pp. 563–564 (Figure 17.1): the **crossing argument**. If the capital supply `Ea` is
continuous on `[r₀, ρ)` with `Ea(r) → ∞` as `r ↑ ρ`, the capital demand `K^d` is continuous on
`[r₀, ρ]`, and `Ea(r₀) < K^d(r₀)`, then `Ea(r*) = K^d(r*)` for some `r* ∈ (r₀, ρ)`. -/
theorem ay_existence {Ea Kd : ℝ → ℝ} {r0 ρ : ℝ} (hr0 : r0 < ρ)
    (hEa : ContinuousOn Ea (Set.Ico r0 ρ)) (hKd : ContinuousOn Kd (Set.Icc r0 ρ))
    (hlim : Tendsto Ea (𝓝[<] ρ) atTop) (hlow : Ea r0 < Kd r0) :
    ∃ r ∈ Set.Ioo r0 ρ, Ea r = Kd r := by
  obtain ⟨rm, -, hrm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hr0.le) hKd
  obtain ⟨r1, hr1E, hr1⟩ :=
    ((hlim.eventually (eventually_gt_atTop (Kd rm))).and (Ioo_mem_nhdsLT hr0)).exists
  have hsub : Set.Icc r0 r1 ⊆ Set.Ico r0 ρ := fun r hr => ⟨hr.1, hr.2.trans_lt hr1.2⟩
  have hcont : ContinuousOn (fun r => Kd r - Ea r) (Set.Icc r0 r1) :=
    (hKd.mono fun r hr => ⟨hr.1, (hr.2.trans_lt hr1.2).le⟩).sub (hEa.mono hsub)
  have hK1 : Kd r1 ≤ Kd rm := hrm ⟨hr1.1.le, hr1.2.le⟩
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Icc' hr1.1.le hcont
    (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Set.Icc _ _)
  simp only at hzero
  have hne : r ≠ r0 := by rintro rfl; linarith
  exact ⟨r, ⟨lt_of_le_of_ne hr.1 hne.symm, hr.2.trans_lt hr1.2⟩, by linarith⟩

/-- Miao, pp. 563–564: existence of a stationary equilibrium interest rate with the
Cobb–Douglas capital demand: if `Ea` is continuous on `(−δ, ρ)`, bounded above on some
`(−δ, r′]`, and `Ea(r) → ∞` as `r ↑ ρ`, then `Ea(r*) = K^d(r*)` for some `r* ∈ (−δ, ρ)`. -/
theorem ay_existence_cd {A α δ L β : ℝ} {Ea : ℝ → ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hEa : ContinuousOn Ea (Set.Ioo (-δ) (ay_rho β)))
    (hlim : Tendsto Ea (𝓝[<] ay_rho β) atTop)
    (hbdd : ∃ r' ∈ Set.Ioo (-δ) (ay_rho β), ∃ B, ∀ r ∈ Set.Ioc (-δ) r', Ea r ≤ B) :
    ∃ r ∈ Set.Ioo (-δ) (ay_rho β), Ea r = ay_Kd A α δ L r := by
  obtain ⟨r', hr', B, hB⟩ := hbdd
  obtain ⟨r0, hr0K, hr0⟩ :=
    (((ay_Kd_tendsto hA hα0 hα1 hL).eventually (eventually_gt_atTop B)).and
      (Ioc_mem_nhdsGT hr'.1)).exists
  have hρ : -δ < ay_rho β := hr'.1.trans hr'.2
  have hr0ρ : r0 < ay_rho β := hr0.2.trans_lt hr'.2
  obtain ⟨r, hr, heq⟩ := ay_existence (Ea := Ea) (Kd := ay_Kd A α δ L) hr0ρ
    (hEa.mono fun r hr => ⟨hr0.1.trans_le hr.1, hr.2⟩)
    ((ay_Kd_continuousOn hA hα0).mono fun r hr => Set.mem_Ioi.2 (hr0.1.trans_le hr.1))
    hlim ((hB r0 hr0).trans_lt hr0K)
  exact ⟨r, ⟨hr0.1.trans hr.1, hr.2⟩, heq⟩

/-- Miao, p. 564 and §17.1.4, p. 568: at an incomplete-markets equilibrium rate `r* < ρ`, the
capital stock exceeds the complete-markets capital stock `K^d(ρ)` (which solves
`F_K = ρ + δ`), and the aggregate saving rate `δα/(r* + δ)` exceeds the complete-markets rate
`δα/(ρ + δ)`: households hold extra assets for precautionary motives. -/
theorem ay_overaccumulation {A α δ L ρ r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hδ : 0 < δ) (hr : -δ < r) (hrρ : r < ρ) :
    ay_Kd A α δ L ρ < ay_Kd A α δ L r ∧ ay_cdFK A α (ay_Kd A α δ L ρ) L = ρ + δ ∧
      δ * α / (ρ + δ) < δ * α / (r + δ) := by
  refine ⟨ay_Kd_strictAnti hA hα0 hα1 hL (Set.mem_Ioi.2 hr)
      (Set.mem_Ioi.2 (hr.trans hrρ)) hrρ, ay_Kd_foc hA hα0 hα1 hL (hr.trans hrρ), ?_⟩
  exact div_lt_div_of_pos_left (mul_pos hδ hα0) (by linarith) (by linarith)

/-- The crossing argument is not vacuous: with `β = 1/2` (`ρ = 1`), `δ = 1/8`, `A = L = 1`,
`α = 1/2`, the supply curve `Ea(r) = 1/(1 − r)` satisfies the hypotheses of `ay_existence_cd`,
so it crosses the capital demand curve at some `r* ∈ (−1/8, 1)`. -/
theorem ay_existence_example :
    ∃ r ∈ Set.Ioo (-(1 / 8 : ℝ)) (ay_rho (1 / 2)),
      1 / (1 - r) = ay_Kd 1 (1 / 2) (1 / 8) 1 r := by
  have hρ : ay_rho (1 / 2) = 1 := by rw [ay_rho]; norm_num
  refine ay_existence_cd (Ea := fun r => 1 / (1 - r)) one_pos (by norm_num) (by norm_num)
    one_pos ?_ ?_ ?_
  · rw [hρ]
    exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      fun r hr => by linarith [hr.2]
  · rw [hρ]
    have h1 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto _
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact Set.mem_Ioi.2 (by linarith [Set.mem_Iio.1 hr])
    exact Tendsto.congr (fun r => by simp [one_div]) (tendsto_inv_nhdsGT_zero.comp h1)
  · refine ⟨0, ⟨by norm_num, by rw [hρ]; norm_num⟩, 1, fun r hr => ?_⟩
    have h : 1 ≤ 1 - r := by linarith [hr.2]
    rw [div_le_one (by linarith)]
    exact h

end Miao.IncompleteMarkets
