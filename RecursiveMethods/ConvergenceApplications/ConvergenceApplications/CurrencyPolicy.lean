/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.CurrencyEnvelope

/-!
# The pure currency economy: the shape of the policy function

SLP §13.5, Exercise 13.5(d), (e), (g), pp. 399–400, using the differentiability of `W` on
`(0, ∞)` (`CurrencyEnvelope.lean`).

* `cashW_deriv_lt`, `cashW_deriv_pos`, `CurrencyDiffHyp.deriv_lt`: `W′ > 0` is strictly
  decreasing, and so is `U₁(·, z)`.
* **The corner condition** (the NOTE on (d)): for `m > 0`, `g(m, z) = y` iff
  `βW′(y) ≤ U₁(m, z)` (`cash_spend_all`, `cash_spend_all_necessary`).
* **Exercise 13.5(g)** (true; `ex_13_5g`): `g(m, z̄) = y` for `0 ≤ m ≤ y`, i.e. `φ(z̄) ≥ y`. The key
  bound `W′(y) ≤ U₁(y, z̄)` (`cashW_deriv_le`) is the NOTE's "Check of (g)", made rigorous:
  `W′(y) = ∫ v₁(y, z′) μ(dz′)` (`cvDerivR_cashW_eq_integral`, dominated convergence) and
  `v₁(y, z′) ≤ max{U₁(y, z̄), βW′(y)}`, including the case `c(y, z′) = 0` (where
  `v₁(y, z′) = βW′(2y)`), which the check omits.
* **Exercise 13.5(e), corrected** (`ex_13_5e_corrected`): if `m₁ < m₂` and `c(m₂, z) > 0`, then
  `c(m₁, z) < c(m₂, z)`, i.e. `0 ≤ g(m₂, z) − g(m₁, z) < m₂ − m₁` (when `c(m₂, z) = 0` the
  difference is `m₂ − m₁`).
* **Exercise 13.5(d), corrected** (`ex_13_5d_corrected`): for each `z` there is `φ(z) ≥ 0` (not
  always `> 0`, `ex_13_5d_counterexample`) with `g(·, z) = y` on `[0, φ(z)]` and `g(·, z)`
  strictly increasing on `[φ(z), ∞)` (`cashPolicy_strictMono_of_gt`); and `φ(z) ≥ φ₀` whenever
  `φ₀ > 0` and `βU₁(y, z̄) ≤ U₁(φ₀, z)`. This exogenous condition gives `φ(z) > 0`; it holds at
  `z̄` with `φ₀ = y` (part (g)), and at every `z` with `lim_{c↓0} U₁(c, z) > βU₁(y, z̄)` (e.g.
  under an Inada condition). The manual's route through the problem without the cash-in-advance
  constraint (`g = max{ḡ, y}`) is not used.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- `(f(a + t) − f(a))/t → f′(a)` as `t ↓ 0`. -/
theorem currency_tendsto_right_quot {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) :
    Tendsto (fun t => t⁻¹ * (f (a + t) - f a)) (𝓝[>] 0) (𝓝 f') := by
  simpa [smul_eq_mul] using hf.tendsto_slope_zero_right

/-- `(f(a) − f(a − t))/t → f′(a)` as `t ↓ 0`. -/
theorem currency_tendsto_left_quot {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) :
    Tendsto (fun t => t⁻¹ * (f a - f (a - t))) (𝓝[>] 0) (𝓝 f') := by
  have h1 := hf.tendsto_slope_zero_left.comp
    (by simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ))))
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, smul_eq_mul, inv_neg, ← sub_eq_add_neg]
  ring

/-- Limits preserve an inequality between difference quotients on `(0, δ)`. -/
theorem currency_le_of_quot_le {A B : ℝ → ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hA : Tendsto A (𝓝[>] 0) (𝓝 a))
    (hB : Tendsto B (𝓝[>] 0) (𝓝 b)) (hle : ∀ t, 0 < t → t < δ → A t ≤ B t) : a ≤ b :=
  le_of_tendsto_of_tendsto hA hB (by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    exact hle t ht.1 ht.2)

/-- For `φ` concave on `ℝ₊`, `a ≥ 0` and `0 < t ≤ δ`, `(φ(a + δ) − φ(a))/δ ≤ (φ(a + t) − φ(a))/t`:
shorter chords starting at `a` are steeper. -/
theorem currency_concave_right_slope_ge {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) {a t δ : ℝ}
    (ha : 0 ≤ a)
    (ht : 0 < t) (htδ : t ≤ δ) : δ⁻¹ * (φ (a + δ) - φ a) ≤ t⁻¹ * (φ (a + t) - φ a) := by
  have hδ : 0 < δ := ht.trans_le htδ
  set l := t / δ
  have hl0 : 0 ≤ l := div_nonneg ht.le hδ.le
  have hl1 : 0 ≤ 1 - l := by
    have : l ≤ 1 := (div_le_one hδ).2 htδ
    linarith
  have hc := hφ.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ a + δ)) (mem_Ici.2 ha) hl0 hl1 (by ring)
  have e : l • (a + δ) + (1 - l) • a = a + t := by
    simp only [smul_eq_mul, l]; field_simp; ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  have h1 : l * (φ (a + δ) - φ a) ≤ φ (a + t) - φ a := by linarith
  calc δ⁻¹ * (φ (a + δ) - φ a) = t⁻¹ * (l * (φ (a + δ) - φ a)) := by
        simp only [l]; field_simp
    _ ≤ t⁻¹ * (φ (a + t) - φ a) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)

variable {U U1 : ℝ → ℝ → ℝ} {β y zl zh : ℝ} (μ : Measure (Icc zl zh)) [IsProbabilityMeasure μ]

/-- `W′` is strictly decreasing on `(0, ∞)`. -/
theorem cashW_deriv_lt (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) : cvDerivR (cashW μ v) b < cvDerivR (cashW μ v) a := by
  have hW := cashW_strictConcave μ h hv
  have hb : 0 < b := ha.trans hab
  exact (hW.lt_slope_of_hasDerivAt (mem_Ici.2 ha.le) (mem_Ici.2 hb.le) hab
    (cashW_hasDerivAt μ h hd hv hb)).trans (hW.slope_lt_of_hasDerivAt (mem_Ici.2 ha.le)
      (mem_Ici.2 hb.le) hab (cashW_hasDerivAt μ h hd hv ha))

/-- `W′(x) > 0` for `x > 0` (`W` is strictly concave and nondecreasing). -/
theorem cashW_deriv_pos (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {a : ℝ} (ha : 0 < a) :
    0 < cvDerivR (cashW μ v) a := by
  have hW := cashW_strictConcave μ h hv
  have := hW.slope_lt_of_hasDerivAt (mem_Ici.2 ha.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ a + 1))
    (by linarith) (cashW_hasDerivAt μ h hd hv ha)
  rw [slope_def_field, show a + 1 - a = 1 by ring, div_one] at this
  have := cashW_mono μ h hv ha.le (by linarith : a ≤ a + 1)
  linarith

/-- `U₁(·, z)` is strictly decreasing on `(0, ∞)`. -/
theorem CurrencyDiffHyp.deriv_lt (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {z : ℝ} (hz : z ∈ Icc zl zh) {a b : ℝ} (ha : 0 < a) (hab : a < b) : U1 b z < U1 a z := by
  have hU := h.U_conc z hz
  have hb : 0 < b := ha.trans hab
  exact (hU.lt_slope_of_hasDerivAt (mem_Ici.2 ha.le) (mem_Ici.2 hb.le) hab
    (hd.deriv z hz b hb)).trans (hU.slope_lt_of_hasDerivAt (mem_Ici.2 ha.le)
      (mem_Ici.2 hb.le) hab (hd.deriv z hz a ha))

/-! ### The corner condition -/

/-- **The corner condition, sufficiency.** If `m > 0` and `βW′(y) ≤ U₁(m, z)`, the household
spends all its money: `g(m, z) = y`. For `m′ = y + s`, `β[W(y + s) − W(y)] ≤ βsW′(y) ≤
sU₁(m, z) ≤ U(m, z) − U(m − s, z)` by concavity of `W` and `U`. -/
theorem cash_spend_all (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m : Ici (0 : ℝ)} (hm : 0 < (m : ℝ)) (hK : β * cvDerivR (cashW μ v) y ≤ U1 m z) :
    (cashPolicy μ U β y v (m, z) : ℝ) = y := by
  have hy := h.y_pos
  have hβ := h.β_pos
  have hW := cashW_concave μ h hv
  refine cashPolicy_eq_of_ge μ h hv (m, z) le_rfl (by linarith [m.2.out]) ?_
  obtain ⟨a1, a2, e1, -⟩ := cashPolicy_spec μ h hv (m, z)
  dsimp only at a2 e1 ⊢
  rw [e1, show (m : ℝ) + y - y = m by ring]
  set g := (cashPolicy μ U β y v (m, z) : ℝ)
  rcases a1.eq_or_lt with hgy | hgy
  · rw [← hgy, show (m : ℝ) + y - y = m by ring]
  · set s := g - y
    have hs : 0 < s := by simp only [s]; linarith
    have hsm : s ≤ m := by simp only [s]; linarith
    have hWs := hW.slope_le_of_hasDerivWithinAt_Ioi (mem_Ici.2 hy.le) (mem_Ici.2 (by linarith))
      hgy (hasDerivWithinAt_cvDerivR hW hy)
    have hUs := (h.U_conc z.1 z.2).concaveOn.le_slope_of_hasDerivAt
      (mem_Ici.2 (by linarith : (0 : ℝ) ≤ (m : ℝ) - s)) (mem_Ici.2 hm.le) (by linarith)
      (hd.deriv z z.2 m hm)
    rw [slope_def_field] at hWs hUs
    rw [show (m : ℝ) - ((m : ℝ) - s) = s by ring] at hUs
    rw [show g - y = s from rfl] at hWs
    rw [div_le_iff₀ hs] at hWs
    rw [le_div_iff₀ hs] at hUs
    have hmg : (m : ℝ) + y - g = (m : ℝ) - s := by simp only [s]; ring
    rw [hmg]
    have hK0 := cashW_deriv_pos μ h hd hv hy
    nlinarith [mul_le_mul_of_nonneg_left hWs hβ.le, mul_le_mul_of_nonneg_right hK hs.le]

/-- **The corner condition, necessity.** If `m > 0` and `g(m, z) = y`, then `βW′(y) ≤ U₁(m, z)`:
saving `t` more is not better, `β[W(y + t) − W(y)] ≤ U(m, z) − U(m − t, z)`. -/
theorem cash_spend_all_necessary (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m : Ici (0 : ℝ)} (hm : 0 < (m : ℝ)) (hg : (cashPolicy μ U β y v (m, z) : ℝ) = y) :
    β * cvDerivR (cashW μ v) y ≤ U1 m z := by
  have hy := h.y_pos
  obtain ⟨-, -, e1, o1⟩ := cashPolicy_spec μ h hv (m, z)
  dsimp only at e1 o1
  rw [hg, show (m : ℝ) + y - y = m by ring] at e1
  refine currency_le_of_quot_le hm ((currency_tendsto_right_quot
    (cashW_hasDerivAt μ h hd hv hy)).const_mul β)
    (currency_tendsto_left_quot (hd.deriv z z.2 m hm)) fun t ht htm => ?_
  have i1 := o1 (y + t) (by linarith) (by linarith)
  rw [show (m : ℝ) + y - (y + t) = (m : ℝ) - t by ring] at i1
  have hti : 0 < t⁻¹ := inv_pos.2 ht
  nlinarith [mul_le_mul_of_nonneg_left (show β * (cashW μ v (y + t) - cashW μ v y) ≤
    U m z - U ((m : ℝ) - t) z by linarith) hti.le]

/-! ### Exercise 13.5(g) -/

/-- `W′(x) = ∫ v₁(x, z′) μ(dz′)` for `x > 0` (dominated convergence of right difference
quotients). -/
theorem cvDerivR_cashW_eq_integral (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {x : ℝ} (hx : 0 < x) :
    cvDerivR (cashW μ v) x = ∫ z, cvDerivR (cashV v z) x ∂μ := by
  have hW := cashW_concave μ h hv
  have hcz : ∀ t, 0 ≤ t → Continuous fun z => cashV v z t := fun t ht => by
    have : (fun z => cashV v z t) = fun z => v (⟨t, ht⟩, z) :=
      funext fun z => cashV_of_mem v z ⟨t, ht⟩
    rw [this]
    exact v.continuous.comp (Continuous.prodMk_right _)
  have hint : ∀ t, 0 ≤ t → Integrable (fun z => cashV v z t) μ := fun t ht => by
    have : (fun z => cashV v z t) = fun z => v (⟨t, ht⟩, z) :=
      funext fun z => cashV_of_mem v z ⟨t, ht⟩
    rw [this]
    exact integrable_section_v μ v _
  have hWint : ∀ t, 0 ≤ t → cashW μ v t = ∫ z, cashV v z t ∂μ := fun t ht => by
    rw [show cashW μ v t = cashW μ v ((⟨t, ht⟩ : Ici (0 : ℝ)) : ℝ) from rfl, cashW_of_mem]
    exact integral_congr_ae (Eventually.of_forall fun z => (cashV_of_mem v z ⟨t, ht⟩).symm)
  have hDCT : Tendsto (fun s => ∫ z, slope (cashV v z) x (x + s) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ z, cvDerivR (cashV v z) x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4 * ‖v‖ / x) ?_ ?_
      (integrable_const _) (Eventually.of_forall fun z =>
        currency_tendsto_slope_right (cashV_concave μ h hv z) hx)
    · filter_upwards [Ioc_mem_nhdsGT (show 0 < x / 2 by linarith)] with s hs
      have : (fun z => slope (cashV v z) x (x + s)) =
          fun z => (cashV v z (x + s) - cashV v z x) / (x + s - x) := by
        funext z; simp only [slope_def_field]
      rw [this]
      exact (((hcz _ (by linarith [hs.1])).sub (hcz x hx.le)).div_const _).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show 0 < x / 2 by linarith)] with s hs
      refine Eventually.of_forall fun z => ?_
      have hb := currency_concave_slopes_bound (cashV_concave μ h hv z) (cashV_mono μ h hv z)
        (fun t _ => abs_cashV_le v z t) hx hs.1 hs.2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hb.1, hb.2.1, hb.2.2]
  have hlimW : Tendsto (fun s => ∫ z, slope (cashV v z) x (x + s) ∂μ) (𝓝[>] 0)
      (𝓝 (cvDerivR (cashW μ v) x)) := by
    refine (currency_tendsto_slope_right hW hx).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hx] with s hs
    simp only [slope_def_field]
    rw [integral_div, integral_sub (hint _ (by linarith [hs.1])) (hint x hx.le),
      hWint _ (by linarith [hs.1]), hWint x hx.le]
  exact tendsto_nhds_unique hlimW hDCT

/-- **The bound `W′(y) ≤ U₁(y, z̄)`** (the check of part (g) in the NOTE). For each `z′`,
`v₁(y, z′) ≤ max{U₁(y, z̄), βW′(y)}`: if `c(y, z′) = y` it is `U₁(y, z′) ≤ U₁(y, z̄)`; if
`0 < c(y, z′) < y` it is `U₁(c, z′) ≤ βW′(g(y, z′)) ≤ βW′(y)` (first-order condition); if
`c(y, z′) = 0` it is `βW′(2y) ≤ βW′(y)`. Integrating, `W′(y) ≤ max{U₁(y, z̄), βW′(y)}`, and
`W′(y) > 0`, `β < 1` force `W′(y) ≤ U₁(y, z̄)`. -/
theorem cashW_deriv_le (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    cvDerivR (cashW μ v) y ≤ U1 y zh := by
  have hy := h.y_pos
  have hβ := h.β_pos
  have hzh : zh ∈ Icc zl zh := ⟨h.hz, le_rfl⟩
  set K := cvDerivR (cashW μ v) y
  have hK0 := cashW_deriv_pos μ h hd hv hy
  have hpt : ∀ z : Icc zl zh, cvDerivR (cashV v z) y ≤ max (U1 y zh) (β * K) := fun z => by
    obtain ⟨hg1, hg2, -, o1⟩ := cashPolicy_spec μ h hv (⟨y, mem_Ici.2 hy.le⟩, z)
    dsimp only at hg2 o1
    set g := (cashPolicy μ U β y v (⟨y, mem_Ici.2 hy.le⟩, z) : ℝ)
    rcases (sub_nonneg.2 hg2).eq_or_lt with hc0 | hcpos
    · -- `c(y, z) = 0`
      have hc : g = y + y := by linarith
      have := (ex_13_5b_deriv μ h hd hv z hy).2.2 hc
      rw [this]
      have := cashW_deriv_lt μ h hd hv hy (by linarith : y < y + y)
      exact le_max_of_le_right (by nlinarith)
    · have hpos := (cash_envelope_pos μ h hd hv z hy hcpos).2.1
      rw [hpos]
      change U1 (y + y - g) z ≤ _
      rcases hg1.eq_or_lt with hgy | hgy
      · -- `c(y, z) = y`
        rw [← hgy, show y + y - y = y by ring]
        exact le_max_of_le_left ((hd.mono y hy).monotoneOn z.2 hzh z.2.2)
      · -- `0 < c(y, z) < y`: the first-order condition
        refine le_max_of_le_right ?_
        have hfoc : U1 (y + y - g) z ≤ β * cvDerivR (cashW μ v) g :=
          currency_le_of_quot_le (by linarith : 0 < g - y)
            (currency_tendsto_right_quot (hd.deriv z z.2 _ hcpos))
            ((currency_tendsto_left_quot
              (cashW_hasDerivAt μ h hd hv (by linarith : 0 < g))).const_mul β)
            fun t ht htg => by
              have i1 := o1 (g - t) (by linarith) (by linarith)
              rw [show y + y - (g - t) = y + y - g + t by ring] at i1
              have hti : 0 < t⁻¹ := inv_pos.2 ht
              have e := cashPolicy_spec μ h hv (⟨y, mem_Ici.2 hy.le⟩, z)
              have e1 := e.2.2.1
              dsimp only at e1
              nlinarith [mul_le_mul_of_nonneg_left (show U (y + y - g + t) z - U (y + y - g) z ≤
                β * (cashW μ v g - cashW μ v (g - t)) by linarith) hti.le]
        have := cashW_deriv_lt μ h hd hv hy hgy
        nlinarith
  have hKint := cvDerivR_cashW_eq_integral μ h hv hy
  have hle : K ≤ max (U1 y zh) (β * K) := by
    have h0 : ∀ z : Icc zl zh, 0 ≤ cvDerivR (cashV v z) y := fun z => by
      have hφ := cashV_concave μ h hv z
      have hs := hφ.slope_le_of_hasDerivWithinAt_Ioi (mem_Ici.2 hy.le)
        (mem_Ici.2 (by linarith : (0 : ℝ) ≤ y + 1)) (by linarith) (hasDerivWithinAt_cvDerivR hφ hy)
      rw [slope_def_field, show y + 1 - y = 1 by ring, div_one] at hs
      have := cashV_mono μ h hv z (mem_Ici.2 hy.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ y + 1))
        (by linarith : y ≤ y + 1)
      linarith
    have := integral_mono_of_nonneg (Eventually.of_forall h0)
      (integrable_const (μ := μ) (max (U1 y zh) (β * K))) (Eventually.of_forall hpt)
    rw [integral_const, probReal_univ, one_smul] at this
    calc K = ∫ z, cvDerivR (cashV v z) y ∂μ := hKint
      _ ≤ max (U1 y zh) (β * K) := this
  rcases le_total (U1 y zh) (β * K) with hm | hm
  · rw [max_eq_right hm] at hle
    nlinarith [h.β_lt]
  · rw [max_eq_left hm] at hle
    exact hle

/-- **Exercise 13.5(g)** (true). `φ(z̄) ≥ y`: `g(m, z̄) = y` for `0 ≤ m ≤ y`, since
`βW′(y) ≤ W′(y) ≤ U₁(y, z̄) ≤ U₁(m, z̄)` (`cashW_deriv_le`, `cash_spend_all`). -/
theorem ex_13_5g (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (m : Ici (0 : ℝ))
    (hm : (m : ℝ) ≤ y) : (cashPolicy μ U β y v (m, ⟨zh, h.hz, le_rfl⟩) : ℝ) = y := by
  have hy := h.y_pos
  rcases (show (0 : ℝ) ≤ m from m.2).eq_or_lt with hm0 | hm0
  · obtain ⟨a1, a2, -, -⟩ := cashPolicy_spec μ h hv (m, ⟨zh, h.hz, le_rfl⟩)
    dsimp only at a2
    rw [← hm0] at a2
    linarith
  · refine cash_spend_all μ h hd hv _ hm0 ?_
    have hK := cashW_deriv_le μ h hd hv
    have hK0 := cashW_deriv_pos μ h hd hv hy
    have hU : U1 y zh ≤ U1 m zh := by
      rcases hm.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (hd.deriv_lt h ⟨h.hz, le_rfl⟩ hm0 hlt).le
    change β * cvDerivR (cashW μ v) y ≤ U1 (m : ℝ) zh
    nlinarith [h.β_lt]

/-! ### Exercise 13.5(e), corrected -/

/-- **Exercise 13.5(e), corrected.** Consumption is strictly increasing wherever it is positive:
if `m₁ < m₂` and `c(m₂, z) > 0`, then `c(m₁, z) < c(m₂, z)`, i.e.
`0 ≤ g(m₂, z) − g(m₁, z) < m₂ − m₁`. (If `c(m₂, z) = 0` then `c(m₁, z) = 0` and
`g(m₂, z) − g(m₁, z) = m₂ − m₁`, which happens in `ex_13_5e_counterexample`.) Proof: with
`c(m₁) = c(m₂) = c > 0`, `g(m₁) < g(m₂)`; the first-order conditions give
`βW′(g(m₁)) ≤ U₁(c, z) ≤ βW′(g(m₂))`, against the strict concavity of `W`. -/
theorem ex_13_5e_corrected (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m₁ m₂ : Ici (0 : ℝ)} (hm : m₁ < m₂)
    (hc : 0 < (m₂ : ℝ) + y - cashPolicy μ U β y v (m₂, z)) :
    (m₁ : ℝ) + y - cashPolicy μ U β y v (m₁, z) < (m₂ : ℝ) + y - cashPolicy μ U β y v (m₂, z) ∧
      0 ≤ (cashPolicy μ U β y v (m₂, z) : ℝ) - cashPolicy μ U β y v (m₁, z) ∧
      (cashPolicy μ U β y v (m₂, z) : ℝ) - cashPolicy μ U β y v (m₁, z) < (m₂ : ℝ) - m₁ := by
  have hy := h.y_pos
  have hβ := h.β_pos
  have hm' : (m₁ : ℝ) < m₂ := hm
  have hweak := cashCons_mono μ h hv z hm.le
  have hgmono := cashPolicy_mono μ h hv z hm.le
  obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (m₁, z)
  obtain ⟨b1, b2, e2, o2⟩ := cashPolicy_spec μ h hv (m₂, z)
  dsimp only at a2 b2 e1 e2 o1 o2 hc
  set g₁ := (cashPolicy μ U β y v (m₁, z) : ℝ)
  set g₂ := (cashPolicy μ U β y v (m₂, z) : ℝ)
  have hstrict : (m₁ : ℝ) + y - g₁ < (m₂ : ℝ) + y - g₂ := by
    refine lt_of_le_of_ne (by linarith) fun heq => ?_
    set c := (m₂ : ℝ) + y - g₂
    have hc₁ : (m₁ : ℝ) + y - g₁ = c := heq
    have hg : g₁ < g₂ := by linarith
    have hg₁ : 0 < g₁ := by linarith
    -- the first-order condition at `m₂` (save less)
    have hA : U1 c z ≤ β * cvDerivR (cashW μ v) g₂ :=
      currency_le_of_quot_le (by linarith : 0 < g₂ - g₁)
        (currency_tendsto_right_quot (hd.deriv z z.2 c hc))
        ((currency_tendsto_left_quot (cashW_hasDerivAt μ h hd hv (by linarith))).const_mul
          β) fun t ht htg => by
          have i1 := o2 (g₂ - t) (by linarith) (by linarith)
          rw [show (m₂ : ℝ) + y - (g₂ - t) = c + t by simp only [c]; ring] at i1
          have hti : 0 < t⁻¹ := inv_pos.2 ht
          nlinarith [mul_le_mul_of_nonneg_left (show U (c + t) z - U c z ≤
            β * (cashW μ v g₂ - cashW μ v (g₂ - t)) by linarith) hti.le]
    -- the first-order condition at `m₁` (save more)
    have hB : β * cvDerivR (cashW μ v) g₁ ≤ U1 c z :=
      currency_le_of_quot_le hc ((currency_tendsto_right_quot
          (cashW_hasDerivAt μ h hd hv hg₁)).const_mul β)
        (currency_tendsto_left_quot (hd.deriv z z.2 c hc)) fun t ht htc => by
          have i1 := o1 (g₁ + t) (by linarith) (by linarith)
          rw [show (m₁ : ℝ) + y - (g₁ + t) = c - t by linarith] at i1
          rw [hc₁] at e1
          have hti : 0 < t⁻¹ := inv_pos.2 ht
          nlinarith [mul_le_mul_of_nonneg_left (show β * (cashW μ v (g₁ + t) - cashW μ v g₁) ≤
            U c z - U (c - t) z by linarith) hti.le]
    have := cashW_deriv_lt μ h hd hv hg₁ hg
    nlinarith
  exact ⟨hstrict, by linarith, by linarith⟩

/-! ### Exercise 13.5(d), corrected -/

/-- Beyond the corner, `g(·, z)` is strictly increasing: if `m₁ < m₂` and `g(m₂, z) > y`, then
`g(m₁, z) < g(m₂, z)`. Otherwise `g(m₁) = g(m₂) = G > y` with `c(m₁) < c(m₂)`; saving less at
`m₁` and more at `m₂` and letting the deviation shrink gives `σ₁ ≤ βW′(G) ≤ σ₂` for chord slopes
`σ₁ > σ₂` of `U(·, z)` (strict concavity). -/
theorem cashPolicy_strictMono_of_gt (h : CurrencyHyp U β y zl zh)
    (hd : CurrencyDiffHyp U U1 zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m₁ m₂ : Ici (0 : ℝ)} (hm : m₁ < m₂) (hg : y < (cashPolicy μ U β y v (m₂, z) : ℝ)) :
    (cashPolicy μ U β y v (m₁, z) : ℝ) < cashPolicy μ U β y v (m₂, z) := by
  have hy := h.y_pos
  have hβ := h.β_pos
  have hm' : (m₁ : ℝ) < m₂ := hm
  have hgmono := cashPolicy_mono μ h hv z hm.le
  refine lt_of_le_of_ne hgmono fun heq => ?_
  obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (m₁, z)
  obtain ⟨b1, b2, e2, o2⟩ := cashPolicy_spec μ h hv (m₂, z)
  dsimp only at a2 b2 e1 e2 o1 o2
  set G := (cashPolicy μ U β y v (m₂, z) : ℝ)
  rw [heq] at a2 e1
  set c₁ := (m₁ : ℝ) + y - G
  set c₂ := (m₂ : ℝ) + y - G
  have hc₁ : 0 ≤ c₁ := by simp only [c₁]; linarith
  have hc₁₂ : c₁ < c₂ := by simp only [c₁, c₂]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (c₂ - c₁) / 3 := ⟨_, rfl⟩
  have hδ3 : 3 * δ = c₂ - c₁ := by rw [hδdef]; ring
  have hδ : 0 < δ := by linarith
  have hUc := (h.U_conc z.1 z.2)
  set σ₁ := δ⁻¹ * (U (c₁ + δ) z - U c₁ z)
  set σ₂ := δ⁻¹ * (U c₂ z - U (c₂ - δ) z)
  have hσ : σ₂ < σ₁ := by
    have s1 := hUc.slope_anti_adjacent (mem_Ici.2 hc₁)
      (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c₂ - δ)) (by linarith : c₁ < c₁ + δ)
      (by linarith : c₁ + δ < c₂ - δ)
    have s2 := hUc.slope_anti_adjacent (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c₁ + δ))
      (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c₂)) (by linarith : c₁ + δ < c₂ - δ)
      (by linarith : c₂ - δ < c₂)
    rw [show c₁ + δ - c₁ = δ by ring] at s1
    rw [show c₂ - (c₂ - δ) = δ by ring] at s2
    have e1 : σ₁ = (U (c₁ + δ) z - U c₁ z) / δ := by simp only [σ₁]; rw [div_eq_inv_mul]
    have e2 : σ₂ = (U c₂ z - U (c₂ - δ) z) / δ := by simp only [σ₂]; rw [div_eq_inv_mul]
    rw [e1, e2]
    linarith
  have hG : 0 < G := by linarith
  have hWd := cashW_hasDerivAt μ h hd hv hG
  -- saving less at `m₁`
  have hA : σ₁ ≤ β * cvDerivR (cashW μ v) G :=
    currency_le_of_quot_le (show 0 < min δ (G - y) from lt_min hδ (by linarith)) tendsto_const_nhds
      ((currency_tendsto_left_quot hWd).const_mul β) fun t ht htδ => by
        have htδ' : t ≤ δ := (htδ.trans_le (min_le_left _ _)).le
        have i1 := o1 (G - t) (by linarith [min_le_right δ (G - y)]) (by linarith)
        rw [show (m₁ : ℝ) + y - (G - t) = c₁ + t by simp only [c₁]; ring] at i1
        have hch := currency_concave_right_slope_ge hUc.concaveOn hc₁ ht htδ'
        have hti : 0 < t⁻¹ := inv_pos.2 ht
        nlinarith [mul_le_mul_of_nonneg_left (show U (c₁ + t) z - U c₁ z ≤
          β * (cashW μ v G - cashW μ v (G - t)) by linarith) hti.le]
  -- saving more at `m₂`
  have hB : β * cvDerivR (cashW μ v) G ≤ σ₂ :=
    currency_le_of_quot_le hδ ((currency_tendsto_right_quot hWd).const_mul β) tendsto_const_nhds
      fun t ht htδ => by
        have i2 := o2 (G + t) (by linarith) (by simp only [c₂] at hδ3; linarith)
        rw [show (m₂ : ℝ) + y - (G + t) = c₂ - t by simp only [c₂]; ring] at i2
        have hch := currency_concave_left_slope_le hUc.concaveOn (a := c₂) ht htδ.le (by linarith)
        have hti : 0 < t⁻¹ := inv_pos.2 ht
        nlinarith [mul_le_mul_of_nonneg_left (show β * (cashW μ v (G + t) - cashW μ v G) ≤
          U c₂ z - U (c₂ - t) z by linarith) hti.le]
  linarith

/-- **Exercise 13.5(d), corrected.** For each `z` there is `φ(z) ≥ 0` with `g(·, z) = y` on
`[0, φ(z)]` and `g(·, z)` strictly increasing on `[φ(z), ∞)`; `φ(z) ≥ φ₀` whenever `φ₀ > 0` and
`βU₁(y, z̄) ≤ U₁(φ₀, z)` (so `φ(z) > 0` under this condition, e.g. when
`U₁(0⁺, z) > βU₁(y, z̄)`, in particular at `z = z̄` with `φ₀ = y`, part (g)). The book's
`φ(z) > 0` for every `z` is false (`ex_13_5d_counterexample`). -/
theorem ex_13_5d_corrected (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    ∃ φ : ℝ, 0 ≤ φ ∧ (∀ m : Ici (0 : ℝ), (m : ℝ) ≤ φ → (cashPolicy μ U β y v (m, z) : ℝ) = y) ∧
      (∀ m₁ m₂ : Ici (0 : ℝ), φ ≤ (m₁ : ℝ) → m₁ < m₂ →
        (cashPolicy μ U β y v (m₁, z) : ℝ) < cashPolicy μ U β y v (m₂, z)) ∧
      ∀ φ₀ : ℝ, 0 < φ₀ → β * U1 y zh ≤ U1 φ₀ z → φ₀ ≤ φ := by
  have hy := h.y_pos
  have hβ := h.β_pos
  obtain ⟨B, hB⟩ := h.U_bdd
  set G : ℝ → ℝ := fun m =>
    (cashPolicy μ U β y v (⟨max m 0, mem_Ici.2 (le_max_right _ _)⟩, z) : ℝ)
  have hGc : Continuous G := continuous_cashPolicy_real μ h hv z
  have hGm : ∀ m : Ici (0 : ℝ), G m = cashPolicy μ U β y v (m, z) := fun m => by
    simp only [G, currency_Ici_max_eq]
  set S := Ici (0 : ℝ) ∩ {m | G m = y}
  have hSc : IsClosed S := isClosed_Ici.inter (isClosed_eq hGc continuous_const)
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨mem_Ici.2 le_rfl, ?_⟩
    have := cashPolicy_spec μ h hv (⟨max 0 0, mem_Ici.2 (le_max_right _ _)⟩, z)
    simp only [mem_ofPred_eq, G]
    have h1 := this.1
    have h2 := this.2.1
    dsimp only at h2
    have h3 : max (0 : ℝ) 0 = 0 := max_self 0
    linarith
  have hK0 := cashW_deriv_pos μ h hd hv hy
  -- `S` is bounded: `βW′(y) ≤ U₁(m, z) ≤ 4B/m` on `S`
  have hSb : BddAbove S := by
    refine ⟨max 1 (4 * B / (β * cvDerivR (cashW μ v) y)), fun m hm => ?_⟩
    by_contra hlt
    push Not at hlt
    have hm1 : 1 < m := (le_max_left _ _).trans_lt hlt
    have hm0 : 0 < m := by linarith
    have hgy : (cashPolicy μ U β y v (⟨m, mem_Ici.2 hm0.le⟩, z) : ℝ) = y := by
      rw [← hGm]; exact hm.2
    have hnec := cash_spend_all_necessary μ h hd hv z (m := ⟨m, mem_Ici.2 hm0.le⟩) hm0 hgy
    have hsl := (h.U_conc z.1 z.2).concaveOn.le_slope_of_hasDerivAt
      (mem_Ici.2 (by linarith : (0 : ℝ) ≤ m / 2)) (mem_Ici.2 hm0.le) (by linarith)
      (hd.deriv z z.2 m hm0)
    rw [slope_def_field, show m - m / 2 = m / 2 by ring] at hsl
    have h1 := abs_le.1 (hB m hm0.le z z.2)
    have h2 := abs_le.1 (hB (m / 2) (by linarith) z z.2)
    have hβK : 0 < β * cvDerivR (cashW μ v) y := mul_pos hβ hK0
    have hlt' : 4 * B / (β * cvDerivR (cashW μ v) y) < m := (le_max_right _ _).trans_lt hlt
    rw [div_lt_iff₀ hβK] at hlt'
    change β * cvDerivR (cashW μ v) y ≤ U1 m z at hnec
    have : U1 m z * (m / 2) ≤ 2 * B := by
      rw [le_div_iff₀ (by linarith)] at hsl
      linarith
    nlinarith
  have hmem := hSc.csSup_mem ⟨0, h0S⟩ hSb
  set φ := sSup S
  have hφ0 : 0 ≤ φ := le_csSup hSb h0S
  have hflat : ∀ m : Ici (0 : ℝ), (m : ℝ) ≤ φ → (cashPolicy μ U β y v (m, z) : ℝ) = y := by
    intro m hm
    have h1 := cashPolicy_mono μ h hv z (m₁ := m) (m₂ := ⟨φ, mem_Ici.2 hφ0⟩) hm
    have h2 := (cashPolicy_spec μ h hv (m, z)).1
    have h3 : (cashPolicy μ U β y v (⟨φ, mem_Ici.2 hφ0⟩, z) : ℝ) = y := by
      rw [← hGm]; exact hmem.2
    linarith
  refine ⟨φ, hφ0, hflat, fun m₁ m₂ hφm hm => ?_, fun φ₀ hφ₀ hU => ?_⟩
  · have hgt : y < (cashPolicy μ U β y v (m₂, z) : ℝ) := by
      refine lt_of_le_of_ne (cashPolicy_spec μ h hv (m₂, z)).1 fun heq => ?_
      have hm₂ : (m₂ : ℝ) ∈ S := ⟨m₂.2, by simp only [mem_ofPred_eq]; rw [hGm]; exact heq.symm⟩
      have := le_csSup hSb hm₂
      have : (m₁ : ℝ) < m₂ := hm
      linarith
    exact cashPolicy_strictMono_of_gt μ h hd hv z hm hgt
  · -- `g(φ₀, z) = y`
    have hK := cashW_deriv_le μ h hd hv
    have hg : (cashPolicy μ U β y v (⟨φ₀, mem_Ici.2 hφ₀.le⟩, z) : ℝ) = y :=
      cash_spend_all μ h hd hv z hφ₀ (by
        change β * cvDerivR (cashW μ v) y ≤ U1 φ₀ z
        nlinarith)
    refine le_csSup hSb ⟨mem_Ici.2 hφ₀.le, ?_⟩
    change G ((⟨φ₀, mem_Ici.2 hφ₀.le⟩ : Ici (0 : ℝ)) : ℝ) = y
    rw [hGm]
    exact hg

end StokeyLucasPrescott.ConvergenceApplications
