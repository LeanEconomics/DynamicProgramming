/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.CurrencyEconomy

/-!
# The pure currency economy: the stationary distribution of money

SLP §13.5, Exercises 13.5(i)–(j) for the household's optimal policy, p. 400.

* `CurrencyDiffHyp`: `U(·, z)` has derivative `U₁(c, z)` at every `c > 0`, and `U₁(c, ·)` is
  strictly increasing on `Z`; `CurrencyDiffHyp.increasingDiff` gives increasing differences.
* `cash_down`: if `m̄ > y` is a fixed point of `g(·, z̲)` and `z̲ < z̄`, then `g(m̄, z̄) < m̄`.
  Otherwise `c(m̄, z) = y` for all `z`; four deviations at `m̄` give
  `[U(y + t, z̄) − U(y, z̄)] − [U(y, z̲) − U(y − t, z̲)] ≤ β∫[2U(y, z′) − U(y − t, z′) −
  U(y + t, z′)]μ(dz′)`, and dividing by `t ↓ 0` (dominated convergence) gives
  `U₁(y, z̄) ≤ U₁(y, z̲)`. Part (g) is not needed.
* `cash_currencyPolicy`: the optimal policy restricted to `X = [y, m̄]` (`cashPolicyX`) satisfies
  `CurrencyPolicy` (parts (c), (e) weak, (f), (h) and the two crossing conditions).
* **Exercises 13.5(i)–(j) for the economy** (`ex_13_5ij_economy`): under the assumptions of
  §13.5, with `z̲ < z̄` and `μ` giving positive mass to every `[z̲, z̲ + δ]` and `[z̄ − δ, z̄]`
  (e.g. under the density condition, `currencyEndMass_of_density`), the transition function of
  real balances on `X = [y, m̄]` is monotone and Feller and satisfies Assumption 12.1; it has a
  unique invariant probability measure `λ*`, `T*ⁿλ₀ ⇒ λ*` for every `λ₀`,
  `∫ m dλ* = ∫∫ g(m, z) μ(dz) λ*(dm)`, and the stationary price levels are exactly
  `p = M/∫ m dλ*`.

**Correction** (Exercise 13.5(i)). The book derives Assumption 12.1 from the slope bound of part
(e), which is false (`ex_13_5e_counterexample`), and from part (g). The proof here uses only the
weak monotonicity of `g` and the crossing conditions `g(m, z̲) > m` on `[y, m̄)` (from the choice
of `m̄`) and `g(m̄, z̄) < m̄` (`cash_down`, which needs `z̲ < z̄`, an assumption the book leaves
implicit).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The differentiability hypotheses of §13.5: `U(·, z)` has derivative `U₁(c, z)` at every
`c > 0`, and `U₁(c, ·)` is strictly increasing on `Z`. -/
structure CurrencyDiffHyp (U U1 : ℝ → ℝ → ℝ) (zl zh : ℝ) : Prop where
  deriv : ∀ z ∈ Icc zl zh, ∀ c, 0 < c → HasDerivAt (fun c => U c z) (U1 c z) c
  mono : ∀ c, 0 < c → StrictMonoOn (U1 c) (Icc zl zh)

variable {U U1 : ℝ → ℝ → ℝ} {β y zl zh : ℝ}

/-- `z ↦ U(c, z)` is continuous on `Z`. -/
theorem CurrencyHyp.continuous_section (h : CurrencyHyp U β y zl zh) {c : ℝ} (hc : 0 ≤ c) :
    Continuous fun z : Icc zl zh => U c z :=
  h.U_cont.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    fun z => ⟨mem_Ici.2 hc, z.2⟩

/-- `c ↦ U(c, z)` is continuous on `ℝ₊`. -/
theorem CurrencyHyp.continuousOn_c (h : CurrencyHyp U β y zl zh) {z : ℝ} (hz : z ∈ Icc zl zh) :
    ContinuousOn (fun c => U c z) (Ici 0) :=
  h.U_cont.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hc => ⟨hc, hz⟩

/-- `z ↦ U(c, z)` is integrable. -/
theorem CurrencyHyp.integrable_section (h : CurrencyHyp U β y zl zh) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 ≤ c) : Integrable (fun z : Icc zl zh => U c z) μ :=
  integrable_of_bounded (h.continuous_section hc).measurable fun z =>
    h.U_bdd.choose_spec c hc z z.2

/-- The differentiability hypotheses give increasing differences. -/
theorem CurrencyDiffHyp.increasingDiff (h : CurrencyHyp U β y zl zh)
    (hd : CurrencyDiffHyp U U1 zl zh) : CurrencyIncreasingDiff U zl zh := by
  intro c c' hc hcc' z z' hz hzz' hz'
  set φ := fun t => U t z' - U t z
  have hcont : ContinuousOn φ (Icc c c') :=
    ((h.continuousOn_c ⟨by linarith, hz'⟩).sub (h.continuousOn_c ⟨hz, by linarith⟩)).mono
      fun t ht => mem_Ici.2 (hc.trans ht.1)
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc c c') hcont fun t ht => by
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_of_le_of_lt hc ht.1
    have hφd : HasDerivAt φ (U1 t z' - U1 t z) t :=
      (hd.deriv z' ⟨by linarith, hz'⟩ t ht0).sub (hd.deriv z ⟨hz, by linarith⟩ t ht0)
    rw [hφd.deriv]
    exact sub_pos.2 (hd.mono t ht0 ⟨hz, by linarith⟩ ⟨by linarith, hz'⟩ hzz')
  have := hmono ⟨le_rfl, hcc'.le⟩ ⟨hcc'.le, le_rfl⟩ hcc'
  simp only [φ] at this
  linarith

/-- For `φ` concave on `ℝ₊` and `0 < t ≤ t₀ ≤ a`, `(φ(a) − φ(a − t))/t ≤ (φ(a) − φ(a − t₀))/t₀`:
longer chords ending at `a` are steeper. -/
theorem currency_concave_left_slope_le {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) {a t t₀ : ℝ}
    (ht : 0 < t)
    (htt : t ≤ t₀) (hta : t₀ ≤ a) : t⁻¹ * (φ a - φ (a - t)) ≤ t₀⁻¹ * (φ a - φ (a - t₀)) := by
  have ht₀ : 0 < t₀ := ht.trans_le htt
  set l := t / t₀
  have hl0 : 0 ≤ l := div_nonneg ht.le ht₀.le
  have hl1 : 0 ≤ 1 - l := by
    have : l ≤ 1 := (div_le_one ht₀).2 htt
    linarith
  have hc := hφ.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ a - t₀))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ a)) hl0 hl1 (by ring)
  have e : l • (a - t₀) + (1 - l) • a = a - t := by
    simp only [smul_eq_mul, l]; field_simp; ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  have h1 : φ a - φ (a - t) ≤ l * (φ a - φ (a - t₀)) := by linarith
  calc t⁻¹ * (φ a - φ (a - t)) ≤ t⁻¹ * (l * (φ a - φ (a - t₀))) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)
    _ = t₀⁻¹ * (φ a - φ (a - t₀)) := by simp only [l]; field_simp

variable (μ : Measure (Icc zl zh)) [IsProbabilityMeasure μ]

/-- **The crossing condition at `z̄`.** If `m̄ > y` is a fixed point of `g(·, z̲)`, then
`g(m̄, z̄) < m̄`. Otherwise `g(m̄, z) = m̄` and `c(m̄, z) = y` for every `z` (part (h)). Saving `t`
more at `z̲`, saving `t` less at `z̄`, and the deviations "keep `m′ = m̄`" at `m̄ ± t` give
`[U(y + t, z̄) − U(y, z̄)] − [U(y, z̲) − U(y − t, z̲)] ≤ β ∫ [2U(y, z′) − U(y − t, z′) −
U(y + t, z′)] μ(dz′)`. Divided by `t`, the left side tends to `U₁(y, z̄) − U₁(y, z̲) > 0` and the
right side to `0` (dominated convergence; the integrand is bounded by concavity). -/
theorem cash_down (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    (hzlt : zl < zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {m : Ici (0 : ℝ)}
    (hym : y < (m : ℝ))
    (hfix : (cashPolicy μ U β y v (m, ⟨zl, le_rfl, h.hz⟩) : ℝ) = m) :
    (cashPolicy μ U β y v (m, ⟨zh, h.hz, le_rfl⟩) : ℝ) < m := by
  set zL : Icc zl zh := ⟨zl, le_rfl, h.hz⟩
  set zH : Icc zl zh := ⟨zh, h.hz, le_rfl⟩
  have hy := h.y_pos
  have hβ := h.β_pos
  have hID := hd.increasingDiff h
  by_contra hge
  push Not at hge
  have hanti := ex_13_5h μ h hID hv m
  have hall : ∀ z : Icc zl zh, (cashPolicy μ U β y v (m, z) : ℝ) = m := fun z =>
    le_antisymm (hfix ▸ hanti (show zL ≤ z from z.2.1)) (hge.trans (hanti z.2.2))
  set mm : ℝ := (m : ℝ)
  -- the value at `m̄`
  have hval : ∀ z : Icc zl zh, v (m, z) = U y z + β * cashW μ v mm := fun z => by
    have := (cashPolicy_spec μ h hv (m, z)).2.2.1
    dsimp only at this
    rw [hall z, show (m : ℝ) + y - m = y by ring] at this
    exact this
  obtain ⟨B, hB⟩ := h.U_bdd
  have hint := integrable_section_v μ v
  have hUi : ∀ c : ℝ, 0 ≤ c → Integrable (fun z : Icc zl zh => U c z) μ := fun c hc =>
    h.integrable_section μ hc
  set t₀ := min (y / 2) (mm - y)
  have ht₀ : 0 < t₀ := lt_min (by linarith) (by linarith)
  -- the key inequality for `0 < t ≤ t₀`
  have hkey : ∀ t, 0 < t → t ≤ t₀ →
      (U (y + t) zh - U y zh) - (U y zl - U (y - t) zl) ≤
        β * ∫ z, (2 * U y z - U (y - t) z - U (y + t) z) ∂μ := by
    intro t ht htt
    have hty : t ≤ y / 2 := htt.trans (min_le_left _ _)
    have htm : t ≤ mm - y := htt.trans (min_le_right _ _)
    obtain ⟨-, -, -, oL⟩ := cashPolicy_spec μ h hv (m, zL)
    obtain ⟨-, -, -, oH⟩ := cashPolicy_spec μ h hv (m, zH)
    dsimp only at oL oH
    have i1 := oL (mm + t) (by linarith) (by linarith)
    have i2 := oH (mm - t) (by linarith) (by linarith)
    rw [hval zL, show mm + y - (mm + t) = y - t by ring] at i1
    rw [hval zH, show mm + y - (mm - t) = y + t by ring] at i2
    -- the deviations "keep `m′ = m̄`"
    set mp : Ici (0 : ℝ) := ⟨mm + t, mem_Ici.2 (by linarith)⟩
    set mn : Ici (0 : ℝ) := ⟨mm - t, mem_Ici.2 (by linarith)⟩
    have hp : ∀ z : Icc zl zh, U (y + t) z + β * cashW μ v mm ≤ v (mp, z) := fun z => by
      have := (cashPolicy_spec μ h hv (mp, z)).2.2.2 mm hym.le (by
        change mm ≤ mm + t + y; linarith)
      dsimp only at this
      rwa [show (mp : ℝ) + y - mm = y + t by change mm + t + y - mm = y + t; ring] at this
    have hn : ∀ z : Icc zl zh, U (y - t) z + β * cashW μ v mm ≤ v (mn, z) := fun z => by
      have := (cashPolicy_spec μ h hv (mn, z)).2.2.2 mm hym.le (by
        change mm ≤ mm - t + y; linarith)
      dsimp only at this
      rwa [show (mn : ℝ) + y - mm = y - t by change mm - t + y - mm = y - t; ring] at this
    have hWp : ∫ z, (U (y + t) z - U y z) ∂μ ≤ cashW μ v (mm + t) - cashW μ v mm := by
      rw [show cashW μ v (mm + t) = cashW μ v (mp : ℝ) from rfl,
        show cashW μ v mm = cashW μ v (m : ℝ) from rfl, cashW_of_mem, cashW_of_mem,
        ← integral_sub (hint _) (hint _)]
      exact integral_mono ((hUi (y + t) (by linarith)).sub (hUi y hy.le))
        ((hint _).sub (hint _)) fun z => by have := hp z; have := hval z; dsimp only; linarith
    have hWn : cashW μ v mm - cashW μ v (mm - t) ≤ ∫ z, (U y z - U (y - t) z) ∂μ := by
      rw [show cashW μ v (mm - t) = cashW μ v (mn : ℝ) from rfl,
        show cashW μ v mm = cashW μ v (m : ℝ) from rfl, cashW_of_mem, cashW_of_mem,
        ← integral_sub (hint _) (hint _)]
      exact integral_mono ((hint _).sub (hint _)) ((hUi y hy.le).sub (hUi (y - t) (by linarith)))
        fun z => by have := hn z; have := hval z; dsimp only; linarith
    have hsplit : ∫ z, (2 * U y z - U (y - t) z - U (y + t) z) ∂μ =
        ∫ z, (U y z - U (y - t) z) ∂μ - ∫ z, (U (y + t) z - U y z) ∂μ := by
      have I1 : Integrable (fun z : Icc zl zh => U y z - U (y - t) z) μ :=
        (hUi y hy.le).sub (hUi (y - t) (by linarith))
      have I2 : Integrable (fun z : Icc zl zh => U (y + t) z - U y z) μ :=
        (hUi (y + t) (by linarith)).sub (hUi y hy.le)
      rw [← integral_sub I1 I2]
      congr 1; funext z; ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hWp hβ.le, mul_le_mul_of_nonneg_left hWn hβ.le]
  -- the limits
  have hzlZ : zl ∈ Icc zl zh := ⟨le_rfl, h.hz⟩
  have hzhZ : zh ∈ Icc zl zh := ⟨h.hz, le_rfl⟩
  have hR : ∀ z ∈ Icc zl zh, Tendsto (fun t => t⁻¹ * (U (y + t) z - U y z)) (𝓝[>] 0)
      (𝓝 (U1 y z)) := fun z hz => by
    simpa [smul_eq_mul] using (hd.deriv z hz y hy).tendsto_slope_zero_right
  have hL : ∀ z ∈ Icc zl zh, Tendsto (fun t => t⁻¹ * (U y z - U (y - t) z)) (𝓝[>] 0)
      (𝓝 (U1 y z)) := fun z hz => by
    have h1 := (hd.deriv z hz y hy).tendsto_slope_zero_left.comp
      (by simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ))))
    refine h1.congr fun t => ?_
    simp only [Function.comp_apply, smul_eq_mul, inv_neg, ← sub_eq_add_neg]
    ring
  have hA : Tendsto (fun t => t⁻¹ * (U (y + t) zh - U y zh) - t⁻¹ * (U y zl - U (y - t) zl))
      (𝓝[>] 0) (𝓝 (U1 y zh - U1 y zl)) := (hR zh hzhZ).sub (hL zl hzlZ)
  have hD : Tendsto (fun t => ∫ z, t⁻¹ * (2 * U y z - U (y - t) z - U (y + t) z) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ _z : Icc zl zh, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B * (y / 2)⁻¹)
      ?_ ?_ (integrable_const _) ?_
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < y / 2 by linarith)] with t ht
      exact (((h.continuous_section hy.le).const_smul (2 : ℝ)).sub
        (h.continuous_section (by linarith [ht.2])) |>.sub
        (h.continuous_section (by linarith [ht.1]))).const_smul t⁻¹ |>.aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < y / 2 by linarith)] with t ht
      refine Eventually.of_forall fun z => ?_
      have hconc := (h.U_conc z.1 z.2).concaveOn
      have hmono := h.U_mono z.1 z.2
      have e1 := currency_concave_exchange hconc (p := y - t) (q := y) (r := y) (t := y + t)
        (mem_Ici.2 (by linarith [ht.2])) (mem_Ici.2 (by linarith [ht.1])) (by linarith [ht.1])
        (by linarith [ht.1]) (by ring)
      have e2 : U y z ≤ U (y + t) z := hmono.monotoneOn (mem_Ici.2 hy.le)
        (mem_Ici.2 (by linarith [ht.1])) (by linarith [ht.1])
      have e3 := currency_concave_left_slope_le hconc (a := y) ht.1 ht.2 (by linarith)
      have hB1 := abs_le.1 (hB y hy.le z z.2)
      have hB2 := abs_le.1 (hB (y - y / 2) (by linarith) z z.2)
      have hti : 0 < t⁻¹ := inv_pos.2 ht.1
      rw [Real.norm_eq_abs, abs_le]
      have hy2 : 0 < (y / 2)⁻¹ := inv_pos.2 (by linarith)
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left e1 hti.le, mul_le_mul_of_nonneg_left e2 hti.le]
      · nlinarith [mul_le_mul_of_nonneg_left e1 hti.le, mul_le_mul_of_nonneg_left e2 hti.le]
    · refine Eventually.of_forall fun z => ?_
      have := (hL z z.2).sub (hR z z.2)
      rw [sub_self] at this
      refine this.congr fun t => ?_
      ring
  rw [integral_zero] at hD
  have hBt : Tendsto (fun t => β * ∫ z, t⁻¹ * (2 * U y z - U (y - t) z - U (y + t) z) ∂μ)
      (𝓝[>] 0) (𝓝 (β * 0)) := hD.const_mul β
  rw [mul_zero] at hBt
  have hle : U1 y zh - U1 y zl ≤ 0 := by
    refine le_of_tendsto_of_tendsto hA hBt ?_
    filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
    have := hkey t ht.1 ht.2
    rw [integral_const_mul, ← mul_sub]
    have hti : 0 < t⁻¹ := inv_pos.2 ht.1
    nlinarith [mul_le_mul_of_nonneg_left this hti.le]
  have := hd.mono y hy hzlZ hzhZ hzlt
  linarith

/-- The optimal policy restricted to `X = [y, m̄]`. -/
noncomputable def cashPolicyX (μ : Measure (Icc zl zh)) (U : ℝ → ℝ → ℝ) (β y : ℝ) {mb : ℝ}
    (hy : 0 < y) (v : Ici (0 : ℝ) × Icc zl zh → ℝ) (m : Icc y mb) (z : Icc zl zh) : ℝ :=
  cashPolicy μ U β y v (⟨m, mem_Ici.2 (hy.le.trans m.2.1)⟩, z)

/-- **The household's policy has the properties used in part (i).** Under the assumptions of
§13.5 (with `z̲ < z̄`), let `v` solve (1) and let `m̄` be the smallest fixed point of `g(·, z̲)` in
`[y, ∞)` (part (f)). Then on `X = [y, m̄]` the policy is continuous (c), `≥ y`, nondecreasing in
`m` (e), nonincreasing in `z` (h), `g(m̄, z̲) = m̄`, `g(m, z̲) > m` on `[y, m̄)` and
`g(m̄, z̄) < m̄` when `y < m̄` (`cash_down`). -/
theorem cash_currencyPolicy (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    (hzlt : zl < zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {mb : ℝ} (hmb : y ≤ mb)
    (hfix : (cashPolicy μ U β y v
      (⟨mb, mem_Ici.2 (h.y_pos.le.trans hmb)⟩, ⟨zl, le_rfl, h.hz⟩) : ℝ) = mb)
    (hup : ∀ m : Ici (0 : ℝ), y ≤ (m : ℝ) → (m : ℝ) < mb →
      (m : ℝ) < cashPolicy μ U β y v (m, ⟨zl, le_rfl, h.hz⟩)) :
    CurrencyPolicy y mb zl zh (cashPolicyX μ U β y (mb := mb) h.y_pos v) := by
  have hy := h.y_pos
  refine ⟨hmb, h.hz, ?_, fun m z => (cashPolicy_spec μ h hv _).1,
    fun z m m' hmm' => cashPolicy_mono μ h hv z hmm', fun m => ex_13_5h μ h (hd.increasingDiff h)
      hv _, hfix, fun m hm => hup ⟨m, mem_Ici.2 (hy.le.trans m.2.1)⟩ m.2.1 hm,
    fun hlt => cash_down μ h hd hzlt hv hlt hfix⟩
  have hc : Continuous fun p : Icc y mb × Icc zl zh =>
      ((⟨(p.1 : ℝ), mem_Ici.2 (hy.le.trans p.1.2.1)⟩ : Ici (0 : ℝ)), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  exact continuous_subtype_val.comp ((ex_13_5c μ h hv).2.comp hc)

/-- **Exercises 13.5(i) and 13.5(j) for the currency economy.** Under the assumptions of §13.5
(`U` bounded, continuous, strictly increasing and strictly concave in `c`, differentiable in `c`
with `U₁(c, ·)` strictly increasing, `0 < β < 1`, `y > 0`, `z̲ < z̄`, and `μ` with positive mass
near both ends of `Z`, e.g. under the density condition), let `v` be the solution of (1), `g` its
policy and `m̄` the smallest fixed point of `g(·, z̲)` in `[y, ∞)`. The transition function on
`X = [y, m̄]` defined by `g` and `μ` is monotone and Feller and satisfies Assumption 12.1, it has
a unique invariant probability measure `λ*`, `T*ⁿλ₀ ⇒ λ*` for every `λ₀`, and for `M > 0` the
stationary price levels are exactly `p = M/∫ m λ*(dm)`. -/
theorem ex_13_5ij_economy (h : CurrencyHyp U β y zl zh) (hd : CurrencyDiffHyp U U1 zl zh)
    (hzlt : zl < zh) (hμ : CurrencyEndMass μ) {M : ℝ} (hM : 0 < M) :
    ∃ v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ,
      bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v ∧
      ∃ mb : ℝ, ∃ hP : CurrencyPolicy y mb zl zh (cashPolicyX μ U β y h.y_pos v),
        IsMonotoneTF (currencyPolicyKernel hP μ) ∧ IsFeller (currencyPolicyKernel hP μ) ∧
        ∃ lam : Measure (Icc y mb), IsProbabilityMeasure lam ∧
          adjointOp (currencyPolicyKernel hP μ) lam = lam ∧
          (∀ ν : Measure (Icc y mb), IsProbabilityMeasure ν →
            adjointOp (currencyPolicyKernel hP μ) ν = ν → ν = lam) ∧
          (∀ lam₀ : Measure (Icc y mb), IsProbabilityMeasure lam₀ →
            ConvWeak (fun n => (adjointOp (currencyPolicyKernel hP μ))^[n] lam₀) lam) ∧
          ∫ m, (m : ℝ) ∂lam = ∫ m, ∫ z, cashPolicyX μ U β y h.y_pos v m z ∂μ ∂lam ∧
          0 < ∫ m, (m : ℝ) ∂lam ∧
          ∀ p : ℝ, 0 < p → (∫ m, (m : ℝ) ∂lam = M / p ↔ p = M / ∫ m, (m : ℝ) ∂lam) := by
  obtain ⟨v, hv, -, -⟩ := ex_13_5a h μ
  obtain ⟨mb, hmb, hfix, hup⟩ := ex_13_5f μ h hv
  have hP := cash_currencyPolicy μ h hd hzlt hv hmb hfix hup
  obtain ⟨-, hM', hF, -, lam, hlam, hinv, huniq, hconv⟩ := ex_13_5i hP μ hμ
  have hj := fun p (hp : 0 < p) => ex_13_5j hP μ h.y_pos lam hinv hM hp
  exact ⟨v, hv, mb, hP, hM', hF, lam, hlam, hinv, huniq, hconv, (hj 1 one_pos).1,
    h.y_pos.trans_le (hj 1 one_pos).2.2.2, fun p hp => (hj p hp).2.2.1⟩

end StokeyLucasPrescott.ConvergenceApplications
