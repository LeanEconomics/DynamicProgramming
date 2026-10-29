/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalEquilibrium

/-!
# The uniform key renewal theorem (MT Theorem 14.5.2, Proposition 14.5.5)

Meyn and Tweedie, pp. 355–358. `renConv Γ f v t = ∫ f(t − u) (δ_v ∗ U)(du)` is the convolution of
`f` with the renewal measure started from a first epoch `v`.

* `renMeas_eq_bind`, `lintegral_renMeas`: `μ ∗ U` is the mixture `∫ μ(dv) δ_v ∗ U`;
  `renMeas_mono_smul`: `μ ≤ c ν` gives `μ ∗ U ≤ c (ν ∗ U)`.
* `renConv_shift`: `renConv Γ f v t = renConv Γ f 1 (t − v + 1)`.
* `exists_renConv_bound` (the bound (14.49)): `sup_{v > 0, t} δ_v ∗ U ∗ f(t) < ∞` for a bounded
  integrable `f ≥ 0` vanishing on `(−∞, 0)` with `f(t) → 0`.
* `truncLaw μ w = μ(0, w]⁻¹ μ|_{(0, w]}` (the truncation on p. 358); `convSupDiff_truncLaw_le` (the
  bound (14.48)); `tendsto_trunc_error`: the truncation errors vanish as `w → ∞`.
* **Proposition 14.5.5** (`proposition_14_5_5`, p. 357): for a spread-out `Γ` with finite mean,
  any two first-epoch laws on `(0, ∞)` (no moment condition) and `f` satisfying (14.37)–(14.39)
  and vanishing on `(−∞, 0)`, `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0`.
* `convAt_eqLaw`: `Γₑ ∗ U ∗ g(t) = β⁻¹ ∫_{s < t} g(s) ds`.
* **Theorem 14.5.2 (i)** (`theorem_14_5_2_i`, p. 355), (14.36):
  `sup_{|g| ≤ f} |Γ₀ ∗ U ∗ g(t) − β⁻¹ ∫ g| → 0`, from Proposition 14.5.5 with `Γ₂ = Γₑ`.
* **Theorem 14.5.2 (ii)** (`theorem_14_5_2_ii`, p. 355), (14.40):
  `sup_{B ⊆ [a, b]} |Γ₀ ∗ U(t + B) − β⁻¹ μ_Leb(B)| → 0`.
* **Theorem 14.5.1 for spread-out laws** (`theorem_14_5_1_spreadOut`, p. 354), (14.35):
  `Γ₀ ∗ U[a + t, b + t] → β⁻¹ (b − a)`.

**Added hypotheses.** First-epoch laws live on `(0, ∞)`, and `Γ(−∞, 0) = 0 < Γ(0, ∞)`. The test
bound `f` is nonnegative and vanishes on `(−∞, 0)`, as the book's `∫₀^∞` in (14.36) presupposes.
This module proves Theorem 14.5.1 only for spread-out `Γ`. The general non-lattice case, which
the book quotes from Feller, is `theorem_14_5_1` in `BlackwellRenewal`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- `v ↦ δ_v ∗ U` is measurable. -/
theorem measurable_renMeas_dirac_fun : Measurable fun v : ℝ => renMeas Γ (Measure.dirac v) :=
  Measure.measurable_of_measurable_coe _ fun _ hs => measurable_renMeas_dirac Γ hs

/-- `μ ∗ U = ∫ μ(dv) δ_v ∗ U`, as a bind. -/
theorem renMeas_eq_bind (μ : Measure ℝ) [SFinite μ] :
    renMeas Γ μ = μ.bind fun v => renMeas Γ (Measure.dirac v) := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_renMeas_dirac_fun Γ).aemeasurable,
    renMeas_eq_lintegral Γ μ hA]

/-- `∫ h d(μ ∗ U) = ∫ μ(dv) ∫ h d(δ_v ∗ U)`. -/
theorem lintegral_renMeas (μ : Measure ℝ) [SFinite μ] {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ u, h u ∂renMeas Γ μ = ∫⁻ v, ∫⁻ u, h u ∂renMeas Γ (Measure.dirac v) ∂μ := by
  rw [renMeas_eq_bind Γ μ, Measure.lintegral_bind (measurable_renMeas_dirac_fun Γ).aemeasurable
    hh.aemeasurable]

/-- `μ ≤ c ν` gives `μ ∗ U ≤ c (ν ∗ U)`. -/
theorem renMeas_mono_smul {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {c : ℝ≥0∞}
    (h : μ ≤ c • ν) : renMeas Γ μ ≤ c • renMeas Γ ν := by
  refine Measure.le_intro fun A hA _ => ?_
  rw [Measure.smul_apply, renMeas_eq_lintegral Γ μ hA, renMeas_eq_lintegral Γ ν hA, smul_eq_mul]
  calc ∫⁻ x, renMeas Γ (Measure.dirac x) A ∂μ ≤ ∫⁻ x, renMeas Γ (Measure.dirac x) A ∂(c • ν) :=
        lintegral_mono' h le_rfl
    _ = c * ∫⁻ x, renMeas Γ (Measure.dirac x) A ∂ν := by
        rw [lintegral_smul_measure, smul_eq_mul]

/-- `δ_v ∗ U ∗ f(t) = ∫ f(t − u) (δ_v ∗ U)(du)`, in `[0, ∞]`. -/
noncomputable def renConv (f : ℝ → ℝ) (v t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ (Measure.dirac v)

/-- `δ_v ∗ U` is `δ_1 ∗ U` shifted by `v − 1`. -/
theorem renMeas_dirac_eq_map (v : ℝ) :
    renMeas Γ (Measure.dirac v) = (renMeas Γ (Measure.dirac 1)).map fun u => u + (v - 1) := by
  ext A hA
  rw [Measure.map_apply (f := fun u => u + (v - 1)) (measurable_id.add measurable_const) hA,
    ← renMeas_dirac_add Γ 1 (v - 1) hA, add_sub_cancel]

/-- **Shift**: `renConv Γ f v t = renConv Γ f 1 (t − v + 1)`. -/
theorem renConv_shift {f : ℝ → ℝ} (hf : Measurable f) (v t : ℝ) :
    renConv Γ f v t = renConv Γ f 1 (t - v + 1) := by
  rw [renConv, renConv, renMeas_dirac_eq_map Γ v, lintegral_map
    (f := fun u => ENNReal.ofReal (f (t - u))) (g := fun u => u + (v - 1))
    (ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub measurable_id)))
    (measurable_id.add measurable_const)]
  refine lintegral_congr fun u => ?_
  congr 2
  ring

omit [IsProbabilityMeasure Γ] in
/-- For `f ≤ d` vanishing on `(−∞, 0)`, `δ_v ∗ U ∗ f(t) ≤ d δ_v ∗ U(−∞, t]`. -/
theorem renConv_le_Iic {f : ℝ → ℝ} (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (v t : ℝ) : renConv Γ f v t ≤ ENNReal.ofReal d * renMeas Γ (Measure.dirac v) (Iic t) := by
  rw [renConv, ← lintegral_indicator_const measurableSet_Iic]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ Iic t
  · rw [indicator_of_mem hu]; exact ENNReal.ofReal_le_ofReal (hfd _)
  · rw [indicator_of_notMem hu, hf0 _ (by simp only [mem_Iic, not_le] at hu; linarith),
      ENNReal.ofReal_zero]

/-- For `f ≥ 0` with `∫ f(t − u) ρ(du) < ∞`, `ρ ∗ f(t)` is the real value of that integral. -/
theorem convAt_eq_toReal {f : ℝ → ℝ} (hf : Measurable f) (hf0' : ∀ s, 0 ≤ f s) (ρ : Measure ℝ)
    (t : ℝ) : convAt ρ f t = (∫⁻ u, ENNReal.ofReal (f (t - u)) ∂ρ).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => hf0' _)
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable

omit [IsProbabilityMeasure Γ] in
/-- A level `w > 0` with `Γₑ(0, w] > 0`. -/
theorem exists_eqLaw_Ioc_pos (hΓpos : 0 < Γ (Ioi 0)) (hm : renMean Γ ≠ ∞) :
    ∃ w : ℝ, 0 < w ∧ 0 < eqLaw Γ (Ioc 0 w) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 0 < Γ (Ici ((j : ℝ) + 1)⁻¹) := by
    refine exists_measure_pos_of_iUnion (hΓpos.trans_le (measure_mono fun y hy => ?_))
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.1 hy)
    exact mem_iUnion.2 ⟨j, mem_Ici.2 (by rw [← one_div]; exact hj.le)⟩
  set w : ℝ := ((j : ℝ) + 1)⁻¹
  have hw : 0 < w := by positivity
  refine ⟨w, hw, ?_⟩
  rw [eqLaw, Measure.smul_apply, fwdSkelInv, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hm) ?_
  refine (lt_of_lt_of_le ?_ (setLIntegral_mono (measurable_tail_Ici Γ) fun s hs =>
    measure_mono (Ici_subset_Ici.2 hs.2))).ne'
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  exact ENNReal.mul_pos hj.ne' (ENNReal.ofReal_pos.2 hw).ne'

/-- **The bound (14.49)**: for a spread-out `Γ` on `[0, ∞)` with finite mean and a bounded
integrable measurable `f ≥ 0` vanishing on `(−∞, 0)` with `f(t) → 0`,
`sup_{v, t} δ_v ∗ U ∗ f(t) < ∞`. (For large `t`, `δ₁ ∗ U ∗ f(t)` is within `1` of
`Γₑ^w ∗ U ∗ f(t) ≤ Γₑ(0, w]⁻¹ m⁻¹ ∫ f`, by Proposition 14.5.4 and `Γₑ ∗ U = m⁻¹ μ_Leb`.) -/
theorem exists_renConv_bound (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : renMean Γ ≠ ∞) {f : ℝ → ℝ} (hf : Measurable f) (hf0' : ∀ s, 0 ≤ f s)
    (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d) (hlim : Tendsto f atTop (𝓝 0))
    (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    ∃ S : ℝ≥0∞, S ≠ ∞ ∧ ∀ v t, renConv Γ f v t ≤ S := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have hm0 : renMean Γ ≠ 0 := by
    refine (?_ : 0 < renMean Γ).ne'
    rw [renMean, lintegral_pos_iff_support ENNReal.measurable_ofReal]
    refine lt_of_lt_of_le hΓpos (measure_mono fun y hy => ?_)
    rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hy
  have hU : (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne'
  obtain ⟨w, hw, hpw⟩ := exists_eqLaw_Ioc_pos Γ hΓpos hm
  set p := eqLaw Γ (Ioc 0 w) with hpdef
  have hpt : p ≠ ∞ := measure_ne_top _ _
  set πw : Measure ℝ := p⁻¹ • (eqLaw Γ).restrict (Ioc 0 w) with hπw
  have hπwp : IsProbabilityMeasure πw := ⟨by
    rw [hπw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hpw.ne' hpt]⟩
  have hπw0 : πw (Iic 0) = 0 := by
    rw [hπw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Ioc 0 w = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [this, measure_empty, smul_zero]
  have hπwm : ∫⁻ x, ENNReal.ofReal x ∂πw ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal w ∂πw) ?_ (lintegral_mono_ae ?_)
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · have hmem : ∀ᵐ x ∂πw, x ∈ Ioc 0 w := by
        rw [hπw]
        exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
      filter_upwards [hmem] with x hx
      exact ENNReal.ofReal_le_ofReal hx.2
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (by norm_num)]
  have hdm : ∫⁻ x, ENNReal.ofReal x ∂Measure.dirac (1 : ℝ) ≠ ∞ := by
    rw [lintegral_dirac' _ ENNReal.measurable_ofReal]; exact ENNReal.ofReal_ne_top
  have hconv := proposition_14_5_4_renewal Γ hΓ0 hΓpos hs hm (Measure.dirac 1) πw hd1 hπw0 hdm
    hπwm hf hf0 hfd hlim
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hconv) 1 one_pos)
  set I := ∫⁻ s, ENNReal.ofReal (f s) with hI
  set S := (p⁻¹ * ((renMean Γ)⁻¹ * I) + 1) +
    ENNReal.ofReal d * (ENNReal.ofReal (Real.exp (T - 1)) *
      (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹) with hS
  have hfm : ∀ s : ℝ, Measurable fun u : ℝ => ENNReal.ofReal (f (s - u)) := fun s =>
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub measurable_id))
  have hbound1 : ∀ s, renConv Γ f 1 s ≤ S := fun s => by
    rcases le_or_gt T s with hsT | hsT
    · -- large `s`: compare with `Γₑ^w`
      have hloc1 : renConv Γ f 1 s ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU)
          (renMeas_dirac_Iic_le Γ 1 s))) (renConv_le_Iic Γ hf0 hfd 1 s)
      have hle2 : ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂renMeas Γ πw ≤
          p⁻¹ * ((renMean Γ)⁻¹ * I) := by
        have hmono := renMeas_mono_smul Γ (μ := πw) (ν := eqLaw Γ) (c := p⁻¹) (by
          rw [hπw]
          refine Measure.le_intro fun A _ _ => ?_
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
          exact mul_le_mul' le_rfl (Measure.restrict_le_self A))
        calc ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂renMeas Γ πw
            ≤ ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂(p⁻¹ • renMeas Γ (eqLaw Γ)) :=
              lintegral_mono' hmono le_rfl
          _ = p⁻¹ * ((renMean Γ)⁻¹ * ∫⁻ u in Ioi 0, ENNReal.ofReal (f (s - u))) := by
              rw [lintegral_smul_measure, renMeas_eqLaw Γ hΓ0 hΓpos hm, lintegral_smul_measure,
                smul_eq_mul, smul_eq_mul]
          _ ≤ p⁻¹ * ((renMean Γ)⁻¹ * I) := by
              refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
              refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
              exact lintegral_sub_left_eq_self (fun x => ENNReal.ofReal (f x)) s
      have hloc2 : ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂renMeas Γ πw ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hpw.ne')
          (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) hint)) hle2
      have htest : ENNReal.ofReal |convAt (renMeas Γ (Measure.dirac 1)) f s -
          convAt (renMeas Γ πw) f s| ≤ 1 := by
        refine le_trans ?_ (hT s hsT)
        exact le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s) =>
          ENNReal.ofReal |convAt (renMeas Γ (Measure.dirac 1)) g s - convAt (renMeas Γ πw) g s|)
          f ⟨hf, fun x => by rw [abs_of_nonneg (hf0' x)]⟩
      rw [convAt_eq_toReal hf hf0', convAt_eq_toReal hf hf0', ENNReal.ofReal_le_one] at htest
      have h1 : renConv Γ f 1 s ≤ ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂renMeas Γ πw + 1 := by
        rw [← ENNReal.ofReal_toReal hloc1, ← ENNReal.ofReal_toReal hloc2, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have := (abs_le.1 htest).2
        change (renConv Γ f 1 s).toReal - _ ≤ 1 at this
        linarith
      calc renConv Γ f 1 s ≤ ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂renMeas Γ πw + 1 := h1
        _ ≤ p⁻¹ * ((renMean Γ)⁻¹ * I) + 1 := add_le_add hle2 le_rfl
        _ ≤ S := le_self_add
    · -- small `s`: local finiteness
      calc renConv Γ f 1 s ≤ ENNReal.ofReal d * renMeas Γ (Measure.dirac 1) (Iic s) :=
            renConv_le_Iic Γ hf0 hfd 1 s
        _ ≤ ENNReal.ofReal d * (ENNReal.ofReal (Real.exp (T - 1)) *
              (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹) :=
            mul_le_mul' le_rfl ((renMeas_dirac_Iic_le Γ 1 s).trans (mul_le_mul'
              (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))) le_rfl))
        _ ≤ S := le_add_self
  refine ⟨S, ?_, fun v t => (le_of_eq (renConv_shift Γ hf v t)).trans (hbound1 _)⟩
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
    hpw.ne') (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) hint), ENNReal.one_ne_top⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU)⟩

/-! ### Truncation and Proposition 14.5.5 -/

/-- `sup_{|g| ≤ f}` satisfies the triangle inequality. -/
theorem convSupDiff_triangle (f : ℝ → ℝ) (ρ₁ ρ₂ ρ₃ : Measure ℝ) (t : ℝ) :
    convSupDiff f ρ₁ ρ₃ t ≤ convSupDiff f ρ₁ ρ₂ t + convSupDiff f ρ₂ ρ₃ t := by
  refine iSup₂_le fun g hg => ?_
  have h1 := le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s) =>
    ENNReal.ofReal |convAt ρ₁ g t - convAt ρ₂ g t|) g hg
  have h2 := le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s) =>
    ENNReal.ofReal |convAt ρ₂ g t - convAt ρ₃ g t|) g hg
  refine le_trans ?_ (add_le_add h1 h2)
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

/-- The truncation `μ^w = μ(0, w]⁻¹ μ|_{(0, w]}`. -/
noncomputable def truncLaw (μ : Measure ℝ) (w : ℝ) : Measure ℝ :=
  (μ (Ioc 0 w))⁻¹ • μ.restrict (Ioc 0 w)

/-- `μ + (μ(0, w]⁻¹ − 1) μ|_{(0, w]} = μ^w + μ|_{(w, ∞)}` for `μ` on `(0, ∞)`. -/
theorem add_eq_truncLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) {w : ℝ}
    (hw : 0 ≤ w) :
    μ + ((μ (Ioc 0 w))⁻¹ - 1) • μ.restrict (Ioc 0 w) = truncLaw μ w + μ.restrict (Ioi w) := by
  have hp1 : 1 ≤ (μ (Ioc 0 w))⁻¹ := ENNReal.one_le_inv.2 prob_le_one
  have hsplit : μ = μ.restrict (Ioc 0 w) + μ.restrict (Ioi w) := by
    have hI : Ioi (0 : ℝ) = Ioc 0 w ∪ Ioi w := (Ioc_union_Ioi_eq_Ioi hw).symm
    rw [← Measure.restrict_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi, ← hI]
    refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
    rw [ae_iff]
    exact measure_mono_null (fun x hx => (not_lt.1 (show ¬ (0 : ℝ) < x from hx) : x ≤ 0)) hμ
  set c := (μ (Ioc 0 w))⁻¹ - 1
  calc μ + c • μ.restrict (Ioc 0 w)
      = (μ.restrict (Ioc 0 w) + μ.restrict (Ioi w)) + c • μ.restrict (Ioc 0 w) := by
        rw [← hsplit]
    _ = (1 + c) • μ.restrict (Ioc 0 w) + μ.restrict (Ioi w) := by
        rw [add_smul, one_smul]; abel
    _ = truncLaw μ w + μ.restrict (Ioi w) := by
        rw [add_tsub_cancel_of_le hp1, truncLaw]

/-- `sup_{|g| ≤ f}` is symmetric. -/
theorem convSupDiff_comm (f : ℝ → ℝ) (ρ₁ ρ₂ : Measure ℝ) (t : ℝ) :
    convSupDiff f ρ₁ ρ₂ t = convSupDiff f ρ₂ ρ₁ t := by
  unfold convSupDiff
  simp_rw [abs_sub_comm (convAt ρ₁ _ t)]

/-- **The truncation bound (14.48)**: if `δ_v ∗ U ∗ f ≤ S` everywhere, then
`sup_{|g| ≤ f} |μ ∗ U ∗ g(t) − μ^w ∗ U ∗ g(t)| ≤ S (μ(w, ∞) + (μ(0, w]⁻¹ − 1) μ(0, w])`. -/
theorem convSupDiff_truncLaw_le {f : ℝ → ℝ} (hf : Measurable f) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) {w : ℝ} (hw : 0 ≤ w) (hp : 0 < μ (Ioc 0 w))
    {S : ℝ≥0∞} (hSt : S ≠ ∞) (hS : ∀ v t, renConv Γ f v t ≤ S) (t : ℝ) :
    convSupDiff f (renMeas Γ μ) (renMeas Γ (truncLaw μ w)) t ≤
      S * (μ (Ioi w) + ((μ (Ioc 0 w))⁻¹ - 1) * μ (Ioc 0 w)) := by
  set c := (μ (Ioc 0 w))⁻¹ - 1 with hc
  have hheq := add_eq_truncLaw μ hμ hw
  have hct : c ≠ ∞ := ENNReal.sub_ne_top (ENNReal.inv_ne_top.2 hp.ne')
  have hTp : IsProbabilityMeasure (truncLaw μ w) := ⟨by
    rw [truncLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)]⟩
  have heq : renMeas Γ μ + renMeas Γ (c • μ.restrict (Ioc 0 w)) =
      renMeas Γ (truncLaw μ w) + renMeas Γ (μ.restrict (Ioi w)) := by
    rw [← renMeas_add, ← renMeas_add, hheq]
  have hm : Measurable fun u : ℝ => ENNReal.ofReal (f (t - u)) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub measurable_id))
  have hint : ∀ (ρ : Measure ℝ) [SFinite ρ], ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ ρ ≤
      S * ρ univ := fun ρ _ => by
    rw [lintegral_renMeas Γ ρ hm]
    calc ∫⁻ v, ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ (Measure.dirac v) ∂ρ
        ≤ ∫⁻ _, S ∂ρ := lintegral_mono fun v => hS v t
      _ = S * ρ univ := lintegral_const S
  have hfin : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ ρ ≠ ∞ := fun ρ _ =>
    ne_top_of_le_ne_top (by rw [measure_univ, mul_one]; exact hSt) (hint ρ)
  refine (convSupDiff_le heq (hfin μ) (hfin _)).trans ?_
  calc ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ (μ.restrict (Ioi w)) +
        ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ (c • μ.restrict (Ioc 0 w))
      ≤ S * (μ.restrict (Ioi w)) univ + S * (c • μ.restrict (Ioc 0 w)) univ :=
        add_le_add (hint _) (hint _)
    _ = S * (μ (Ioi w) + c * μ (Ioc 0 w)) := by
        rw [Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ,
          smul_eq_mul, mul_add]

/-- The truncation errors vanish: `μ(n, ∞) + (μ(0, n]⁻¹ − 1) μ(0, n] → 0` and `μ(0, n] → 1`. -/
theorem tendsto_trunc_error (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) :
    Tendsto (fun n : ℕ => μ (Ioc 0 (n : ℝ))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => μ (Ioi (n : ℝ)) + ((μ (Ioc 0 (n : ℝ)))⁻¹ - 1) * μ (Ioc 0 (n : ℝ)))
        atTop (𝓝 0) := by
  have hmono : Monotone fun n : ℕ => Ioc (0 : ℝ) n := fun m n hmn =>
    Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have hU : ⋃ n : ℕ, Ioc (0 : ℝ) n = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨n, h, -⟩; exact h
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx, hn⟩
  have h1 : μ (Ioi 0) = 1 := by
    rw [← compl_Iic, prob_compl_eq_one_iff measurableSet_Iic]; exact hμ
  have hp : Tendsto (fun n : ℕ => μ (Ioc 0 (n : ℝ))) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hU, h1] at h
  have hanti : Antitone fun n : ℕ => Ioi (n : ℝ) := fun m n hmn =>
    Ioi_subset_Ioi (by exact_mod_cast hmn)
  have hI : ⋂ n : ℕ, Ioi (n : ℝ) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, hn⟩
  have hq : Tendsto (fun n : ℕ => μ (Ioi (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Ioi.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rwa [hI, measure_empty] at h
  have hinv : Tendsto (fun n : ℕ => (μ (Ioc 0 (n : ℝ)))⁻¹) atTop (𝓝 1) := by
    have h := tendsto_inv_iff.2 hp
    rwa [inv_one] at h
  have hsub := ENNReal.Tendsto.sub hinv (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
    (Or.inl ENNReal.one_ne_top)
  rw [tsub_self] at hsub
  have hmul := ENNReal.Tendsto.mul hsub (Or.inr ENNReal.one_ne_top) hp (Or.inl one_ne_zero)
  rw [zero_mul] at hmul
  have hadd := hq.add hmul
  rw [add_zero] at hadd
  exact ⟨hp, hadd⟩

/-- `μ^w` lives on `(0, w]`, so it has finite mean and does not charge `(−∞, 0]`. -/
theorem truncLaw_props (μ : Measure ℝ) (w : ℝ) :
    truncLaw μ w (Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal x ∂truncLaw μ w ≤
      ENNReal.ofReal w * truncLaw μ w univ := by
  constructor
  · rw [truncLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Ioc 0 w = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [this, measure_empty, smul_zero]
  · rw [← lintegral_const]
    refine lintegral_mono_ae ?_
    have hmem : ∀ᵐ x ∂truncLaw μ w, x ∈ Ioc 0 w := by
      rw [truncLaw]
      exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
    filter_upwards [hmem] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2

/-- **Proposition 14.5.5** (MT p. 357): for a spread-out `Γ` on `[0, ∞)` with finite mean, any two
first-epoch laws `Γ₁, Γ₂` on `(0, ∞)` and a bounded integrable measurable `f ≥ 0` vanishing on
`(−∞, 0)` with `f(t) → 0`, `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0`. -/
theorem proposition_14_5_5 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : renMean Γ ≠ ∞) (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : μ₁ (Iic 0) = 0) (h₂ : μ₂ (Iic 0) = 0) {f : ℝ → ℝ} (hf : Measurable f)
    (hf0' : ∀ s, 0 ≤ f s) (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (hlim : Tendsto f atTop (𝓝 0)) (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (convSupDiff f (renMeas Γ μ₁) (renMeas Γ μ₂)) atTop (𝓝 0) := by
  obtain ⟨S, hSt, hS⟩ := exists_renConv_bound Γ hΓ0 hΓpos hs hm hf hf0' hf0 hfd hlim hint
  obtain ⟨hp₁, he₁⟩ := tendsto_trunc_error μ₁ h₁
  obtain ⟨hp₂, he₂⟩ := tendsto_trunc_error μ₂ h₂
  have he := ENNReal.Tendsto.const_mul (he₁.add he₂) (a := S) (Or.inr hSt)
  rw [add_zero, mul_zero] at he
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- a truncation level with small errors and positive masses
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 he (ε / 2) hε2).and
    (((tendsto_order.1 hp₁).1 0 one_pos).and ((tendsto_order.1 hp₂).1 0 one_pos))).exists
  obtain ⟨hne, hpos₁, hpos₂⟩ := hn
  have hw : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT₁ : IsProbabilityMeasure (truncLaw μ₁ n) := ⟨by
    rw [truncLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos₁.ne' (measure_ne_top _ _)]⟩
  have hT₂ : IsProbabilityMeasure (truncLaw μ₂ n) := ⟨by
    rw [truncLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos₂.ne' (measure_ne_top _ _)]⟩
  obtain ⟨hz₁, hm₁⟩ := truncLaw_props μ₁ (n : ℝ)
  obtain ⟨hz₂, hm₂⟩ := truncLaw_props μ₂ (n : ℝ)
  rw [measure_univ, mul_one] at hm₁ hm₂
  have hmid := proposition_14_5_4_renewal Γ hΓ0 hΓpos hs hm (truncLaw μ₁ n) (truncLaw μ₂ n) hz₁ hz₂
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm₁) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm₂)
    hf hf0 hfd hlim
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hmid) (ε / 2) hε2] with t ht
  calc convSupDiff f (renMeas Γ μ₁) (renMeas Γ μ₂) t
      ≤ convSupDiff f (renMeas Γ μ₁) (renMeas Γ (truncLaw μ₁ n)) t +
          convSupDiff f (renMeas Γ (truncLaw μ₁ n)) (renMeas Γ μ₂) t :=
        convSupDiff_triangle f _ _ _ t
    _ ≤ convSupDiff f (renMeas Γ μ₁) (renMeas Γ (truncLaw μ₁ n)) t +
          (convSupDiff f (renMeas Γ (truncLaw μ₁ n)) (renMeas Γ (truncLaw μ₂ n)) t +
            convSupDiff f (renMeas Γ (truncLaw μ₂ n)) (renMeas Γ μ₂) t) :=
        add_le_add le_rfl (convSupDiff_triangle f _ _ _ t)
    _ ≤ S * (μ₁ (Ioi (n : ℝ)) + ((μ₁ (Ioc 0 (n : ℝ)))⁻¹ - 1) * μ₁ (Ioc 0 (n : ℝ))) +
          (ε / 2 + S * (μ₂ (Ioi (n : ℝ)) +
            ((μ₂ (Ioc 0 (n : ℝ)))⁻¹ - 1) * μ₂ (Ioc 0 (n : ℝ)))) := by
        refine add_le_add (convSupDiff_truncLaw_le Γ hf μ₁ h₁ hw hpos₁ hSt hS t)
          (add_le_add ht ?_)
        rw [convSupDiff_comm]
        exact convSupDiff_truncLaw_le Γ hf μ₂ h₂ hw hpos₂ hSt hS t
    _ = ε / 2 + S * ((μ₁ (Ioi (n : ℝ)) + ((μ₁ (Ioc 0 (n : ℝ)))⁻¹ - 1) * μ₁ (Ioc 0 (n : ℝ))) +
          (μ₂ (Ioi (n : ℝ)) + ((μ₂ (Ioc 0 (n : ℝ)))⁻¹ - 1) * μ₂ (Ioc 0 (n : ℝ)))) := by
        rw [mul_add]; ring
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hne
    _ = ε := ENNReal.add_halves ε

/-! ### Theorem 14.5.2 and the spread-out case of Theorem 14.5.1 -/

/-- The equilibrium convolution: `Γₑ ∗ U ∗ g(t) = m⁻¹ ∫_{s < t} g(s) ds`. -/
theorem convAt_eqLaw (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hm : renMean Γ ≠ ∞)
    (g : ℝ → ℝ) (t : ℝ) :
    convAt (renMeas Γ (eqLaw Γ)) g t = ((renMean Γ)⁻¹).toReal * ∫ s in Iio t, g s := by
  rw [convAt, renMeas_eqLaw Γ hΓ0 hΓpos hm, integral_smul_measure, smul_eq_mul,
    ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Iio]
  congr 1
  have e : (Ioi 0).indicator (fun u => g (t - u)) = fun u => (Iio t).indicator g (t - u) := by
    funext u
    by_cases hu : 0 < u
    · rw [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu),
        indicator_of_mem (show t - u ∈ Iio t by simp only [mem_Iio]; linarith)]
    · rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu),
        indicator_of_notMem (show t - u ∉ Iio t by
          simp only [mem_Iio, not_lt]; linarith [not_lt.1 hu])]
  rw [e]
  exact integral_sub_left_eq_self ((Iio t).indicator g) volume t

/-- The tail `∫_{s ≥ t} f(s) ds → 0` for an integrable `f`. -/
theorem tendsto_setLIntegral_Ici {f : ℝ → ℝ} (hf : Measurable f)
    (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (fun t => ∫⁻ s in Ici t, ENNReal.ofReal (f s)) atTop (𝓝 0) := by
  have hF : Measurable fun s => ENNReal.ofReal (f s) := ENNReal.measurable_ofReal.comp hf
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun t s => (Ici t).indicator (fun s => ENNReal.ofReal (f s)) s) (f := fun _ => 0)
    (fun s => ENNReal.ofReal (f s)) (Eventually.of_forall fun t => hF.indicator measurableSet_Ici)
    (Eventually.of_forall fun t => Eventually.of_forall fun s =>
      indicator_le_self' (fun _ _ => zero_le) s) hint
    (Eventually.of_forall fun s => tendsto_const_nhds.congr' (eventually_atTop.2 ⟨s + 1,
      fun t ht => (indicator_of_notMem (show s ∉ Ici t by
        simp only [mem_Ici, not_le]; linarith) _).symm⟩))
  rw [lintegral_zero] at h
  refine h.congr fun t => ?_
  rw [lintegral_indicator measurableSet_Ici]

/-- **Theorem 14.5.2 (i)** (MT p. 355), (14.36): for a spread-out `Γ` on `[0, ∞)` with finite mean
`β`, every first-epoch law `Γ₀` on `(0, ∞)` and every bounded integrable measurable `f ≥ 0`
vanishing on `(−∞, 0)` with `f(t) → 0` ((14.37)–(14.39)),
`sup_{|g| ≤ f} |Γ₀ ∗ U ∗ g(t) − β⁻¹ ∫ g| → 0`. -/
theorem theorem_14_5_2_i (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : renMean Γ ≠ ∞) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0' : ∀ s, 0 ≤ f s) (hf0 : ∀ s < 0, f s = 0) {d : ℝ}
    (hfd : ∀ s, f s ≤ d) (hlim : Tendsto f atTop (𝓝 0)) (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (fun t => ⨆ (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s),
      ENNReal.ofReal |convAt (renMeas Γ μ) g t - ((renMean Γ).toReal)⁻¹ * ∫ s, g s|)
      atTop (𝓝 0) := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have h55 := proposition_14_5_5 Γ hΓ0 hΓpos hs hm μ (eqLaw Γ) hμ (eqLaw_Iic_zero Γ) hf hf0'
    hf0 hfd hlim hint
  have htail := ENNReal.Tendsto.const_mul (tendsto_setLIntegral_Ici hf hint)
    (a := ENNReal.ofReal ((renMean Γ).toReal)⁻¹) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at htail
  have hsum := h55.add htail
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun t => iSup₂_le fun g hg => ?_
  have hgb : ∀ s, ENNReal.ofReal |g s| ≤ ENNReal.ofReal (f s) := fun s =>
    ENNReal.ofReal_le_ofReal (hg.2 s)
  have hgi : Integrable g volume := integrable_of_ofReal_abs_le hg.1 hgb hint
  have h1 : ENNReal.ofReal |convAt (renMeas Γ μ) g t - convAt (renMeas Γ (eqLaw Γ)) g t| ≤
      convSupDiff f (renMeas Γ μ) (renMeas Γ (eqLaw Γ)) t :=
    le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s) =>
      ENNReal.ofReal |convAt (renMeas Γ μ) g t - convAt (renMeas Γ (eqLaw Γ)) g t|) g hg
  have h2 : ENNReal.ofReal |convAt (renMeas Γ (eqLaw Γ)) g t -
      ((renMean Γ).toReal)⁻¹ * ∫ s, g s| ≤
      ENNReal.ofReal ((renMean Γ).toReal)⁻¹ * ∫⁻ s in Ici t, ENNReal.ofReal (f s) := by
    rw [convAt_eqLaw Γ hΓ0 hΓpos hm g t, ENNReal.toReal_inv,
      ← integral_add_compl measurableSet_Iio hgi, compl_Iio, mul_add, sub_add_cancel_left,
      abs_neg, abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg)]
    exact mul_le_mul' le_rfl (ofReal_abs_integral_le_lintegral (μ := volume.restrict (Ici t)) hgb)
  calc ENNReal.ofReal |convAt (renMeas Γ μ) g t - ((renMean Γ).toReal)⁻¹ * ∫ s, g s|
      ≤ ENNReal.ofReal |convAt (renMeas Γ μ) g t - convAt (renMeas Γ (eqLaw Γ)) g t| +
          ENNReal.ofReal |convAt (renMeas Γ (eqLaw Γ)) g t -
            ((renMean Γ).toReal)⁻¹ * ∫ s, g s| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ := add_le_add h1 h2

/-- **Theorem 14.5.2 (ii)** (MT p. 355), (14.40): for a spread-out `Γ` with finite mean `β` and a
first-epoch law `Γ₀` on `(0, ∞)`, `sup_{B ⊆ [a, b]} |Γ₀ ∗ U(t + B) − β⁻¹ μ_Leb(B)| → 0`. -/
theorem theorem_14_5_2_ii (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : renMean Γ ≠ ∞) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0)
    (a b : ℝ) :
    Tendsto (fun t => ⨆ (B : Set ℝ) (_ : MeasurableSet B ∧ B ⊆ Icc a b),
      ENNReal.ofReal |(renMeas Γ μ).real {u | u - t ∈ B} -
        ((renMean Γ).toReal)⁻¹ * volume.real B|) atTop (𝓝 0) := by
  set f : ℝ → ℝ := (Icc 0 (b - a)).indicator 1 with hfdef
  have hf : Measurable f := measurable_one.indicator measurableSet_Icc
  have hf0' : ∀ s, 0 ≤ f s := fun s => indicator_nonneg (fun _ _ => zero_le_one) s
  have hf0 : ∀ s < 0, f s = 0 := fun s hs =>
    indicator_of_notMem (fun h => absurd h.1 (not_le.2 hs)) _
  have hfd : ∀ s, f s ≤ 1 := fun s => by
    by_cases h : s ∈ Icc 0 (b - a)
    · rw [hfdef, indicator_of_mem h, Pi.one_apply]
    · rw [hfdef, indicator_of_notMem h]; exact zero_le_one
  have hlim : Tendsto f atTop (𝓝 0) := tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨b - a + 1, fun s hs => (indicator_of_notMem (fun h => by linarith [h.2]) _).symm⟩)
  have hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞ := by
    have e : (fun s => ENNReal.ofReal (f s)) = (Icc 0 (b - a)).indicator 1 := by
      funext s
      by_cases h : s ∈ Icc 0 (b - a)
      · rw [hfdef, indicator_of_mem h, indicator_of_mem h, Pi.one_apply, Pi.one_apply,
          ENNReal.ofReal_one]
      · rw [hfdef, indicator_of_notMem h, indicator_of_notMem h, ENNReal.ofReal_zero]
    rw [e, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact theorem_14_5_2_ii_of_i (renMeas Γ μ) _
    (theorem_14_5_2_i Γ hΓ0 hΓpos hs hm μ hμ hf hf0' hf0 hfd hlim hint)

/-- **Theorem 14.5.1** for spread-out laws (MT p. 354), (14.35): for a spread-out `Γ` with finite
mean `β`, a first-epoch law `Γ₀` on `(0, ∞)` and `a ≤ b`, `Γ₀ ∗ U[a + t, b + t] → β⁻¹ (b − a)`
(a consequence of (14.40)). -/
theorem theorem_14_5_1_spreadOut (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hs : IsSpreadOut Γ) (hm : renMean Γ ≠ ∞) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iic 0) = 0) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun t => (renMeas Γ μ).real (Icc (a + t) (b + t))) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * (b - a))) := by
  have h := theorem_14_5_2_ii Γ hΓ0 hΓpos hs hm μ hμ a b
  have hle : ∀ t, ENNReal.ofReal |(renMeas Γ μ).real (Icc (a + t) (b + t)) -
      ((renMean Γ).toReal)⁻¹ * (b - a)| ≤ ⨆ (B : Set ℝ) (_ : MeasurableSet B ∧ B ⊆ Icc a b),
        ENNReal.ofReal |(renMeas Γ μ).real {u | u - t ∈ B} -
          ((renMean Γ).toReal)⁻¹ * volume.real B| := fun t => by
    have e1 : {u : ℝ | u - t ∈ Icc a b} = Icc (a + t) (b + t) := by
      ext u; simp only [mem_ofPred_eq, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have e2 : volume.real (Icc a b) = b - a := by
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
    have := le_iSup₂ (f := fun (B : Set ℝ) (_ : MeasurableSet B ∧ B ⊆ Icc a b) =>
      ENNReal.ofReal |(renMeas Γ μ).real {u | u - t ∈ B} -
        ((renMean Γ).toReal)⁻¹ * volume.real B|) (Icc a b) ⟨measurableSet_Icc, subset_rfl⟩
    rwa [e1, e2] at this
  have h0 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hle
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using h1

end MeynTweedie.FErgodicity
