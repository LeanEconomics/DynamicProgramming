/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalUniform

/-!
# Absolutely continuous first epochs: Theorem 14.5.2 (iii) (MT §14.5)

Meyn and Tweedie, Theorem 14.5.2 (iii) (p. 355) and its proof on p. 358.

* `tendsto_lintegral_sub_of_ac` (the step (14.50)): for a finite measure `σ ≪ μ_Leb` and a bounded
  integrable `f`, `∫ f(t − u) σ(du) → 0` as `t → ∞`, without (14.39).
* `renMeas_absolutelyContinuous` (p. 358, quoted from Feller): if `Γ₀ ≪ μ_Leb` then
  `Γ₀ ∗ U ≪ μ_Leb`, for every increment law `Γ`.
* `exists_coupling_le`: in `ρ₁ + σ₂ = ρ₂ + σ₁` with `σ₁, σ₂` finite, the pair `σ₁, σ₂` can be
  replaced by the Jordan parts `α ≤ ρ₁`, `β ≤ ρ₂` of `σ₁ − σ₂`.
* **Proposition 14.5.4 without (14.39)** (`proposition_14_5_4_ac`, p. 358): for first-epoch laws
  `Γ₁, Γ₂ ≪ μ_Leb` with finite means and a bounded integrable `f` vanishing on `(−∞, 0)`,
  `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0`.
* `smoothFn`, `smoothBound`: the smoothings `Γ₀ ⋆ g(s) = ∫ g(s − u) Γ₀(du)`;
  `sFinite_renMeas`: `μ ∗ U` is s-finite; `renMeas_eq_map_prod`: `Γ₀ ∗ U` is the image of
  `Γ₀ ⊗ (δ₁ ∗ U)` under `(v, u) ↦ u + v − 1`;
  `convAt_renMeas_eq_smooth`: `Γ₀ ∗ U ∗ g(t) = δ₁ ∗ U ∗ (Γ₀ ⋆ g)(t + 1)`.
* **Theorem 14.5.2 (iii)** (`theorem_14_5_2_iii`, p. 355): for a spread-out `Γ` with finite mean
  `β` and an absolutely continuous first-epoch law `Γ₀` on `(0, ∞)`, the uniform convergence
  (14.36) holds for every bounded integrable `f ≥ 0` vanishing on `(−∞, 0)`, without (14.39).

**Correction.** The book obtains (iii) from Proposition 14.5.4 without (14.39) "by the truncation
argument of Proposition 14.5.5". That argument needs `sup_x U ∗ f(x) < ∞`, which (14.49) derives
from Proposition 14.5.4 with `Γ₁ = δ₀`; that use needs (14.39), and `δ₀` is not absolutely
continuous. We argue differently. The smoothing `F = Γ₀ ⋆ f` is bounded and integrable, vanishes on
`(−∞, 0)`, and tends to `0` by (14.50). It therefore satisfies (14.37)–(14.39). For `|g| ≤ f`, the
smoothing `G = Γ₀ ⋆ g` has `|G| ≤ F`, `∫ G = ∫ g`, and `Γ₀ ∗ U ∗ g(t) = δ₁ ∗ U ∗ G(t + 1)`. So (iii)
is part (i) for the first epoch `δ₁` and the bound `F`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ### The step (14.50) -/

/-- **The step (14.50)**: for a finite measure `σ ≪ μ_Leb` and a measurable `f ≤ d` with
`∫ f⁺ < ∞`, `∫ f(t − u)⁺ σ(du) → 0` as `t → ∞`. The set where `f(t − u) ≥ η` and `u ≤ n` has
Lebesgue measure at most `η⁻¹ ∫_{s ≥ t − n} f⁺`, hence small `σ`-measure. -/
theorem tendsto_lintegral_sub_of_ac {σ : Measure ℝ} [IsFiniteMeasure σ] (hσ : σ ≪ volume)
    {f : ℝ → ℝ} (hf : Measurable f) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (fun t => ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ) atTop (𝓝 0) := by
  set D := ENNReal.ofReal d with hD
  set ρ := σ.rnDeriv volume with hρ
  have hσeq : volume.withDensity ρ = σ := Measure.withDensity_rnDeriv_eq σ volume hσ
  have hhint : ∫⁻ x, ρ x ≠ ∞ := by
    have e := withDensity_apply ρ MeasurableSet.univ (μ := volume)
    rw [hσeq, Measure.restrict_univ] at e
    rw [← e]
    exact measure_ne_top σ univ
  -- the sets `A n t = {u ≤ n : f(t − u) ≥ (n + 1)⁻¹}`
  set A : ℕ → ℝ → Set ℝ := fun n t => {u | u ≤ n ∧ ((n : ℝ) + 1)⁻¹ ≤ f (t - u)} with hA
  have hAm : ∀ n t, MeasurableSet (A n t) := fun n t =>
    (measurableSet_le measurable_id measurable_const).inter
      (measurableSet_le measurable_const (hf.comp (measurable_const.sub measurable_id)))
  have hpt : ∀ (n : ℕ) (t u : ℝ), ENNReal.ofReal (f (t - u)) ≤
      (Ioi (n : ℝ)).indicator (fun _ => D) u + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ +
        (A n t).indicator (fun _ => D) u := fun n t u => by
    by_cases hu : u ∈ Ioi (n : ℝ)
    · rw [indicator_of_mem hu]
      exact le_add_right ((ENNReal.ofReal_le_ofReal (hfd _)).trans le_self_add)
    · by_cases hv : ((n : ℝ) + 1)⁻¹ ≤ f (t - u)
      · have hmem : u ∈ A n t := ⟨not_lt.1 hu, hv⟩
        rw [indicator_of_mem hmem]
        exact (ENNReal.ofReal_le_ofReal (hfd _)).trans le_add_self
      · exact le_add_right ((ENNReal.ofReal_le_ofReal (not_le.1 hv).le).trans le_add_self)
  have hbd : ∀ (n : ℕ) (t : ℝ), ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ ≤
      (D * σ (Ioi (n : ℝ)) + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * σ univ) + D * σ (A n t) := by
    intro n t
    refine (lintegral_mono (hpt n t)).trans (le_of_eq ?_)
    rw [lintegral_add_right _ (measurable_const.indicator (hAm n t)),
      lintegral_add_right _ measurable_const, lintegral_indicator_const measurableSet_Ioi,
      lintegral_const, lintegral_indicator_const (hAm n t)]
  -- the constant part vanishes as `n → ∞`
  have hc : Tendsto (fun n : ℕ => D * σ (Ioi (n : ℝ)) + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * σ univ)
      atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => Ioi (n : ℝ) := fun m n hmn =>
      Ioi_subset_Ioi (by exact_mod_cast hmn)
    have hI : ⋂ n : ℕ, Ioi (n : ℝ) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hn⟩
    have h1 : Tendsto (fun n : ℕ => σ (Ioi (n : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := σ)
        (fun n => measurableSet_Ioi.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rwa [hI, measure_empty] at h
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    have h3 := (ENNReal.Tendsto.const_mul h1 (a := D) (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.mul_const h2 (Or.inr (measure_ne_top σ univ)))
    rwa [mul_zero, zero_mul, add_zero] at h3
  -- for fixed `n`, the variable part vanishes as `t → ∞`
  have hvar : ∀ n : ℕ, Tendsto (fun t => D * σ (A n t)) atTop (𝓝 0) := fun n => by
    set η : ℝ := ((n : ℝ) + 1)⁻¹ with hη
    have hηpos : 0 < η := inv_pos.2 (by positivity)
    have h0 : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.2 hηpos).ne'
    have hF : Measurable fun s => ENNReal.ofReal (f s) := ENNReal.measurable_ofReal.comp hf
    set I : ℝ → ℝ≥0∞ := fun t => ∫⁻ s in Ici (t + -(n : ℝ)), ENNReal.ofReal (f s) with hIdef
    have hI : Tendsto I atTop (𝓝 0) := (tendsto_setLIntegral_Ici hf hint).comp
      (tendsto_atTop_add_const_right atTop (-(n : ℝ)) tendsto_id)
    have hvol : ∀ t, volume (A n t) ≤ (ENNReal.ofReal η)⁻¹ * I t := fun t => by
      set C : Set ℝ := {s | ENNReal.ofReal η ≤ ENNReal.ofReal (f s)} with hC
      have hCm : MeasurableSet C := measurableSet_le measurable_const hF
      have hsub : A n t ⊆ (fun u => t - u) ⁻¹' (C ∩ Ici (t + -(n : ℝ))) := fun u hu =>
        ⟨ENNReal.ofReal_le_ofReal hu.2, by
          change t + -(n : ℝ) ≤ t - u
          linarith [hu.1]⟩
      have hpres := (Measure.measurePreserving_sub_left volume t).measure_preimage
        (hCm.inter (measurableSet_Ici (a := t + -(n : ℝ)))).nullMeasurableSet
      have hmk := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (Ici (t + -(n : ℝ))))
        hF.aemeasurable (ENNReal.ofReal η)
      rw [Measure.restrict_apply hCm] at hmk
      calc volume (A n t) ≤ volume (C ∩ Ici (t + -(n : ℝ))) := (measure_mono hsub).trans
            (le_of_eq hpres)
        _ = (ENNReal.ofReal η)⁻¹ * ENNReal.ofReal η * volume (C ∩ Ici (t + -(n : ℝ))) := by
            rw [ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]
        _ = (ENNReal.ofReal η)⁻¹ * (ENNReal.ofReal η * volume (C ∩ Ici (t + -(n : ℝ)))) :=
            mul_assoc _ _ _
        _ ≤ (ENNReal.ofReal η)⁻¹ * I t := mul_le_mul' le_rfl hmk
    have hupper := ENNReal.Tendsto.const_mul hI (a := (ENNReal.ofReal η)⁻¹)
      (Or.inr (ENNReal.inv_ne_top.2 h0))
    rw [mul_zero] at hupper
    have hvol0 : Tendsto (fun t => volume (A n t)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le) hvol
    have hσA : Tendsto (fun t => σ (A n t)) atTop (𝓝 0) := by
      have h := tendsto_setLIntegral_zero hhint (s := A n) (l := atTop) hvol0
      refine h.congr fun t => ?_
      rw [← withDensity_apply ρ (hAm n t), hσeq]
    have h := ENNReal.Tendsto.const_mul hσA (a := D) (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at h
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hc) (ε / 2) hε2).exists
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hvar n)) (ε / 2) hε2] with t ht
  calc ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ
      ≤ (D * σ (Ioi (n : ℝ)) + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * σ univ) + D * σ (A n t) :=
        hbd n t
    _ ≤ ε / 2 + ε / 2 := add_le_add hn ht
    _ = ε := ENNReal.add_halves ε

/-! ### Absolute continuity of `Γ₀ ∗ U` and Proposition 14.5.4 without (14.39) -/

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- **Absolute continuity of `Γ₀ ∗ U`** (MT p. 358, quoted from Feller): if the first-epoch law `μ`
is absolutely continuous then so is `μ ∗ U`. Each epoch `x + Y₀ + ⋯ + Y_{m−1}` is `x` shifted by
an independent amount. -/
theorem renMeas_absolutelyContinuous (μ : Measure ℝ) [SFinite μ] (hμ : μ ≪ volume) :
    renMeas Γ μ ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [renMeas_apply Γ μ hA]
  refine ENNReal.tsum_eq_zero.2 fun m => ?_
  rw [Measure.prod_apply_symm (s := {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (m + 1) ∈ A})
    ((measurable_resEpoch (m + 1)) hA)]
  refine (lintegral_congr fun w => ?_).trans lintegral_zero
  have e : (fun x => (x, w)) ⁻¹' {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (m + 1) ∈ A} =
      (fun x => x + ∑ i ∈ Finset.range m, w i) ⁻¹' A := rfl
  rw [e]
  exact hμ (by rw [measure_preimage_add_right]; exact h0)

/-- **Minimal coupling**: if `ρ₁ + σ₂ = ρ₂ + σ₁` with `σ₁, σ₂` finite, the Jordan parts `α ≤ ρ₁`,
`β ≤ ρ₂` of `σ₁ − σ₂` satisfy `ρ₁ + β = ρ₂ + α`. -/
theorem exists_coupling_le {ρ₁ ρ₂ σ₁ σ₂ : Measure ℝ} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    (heq : ρ₁ + σ₂ = ρ₂ + σ₁) :
    ∃ α β : Measure ℝ, IsFiniteMeasure α ∧ IsFiniteMeasure β ∧ α ≤ ρ₁ ∧ β ≤ ρ₂ ∧
      ρ₁ + β = ρ₂ + α := by
  obtain ⟨S, hS, h1, h2⟩ := hahn_decomposition σ₁ σ₂
  have hle1 : σ₂.restrict S ≤ σ₁.restrict S := Measure.le_intro fun t ht _ => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h1 _ (ht.inter hS) inter_subset_right
  have hle2 : σ₁.restrict Sᶜ ≤ σ₂.restrict Sᶜ := Measure.le_intro fun t ht _ => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h2 _ (ht.inter hS.compl) inter_subset_right
  set α := σ₁.restrict S - σ₂.restrict S with hα
  set β := σ₂.restrict Sᶜ - σ₁.restrict Sᶜ with hβ
  have hαc : α + σ₂.restrict S = σ₁.restrict S := Measure.sub_add_cancel_of_le hle1
  have hβc : β + σ₁.restrict Sᶜ = σ₂.restrict Sᶜ := Measure.sub_add_cancel_of_le hle2
  have hρS : ρ₁.restrict S = ρ₂.restrict S + α := by
    ext A hA
    have e : (ρ₁.restrict S + σ₂.restrict S) A = (ρ₂.restrict S + σ₁.restrict S) A := by
      rw [← Measure.restrict_add, ← Measure.restrict_add, heq]
    rw [Measure.add_apply, Measure.add_apply, ← hαc, Measure.add_apply, ← add_assoc] at e
    rw [Measure.add_apply]
    exact (ENNReal.add_left_inj (measure_ne_top _ _)).1 e
  have hρSc : ρ₁.restrict Sᶜ + β = ρ₂.restrict Sᶜ := by
    ext A hA
    have e : (ρ₁.restrict Sᶜ + σ₂.restrict Sᶜ) A = (ρ₂.restrict Sᶜ + σ₁.restrict Sᶜ) A := by
      rw [← Measure.restrict_add, ← Measure.restrict_add, heq]
    rw [Measure.add_apply, Measure.add_apply, ← hβc, Measure.add_apply, ← add_assoc] at e
    rw [Measure.add_apply]
    exact (ENNReal.add_left_inj (measure_ne_top _ _)).1 e
  have hαle : α ≤ σ₁.restrict S := hαc ▸ Measure.le_add_right le_rfl
  have hβle : β ≤ σ₂.restrict Sᶜ := hβc ▸ Measure.le_add_right le_rfl
  refine ⟨α, β, ⟨lt_of_le_of_lt (hαle univ) (measure_lt_top _ _)⟩,
    ⟨lt_of_le_of_lt (hβle univ) (measure_lt_top _ _)⟩, ?_, ?_, ?_⟩
  · calc α ≤ ρ₂.restrict S + α := Measure.le_add_left le_rfl
      _ = ρ₁.restrict S := hρS.symm
      _ ≤ ρ₁ := Measure.restrict_le_self
  · calc β ≤ ρ₁.restrict Sᶜ + β := Measure.le_add_left le_rfl
      _ = ρ₂.restrict Sᶜ := hρSc
      _ ≤ ρ₂ := Measure.restrict_le_self
  · conv_lhs => rw [← Measure.restrict_add_restrict_compl hS (μ := ρ₁)]
    conv_rhs => rw [← Measure.restrict_add_restrict_compl hS (μ := ρ₂)]
    rw [add_assoc, hρSc, hρS]
    exact add_right_comm _ _ _

/-- **Proposition 14.5.4 without (14.39)** (MT p. 358): for a spread-out `Γ` on `[0, ∞)` with
finite mean, absolutely continuous first-epoch laws `Γ₁, Γ₂` on `(0, ∞)` with finite means, and a
bounded integrable measurable `f` vanishing on `(−∞, 0)`,
`sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0`. -/
theorem proposition_14_5_4_ac (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞) (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : μ₁ (Iic 0) = 0) (h₂ : μ₂ (Iic 0) = 0)
    (hm₁ : ∫⁻ x, ENNReal.ofReal x ∂μ₁ ≠ ∞) (hm₂ : ∫⁻ x, ENNReal.ofReal x ∂μ₂ ≠ ∞)
    (hac₁ : μ₁ ≪ volume) (hac₂ : μ₂ ≪ volume) {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (convSupDiff f (renMeas Γ μ₁) (renMeas Γ μ₂)) atTop (𝓝 0) := by
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, heq⟩ := proposition_14_5_3 Γ hΓ0 hΓpos hs hm μ₁ μ₂ h₁ h₂ hm₁ hm₂
  obtain ⟨α, β, hα, hβ, hαle, hβle, heq'⟩ := exists_coupling_le heq
  have hloc : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Iic 0) = 0 → ∀ t,
      ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ μ ≠ ∞ := fun μ _ hμ t => by
    have hle : ∀ u, ENNReal.ofReal (f (t - u)) ≤ (Iic t).indicator (fun _ => ENNReal.ofReal d) u :=
      fun u => by
        by_cases hu : u ∈ Iic t
        · rw [indicator_of_mem hu]; exact ENNReal.ofReal_le_ofReal (hfd _)
        · rw [indicator_of_notMem hu, hf0 _ (by simp only [mem_Iic, not_le] at hu; linarith),
            ENNReal.ofReal_zero]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_indicator_const measurableSet_Iic]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0
        hΓpos)).ne')) (renMeas_Iic_le Γ μ hμ t))
  have hA := tendsto_lintegral_sub_of_ac ((Measure.absolutelyContinuous_of_le hαle).trans
    (renMeas_absolutelyContinuous Γ μ₁ hac₁)) hf hfd hint
  have hB := tendsto_lintegral_sub_of_ac ((Measure.absolutelyContinuous_of_le hβle).trans
    (renMeas_absolutelyContinuous Γ μ₂ hac₂)) hf hfd hint
  have hAB := hA.add hB
  rw [add_zero] at hAB
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAB (fun _ => zero_le)
    fun t => convSupDiff_le heq' (hloc μ₁ h₁ t) (hloc μ₂ h₂ t)

/-! ### Smoothing by the first-epoch law -/

/-- The smoothing `μ ⋆ g(s) = ∫ g(s − u) μ(du)` of `g` by a first-epoch law `μ`. -/
noncomputable def smoothFn (μ : Measure ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u, g (s - u) ∂μ

/-- The smoothing `μ ⋆ f(s)` of a bound `f`, as a Lebesgue integral of `f⁺`. -/
noncomputable def smoothBound (μ : Measure ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ).toReal

/-- `μ ∗ U` is s-finite: a countable sum of finite measures. -/
theorem sFinite_renMeas (μ : Measure ℝ) [SFinite μ] : SFinite (renMeas Γ μ) := by
  unfold renMeas
  infer_instance

/-- `μ ∗ U` is the image of `μ ⊗ (δ₁ ∗ U)` under `(v, u) ↦ u + (v − 1)`. -/
theorem renMeas_eq_map_prod (μ : Measure ℝ) [SFinite μ] :
    renMeas Γ μ = (μ.prod (renMeas Γ (Measure.dirac 1))).map
      (fun p : ℝ × ℝ => p.2 + (p.1 - 1)) := by
  have := sFinite_renMeas Γ (Measure.dirac (1 : ℝ))
  have hmeas : Measurable fun p : ℝ × ℝ => p.2 + (p.1 - 1) :=
    measurable_snd.add (measurable_fst.sub measurable_const)
  ext A hA
  rw [renMeas_eq_lintegral Γ μ hA, Measure.map_apply hmeas hA, Measure.prod_apply (hmeas hA)]
  refine lintegral_congr fun x => ?_
  rw [renMeas_dirac_eq_map Γ x, Measure.map_apply (f := fun u => u + (x - 1))
    (measurable_id.add measurable_const) hA]
  rfl

/-- **The smoothing identity**: `μ ∗ U ∗ g(t) = δ₁ ∗ U ∗ (μ ⋆ g)(t + 1)` for a first-epoch law `μ`
on `(0, ∞)` and a measurable `g` dominated by a bounded `f` vanishing on `(−∞, 0)`. -/
theorem convAt_renMeas_eq_smooth (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) {f : ℝ → ℝ} (hf0 : ∀ s < 0, f s = 0) {d : ℝ}
    (hfd : ∀ s, f s ≤ d) {g : ℝ → ℝ} (hg : Measurable g) (hgf : ∀ s, |g s| ≤ f s) (t : ℝ) :
    convAt (renMeas Γ μ) g t = convAt (renMeas Γ (Measure.dirac 1)) (smoothFn μ g) (t + 1) := by
  have := sFinite_renMeas Γ (Measure.dirac (1 : ℝ))
  have hmeas : Measurable fun p : ℝ × ℝ => p.2 + (p.1 - 1) :=
    measurable_snd.add (measurable_fst.sub measurable_const)
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
      simp only [mem_Iic, not_le]; exact one_pos)]
  -- integrability on the product
  set E : Set (ℝ × ℝ) := (univ ×ˢ Iic (t + 1)) ∪ (Iic 0 ×ˢ univ) with hE
  have hEm : MeasurableSet E :=
    (MeasurableSet.univ.prod measurableSet_Iic).union (measurableSet_Iic.prod MeasurableSet.univ)
  have hEfin : (μ.prod (renMeas Γ (Measure.dirac 1))) E ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    rw [Measure.prod_prod, Measure.prod_prod, hμ, zero_mul, add_zero, measure_univ, one_mul]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2
      (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne'))
      (renMeas_Iic_le Γ (Measure.dirac 1) hd1 (t + 1))
  have hInt : Integrable (fun z : ℝ × ℝ => g (t - (z.2 + (z.1 - 1))))
      (μ.prod (renMeas Γ (Measure.dirac 1))) := by
    refine Integrable.mono' ((integrable_indicator_iff hEm).2 (integrableOn_const hEfin
      (C := d))) (hg.comp (measurable_const.sub hmeas)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz]
      exact (hgf _).trans (hfd _)
    · rw [indicator_of_notMem hz]
      have h2 : t + 1 < z.2 := by
        by_contra h
        exact hz (Or.inl ⟨mem_univ _, not_lt.1 h⟩)
      have h1 : 0 < z.1 := by
        by_contra h
        exact hz (Or.inr ⟨not_lt.1 h, mem_univ _⟩)
      have hb := hgf (t - (z.2 + (z.1 - 1)))
      rwa [hf0 _ (by linarith)] at hb
  rw [convAt, renMeas_eq_map_prod Γ μ, integral_map (f := fun u => g (t - u)) hmeas.aemeasurable
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable,
    integral_prod_symm _ hInt, convAt]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  change ∫ v, g (t - (u + (v - 1))) ∂μ = ∫ v, g (t + 1 - u - v) ∂μ
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  change g (t - (u + (v - 1))) = g (t + 1 - u - v)
  congr 1
  ring

/-- **Theorem 14.5.2 (iii)** (MT p. 355): for a spread-out `Γ` on `[0, ∞)` with finite mean `β`,
an absolutely continuous first-epoch law `Γ₀` on `(0, ∞)` and a bounded integrable measurable
`f ≥ 0` vanishing on `(−∞, 0)` ((14.37), (14.38); no (14.39)),
`sup_{|g| ≤ f} |Γ₀ ∗ U ∗ g(t) − β⁻¹ ∫ g| → 0`. -/
theorem theorem_14_5_2_iii (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : renMean Γ ≠ ∞) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0)
    (hac : μ ≪ volume) {f : ℝ → ℝ} (hf : Measurable f) (hf0' : ∀ s, 0 ≤ f s)
    (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (hint : ∫⁻ s, ENNReal.ofReal (f s) ≠ ∞) :
    Tendsto (fun t => ⨆ (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s),
      ENNReal.ofReal |convAt (renMeas Γ μ) g t - ((renMean Γ).toReal)⁻¹ * ∫ s, g s|)
      atTop (𝓝 0) := by
  have hd0 : 0 ≤ d := (hf0' 0).trans (hfd 0)
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
      simp only [mem_Iic, not_le]; exact one_pos)]
  have hjm : Measurable (Function.uncurry fun s u : ℝ => ENNReal.ofReal (f (s - u))) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_fst.sub measurable_snd))
  have hlfin : ∀ s, ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ ≠ ∞ := fun s => by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := d)) ?_
    calc ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ ≤ ∫⁻ _, ENNReal.ofReal d ∂μ :=
          lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hfd _)
      _ = ENNReal.ofReal d := by rw [lintegral_const, measure_univ, mul_one]
  -- the smoothed bound `F = μ ⋆ f` satisfies (14.37)–(14.39)
  have hFm : Measurable (smoothBound μ f) :=
    ENNReal.measurable_toReal.comp hjm.lintegral_prod_right'
  have hF0' : ∀ s, 0 ≤ smoothBound μ f s := fun s => ENNReal.toReal_nonneg
  have hF0 : ∀ s < 0, smoothBound μ f s = 0 := fun s hs => by
    have hae : ∀ᵐ u ∂μ, ENNReal.ofReal (f (s - u)) = 0 := by
      have hpos : ∀ᵐ u ∂μ, 0 < u := ae_iff.2 (measure_mono_null
        (fun v hv => (not_lt.1 hv : v ≤ 0)) hμ)
      filter_upwards [hpos] with u hu
      rw [hf0 _ (by linarith), ENNReal.ofReal_zero]
    rw [smoothBound, lintegral_congr_ae hae, lintegral_zero, ENNReal.toReal_zero]
  have hFd : ∀ s, smoothBound μ f s ≤ d := fun s => by
    refine ENNReal.toReal_le_of_le_ofReal hd0 ?_
    calc ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ ≤ ∫⁻ _, ENNReal.ofReal d ∂μ :=
          lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hfd _)
      _ = ENNReal.ofReal d := by rw [lintegral_const, measure_univ, mul_one]
  have hFlim : Tendsto (smoothBound μ f) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_lintegral_sub_of_ac hac hf hfd hint)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hswap : ∫⁻ s, ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ = ∫⁻ s, ENNReal.ofReal (f s) := by
    rw [lintegral_lintegral_swap hjm.aemeasurable]
    have e : ∀ u, ∫⁻ s, ENNReal.ofReal (f (s - u)) = ∫⁻ s, ENNReal.ofReal (f s) := fun u =>
      lintegral_sub_right_eq_self (fun s => ENNReal.ofReal (f s)) u
    rw [lintegral_congr e, lintegral_const, measure_univ, mul_one]
  have hFint : ∫⁻ s, ENNReal.ofReal (smoothBound μ f s) ≠ ∞ := by
    have e : ∀ s, ENNReal.ofReal (smoothBound μ f s) = ∫⁻ u, ENNReal.ofReal (f (s - u)) ∂μ :=
      fun s => ENNReal.ofReal_toReal (hlfin s)
    rw [lintegral_congr e, hswap]
    exact hint
  -- the smoothed test functions
  have hGm : ∀ g : ℝ → ℝ, Measurable g → Measurable (smoothFn μ g) := fun g hg =>
    ((hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := μ)).measurable
  have hGb : ∀ g : ℝ → ℝ, (∀ s, |g s| ≤ f s) → ∀ s, |smoothFn μ g s| ≤ smoothBound μ f s :=
    fun g hgf s => by
      rw [← Real.norm_eq_abs, smoothFn, smoothBound]
      refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono (hlfin s)
        (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
      rw [Real.norm_eq_abs]
      exact hgf _
  have hGint : ∀ g : ℝ → ℝ, Measurable g → (∀ s, |g s| ≤ f s) →
      ∫ s, smoothFn μ g s = ∫ s, g s := fun g hg hgf => by
    have hB : Integrable (fun p : ℝ × ℝ => f (p.1 - p.2)) (volume.prod μ) := by
      refine ⟨(hf.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => hf0' _)).2 ?_⟩
      rw [lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (f (p.1 - p.2))) hjm.aemeasurable]
      exact lt_top_iff_ne_top.2 (hswap ▸ hint)
    have hI : Integrable (Function.uncurry fun s u : ℝ => g (s - u)) (volume.prod μ) := by
      refine Integrable.mono' hB (hg.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      change ‖g (p.1 - p.2)‖ ≤ f (p.1 - p.2)
      rw [Real.norm_eq_abs]
      exact hgf _
    have e : ∀ u, ∫ s, g (s - u) = ∫ s, g s := fun u => integral_sub_right_eq_self g u
    change ∫ s, ∫ u, g (s - u) ∂μ = ∫ s, g s
    rw [integral_integral_swap hI, integral_congr_ae (ae_of_all _ e), integral_const, probReal_univ,
      one_smul]
  -- part (i) for the first epoch `δ₁` and the bound `F`
  have hi := theorem_14_5_2_i Γ hΓ0 hΓpos hs hm (Measure.dirac 1) hd1 hFm hF0' hF0 hFd hFlim hFint
  have hi1 := hi.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi1 (fun _ => zero_le)
    fun t => ?_
  refine iSup₂_le fun g hg => ?_
  rw [convAt_renMeas_eq_smooth Γ hΓ0 hΓpos μ hμ hf0 hfd hg.1 hg.2 t, ← hGint g hg.1 hg.2]
  exact le_iSup₂ (f := fun (G : ℝ → ℝ) (_ : Measurable G ∧ ∀ s, |G s| ≤ smoothBound μ f s) =>
    ENNReal.ofReal |convAt (renMeas Γ (Measure.dirac 1)) G (t + 1) -
      ((renMean Γ).toReal)⁻¹ * ∫ s, G s|) (smoothFn μ g) ⟨hGm g hg.1, hGb g hg.2⟩

end MeynTweedie.FErgodicity
