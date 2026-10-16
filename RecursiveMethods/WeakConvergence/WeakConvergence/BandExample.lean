/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import WeakConvergence.MonotoneProcesses

/-!
# Exercise 12.13: monotone and Feller are not enough for uniqueness (SLP pp. 380–381)

The book's example is drawn (Figure 12.4): `P(s, ·)` is uniform on a band `[h(s), H(s)]` between
two continuous nondecreasing curves, with two intervals `E₁`, `E₂` mapped into themselves and a
transient interval `F` between them. We realise it explicitly with `E₁ = [0, 1]`, `F = (1, 2)`,
`E₂ = [2, 3]` and, writing `c(x) = max 0 (min x 1)`,

* `h(s) = c(s)/2 + (3/2) c(10(s − 1.9)) + c(s − 2)/2`,
* `H(s) = 1/2 + c(s)/2 + (3/2) c(10(s − 1)) + c(s − 2)/2`,

so that `H − h ≥ 1/2` (the book's denominator `μ([h(s), H(s)])` is positive), `h(s) = s/2`,
`H(s) = (1 + s)/2` on `E₁`, `h(s) = 1 + s/2`, `H(s) = 3/2 + s/2` on `E₂`, and on `F` the band
reaches into `E₁` (when `s ≤ 1.9`, `h(s) = 1/2`) or into `E₂` (when `s ≥ 1.1`, `H(s) = 5/2`). The
state space is `ℝ`; all mass lies in `[0, 3]`.

* (a) `P` is monotone and Feller (`ex_12_13a`);
* (b) `E₁` and `E₂` are disjoint and invariant (`Pⁿ(s, Eᵢ) = 1` for `s ∈ Eᵢ`), and from every
  `s ∈ F` the process enters `E₁ ∪ E₂`, which it never leaves, with positive probability
  (`ex_12_13b`). (For general state spaces SLP never defines a "transient set", see the Chapter 11
  corrections; this is the finite-chain notion of p. 333: a positive probability of leaving and
  never returning.)
* (c) `T*ⁿδ₀` and `T*ⁿδ₃` have no common weak limit (`ex_12_13c`): every weak limit of the first
  is concentrated on `E₁`, of the second on `E₂`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ### The clamp and the band -/

/-- `c(x) = max 0 (min x 1)`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem monotone_clamp01 : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right 1 h)

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem clamp01_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  rw [clamp01, min_eq_left (h.trans zero_le_one), max_eq_left h]

theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  rw [clamp01, min_eq_right h, max_eq_right zero_le_one]

theorem clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  rw [clamp01, min_eq_left h1, max_eq_right h0]

/-- The lower curve `h`. -/
noncomputable def lowEnd (s : ℝ) : ℝ :=
  clamp01 s / 2 + 3 / 2 * clamp01 (10 * (s - 19 / 10)) + clamp01 (s - 2) / 2

/-- The upper curve `H`. -/
noncomputable def highEnd (s : ℝ) : ℝ :=
  1 / 2 + clamp01 s / 2 + 3 / 2 * clamp01 (10 * (s - 1)) + clamp01 (s - 2) / 2

theorem continuous_lowEnd : Continuous lowEnd :=
  ((continuous_clamp01.div_const 2).add ((continuous_clamp01.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).const_mul _)).add
    ((continuous_clamp01.comp (continuous_id.sub continuous_const)).div_const 2)

theorem continuous_highEnd : Continuous highEnd :=
  ((continuous_const.add (continuous_clamp01.div_const 2)).add ((continuous_clamp01.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).const_mul _)).add
    ((continuous_clamp01.comp (continuous_id.sub continuous_const)).div_const 2)

theorem monotone_lowEnd : Monotone lowEnd := fun s t h => by
  have h1 := monotone_clamp01 h
  have h2 := monotone_clamp01 (show 10 * (s - 19 / 10) ≤ 10 * (t - 19 / 10) by linarith)
  have h3 := monotone_clamp01 (show s - 2 ≤ t - 2 by linarith)
  simp only [lowEnd]; linarith

theorem monotone_highEnd : Monotone highEnd := fun s t h => by
  have h1 := monotone_clamp01 h
  have h2 := monotone_clamp01 (show 10 * (s - 1) ≤ 10 * (t - 1) by linarith)
  have h3 := monotone_clamp01 (show s - 2 ≤ t - 2 by linarith)
  simp only [highEnd]; linarith

theorem lowEnd_nonneg (s : ℝ) : 0 ≤ lowEnd s := by
  have := clamp01_nonneg s; have := clamp01_nonneg (10 * (s - 19 / 10))
  have := clamp01_nonneg (s - 2)
  simp only [lowEnd]; linarith

theorem highEnd_le (s : ℝ) : highEnd s ≤ 3 := by
  have := clamp01_le_one s; have := clamp01_le_one (10 * (s - 1))
  have := clamp01_le_one (s - 2)
  simp only [highEnd]; linarith

/-- The band has width at least `1/2`. -/
theorem gap_le (s : ℝ) : 1 / 2 ≤ highEnd s - lowEnd s := by
  have := monotone_clamp01 (show 10 * (s - 19 / 10) ≤ 10 * (s - 1) by linarith)
  simp only [highEnd, lowEnd]; linarith

/-- The point at fraction `u` of the band. -/
noncomputable def bandPt (s u : ℝ) : ℝ := lowEnd s + u * (highEnd s - lowEnd s)

theorem continuous_bandPt : Continuous fun p : ℝ × ℝ => bandPt p.1 p.2 :=
  (continuous_lowEnd.comp continuous_fst).add (continuous_snd.mul
    ((continuous_highEnd.comp continuous_fst).sub (continuous_lowEnd.comp continuous_fst)))

theorem continuous_bandPt_left (u : ℝ) : Continuous fun s => bandPt s u :=
  continuous_bandPt.comp (continuous_id.prodMk continuous_const)

theorem continuous_bandPt_right (s : ℝ) : Continuous (bandPt s) :=
  continuous_bandPt.comp (continuous_const.prodMk continuous_id)

theorem bandPt_mono {s t u : ℝ} (hst : s ≤ t) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ≤ bandPt t u := by
  have h1 := monotone_lowEnd hst
  have h2 := monotone_highEnd hst
  simp only [bandPt]
  nlinarith [hu.1, hu.2]

/-! ### The transition function -/

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Icc 0 1)

theorem isProbabilityMeasure_unif : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Icc]⟩

theorem unif_Icc {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1) : unif (Icc a b) = ENNReal.ofReal (b - a) := by
  rw [unif, Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_eq_left h0,
    min_eq_left h1, Real.volume_Icc]

/-- `P(s, ·)`: the uniform distribution on `[h(s), H(s)]`, as the image of `unif` under
`u ↦ h(s) + u (H(s) − h(s))`. -/
noncomputable def bandKernel : Kernel ℝ ℝ :=
  haveI := isProbabilityMeasure_unif
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const ℝ unif)
    fun p => bandPt p.1 p.2

theorem bandKernel_apply (s : ℝ) : bandKernel s = unif.map (bandPt s) := by
  have := isProbabilityMeasure_unif
  rw [bandKernel, Kernel.map_apply _ continuous_bandPt.measurable, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map continuous_bandPt.measurable measurable_prodMk_left]
  rfl

theorem isMarkovKernel_bandKernel : IsMarkovKernel bandKernel := by
  have := isProbabilityMeasure_unif
  exact Kernel.IsMarkovKernel.map _ continuous_bandPt.measurable

theorem bandKernel_apply_set (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    bandKernel s A = unif (bandPt s ⁻¹' A) := by
  rw [bandKernel_apply, Measure.map_apply (continuous_bandPt_right s).measurable hA]

theorem integral_bandKernel (s : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂bandKernel s = ∫ u, f (bandPt s u) ∂unif := by
  rw [bandKernel_apply, integral_map (continuous_bandPt_right s).measurable.aemeasurable
    hf.aestronglyMeasurable]

/-- **Exercise 12.13a.** `P` is monotone and has the Feller property. -/
theorem ex_12_13a : IsMonotoneTF bandKernel ∧ IsFeller bandKernel := by
  have := isProbabilityMeasure_unif
  have hint : ∀ {f : ℝ → ℝ}, Measurable f → ∀ {M : ℝ}, (∀ x, |f x| ≤ M) → ∀ s,
      Integrable (fun u => f (bandPt s u)) unif := fun hf _ hM s =>
    integrable_of_bounded (hf.comp (continuous_bandPt_right s).measurable) fun u => hM _
  refine ⟨fun f hf ⟨M, hM⟩ hm s t hst => ?_, fun f hf ⟨M, hM⟩ => ?_⟩
  · change ∫ x, f x ∂bandKernel s ≤ ∫ x, f x ∂bandKernel t
    rw [integral_bandKernel s hf, integral_bandKernel t hf]
    exact integral_mono_ae (hint hf hM s) (hint hf hM t)
      (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => hm (bandPt_mono hst hu))
  · have : markovOpR bandKernel f = fun s => ∫ u, f (bandPt s u) ∂unif :=
      funext fun s => integral_bandKernel s hf.measurable
    rw [this]
    exact continuous_of_dominated (bound := fun _ => M)
      (fun s => (hf.comp (continuous_bandPt_right s)).aestronglyMeasurable)
      (fun s => Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hM _)
      (integrable_const M) (Eventually.of_forall fun u => hf.comp (continuous_bandPt_left u))

/-! ### Invariant sets -/

/-- If `P(s, E) = 1` for every `s ∈ E`, then `Pⁿ(s, E) = 1` for every `s ∈ E` and `n`. -/
theorem kpow_eq_one_of_invariant {S : Type*} [MeasurableSpace S] (κ : Kernel S S)
    [IsMarkovKernel κ] {E : Set S} (hE : MeasurableSet E) (h : ∀ s ∈ E, κ s E = 1) :
    ∀ n, ∀ s ∈ E, kpow κ n s E = 1 := by
  intro n
  induction n with
  | zero => intro s hs; simp [kpow, Kernel.id_apply, Measure.dirac_apply_of_mem hs]
  | succ n ih =>
    intro s hs
    have := ex_8_4a κ n
    change (kpow κ n ∘ₖ κ) s E = 1
    rw [Kernel.comp_apply' _ _ _ hE]
    refine le_antisymm ?_ ?_
    · calc ∫⁻ b, kpow κ n b E ∂κ s ≤ ∫⁻ _, 1 ∂κ s := lintegral_mono fun b => prob_le_one
        _ = 1 := by simp
    · calc (1 : ℝ≥0∞) = κ s E := (h s hs).symm
        _ = ∫⁻ b, E.indicator 1 b ∂κ s := (lintegral_indicator_one hE).symm
        _ ≤ ∫⁻ b, kpow κ n b E ∂κ s := lintegral_mono fun b => by
            by_cases hb : b ∈ E
            · rw [indicator_of_mem hb, Pi.one_apply, ih b hb]
            · rw [indicator_of_notMem hb]; exact zero_le

theorem bandKernel_eq_one {s : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (h : ∀ u ∈ Icc (0 : ℝ) 1, bandPt s u ∈ E) : bandKernel s E = 1 := by
  rw [bandKernel_apply_set s hE, unif, Measure.restrict_apply (hE.preimage
    (continuous_bandPt_right s).measurable), inter_eq_right.2
      (show Icc (0 : ℝ) 1 ⊆ bandPt s ⁻¹' E from h), Real.volume_Icc]
  norm_num

theorem bandPt_E₁ {s u : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ∈ Icc (0 : ℝ) 1 := by
  have e1 := clamp01_of_mem hs.1 hs.2
  have e2 := clamp01_of_nonpos (show 10 * (s - 19 / 10) ≤ 0 by linarith [hs.2])
  have e3 := clamp01_of_nonpos (show s - 2 ≤ 0 by linarith [hs.2])
  have e4 := clamp01_of_nonpos (show 10 * (s - 1) ≤ 0 by linarith [hs.2])
  simp only [bandPt, lowEnd, highEnd, e1, e2, e3, e4, mem_Icc]
  constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]

theorem bandPt_E₂ {s u : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ∈ Icc (2 : ℝ) 3 := by
  have e1 := clamp01_of_one_le (show 1 ≤ s by linarith [hs.1])
  have e2 := clamp01_of_one_le (show 1 ≤ 10 * (s - 19 / 10) by linarith [hs.1])
  have e3 := clamp01_of_mem (show 0 ≤ s - 2 by linarith [hs.1]) (show s - 2 ≤ 1 by
    linarith [hs.2])
  have e4 := clamp01_of_one_le (show 1 ≤ 10 * (s - 1) by linarith [hs.1])
  simp only [bandPt, lowEnd, highEnd, e1, e2, e3, e4, mem_Icc]
  constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]

/-- From `s ∈ (1, 2)` the band reaches `E₁ ∪ E₂` with probability at least `1/5`. -/
theorem bandKernel_leave {s : ℝ} (hs : s ∈ Ioo (1 : ℝ) 2) :
    0 < bandKernel s (Icc 0 1 ∪ Icc 2 3) := by
  have hm : MeasurableSet (Icc (0 : ℝ) 1 ∪ Icc 2 3) := measurableSet_Icc.union measurableSet_Icc
  rw [bandKernel_apply_set s hm]
  have hc1 := clamp01_of_one_le (show 1 ≤ s by linarith [hs.1])
  have hc3 := clamp01_of_nonpos (show s - 2 ≤ 0 by linarith [hs.2])
  have hH := highEnd_le s
  have hh := lowEnd_nonneg s
  have hgap := gap_le s
  by_cases h19 : s ≤ 19 / 10
  · -- `h(s) = 1/2`: the bottom fifth of the band lies in `E₁`
    have hc2 := clamp01_of_nonpos (show 10 * (s - 19 / 10) ≤ 0 by linarith)
    have hlow : lowEnd s = 1 / 2 := by simp only [lowEnd, hc1, hc2, hc3]; norm_num
    have hsub : Icc (0 : ℝ) (1 / 5) ⊆ bandPt s ⁻¹' (Icc 0 1 ∪ Icc 2 3) := fun u hu => by
      left
      simp only [bandPt, hlow, mem_Icc] at hu ⊢
      rw [hlow] at hgap
      constructor <;> nlinarith [hu.1, hu.2]
    calc (0 : ℝ≥0∞) < unif (Icc 0 (1 / 5)) := by
          rw [unif_Icc le_rfl (by norm_num)]; norm_num
      _ ≤ _ := measure_mono hsub
  · -- `H(s) = 5/2`: the top fifth of the band lies in `E₂`
    have hc4 := clamp01_of_one_le (show 1 ≤ 10 * (s - 1) by linarith)
    have hhigh : highEnd s = 5 / 2 := by simp only [highEnd, hc1, hc4, hc3]; norm_num
    have hlow2 : lowEnd s ≤ 2 := by
      have := clamp01_le_one (10 * (s - 19 / 10))
      simp only [lowEnd, hc1, hc3]; linarith
    have hsub : Icc (4 / 5 : ℝ) 1 ⊆ bandPt s ⁻¹' (Icc 0 1 ∪ Icc 2 3) := fun u hu => by
      right
      simp only [bandPt, hhigh, mem_Icc] at hu ⊢
      constructor <;> nlinarith [hu.1, hu.2]
    calc (0 : ℝ≥0∞) < unif (Icc (4 / 5) 1) := by
          rw [unif_Icc (by norm_num) le_rfl]; norm_num
      _ ≤ _ := measure_mono hsub

/-- **Exercise 12.13b.** `E₁ = [0, 1]` and `E₂ = [2, 3]` are disjoint and invariant, and from every
point of `F = (1, 2)` the process enters `E₁ ∪ E₂` with positive probability. -/
theorem ex_12_13b :
    Disjoint (Icc (0 : ℝ) 1) (Icc 2 3) ∧
      (∀ n, ∀ s ∈ Icc (0 : ℝ) 1, kpow bandKernel n s (Icc 0 1) = 1) ∧
      (∀ n, ∀ s ∈ Icc (2 : ℝ) 3, kpow bandKernel n s (Icc 2 3) = 1) ∧
      ∀ s ∈ Ioo (1 : ℝ) 2, 0 < bandKernel s (Icc 0 1 ∪ Icc 2 3) := by
  have := isMarkovKernel_bandKernel
  refine ⟨?_, kpow_eq_one_of_invariant _ measurableSet_Icc fun s hs =>
      bandKernel_eq_one measurableSet_Icc fun u hu => bandPt_E₁ hs hu,
    kpow_eq_one_of_invariant _ measurableSet_Icc fun s hs =>
      bandKernel_eq_one measurableSet_Icc fun u hu => bandPt_E₂ hs hu,
    fun s hs => bandKernel_leave hs⟩
  rw [Set.disjoint_iff]
  intro x ⟨h1, h2⟩
  linarith [h1.2, h2.1]

/-- **Exercise 12.13c.** `T*ⁿδ₀` and `T*ⁿδ₃` have no common weak limit. -/
theorem ex_12_13c :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp bandKernel)^[n] (Measure.dirac 0)) μ ∧
      ConvWeak (fun n => (adjointOp bandKernel)^[n] (Measure.dirac 3)) μ := by
  rintro ⟨μ, hμ, h0, h3⟩
  have := isMarkovKernel_bandKernel
  obtain ⟨hdis, hE₁, hE₂, -⟩ := ex_12_13b
  have : ∀ (s : ℝ) n, IsProbabilityMeasure ((adjointOp bandKernel)^[n] (Measure.dirac s)) :=
    fun s n => isProbabilityMeasure_iterate _ n
  have m1 := measure_eq_one_of_convWeak h0 isClosed_Icc fun n => by
    rw [iterate_dirac]; exact hE₁ n 0 ⟨le_rfl, zero_le_one⟩
  have m2 := measure_eq_one_of_convWeak h3 isClosed_Icc fun n => by
    rw [iterate_dirac]; exact hE₂ n 3 ⟨by norm_num, le_rfl⟩
  have := measure_union hdis measurableSet_Icc (μ := μ)
  rw [m1, m2] at this
  have h2 : μ (Icc 0 1 ∪ Icc 2 3) ≤ 1 := prob_le_one
  rw [this] at h2
  norm_num at h2

end StokeyLucasPrescott.WeakConvergence
