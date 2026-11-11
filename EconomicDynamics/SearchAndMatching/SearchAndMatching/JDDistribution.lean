/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.JDBasics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Probability.Notation
import Mathlib.Topology.Order.IntermediateValue

/-!
# The productivity distribution of Miao §18.2: the option-value integral

Miao, *Economic Dynamics in Discrete Time*, §18.2, pp. 600–604. Idiosyncratic productivity `z`
is drawn from a distribution `G` on `(0, ∞)` with mean `1`. Everything in §18.2 depends on `G`
only through the integral

  `Φ(c) = ∫_c^∞ (z − c) dG(z) = ∫ max(z − c, 0) dG(z)`  (`jd_Phi`, `jd_Phi_eq_setIntegral`),

the expected surplus above a reservation productivity `c`, which appears in (18.41)–(18.45).
`G` is a probability measure `μ` on `ℝ` with `∫ |z| dμ < ∞`; the book's support and mean
assumptions (`μ(−∞, 0] = 0`, `∫ z dμ = 1`) are only needed for `jd_Phi_of_nonpos`.

Proved: `Φ ≥ 0` and is antitone, `1`-Lipschitz and continuous; `Φ(c′) − Φ(c) ≥ (c − c′)(1 − G(c))`
for `c′ ≤ c` (`jd_Phi_gap`), so `Φ` is strictly decreasing where `1 − G > 0`; `Φ(c) > 0` iff
`G(c) < 1` (`jd_Phi_pos_iff`); `Φ(c) = 1 − c` for `c ≤ 0` (`jd_Phi_of_nonpos`); `Φ(c) → 0` as
`c → ∞` (`jd_Phi_tendsto_atTop`); and `Φ′(c) = −(1 − G(c))` at every `c` that is not an atom of
`G` (`jd_Phi_hasDerivAt`), the slope used in the linearisation of the job creation condition.
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- Miao, (18.41), p. 603: the option-value integral `Φ(c) = ∫ max(z − c, 0) dG(z)`. -/
noncomputable def jd_Phi (μ : Measure ℝ) (c : ℝ) : ℝ := ∫ z, max (z - c) 0 ∂μ

/-- Miao, p. 600: the distribution function `G(c) = μ(−∞, c]` of idiosyncratic productivity. -/
noncomputable def jd_G (μ : Measure ℝ) (c : ℝ) : ℝ := μ.real (Set.Iic c)

/-- Miao, p. 600: `1 − G(c) = μ(c, ∞)` for a probability measure. -/
theorem jd_one_sub_G (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    1 - jd_G μ c = μ.real (Set.Ioi c) := by
  unfold jd_G
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- Miao, p. 600: `G` is nondecreasing. -/
theorem jd_G_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (jd_G μ) := by
  intro c c' h
  exact measureReal_mono (Set.Iic_subset_Iic.mpr h)

/-- Miao, p. 600: `0 ≤ G ≤ 1`. -/
theorem jd_G_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    0 ≤ jd_G μ c ∧ jd_G μ c ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The integrand of `Φ` is integrable. -/
theorem jd_Phi_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : Integrable (fun z => max (z - c) 0) μ :=
  (hint.sub (integrable_const c)).pos_part

/-- Miao, p. 603: `Φ(c) ≥ 0`. -/
theorem jd_Phi_nonneg (μ : Measure ℝ) (c : ℝ) : 0 ≤ jd_Phi μ c :=
  integral_nonneg fun _ => le_max_right _ _

/-- Miao, (18.41), p. 603: `Φ(c) = ∫_c^∞ (z − c) dG(z)`. -/
theorem jd_Phi_eq_setIntegral (μ : Measure ℝ) (c : ℝ) :
    jd_Phi μ c = ∫ z in Set.Ioi c, (z - c) ∂μ := by
  unfold jd_Phi
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : c < z
  · simp [Set.indicator, hz, max_eq_left (sub_nonneg.mpr hz.le)]
  · simp [Set.indicator, hz, max_eq_right (sub_nonpos.mpr (not_lt.mp hz))]

/-- Miao, p. 604 (the job creation curve slopes down): `Φ` is antitone. -/
theorem jd_Phi_antitone {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Antitone (jd_Phi μ) := by
  intro c c' h
  exact integral_mono (jd_Phi_integrable hint c') (jd_Phi_integrable hint c)
    fun z => max_le_max (by linarith) le_rfl

/-- `Φ` is `1`-Lipschitz: `Φ(c) − Φ(c′) ≤ c′ − c` for `c ≤ c′`. -/
theorem jd_Phi_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c c' : ℝ} (h : c ≤ c') :
    jd_Phi μ c - jd_Phi μ c' ≤ c' - c := by
  unfold jd_Phi
  rw [← integral_sub (jd_Phi_integrable hint c) (jd_Phi_integrable hint c')]
  have : ∫ _z, (c' - c) ∂μ = c' - c := by simp
  rw [← this]
  refine integral_mono ((jd_Phi_integrable hint c).sub (jd_Phi_integrable hint c'))
    (integrable_const _) fun z => ?_
  simp only
  rcases le_total (z - c') 0 with h1 | h1 <;> rcases le_total (z - c) 0 with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith

/-- `|Φ(c) − Φ(c′)| ≤ |c − c′|`. -/
theorem jd_Phi_abs_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c c' : ℝ) :
    |jd_Phi μ c - jd_Phi μ c'| ≤ |c - c'| := by
  rcases le_total c c' with h | h
  · have h1 := jd_Phi_sub_le hint h
    have h2 := jd_Phi_antitone hint h
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := jd_Phi_sub_le hint h
    have h2 := jd_Phi_antitone hint h
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `Φ` is continuous. -/
theorem jd_Phi_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Continuous (jd_Phi μ) := by
  refine (LipschitzWith.of_dist_le_mul fun c c' => ?_).continuous (K := 1)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact jd_Phi_abs_sub_le hint c c'

/-- Miao, p. 604: for `c′ ≤ c`, `Φ(c′) − Φ(c) ≥ (c − c′)(1 − G(c))`; `Φ` strictly decreases
wherever matches above the cutoff have positive probability. -/
theorem jd_Phi_gap {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c c' : ℝ} (h : c' ≤ c) :
    (c - c') * μ.real (Set.Ioi c) ≤ jd_Phi μ c' - jd_Phi μ c := by
  unfold jd_Phi
  rw [← integral_sub (jd_Phi_integrable hint c') (jd_Phi_integrable hint c)]
  have : ∫ z, (Set.Ioi c).indicator (fun _ => c - c') z ∂μ = (c - c') * μ.real (Set.Ioi c) := by
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
  rw [← this]
  refine integral_mono ((integrable_const (c - c')).indicator measurableSet_Ioi)
    ((jd_Phi_integrable hint c').sub (jd_Phi_integrable hint c)) fun z => ?_
  simp only [Set.indicator, Set.mem_Ioi]
  split_ifs with hz
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rcases le_total (z - c') 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_right (by linarith)]; simp
    · rw [max_eq_left h1, max_eq_right (by linarith)]; linarith

/-- Miao, p. 604: `Φ(c) > 0` iff `G(c) < 1`, i.e. iff `μ(c, ∞) > 0`. -/
theorem jd_Phi_pos_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : 0 < jd_Phi μ c ↔ 0 < μ (Set.Ioi c) := by
  unfold jd_Phi
  rw [integral_pos_iff_support_of_nonneg (f := fun z => max (z - c) 0)
    (fun _ => le_max_right _ _) (jd_Phi_integrable hint c)]
  have : Function.support (fun z => max (z - c) 0) = Set.Ioi c := by
    ext z
    simp only [Function.mem_support, Set.mem_Ioi, ne_eq]
    constructor
    · intro hz
      by_contra h
      exact hz (max_eq_right (by linarith [not_lt.mp h]))
    · intro hz
      rw [max_eq_left (by linarith)]
      linarith
  rw [this]

/-- Miao, p. 604: `Φ(c) > 0` iff `1 − G(c) > 0` (real-valued form). -/
theorem jd_Phi_pos_iff_real {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : 0 < jd_Phi μ c ↔ 0 < μ.real (Set.Ioi c) := by
  rw [jd_Phi_pos_iff hint, measureReal_def, ENNReal.toReal_pos_iff]
  simp [measure_lt_top]

/-- Miao, p. 604: `Φ` is strictly decreasing to the right of a point where it is positive:
`c₁ < c₂` and `Φ(c₁) > 0` imply `Φ(c₂) < Φ(c₁)`. -/
theorem jd_Phi_strictAnti_of_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c₁ c₂ : ℝ} (hc : c₁ < c₂) (hP : 0 < jd_Phi μ c₁) :
    jd_Phi μ c₂ < jd_Phi μ c₁ := by
  rcases (jd_Phi_nonneg μ c₂).lt_or_eq with h | h
  · have hm := (jd_Phi_pos_iff_real hint c₂).mp h
    have hgap := jd_Phi_gap hint hc.le
    have : 0 < (c₂ - c₁) * μ.real (Set.Ioi c₂) := mul_pos (by linarith) hm
    linarith
  · rw [← h]; exact hP

/-- Miao, p. 600 (support `(0, ∞)`, mean `1`): `Φ(c) = 1 − c` for `c ≤ 0`. -/
theorem jd_Phi_of_nonpos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (hsupp : μ (Set.Iic 0) = 0) (hmean : ∫ z, z ∂μ = 1)
    {c : ℝ} (hc : c ≤ 0) : jd_Phi μ c = 1 - c := by
  unfold jd_Phi
  have hae : (fun z => max (z - c) 0) =ᵐ[μ] fun z => z - c := by
    have : ∀ᵐ z ∂μ, z ∉ Set.Iic (0 : ℝ) := measure_eq_zero_iff_ae_notMem.mp hsupp
    filter_upwards [this] with z hz
    simp only [Set.mem_Iic, not_le] at hz
    exact max_eq_left (by linarith)
  rw [integral_congr_ae hae, integral_sub hint (integrable_const c), hmean]
  simp

/-- Miao, p. 604: `Φ(c) → 0` as `c → ∞`. -/
theorem jd_Phi_tendsto_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Tendsto (jd_Phi μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun c z => max (z - c) 0) (f := fun _ => (0 : ℝ)) (fun z => |z|)
    (Eventually.of_forall fun c => (jd_Phi_integrable hint c).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop 0] with c hc
      refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self z]) (abs_nonneg z))
    hint.abs
    (Eventually.of_forall fun z => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop z] with c hc
      exact (max_eq_right (by linarith)).symm)
  have e : jd_Phi μ = fun n => ∫ a, max (a - n) 0 ∂μ := rfl
  rw [e]
  simpa using h

/-- Miao, p. 603 (linearisation of (18.41)): at a non-atom `c` of `G`, `Φ′(c) = −(1 − G(c))`. -/
theorem jd_Phi_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c : ℝ} (hc : μ {c} = 0) :
    HasDerivAt (jd_Phi μ) (-μ.real (Set.Ioi c)) c := by
  set g : ℝ → ℝ := fun r => μ.real (Set.Icc (c - r) (c + r)) with hg
  have gmono : MonotoneOn g (Set.Ici 0) := by
    intro r _ r' _ h
    exact measureReal_mono (Set.Icc_subset_Icc (by linarith) (by linarith))
  -- `g r → μ {c} = 0` as `r ↓ 0`
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (s := fun r => Set.Icc (c - r) (c + r))
      (a := (0 : ℝ)) (fun r _ => measurableSet_Icc.nullMeasurableSet)
      (fun i j _ hij => Set.Icc_subset_Icc (by linarith) (by linarith))
      ⟨1, one_pos, measure_ne_top _ _⟩
    have hint' : (⋂ r > (0 : ℝ), Set.Icc (c - r) (c + r)) = {c} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · intro hz
        by_contra hne
        have hpos : 0 < |z - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
        have := hz (|z - c| / 2) (by linarith)
        rcases le_total 0 (z - c) with h1 | h1
        · rw [abs_of_nonneg h1] at hpos this; linarith [this.2]
        · rw [abs_of_nonpos h1] at hpos this; linarith [this.1]
      · rintro rfl r hr
        constructor <;> linarith
    rw [hint', hc] at h
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [g, Function.comp_def, measureReal_def] using h2
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨r₀, hr₀, hr₀pos⟩ := (hev.and self_mem_nhdsWithin).exists
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr₀pos] with h hh
  have hh' : |h| < r₀ := by simpa [Real.dist_eq] using hh
  -- the integrand bound
  have hbound : ∀ z, ‖max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z‖
      ≤ (Set.Icc (c - |h|) (c + |h|)).indicator (fun _ => 2 * |h|) z := by
    intro z
    rw [Real.norm_eq_abs]
    have hmm : |max (z - (c + h)) 0 - max (z - c) 0| ≤ |h| := by
      have := abs_max_sub_max_le_abs (z - (c + h)) (z - c) 0
      have e : z - (c + h) - (z - c) = -h := by ring
      rwa [e, abs_neg] at this
    by_cases hin : z ∈ Set.Icc (c - |h|) (c + |h|)
    · rw [Set.indicator_of_mem hin]
      have hi : |(Set.Ioi c).indicator (fun _ => h) z| ≤ |h| := by
        by_cases hz : z ∈ Set.Ioi c
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]; simp
      calc _ ≤ |max (z - (c + h)) 0 - max (z - c) 0| + |(Set.Ioi c).indicator (fun _ => h) z| :=
            abs_add_le _ _
        _ ≤ 2 * |h| := by linarith
    · rw [Set.indicator_of_notMem hin]
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      have hab := le_abs_self h
      have hab' := neg_abs_le h
      rcases hin with hz | hz
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith),
          max_eq_right (by linarith), max_eq_right (by linarith)]
        simp
      · rw [Set.indicator_of_mem (by simp only [Set.mem_Ioi]; linarith),
          max_eq_left (by linarith), max_eq_left (by linarith)]
        simp only [abs_nonpos_iff]
        ring
  have hint1 := jd_Phi_integrable hint (c + h)
  have hint2 := jd_Phi_integrable hint c
  have hint3 : Integrable ((Set.Ioi c).indicator (fun _ => h)) μ :=
    (integrable_const h).indicator measurableSet_Ioi
  have hexpr : jd_Phi μ (c + h) - jd_Phi μ c - h • (-μ.real (Set.Ioi c)) =
      ∫ z, (max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z) ∂μ := by
    have hsub : Integrable (fun z => max (z - (c + h)) 0 - max (z - c) 0) μ := hint1.sub hint2
    rw [integral_add hsub hint3, integral_sub hint1 hint2,
      integral_indicator_const _ measurableSet_Ioi]
    simp only [jd_Phi, smul_eq_mul]
    ring
  rw [hexpr]
  have hgle : g |h| ≤ g r₀ := gmono (abs_nonneg h) hr₀pos.le hh'.le
  have hgr : g r₀ < ε / 2 := hr₀
  calc ‖∫ z, (max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z) ∂μ‖
      ≤ ∫ z, (Set.Icc (c - |h|) (c + |h|)).indicator (fun _ => 2 * |h|) z ∂μ :=
        norm_integral_le_of_norm_le ((integrable_const _).indicator measurableSet_Icc)
          (Eventually.of_forall hbound)
    _ = g |h| * (2 * |h|) := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    _ ≤ ε / 2 * (2 * |h|) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε * ‖h‖ := by rw [Real.norm_eq_abs]; ring

end Miao.SearchAndMatching
