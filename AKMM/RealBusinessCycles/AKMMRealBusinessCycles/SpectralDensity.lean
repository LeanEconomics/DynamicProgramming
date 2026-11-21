/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMRealBusinessCycles.Herglotz

/-!
# Spectral measures of weakly stationary processes

AKMM, §14.3.1, pp. 412–413 and Appendix 14.A, p. 863 (beyond the text: the book assumes the
spectrum exists).

* Weakly stationary processes (`sdenStationary`): `X : ℤ → H` in a complex Hilbert space (for
  example mean-zero `L²(Ω, ℂ)`) with `⟪Xₜ, Xₜ₊ₕ⟫ = E[Xₜ₊ₕX̄ₜ] = γ(h)` for all `t`. The
  autocovariance is positive definite (`sden_posDef`), so the process has a unique spectral
  measure `F` with `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF` (`sden_spectral`, by `herg_exists`).
* **The spectral density** (`sden_density`): if `Σ|γ(h)| < ∞`, `F` has the continuous density
  `f = (1/T)Σₕγ(h)e_{−h} ≥ 0` (real) with respect to Lebesgue measure on the circle (`sdenMeasure`);
  for `T = 2π` this is the book's `s(ω) = (1/2π)Σₖγₖe^{−ikω}`. The proof: the Fourier
  coefficients of the series are `γ` (`sden_coeff`, termwise integration), the series is the
  pointwise limit of the Fejér densities and so real and nonnegative (`sden_series_nonneg`,
  Tannery's theorem), and uniqueness.
* **AR(1)** (`sdenAR1`, `γ(h) = ρ^{|h|}/(1 − ρ²)`, `|ρ| < 1`): absolutely summable
  (`sden_ar1_summable`); the spectrum in closed form `1/((1 − ρe_{−1})(1 − ρe₁)) = 1/|1 − ρe_{−1}|²`
  (`sden_ar1_series`, `sden_ar1_eq_normSq`), `= 1/(1 − 2ρ cos θ + ρ²)` (`sden_ar1_normSq_cos`), so
  the spectral density is `1/(2π(1 − 2ρ cos ω + ρ²))` for `T = 2π`; the spectral measure
  (`sden_ar1_measure`, `sden_ar1_coeff`) and positive definiteness (`sden_ar1_posDef`).
* Concrete processes: white noise `εₜ = eₜ ∈ L²(Haar)` (`sden_white_noise`) and the AR(1) process
  `Xₜ = eₜ/(1 − ρe_{−1}) ∈ L²(Haar)` (`sdenAR1Proc`), which satisfies `Xₜ = ρXₜ₋₁ + εₜ`
  (`sden_ar1_recursion`) and is weakly stationary with autocovariance `ρ^{|h|}/(1 − ρ²)`
  (`sden_ar1_stationary`).
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {T : ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A weakly stationary process `X : ℤ → H` in a complex Hilbert space (e.g. mean-zero
`L²(Ω, ℂ)`) with autocovariance `γ`: `⟪X_t, X_{t+h}⟫ = E[X_{t+h} X̄_t] = γ(h)` for all `t`. -/
def sdenStationary (X : ℤ → H) (γ : ℤ → ℂ) : Prop :=
  ∀ t h, ⟪X t, X (t + h)⟫_ℂ = γ h

/-- The autocovariance of a weakly stationary process is positive definite:
`Σⱼₖ cⱼc̄ₖγ(j − k) = ‖Σⱼ cⱼXⱼ‖²`. -/
theorem sden_posDef {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) : hergPosDef γ := by
  intro s c
  have key : ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k) =
      ⟪∑ k ∈ s, c k • X k, ∑ j ∈ s, c j • X j⟫_ℂ := by
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← hX j (k - j), add_sub_cancel]
    ring
  rw [key]
  exact ⟨by simpa using inner_self_im (𝕜 := ℂ) (∑ j ∈ s, c j • X j),
    by simpa using inner_self_nonneg (𝕜 := ℂ) (x := ∑ j ∈ s, c j • X j)⟩

/-- AKMM, pp. 412–413 (beyond the text). **Every weakly stationary process has a spectral
measure** (Herglotz):
`⟪X_s, X_t⟫ = ∫ e_{t−s} dF` for a finite measure `F` on the circle, unique by `herg_unique`. -/
theorem sden_spectral [Fact (0 < T)] {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) :
    ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧
      (∀ h, γ h = ∫ x, fourier h x ∂F) ∧ ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F := by
  obtain ⟨F, hF, hγ⟩ := herg_exists (T := T) (sden_posDef hX)
  refine ⟨F, hF, hγ, fun s t => ?_⟩
  rw [← hγ, ← hX s (t - s), add_sub_cancel]

theorem sden_norm_fourier (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-- `∫ eₘe_{−h} dHaar = δₘₕ`. -/
theorem sden_integral_fourier_mul [Fact (0 < T)] (m h : ℤ) :
    ∫ x, fourier m x * fourier (-h) x ∂(haarAddCircle (T := T)) = if m = h then 1 else 0 := by
  simp_rw [← fourier_add]
  rw [herg_integral_fourier]
  rcases eq_or_ne m h with rfl | hmh
  · simp
  · have : m + -h ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.2 hmh
    simp [this, hmh]

/-- The series `Σₕ γ(h)e_{−h}(x)`, i.e. `T` times the spectral density
(`s(ω) = (1/2π)Σₖγₖe^{−ikω}` for `T = 2π`, AKMM p. 863). -/
noncomputable def sdenSeries (γ : ℤ → ℂ) (x : AddCircle T) : ℂ :=
  ∑' h, γ h * fourier (-h) x

theorem sden_series_continuous {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) :
    Continuous (sdenSeries (T := T) γ) :=
  continuous_tsum (fun h => continuous_const.mul (fourier (-h)).continuous) hs
    (fun h x => by rw [norm_mul, sden_norm_fourier, mul_one])

/-- The Fourier coefficients of the series are `γ`: `∫ eₘ(Σₕγ(h)e_{−h}) dHaar = γ(m)`
(the inversion formula of AKMM p. 863 on the circle, complex `γ`). -/
theorem sden_coeff [Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) (m : ℤ) :
    ∫ x, fourier m x * sdenSeries (T := T) γ x ∂haarAddCircle = γ m := by
  unfold sdenSeries
  simp_rw [← tsum_mul_left]
  have hterm : ∀ h, ∫ x, fourier m x * (γ h * fourier (-h) x) ∂(haarAddCircle (T := T)) =
      if m = h then γ h else 0 := by
    intro h
    simp_rw [mul_left_comm (fourier m _)]
    rw [integral_const_mul, sden_integral_fourier_mul]
    split_ifs <;> simp
  rw [← integral_tsum_of_summable_integral_norm]
  · simp_rw [hterm]
    rw [tsum_eq_single m fun b hb => by simp [Ne.symm hb]]
    simp
  · exact fun h => herg_integrable _ (by fun_prop)
  · refine hs.congr fun h => ?_
    simp_rw [norm_mul, sden_norm_fourier, one_mul, mul_one]
    simp

/-- For positive definite, absolutely summable `γ`, the series `Σₕγ(h)e_{−h}(x)` is real and
nonnegative: it is the pointwise limit of the Fejér densities (Tannery's theorem). -/
theorem sden_series_nonneg {γ : ℤ → ℂ} (hpd : hergPosDef γ) (hs : Summable fun h => ‖γ h‖)
    (x : AddCircle T) : (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re := by
  set f : ℕ → ℤ → ℂ := fun n h => if h ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) then
    (((((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * γ h * fourier (-h) x
    else 0 with hf
  have hfej : ∀ n, ∑' h, f n h = hergFejer γ (n + 1) x := by
    intro n
    rw [tsum_eq_sum (s := Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ))
      fun b hb => by simp only [hf, hb, ↓reduceIte]]
    unfold hergFejer
    exact Finset.sum_congr rfl fun h hh => by simp only [hf, hh, ↓reduceIte]
  have hlim : Tendsto (fun n => ∑' h, f n h) atTop (𝓝 (sdenSeries γ x)) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun h => ?_) (Eventually.of_forall
      fun n h => ?_)
    · have hev : (fun n : ℕ => ((1 - |(h : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) *
          (γ h * fourier (-h) x)) =ᶠ[atTop] fun n => f n h := by
        filter_upwards [eventually_gt_atTop h.natAbs] with n hn
        have hmem : h ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
          rw [Finset.mem_Ioo]
          omega
        simp only [hf, hmem, ↓reduceIte]
        rw [mul_assoc]
        congr 1
        push_cast
        field_simp
      have hl : Tendsto (fun n : ℕ => (1 - |(h : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ)) atTop
          (𝓝 1) := by
        simpa using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(h : ℝ)|)
      have := ((continuous_ofReal.tendsto 1).comp hl).mul_const (γ h * fourier (-h) x)
      simp only [ofReal_one, one_mul] at this
      exact this.congr' hev
    · simp only [hf]
      split_ifs with hh
      · rw [norm_mul, norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [Finset.mem_Ioo] at hh
        have h1 : |(h : ℝ)| < ((n + 1 : ℕ) : ℝ) := by
          rw [abs_lt]
          constructor <;> push_cast <;> [linarith [(by exact_mod_cast hh.1 :
            (-((n : ℝ) + 1)) < h)]; linarith [(by exact_mod_cast hh.2 : (h : ℝ) < (n : ℝ) + 1)]]
        have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have h2 : 0 ≤ (((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) :=
          div_nonneg (by linarith) hN.le
        have h3 : (((n + 1 : ℕ) : ℝ) - |(h : ℝ)|) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hN]
          linarith [abs_nonneg (h : ℝ)]
        rw [abs_of_nonneg h2]
        exact mul_le_of_le_one_left (norm_nonneg _) h3
      · simp
  simp_rw [hfej] at hlim
  have hK : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  exact hK.mem_of_tendsto hlim (Eventually.of_forall fun n => herg_fejer_nonneg hpd (n + 1) x)

/-- The measure `F(dx) = f(x)dx` with density `f = Re(Σₕγ(h)e_{−h})/T` with respect to Lebesgue
measure on the circle (for `T = 2π`: `s(ω)dω`, `s(ω) = (1/2π)Σₖγₖe^{−ikω}`, AKMM p. 863). -/
noncomputable def sdenMeasure [Fact (0 < T)] (γ : ℤ → ℂ) : Measure (AddCircle T) :=
  (volume : Measure (AddCircle T)).withDensity fun x => ENNReal.ofReal ((sdenSeries γ x).re / T)

theorem sden_measure_finite [Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖) :
    IsFiniteMeasure (sdenMeasure (T := T) γ) :=
  isFiniteMeasure_withDensity_ofReal
    (((continuous_re.comp (sden_series_continuous hs)).div_const T).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

/-- If the series is real and nonnegative, the density measure has Fourier coefficients `γ`. -/
theorem sden_measure_coeff [hT : Fact (0 < T)] {γ : ℤ → ℂ} (hs : Summable fun h => ‖γ h‖)
    (hnn : ∀ x : AddCircle T, (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re) (m : ℤ) :
    ∫ x, fourier m x ∂(sdenMeasure (T := T) γ) = γ m := by
  unfold sdenMeasure
  have hmeas : Measurable fun x : AddCircle T => (sdenSeries γ x).re / T :=
    ((continuous_re.comp (sden_series_continuous hs)).div_const T).measurable
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal ((sdenSeries γ x).re / T))
    (ENNReal.measurable_ofReal.comp hmeas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ x : AddCircle T, (ENNReal.ofReal ((sdenSeries γ x).re / T)).toReal • fourier m x =
      T⁻¹ • (fourier m x * sdenSeries γ x) := by
    intro x
    rw [ENNReal.toReal_ofReal (div_nonneg (hnn x).2 hT.out.le)]
    have hx : sdenSeries γ x = ((sdenSeries γ x).re : ℂ) :=
      Complex.ext (by simp) (by simp [(hnn x).1])
    conv_rhs => rw [hx]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [e]
  rw [integral_smul, ← integral_haarAddCircle, sden_coeff hs]

/-- AKMM, p. 863 (the spectrum, made precise). **The spectral density.** If `γ` is positive definite
and `Σ|γ(h)| < ∞`, its spectral measure `F` has the continuous density `f(x) = (1/T)Σₕγ(h)e_{−h}(x)
≥ 0` (real) with respect to Lebesgue measure on the circle; for `T = 2π`, `f(ω) =
(1/2π)Σₕγ(h)e^{−ihω}`. -/
theorem sden_density [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (hs : Summable fun h => ‖γ h‖) (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    (hF : ∀ h, γ h = ∫ x, fourier h x ∂F) :
    F = sdenMeasure γ ∧ Continuous (fun x => (sdenSeries (T := T) γ x).re / T) ∧
      ∀ x : AddCircle T, (sdenSeries γ x).im = 0 ∧ 0 ≤ (sdenSeries γ x).re / T := by
  have := sden_measure_finite (T := T) hs
  refine ⟨herg_unique fun h => ?_, (continuous_re.comp (sden_series_continuous hs)).div_const T,
    fun x => ⟨(sden_series_nonneg hpd hs x).1,
      div_nonneg (sden_series_nonneg hpd hs x).2 (Fact.out : 0 < T).le⟩⟩
  rw [← hF, sden_measure_coeff hs (sden_series_nonneg hpd hs)]

/-- The autocovariance `γ(h) = ρ^{|h|}/(1 − ρ²)` of the AR(1) process `Xₜ = ρXₜ₋₁ + εₜ` with
unit-variance white noise. -/
noncomputable def sdenAR1 (ρ : ℝ) (h : ℤ) : ℂ :=
  ((ρ ^ h.natAbs / (1 - ρ ^ 2) : ℝ) : ℂ)

theorem sden_ar1_summable {ρ : ℝ} (hρ : |ρ| < 1) : Summable fun h => ‖sdenAR1 ρ h‖ := by
  have hd : 0 < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
  have e : ∀ h : ℤ, ‖sdenAR1 ρ h‖ = |ρ| ^ h.natAbs / (1 - ρ ^ 2) := fun h => by
    rw [sdenAR1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hd]
  simp_rw [e]
  have hg : Summable fun n : ℕ => |ρ| ^ n / (1 - ρ ^ 2) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).div_const _
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hg
  · have : (fun n : ℕ => |ρ| ^ (-((n : ℤ) + 1)).natAbs / (1 - ρ ^ 2)) =
        fun n => |ρ| ^ (n + 1) / (1 - ρ ^ 2) := by
      funext n
      congr 2
    rw [this]
    exact (summable_nat_add_iff 1).2 hg

theorem sden_fourier_mul_nat (k : ℤ) (n : ℕ) (x : AddCircle T) :
    fourier (k * n) x = fourier k x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, mul_add, mul_one, fourier_add, ih, pow_succ]

theorem sden_one_sub_ne_zero {ρ : ℝ} (hρ : |ρ| < 1) (n : ℤ) (x : AddCircle T) :
    1 - (ρ : ℂ) * fourier n x ≠ 0 := by
  intro h
  have : ‖(ρ : ℂ) * fourier n x‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
  rw [norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  linarith

theorem sden_ar1_alg {r z w : ℂ} (hzw : z * w = 1) (hd : 1 - r ^ 2 ≠ 0) (hw0 : 1 - r * w ≠ 0)
    (hz0 : 1 - r * z ≠ 0) :
    (1 - r ^ 2)⁻¹ * (1 - r * w)⁻¹ + (1 - r ^ 2)⁻¹ * (r * z) * (1 - r * z)⁻¹ =
      ((1 - r * w) * (1 - r * z))⁻¹ := by
  field_simp
  linear_combination (-r ^ 2) * hzw

/-- AKMM, p. 863, for the AR(1). **The AR(1) spectrum in closed form.** For `|ρ| < 1`,
`Σₕρ^{|h|}e_{−h}(x)/(1 − ρ²) = 1/((1 − ρe_{−1}(x))(1 − ρe₁(x))) = 1/|1 − ρe^{−iω}|²`. -/
theorem sden_ar1_series {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    sdenSeries (sdenAR1 ρ) x = ((1 - ρ * fourier (-1) x) * (1 - ρ * fourier 1 x))⁻¹ := by
  have hzw : fourier (T := T) 1 x * fourier (-1) x = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  have hn : ∀ n : ℤ, ‖(ρ : ℂ) * fourier (T := T) n x‖ < 1 := fun n => by
    rw [norm_mul, sden_norm_fourier, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hρ
  have hd : (1 - (ρ : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
    exact_mod_cast this.ne'
  have h1 : HasSum (fun n : ℕ => sdenAR1 ρ n * fourier (-(n : ℤ)) x)
      ((1 - (ρ : ℂ) ^ 2)⁻¹ * (1 - ρ * fourier (-1) x)⁻¹) := by
    have e : (fun n : ℕ => sdenAR1 ρ n * fourier (-(n : ℤ)) x) =
        fun n : ℕ => (1 - (ρ : ℂ) ^ 2)⁻¹ * ((ρ : ℂ) * fourier (-1) x) ^ n := by
      funext n
      rw [show -(n : ℤ) = -1 * n by ring, sden_fourier_mul_nat, sdenAR1, Int.natAbs_natCast]
      push_cast
      ring
    rw [e]
    exact (hasSum_geometric_of_norm_lt_one (hn (-1))).mul_left _
  have h2 : HasSum (fun n : ℕ => sdenAR1 ρ (-((n : ℤ) + 1)) * fourier (-(-((n : ℤ) + 1))) x)
      ((1 - (ρ : ℂ) ^ 2)⁻¹ * (ρ * fourier 1 x) * (1 - ρ * fourier 1 x)⁻¹) := by
    have e : (fun n : ℕ => sdenAR1 ρ (-((n : ℤ) + 1)) * fourier (-(-((n : ℤ) + 1))) x) =
        fun n : ℕ => (1 - (ρ : ℂ) ^ 2)⁻¹ * ((ρ : ℂ) * fourier 1 x) *
          ((ρ : ℂ) * fourier 1 x) ^ n := by
      funext n
      have ha : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [neg_neg, show (n : ℤ) + 1 = 1 * ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        sden_fourier_mul_nat, sdenAR1, show 1 * ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
        ha]
      push_cast
      ring
    rw [e]
    exact (hasSum_geometric_of_norm_lt_one (hn 1)).mul_left _
  rw [sdenSeries, (HasSum.of_nat_of_neg_add_one
    (f := fun h : ℤ => sdenAR1 ρ h * fourier (-h) x) h1 h2).tsum_eq]
  exact sden_ar1_alg hzw hd (sden_one_sub_ne_zero hρ (-1) x) (sden_one_sub_ne_zero hρ 1 x)

/-- The AR(1) spectral density in the book's form: with `x = ω ∈ ℝ` and `θ = 2πω/T`
(`θ = ω` for `T = 2π`), `(1 − ρe^{−iθ})(1 − ρe^{iθ}) = 1 − 2ρ cos θ + ρ²`. -/
theorem sden_ar1_cos (ρ ω : ℝ) :
    (1 - ρ * fourier (-1) (ω : AddCircle T)) * (1 - ρ * fourier 1 (ω : AddCircle T)) =
      ((1 - 2 * ρ * Real.cos (2 * Real.pi * ω / T) + ρ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  set θ : ℝ := 2 * Real.pi * ω / T
  have e1 : 2 * (Real.pi : ℂ) * I * ((-1 : ℤ) : ℂ) * ω / T = -(θ : ℂ) * I := by
    simp only [θ]; push_cast; ring
  have e2 : 2 * (Real.pi : ℂ) * I * ((1 : ℤ) : ℂ) * ω / T = (θ : ℂ) * I := by
    simp only [θ]; push_cast; ring
  rw [e1, e2]
  have hc := Complex.two_cos (θ : ℂ)
  have hp : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  push_cast
  rw [← Complex.ofReal_cos] at hc ⊢
  linear_combination (ρ : ℂ) ^ 2 * hp + (ρ : ℂ) * hc

theorem sden_conj_one_sub (ρ : ℝ) (x : AddCircle T) :
    conj (1 - (ρ : ℂ) * fourier (-1) x) = 1 - ρ * fourier 1 x := by
  rw [map_sub, map_one, map_mul, Complex.conj_ofReal, ← fourier_neg, neg_neg]

/-- The AR(1) spectrum is `1/|1 − ρe_{−1}(x)|²`, real and positive. -/
theorem sden_ar1_eq_normSq {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    sdenSeries (sdenAR1 ρ) x = (((Complex.normSq (1 - ρ * fourier (-1) x))⁻¹ : ℝ) : ℂ) := by
  rw [sden_ar1_series hρ, ← sden_conj_one_sub, Complex.mul_conj, ofReal_inv]

/-- AKMM p. 863 for the AR(1): with `x = ω` and `θ = 2πω/T`, `|1 − ρe^{−iθ}|² = 1 − 2ρ cos θ + ρ²`,
so the AR(1) spectral density is `1/(T(1 − 2ρ cos θ + ρ²))` (`1/(2π(1 − 2ρ cos ω + ρ²))`
for `T = 2π`). -/
theorem sden_ar1_normSq_cos (ρ ω : ℝ) :
    Complex.normSq (1 - ρ * fourier (-1) (ω : AddCircle T)) =
      1 - 2 * ρ * Real.cos (2 * Real.pi * ω / T) + ρ ^ 2 := by
  have := sden_ar1_cos (T := T) ρ ω
  rw [← sden_conj_one_sub, Complex.mul_conj] at this
  exact_mod_cast this

theorem sden_ar1_nonneg {ρ : ℝ} (hρ : |ρ| < 1) (x : AddCircle T) :
    (sdenSeries (sdenAR1 ρ) x).im = 0 ∧ 0 ≤ (sdenSeries (sdenAR1 ρ) x).re := by
  rw [sden_ar1_eq_normSq hρ, ofReal_im, ofReal_re]
  exact ⟨rfl, inv_nonneg.2 (Complex.normSq_nonneg _)⟩

/-- The AR(1) spectral measure: density `1/(T|1 − ρe_{−1}(x)|²)` with respect to Lebesgue
measure on the circle. -/
theorem sden_ar1_measure [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) :
    sdenMeasure (T := T) (sdenAR1 ρ) = (volume : Measure (AddCircle T)).withDensity
      fun x => ENNReal.ofReal ((Complex.normSq (1 - ρ * fourier (-1) x))⁻¹ / T) := by
  unfold sdenMeasure
  simp_rw [sden_ar1_eq_normSq hρ, ofReal_re]

/-- The AR(1) autocovariance `ρ^{|h|}/(1 − ρ²)` is the sequence of Fourier coefficients of its
spectral measure, hence positive definite (Herglotz). -/
theorem sden_ar1_coeff [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) (h : ℤ) :
    ∫ x, fourier h x ∂(sdenMeasure (T := T) (sdenAR1 ρ)) = sdenAR1 ρ h :=
  sden_measure_coeff (sden_ar1_summable hρ) (sden_ar1_nonneg hρ) h

theorem sden_ar1_posDef [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) : hergPosDef (sdenAR1 ρ) := by
  have := sden_measure_finite (T := T) (sden_ar1_summable hρ)
  exact herg_posDef_of_measure (sdenMeasure (T := T) (sdenAR1 ρ))
    fun h => (sden_ar1_coeff hρ h).symm

/-- **White noise**: the exponentials `eₜ ∈ L²(Haar)` are a weakly stationary process with
`γ(0) = 1`, `γ(h) = 0` for `h ≠ 0` (orthonormality); its spectral measure is Haar measure,
density `1/T` (`1/2π`). -/
theorem sden_white_noise [Fact (0 < T)] :
    sdenStationary (fourierLp (T := T) 2) (fun h => if h = 0 then 1 else 0) := by
  intro t h
  rw [orthonormal_iff_ite.1 orthonormal_fourier]
  simp

/-- `φ(x) = 1/(1 − ρe_{−1}(x)) = Σⱼρʲe_{−j}(x)`, the transfer function of the AR(1) filter. -/
noncomputable def sdenPhi (ρ : ℝ) (hρ : |ρ| < 1) : C(AddCircle T, ℂ) :=
  ⟨fun x => (1 - ρ * fourier (-1) x)⁻¹,
    (continuous_const.sub (continuous_const.mul (fourier (-1)).continuous)).inv₀
      fun x => sden_one_sub_ne_zero hρ (-1) x⟩

/-- The AR(1) process `Xₜ = eₜφ ∈ L²(Haar)` driven by the white noise `εₜ = eₜ`. -/
noncomputable def sdenAR1Proc [Fact (0 < T)] (ρ : ℝ) (hρ : |ρ| < 1) (t : ℤ) :
    MeasureTheory.Lp ℂ 2 (haarAddCircle (T := T)) :=
  ContinuousMap.toLp 2 haarAddCircle ℂ (fourier t * sdenPhi ρ hρ)

/-- The AR(1) recursion `Xₜ = ρXₜ₋₁ + εₜ`. -/
theorem sden_ar1_recursion [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) (t : ℤ) :
    sdenAR1Proc (T := T) ρ hρ t = (ρ : ℂ) • sdenAR1Proc ρ hρ (t - 1) + fourierLp 2 t := by
  unfold sdenAR1Proc
  rw [← map_smul, ← map_add]
  congr 1
  ext x
  have hne := sden_one_sub_ne_zero hρ (-1) x
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, sdenPhi,
    ContinuousMap.coe_mk, smul_eq_mul, sub_eq_add_neg t 1, fourier_add]
  field_simp
  ring

/-- The AR(1) process is weakly stationary with autocovariance `ρ^{|h|}/(1 − ρ²)`. -/
theorem sden_ar1_stationary [Fact (0 < T)] {ρ : ℝ} (hρ : |ρ| < 1) :
    sdenStationary (sdenAR1Proc (T := T) ρ hρ) (sdenAR1 ρ) := by
  intro t h
  unfold sdenAR1Proc
  rw [ContinuousMap.inner_toLp]
  have e : ∀ x : AddCircle T, (fourier (t + h) * sdenPhi ρ hρ : C(AddCircle T, ℂ)) x *
      conj ((fourier t * sdenPhi ρ hρ : C(AddCircle T, ℂ)) x) =
        fourier h x * sdenSeries (sdenAR1 ρ) x := by
    intro x
    have hc : fourier t x * fourier (-t) x = 1 := by
      rw [← fourier_add, add_neg_cancel, fourier_zero]
    rw [sden_ar1_series hρ]
    simp only [ContinuousMap.mul_apply, sdenPhi, ContinuousMap.coe_mk, map_mul, map_inv₀,
      sden_conj_one_sub, ← fourier_neg, fourier_add, mul_inv]
    linear_combination (fourier h x * (1 - ρ * fourier (-1) x)⁻¹ * (1 - ρ * fourier 1 x)⁻¹) * hc
  simp_rw [e]
  exact sden_coeff (sden_ar1_summable hρ) h

end AKMM.RealBusinessCycles
