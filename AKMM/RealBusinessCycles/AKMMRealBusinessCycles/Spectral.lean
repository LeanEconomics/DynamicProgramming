/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The spectrum of a stationary process

AKMM, Appendix 14.A, pp. 863–864.

For an absolutely summable autocovariance sequence `γ : ℤ → ℝ`, the spectrum is
`s(ω) = (1/2π)Σₖ γₖe^{−ikω}` (`specC`, complex-valued).

* Orthogonality: `∫_{−π}^{π} e^{imω}dω = 2π` if `m = 0` and `0` otherwise (`appx_orth`).
* **The inversion formula** `∫_{−π}^{π} s(ω)e^{ikω}dω = γₖ` (`appx_inversion`), interchanging the
  sum and the integral by dominated convergence (the bound `Σ|γₙ| < ∞`).
* **The variance** `Var(Y) = γ₀ = ∫_{−π}^{π} s(ω)dω` (`appx_variance`).
* For symmetric `γ` (`γ₋ₖ = γₖ`, as for autocovariances) the spectrum is even
  (`appx_spec_even`), so the variance contributed by the band `ω₁ ≤ |ω| ≤ ω₂` is
  `2∫_{ω₁}^{ω₂}s` (`appx_band_variance`).
* **Linear filters** (finite, `Y^c_t = Σ_{j∈J}c_jY_{t−j}`): the filtered autocovariances are
  `γ^c_k = Σ_jΣ_l c_jc_lγ_{k−j+l}` (`appx_filter_autocov`, from second moments of the process),
  and the filtered spectrum is `C(e^{−iω})C(e^{iω})s(ω) = |C(e^{−iω})|²s(ω)`
  (`appx_filtered_spectrum`, `appx_transfer_normSq`).

Departures: filters are finite (lead–lag polynomials with finitely many terms); the HP and
band-pass filters are infinite two-sided filters, for which only the gain functions are formalised
(`Gains`). The spectral representation theorem (Cramér) is proved in Hilbert-space form in
`Herglotz`, `SpectralDensity` and `Cramer`.
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory

/-- AKMM, p. 863: the spectrum `s(ω) = (1/2π)Σₖ γₖe^{−ikω}`. -/
noncomputable def specC (γ : ℤ → ℝ) (ω : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I)

/-- Orthogonality of the exponentials on `[−π, π]`. -/
theorem appx_orth (m : ℤ) :
    ∫ ω in (-Real.pi)..Real.pi, Complex.exp ((((m : ℝ) * ω : ℝ) : ℂ) * I) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, zero_mul, ofReal_zero, Complex.exp_zero,
      intervalIntegral.integral_const, real_smul, mul_one]
    push_cast
    ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hm) I_ne_zero
    have e : (fun ω : ℝ => Complex.exp ((((m : ℝ) * ω : ℝ) : ℂ) * I)) =
        fun ω : ℝ => Complex.exp ((m : ℂ) * I * ω) := by
      funext ω; push_cast; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((m : ℂ) * I * (Real.pi : ℂ)) =
        Complex.exp ((m : ℂ) * I * ((-Real.pi : ℝ) : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I m
      rw [show (m : ℂ) * I * (Real.pi : ℂ) =
        (m : ℂ) * I * ((-Real.pi : ℝ) : ℂ) + m * (2 * Real.pi * I) by push_cast; ring,
        Complex.exp_add, h1, mul_one]
    rw [h2, sub_self, zero_div]

/-- The summands `γₙe^{i(k−n)ω}` of `s(ω)e^{ikω}`, up to `1/2π`. -/
theorem appx_spec_mul_exp (γ : ℤ → ℝ) (k : ℤ) (ω : ℝ) :
    specC γ ω * Complex.exp ((((k : ℝ) * ω : ℝ) : ℂ) * I) =
      (1 / (2 * Real.pi) : ℂ) *
        ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((((k - n : ℤ) : ℝ) * ω : ℝ) : ℂ) * I) := by
  unfold specC
  rw [mul_assoc, ← tsum_mul_right]
  congr 2
  funext n
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem appx_norm_term (γ : ℤ → ℝ) (n : ℤ) (x : ℝ) :
    ‖(γ n : ℂ) * Complex.exp ((x : ℂ) * I)‖ = |γ n| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **AKMM, p. 863: the inversion formula.** If `Σ|γₙ| < ∞`, then
`∫_{−π}^{π} s(ω)e^{ikω}dω = γₖ` for every integer `k`. -/
theorem appx_inversion (γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|) (k : ℤ) :
    ∫ ω in (-Real.pi)..Real.pi, specC γ ω * Complex.exp ((((k : ℝ) * ω : ℝ) : ℂ) * I) = γ k := by
  set F : ℤ → ℝ → ℂ := fun n ω =>
    (γ n : ℂ) * Complex.exp (((((k - n : ℤ) : ℝ) * ω : ℝ) : ℂ) * I) with hFdef
  have hsumm : ∀ ω, Summable fun n => F n ω := fun ω =>
    Summable.of_norm_bounded hγ fun n => (appx_norm_term γ n _).le
  have hcont : ∀ n, Continuous (F n) := fun n => by
    simp only [hFdef]; fun_prop
  have hS := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -Real.pi) (b := Real.pi) (F := F) (f := fun ω => ∑' n, F n ω)
    (fun n _ => |γ n|) (fun n => (hcont n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t _ => (appx_norm_term γ n _).le)
    (ae_of_all _ fun _ _ => hγ) intervalIntegrable_const
    (ae_of_all _ fun t _ => (hsumm t).hasSum)
  have hval : ∀ n, ∫ ω in (-Real.pi)..Real.pi, F n ω =
      if n = k then (γ k : ℂ) * (2 * Real.pi) else 0 := fun n => by
    simp only [hFdef]
    rw [intervalIntegral.integral_const_mul, appx_orth]
    by_cases h : n = k
    · subst h; simp
    · have : k - n ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      simp [this, h]
  simp only [hval] at hS
  have hI := hS.unique (hasSum_ite_eq k _)
  simp only [appx_spec_mul_exp]
  rw [intervalIntegral.integral_const_mul, hI]
  have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- **AKMM, p. 864: the variance is the integral of the spectrum**,
`Var(Yₜ) = γ₀ = ∫_{−π}^{π} s(ω)dω`. -/
theorem appx_variance (γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|) :
    ∫ ω in (-Real.pi)..Real.pi, specC γ ω = γ 0 := by
  have := appx_inversion γ hγ 0
  simpa using this

/-- For a symmetric autocovariance sequence (`γ₋ₙ = γₙ`), the spectrum is even. -/
theorem appx_spec_even (γ : ℤ → ℝ) (hsym : ∀ n, γ (-n) = γ n) (ω : ℝ) :
    specC γ (-ω) = specC γ ω := by
  unfold specC
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  simp only [Equiv.neg_apply, hsym, Int.cast_neg]
  congr 3
  ring_nf

/-- **AKMM, p. 864, the variance of a frequency band, corrected.** For symmetric `γ` the variance
contributed by the frequencies `ω₁ ≤ |ω| ≤ ω₂` is `∫_{−ω₂}^{−ω₁}s + ∫_{ω₁}^{ω₂}s = 2∫_{ω₁}^{ω₂}s`
(the book writes `∫_{ω₁}^{ω₂}f(ω)dω`, with `f` undefined and the negative band omitted). -/
theorem appx_band_variance (γ : ℤ → ℝ) (hsym : ∀ n, γ (-n) = γ n) (ω₁ ω₂ : ℝ) :
    (∫ ω in (-ω₂)..(-ω₁), specC γ ω) + ∫ ω in ω₁..ω₂, specC γ ω =
      2 * ∫ ω in ω₁..ω₂, specC γ ω := by
  have h := intervalIntegral.integral_comp_neg (a := ω₁) (b := ω₂) (fun ω => specC γ ω)
  simp only [appx_spec_even γ hsym] at h
  rw [← h]
  ring

/-- The autocovariances of the filtered series `Σ_{j∈J}c_jY_{t−j}`:
`γ^c_k = Σ_jΣ_l c_jc_lγ_{k−j+l}`. -/
def filtAutocov (J : Finset ℤ) (c γ : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l)

/-- The transfer function `C(e^{−iω}) = Σ_{j∈J}c_je^{−ijω}` of the filter. -/
noncomputable def transferFn (J : Finset ℤ) (c : ℤ → ℝ) (ω : ℝ) : ℂ :=
  ∑ j ∈ J, (c j : ℂ) * Complex.exp (((-(j * ω) : ℝ) : ℂ) * I)

/-- AKMM, p. 864: if `Y` has second moments `E[Y_sY_t] = γ_{s−t}` (mean zero, weakly stationary),
the filtered series `Y^c_t = Σ_{j∈J}c_jY_{t−j}` has `E[Y^c_tY^c_{t−k}] = γ^c_k`. -/
theorem appx_filter_autocov {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (Y : ℤ → Ω → ℝ) (γ : ℤ → ℝ) (hY : ∀ s t, ∫ x, Y s x * Y t x ∂μ = γ (s - t))
    (hint : ∀ s t, Integrable (fun x => Y s x * Y t x) μ) (J : Finset ℤ) (c : ℤ → ℝ)
    (t k : ℤ) :
    ∫ x, (∑ j ∈ J, c j * Y (t - j) x) * (∑ l ∈ J, c l * Y (t - k - l) x) ∂μ =
      filtAutocov J c γ k := by
  have e : ∀ x, (∑ j ∈ J, c j * Y (t - j) x) * (∑ l ∈ J, c l * Y (t - k - l) x) =
      ∑ j ∈ J, ∑ l ∈ J, c j * c l * (Y (t - j) x * Y (t - k - l) x) := fun x => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (hint _ _).const_mul _]
  unfold filtAutocov
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint _ _).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, hY]
  congr 2
  ring

/-- **AKMM, p. 864: the spectrum of a filtered series.** For a finite filter `c` on `J` and
absolutely summable `γ`, `s^c(ω) = C(e^{−iω})C(e^{iω})s(ω)`. -/
theorem appx_filtered_spectrum (J : Finset ℤ) (c γ : ℤ → ℝ) (hγ : Summable fun n => |γ n|)
    (ω : ℝ) :
    specC (filtAutocov J c γ) ω = transferFn J c ω * transferFn J c (-ω) * specC γ ω := by
  set E : ℤ → ℂ := fun n => Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) with hE
  have hEadd : ∀ m j l : ℤ, E (m + (j - l)) = E m * E j * E (-l) := fun m j l => by
    simp only [hE, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum1 : ∀ j l : ℤ, Summable fun k : ℤ => ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k :=
    fun j l => by
      have hs : Summable fun k : ℤ => |c j * c l| * |γ (k + (l - j))| :=
        (hγ.comp_injective (add_left_injective (l - j))).mul_left _
      refine Summable.of_norm_bounded hs fun k => le_of_eq ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, show k - j + l = k + (l - j) by ring]
  unfold specC
  suffices key : ∑' n : ℤ,
      ((filtAutocov J c γ n : ℝ) : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) =
      transferFn J c ω * transferFn J c (-ω) *
        ∑' n : ℤ, (γ n : ℂ) * Complex.exp (((-(n * ω) : ℝ) : ℂ) * I) by
    rw [key]; ring
  simp only [filtAutocov]
  have e1 : ∀ k : ℤ, ((∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ∑ j ∈ J, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k := fun k => by
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  rw [show (fun k : ℤ => ((∑ j ∈ J, ∑ l ∈ J, c j * c l * γ (k - j + l) : ℝ) : ℂ) *
      Complex.exp (((-(k * ω) : ℝ) : ℂ) * I)) =
      fun k => ∑ j ∈ J, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k from funext e1]
  rw [Summable.tsum_finsetSum fun j _ => summable_sum fun l _ => hsum1 j l]
  have inner : ∀ j l : ℤ, ∑' k : ℤ, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ((c j : ℂ) * E j) * ((c l : ℂ) * E (-l)) * ∑' m : ℤ, (γ m : ℂ) * E m := fun j l => by
    rw [← (Equiv.addRight (j - l)).tsum_eq, ← tsum_mul_left]
    congr 1
    funext m
    simp only [Equiv.coe_addRight, hEadd]
    rw [show m + (j - l) - j + l = m by ring]
    push_cast
    ring
  have hsj : ∀ j, ∑' k : ℤ, ∑ l ∈ J, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k =
      ∑ l ∈ J, ∑' k : ℤ, ((c j * c l * γ (k - j + l) : ℝ) : ℂ) * E k := fun j =>
    Summable.tsum_finsetSum fun l _ => hsum1 j l
  simp only [hsj, inner]
  unfold transferFn
  simp only [hE]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring_nf

/-- AKMM, p. 864: `C(e^{−iω})C(e^{iω}) = |C(e^{−iω})|²` for a real filter, so
`s^c = |C(e^{−iω})|²s`. -/
theorem appx_transfer_normSq (J : Finset ℤ) (c : ℤ → ℝ) (ω : ℝ) :
    transferFn J c ω * transferFn J c (-ω) = Complex.normSq (transferFn J c ω) := by
  rw [← Complex.mul_conj]
  congr 1
  unfold transferFn
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

end AKMM.RealBusinessCycles
