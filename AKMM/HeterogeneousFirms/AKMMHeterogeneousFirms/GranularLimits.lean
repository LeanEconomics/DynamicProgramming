/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Granular volatility as the number of firms grows (AKMM §22.7, pp. 682, 684–685)

AKMM, §22.7, pp. 682 and 684–685, after Gabaix (2011). With `N` firms of sizes `S₀, …, S_{N−1}`
and firm volatility `σ`, GDP volatility (22.30) is `σ_Y = σ √(Σ Sᵢ²) / Σ Sᵢ` (`gabaixVol`,
`gabaixVol_eq_shares`). The book contrasts `σ_Y ∝ 1/√N` (thin tails) with Gabaix's
`σ_Y ∼ v_ζ σ / log N` under Zipf's law (p. 685). This module goes **beyond the text** (decision
5) and proves the parts of Gabaix's analysis that need no stable laws.

* **Finite variance, i.i.d. sizes** (the "law of large numbers" calculation of p. 682 with
  random sizes): if the sizes are i.i.d., positive, with `E[S²] < ∞`, then almost surely
  `√N σ_Y → σ √(E[S²]) / E[S]` (`gabaix_iid_sqrt_tendsto`, by the strong law of large numbers),
  so `σ_Y → 0` like `1/√N` (`gabaix_iid_vol_tendsto_zero`).
* **The Pareto law** (22.33) with scale `t` and exponent `ζ` (`χ = t^ζ`): `E[Sⁿ] = ζtⁿ/(ζ − n)`
  for `n < ζ` (`gabaix_pareto_density_pow`, `gabaix_pareto_moment`), and `E[Sⁿ] = ∞` for `n ≥ ζ`
  (`gabaix_pareto_not_integrable_pow`), so the variance is infinite exactly when `ζ ≤ 2`. For
  i.i.d. Pareto sizes on the product space: if `ζ > 2`, almost surely
  `√N σ_Y → σ(ζ − 1)/√(ζ(ζ − 2))` (`gabaix_pareto_iid`); if `1 < ζ ≤ 2`, almost surely
  `√N σ_Y → ∞` (`gabaix_pareto_iid_fat`, from the general infinite-variance result
  `gabaix_iid_infinite_variance`, by the strong law for truncations): the fat tail breaks the
  `1/√N` law.
* **The deterministic rank-size rule** `Sᵢ = i^{−1/ζ}` (`gabaixRank`, the firm of rank `i` in
  Zipf's law (22.33) in its deterministic form). Sums of `i^{−β}` are compared with integrals
  (`gabaix_sum_rpow_bounds`, `gabaix_sum_rpow_tendsto`, `gabaix_harmonic_div_log_tendsto`).
  The three regimes:
  - `ζ = 1` (Zipf): `log N · σ_Y → σπ/√6` (`gabaix_zipf_log_tendsto`), the book's
    `1/log N` scaling with an explicit constant;
  - `1 < ζ < 2`: `N^{1−1/ζ} σ_Y → σ(1 − 1/ζ)√(Σᵢ i^{−2/ζ})`
    (`gabaix_rank_mid_tendsto`), so `σ_Y` falls more slowly than `1/√N`
    (`gabaix_rank_mid_sqrt_tendsto_atTop`);
  - `ζ = 2`: `√(N/log N) σ_Y → σ/2` (`gabaix_rank_two_tendsto`);
  - `ζ > 2`: `√N σ_Y → σ(ζ − 1)/√(ζ(ζ − 2))` (`gabaix_rank_thin_tendsto`), the same constant as
    for i.i.d. Pareto sizes.
* **The largest firm** (pathwise, for every realisation of the sizes, in particular almost
  surely for i.i.d. Pareto sizes with `ζ = 1`: `gabaix_pareto_vol_ge_share`):
  `σ_Y ≥ σ maxᵢ Sᵢ / Σ Sᵢ` (`gabaix_vol_ge_share`), and `σ_Y ≤ σ` (`gabaix_vol_le`); for
  the Zipf rank-size rule `σ_Y ≥ σ/(1 + log N)` for every `N ≥ 1` (`gabaix_zipf_vol_ge`).

Not formalised: Gabaix's theorem itself, that for i.i.d. Pareto sizes with `ζ < 2` the
normalised volatility converges **in distribution** to a nondegenerate random variable `v_ζσ`
(a generalised central limit theorem with stable limit laws, which Mathlib does not have), and
the numerical illustrations `1/log 10⁶ ≈ 0.072` and Gabaix's coefficient `0.12`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace AKMM.HeterogeneousFirms

/-! ### GDP volatility of the first `N` firms -/

/-- AKMM, (22.30), p. 682: GDP volatility of the first `N` firms with sizes `S 0, …, S (N − 1)`
and firm volatility `σ`, `σ_Y = σ √(Σ Sᵢ²) / Σ Sᵢ`. -/
noncomputable def gabaixVol (σ : ℝ) (S : ℕ → ℝ) (N : ℕ) : ℝ :=
  σ * Real.sqrt (∑ i ∈ Finset.range N, S i ^ 2) / ∑ i ∈ Finset.range N, S i

/-- AKMM, (22.30), p. 682: `gabaixVol` is (22.30), `σ √(Σ (Sᵢ/Y)²)` with `Y = Σ Sᵢ`. -/
theorem gabaixVol_eq_shares (σ : ℝ) (S : ℕ → ℝ) (N : ℕ)
    (hY : 0 < ∑ i ∈ Finset.range N, S i) :
    gabaixVol σ S N =
      σ * Real.sqrt (∑ i ∈ Finset.range N, (S i / ∑ j ∈ Finset.range N, S j) ^ 2) := by
  set Y := ∑ j ∈ Finset.range N, S j
  have e : ∑ i ∈ Finset.range N, (S i / Y) ^ 2 = (∑ i ∈ Finset.range N, S i ^ 2) / Y ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [div_pow]
  rw [e, Real.sqrt_div' _ (sq_nonneg Y), Real.sqrt_sq hY.le, gabaixVol]
  ring

/-- AKMM, p. 682: rescaling by `√N`, `√N σ_Y = σ √(N⁻¹ Σ Sᵢ²) / (N⁻¹ Σ Sᵢ)`: sample moments. -/
theorem gabaix_sqrt_mul_vol (σ : ℝ) (S : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    Real.sqrt N * gabaixVol σ S N =
      σ * Real.sqrt ((N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S i ^ 2) /
        ((N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S i) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN'
  rw [Real.sqrt_mul (inv_nonneg.2 hN'.le), Real.sqrt_inv, gabaixVol]
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN'.le
  by_cases hB : ∑ i ∈ Finset.range N, S i = 0
  · rw [hB]; simp
  · have hi : (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ := by rw [← mul_inv, hsq]
    rw [hi]
    field_simp

/-! ### Thin tails: i.i.d. sizes with finite variance -/

/-- AKMM, p. 682, beyond the text: **i.i.d. sizes with finite variance**. If the firm sizes
`X 0, X 1, …` are pairwise independent, identically distributed, positive and square
integrable, then almost surely `√N σ_Y → σ √(E[S²]) / E[S]`: aggregate volatility falls like
`1/√N`. By the strong law of large numbers applied to `Sᵢ` and to `Sᵢ²`. -/
theorem gabaix_iid_sqrt_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hpos : ∀ᵐ ω ∂μ, 0 < X 0 ω) (σ : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ (fun i => X i ω) N) atTop
      (𝓝 (σ * Real.sqrt (∫ ω, X 0 ω ^ 2 ∂μ) / ∫ ω, X 0 ω ∂μ)) := by
  have hint : Integrable (X 0) μ := hL2.integrable one_le_two
  have hm : 0 < ∫ ω, X 0 ω ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le) hint]
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h' : ∀ᵐ ω ∂μ, ω ∉ Function.support (X 0) := measure_eq_zero_iff_ae_notMem.1 h0
    obtain ⟨ω, h1, h2⟩ := (hpos.and h').exists
    exact h2 (Function.mem_support.2 h1.ne')
  have h1 := strong_law_ae X hint hindep hident
  have h2 := strong_law_ae (fun i ω => X i ω ^ 2) hL2.integrable_sq
    (fun i j hij => (hindep hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
    (fun i => (hident i).comp (measurable_id.pow_const 2))
  filter_upwards [h1, h2] with ω h1 h2
  have hlim := ((h2.sqrt).const_mul σ).div h1 hm.ne'
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [gabaix_sqrt_mul_vol σ _ hN]
  simp only [smul_eq_mul, Pi.div_apply]

/-- AKMM, p. 682, beyond the text: with i.i.d. square-integrable positive sizes, aggregate
volatility vanishes almost surely as `N → ∞`. -/
theorem gabaix_iid_vol_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hpos : ∀ᵐ ω ∂μ, 0 < X 0 ω) (σ : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => gabaixVol σ (fun i => X i ω) N) atTop (𝓝 0) := by
  filter_upwards [gabaix_iid_sqrt_tendsto X hL2 hindep hident hpos σ] with ω h
  have hinv : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop)
  have := hinv.mul h
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  field_simp

/-! ### The Pareto law (22.33) -/

/-- AKMM, (22.33), p. 684: the Pareto density times `xⁿ` is `ζt^ζ x^{n−ζ−1}` on `[t, ∞)` and
zero below `t`. -/
theorem gabaix_pareto_density_pow {t ζ : ℝ} (ht : 0 < t) (hζ : 0 < ζ) (n : ℕ) :
    (fun x : ℝ => (paretoPDF t ζ x).toReal • x ^ n) =
      Set.indicator (Set.Ici t) (fun x => ζ * t ^ ζ * x ^ ((n : ℝ) - ζ - 1)) := by
  funext x
  rw [paretoPDF, ENNReal.toReal_ofReal (paretoPDFReal_nonneg ht.le hζ.le x), smul_eq_mul,
    paretoPDFReal]
  by_cases hx : t ≤ x
  · have hx0 : 0 < x := ht.trans_le hx
    simp only [hx, ↓reduceIte, Set.indicator_of_mem (Set.mem_Ici.2 hx)]
    rw [← Real.rpow_natCast x n, mul_assoc, ← Real.rpow_add hx0]
    ring_nf
  · simp [hx]

/-- AKMM, (22.33), p. 684, beyond the text: **fat tails**: under the Pareto law with exponent
`ζ`, the moment `E[Sⁿ]` is infinite (`Sⁿ` is not integrable) when `n ≥ ζ`. In particular the
size distribution has infinite variance for `ζ ≤ 2`, the fat-tailed case of p. 685. -/
theorem gabaix_pareto_not_integrable_pow {t ζ : ℝ} (ht : 0 < t) (hζ : 0 < ζ) (n : ℕ)
    (hn : ζ ≤ n) : ¬ Integrable (fun x : ℝ => x ^ n) (paretoMeasure t ζ) := by
  have hmeas : Measurable (paretoPDF t ζ) := (measurable_paretoPDFReal t ζ).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), paretoPDF t ζ x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [paretoMeasure, integrable_withDensity_iff_integrable_smul' hmeas hlt,
    gabaix_pareto_density_pow ht hζ n, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  intro h
  have hc : ζ * t ^ ζ ≠ 0 := (mul_pos hζ (Real.rpow_pos_of_pos ht ζ)).ne'
  have h' : IntegrableOn (fun x : ℝ => x ^ ((n : ℝ) - ζ - 1)) (Set.Ioi t) := by
    refine IntegrableOn.congr_fun (h.const_mul (ζ * t ^ ζ)⁻¹) (fun x _ => ?_) measurableSet_Ioi
    field_simp
  have := (integrableOn_Ioi_rpow_iff ht).1 h'
  linarith

/-- AKMM, (22.33), p. 684, beyond the text: **moments of the Pareto law** with scale `t > 0` and
exponent `ζ` (`Pr[S > x] = (t/x)^ζ` for `x ≥ t`, so `χ = t^ζ`): for `n < ζ`, `Sⁿ` is
integrable and `E[Sⁿ] = ζtⁿ/(ζ − n)`. -/
theorem gabaix_pareto_moment {t ζ : ℝ} (ht : 0 < t) (n : ℕ) (hn : (n : ℝ) < ζ) :
    Integrable (fun x : ℝ => x ^ n) (paretoMeasure t ζ) ∧
      ∫ x, x ^ n ∂(paretoMeasure t ζ) = ζ * t ^ n / (ζ - n) := by
  have hζ : 0 < ζ := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  have hmeas : Measurable (paretoPDF t ζ) := (measurable_paretoPDFReal t ζ).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), paretoPDF t ζ x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hfun := gabaix_pareto_density_pow ht hζ n
  have hpow : (n : ℝ) - ζ - 1 < -1 := by linarith
  have hon : IntegrableOn (fun x => ζ * t ^ ζ * x ^ ((n : ℝ) - ζ - 1)) (Set.Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 ((integrableOn_Ioi_rpow_of_lt hpow ht).const_mul _)
  refine ⟨?_, ?_⟩
  · rw [paretoMeasure, integrable_withDensity_iff_integrable_smul' hmeas hlt, hfun]
    exact (integrable_indicator_iff measurableSet_Ici).2 hon
  · rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt, hfun,
      integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt hpow ht]
    have hd : (n : ℝ) - ζ - 1 + 1 = -(ζ - n) := by ring
    have hne : ζ - n ≠ 0 := (sub_pos.2 hn).ne'
    have e : t ^ ζ * t ^ (-(ζ - n)) = t ^ n := by
      rw [← Real.rpow_add ht, show ζ + -(ζ - n) = (n : ℝ) by ring, Real.rpow_natCast]
    rw [hd, neg_div_neg_eq, ← e]
    field_simp

/-- AKMM, (22.33), p. 685, beyond the text: **i.i.d. Pareto sizes with `ζ > 2`**. On the
product space of i.i.d. Pareto(`t`, `ζ`) sizes, almost surely
`√N σ_Y → σ(ζ − 1)/√(ζ(ζ − 2))`: with a tail thinner than `ζ = 2`, aggregate volatility falls
like `1/√N`, as in the equal-size calculation of p. 682. -/
theorem gabaix_pareto_iid {t ζ : ℝ} (ht : 0 < t) (hζ : 2 < ζ)
    [IsProbabilityMeasure (paretoMeasure t ζ)] (σ : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ),
      Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ ω N) atTop
        (𝓝 (σ * (ζ - 1) / Real.sqrt (ζ * (ζ - 2)))) := by
  set P := Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ
  set X : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
  have hmp : ∀ i, MeasurePreserving (X i) P (paretoMeasure t ζ) := fun i =>
    measurePreserving_eval_infinitePi _ i
  have hindep : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ => paretoMeasure t ζ) (X := fun _ => id)
      (fun _ => measurable_id)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hmp i).measurable.aemeasurable, (hmp 0).measurable.aemeasurable,
      (hmp i).map_eq.trans (hmp 0).map_eq.symm⟩
  have h1 := gabaix_pareto_moment (ζ := ζ) ht 1 (by norm_num; linarith)
  have h2 := gabaix_pareto_moment (ζ := ζ) ht 2 (by norm_num; linarith)
  have hL2' : MemLp (fun x : ℝ => x) 2 (paretoMeasure t ζ) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2.1
  have hL2 : MemLp (X 0) 2 P := hL2'.comp_measurePreserving (hmp 0)
  have hpos0 : ∀ᵐ x ∂(paretoMeasure t ζ), 0 < x := by
    rw [paretoMeasure, ae_withDensity_iff
      (show Measurable (paretoPDF t ζ) from (measurable_paretoPDFReal t ζ).ennreal_ofReal)]
    refine ae_of_all _ fun x hx => ?_
    by_contra hx0
    have : x < t := lt_of_le_of_lt (not_lt.1 hx0) ht
    exact hx (paretoPDF_of_lt this)
  have hpos : ∀ᵐ ω ∂P, 0 < X 0 ω := (hmp 0).quasiMeasurePreserving.ae hpos0
  have hE1 : ∫ ω, X 0 ω ∂P = ζ * t / (ζ - 1) := by
    have := h1.2
    rw [← (hmp 0).map_eq, integral_map (hmp 0).measurable.aemeasurable
      (continuous_pow 1).aestronglyMeasurable] at this
    simpa using this
  have hE2 : ∫ ω, X 0 ω ^ 2 ∂P = ζ * t ^ 2 / (ζ - 2) := by
    have := h2.2
    rw [← (hmp 0).map_eq, integral_map (hmp 0).measurable.aemeasurable
      (continuous_pow 2).aestronglyMeasurable] at this
    simpa using this
  have hlim := gabaix_iid_sqrt_tendsto X hL2 (fun i j hij => hindep.indepFun hij) hident hpos σ
  rw [hE1, hE2] at hlim
  have hc : σ * Real.sqrt (ζ * t ^ 2 / (ζ - 2)) / (ζ * t / (ζ - 1)) =
      σ * (ζ - 1) / Real.sqrt (ζ * (ζ - 2)) := by
    have hz : 0 < ζ := by linarith
    have hz2 : 0 < ζ - 2 := by linarith
    have hz1 : 0 < ζ - 1 := by linarith
    have hapos := Real.sqrt_pos.2 hz
    have hbpos := Real.sqrt_pos.2 hz2
    rw [Real.sqrt_div' _ hz2.le, Real.sqrt_mul hz.le, Real.sqrt_sq ht.le, Real.sqrt_mul hz.le]
    field_simp
    rw [Real.sq_sqrt hz.le]
  rw [hc] at hlim
  exact hlim

/-! ### Fat tails: i.i.d. sizes with infinite variance -/

/-- AKMM, p. 685, beyond the text: **i.i.d. sizes with infinite variance**. If the firm sizes
are pairwise independent, identically distributed, positive and integrable but `E[S²] = ∞`,
then almost surely `√N σ_Y → ∞`: aggregate volatility falls strictly more slowly than `1/√N`.
By the strong law applied to the truncations `min(Sᵢ², M)` and monotone convergence. -/
theorem gabaix_iid_infinite_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hsq : ¬ Integrable (fun ω => X 0 ω ^ 2) μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hpos : ∀ᵐ ω ∂μ, 0 < X 0 ω) {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ (fun i => X i ω) N) atTop
      atTop := by
  have hm : 0 < ∫ ω, X 0 ω ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le) hint]
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h' : ∀ᵐ ω ∂μ, ω ∉ Function.support (X 0) := measure_eq_zero_iff_ae_notMem.1 h0
    obtain ⟨ω, h1, h2⟩ := (hpos.and h').exists
    exact h2 (Function.mem_support.2 h1.ne')
  have hX0m : AEMeasurable (X 0) μ := (hident 0).aemeasurable_fst
  have hgm : ∀ M : ℕ, Measurable (fun x : ℝ => min (x ^ 2) (M : ℝ)) := fun M =>
    (measurable_id.pow_const 2).min measurable_const
  have hYint : ∀ M : ℕ, Integrable (fun ω => min (X 0 ω ^ 2) (M : ℝ)) μ := fun M =>
    Integrable.of_bound ((hgm M).comp_aemeasurable hX0m).aestronglyMeasurable M
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (Nat.cast_nonneg M))]
        exact min_le_right _ _)
  have hslln : ∀ᵐ ω ∂μ, ∀ M : ℕ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
      ∑ i ∈ Finset.range N, min (X i ω ^ 2) (M : ℝ)) atTop
      (𝓝 (∫ ω, min (X 0 ω ^ 2) (M : ℝ) ∂μ)) :=
    ae_all_iff.2 fun M => strong_law_ae (fun i ω => min (X i ω ^ 2) (M : ℝ)) (hYint M)
      (fun i j hij => (hindep hij).comp (hgm M) (hgm M)) (fun i => (hident i).comp (hgm M))
  have h1 := strong_law_ae X hint hindep hident
  have hinf : ∫⁻ ω, ENNReal.ofReal (X 0 ω ^ 2) ∂μ = ⊤ := by
    by_contra h
    apply hsq
    refine ⟨(hX0m.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
    exact lt_top_iff_ne_top.2 h
  have hten : Tendsto (fun M : ℕ => ∫⁻ ω, ENNReal.ofReal (min (X 0 ω ^ 2) (M : ℝ)) ∂μ) atTop
      (𝓝 ⊤) := by
    rw [← hinf]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun M => (((hgm M).comp_aemeasurable hX0m)).ennreal_ofReal)
      (ae_of_all _ fun ω M M' hMM' => ENNReal.ofReal_le_ofReal
        (min_le_min_left _ (by exact_mod_cast hMM')))
      (ae_of_all _ fun ω => ?_)
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈X 0 ω ^ 2⌉₊) fun M hM => min_eq_left ?_
    exact (Nat.le_ceil _).trans (by exact_mod_cast hM)
  have hbig : ∀ C : ℝ, ∃ M : ℕ, C < ∫ ω, min (X 0 ω ^ 2) (M : ℝ) ∂μ := by
    intro C
    obtain ⟨M, hM⟩ := ((ENNReal.tendsto_nhds_top_iff_nnreal.1 hten) C.toNNReal).exists
    refine ⟨M, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal (hYint M)
      (ae_of_all _ fun ω => le_min (sq_nonneg _) (Nat.cast_nonneg M))] at hM
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hM).1
  filter_upwards [h1, hslln] with ω h1 hY
  have hA : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, X i ω ^ 2) atTop
      atTop := by
    rw [tendsto_atTop]
    intro C
    obtain ⟨M, hM⟩ := hbig C
    filter_upwards [(hY M).eventually (lt_mem_nhds hM)] with N hN
    rw [smul_eq_mul] at hN
    have hle : ∑ i ∈ Finset.range N, min (X i ω ^ 2) (M : ℝ) ≤
        ∑ i ∈ Finset.range N, X i ω ^ 2 :=
      Finset.sum_le_sum fun i _ => min_le_left _ _
    have := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (Nat.cast_nonneg N))
    linarith
  have hlim := ((Real.tendsto_sqrt_atTop.comp hA).const_mul_atTop hσ).atTop_mul_pos
    (inv_pos.2 hm) ((h1.inv₀ hm.ne'))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [gabaix_sqrt_mul_vol σ _ hN]
  simp only [Function.comp_apply, smul_eq_mul, div_eq_mul_inv]

/-- AKMM, p. 685, beyond the text: **i.i.d. Pareto sizes with `1 < ζ ≤ 2`**. On the product
space of i.i.d. Pareto(`t`, `ζ`) sizes, almost surely `√N σ_Y → ∞`: the fat tail breaks the
`1/√N` law of p. 682. (The rate itself, `N^{−(1−1/ζ)}` in distribution, is the stable-law part
of Gabaix's theorem, not formalised; see `gabaix_rank_mid_tendsto` for the rank-size rule.) -/
theorem gabaix_pareto_iid_fat {t ζ : ℝ} (ht : 0 < t) (h1 : 1 < ζ) (h2 : ζ ≤ 2)
    [IsProbabilityMeasure (paretoMeasure t ζ)] {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ),
      Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ ω N) atTop atTop := by
  set P := Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ
  set X : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
  have hmp : ∀ i, MeasurePreserving (X i) P (paretoMeasure t ζ) := fun i =>
    measurePreserving_eval_infinitePi _ i
  have hindep : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ => paretoMeasure t ζ) (X := fun _ => id)
      (fun _ => measurable_id)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hmp i).measurable.aemeasurable, (hmp 0).measurable.aemeasurable,
      (hmp i).map_eq.trans (hmp 0).map_eq.symm⟩
  have hint1 := (gabaix_pareto_moment (ζ := ζ) ht 1 (by norm_num; linarith)).1
  have hint : Integrable (X 0) P := by
    rw [← (hmp 0).map_eq, integrable_map_measure (by fun_prop)
      (hmp 0).measurable.aemeasurable] at hint1
    simp only [pow_one] at hint1
    exact hint1
  have hsq : ¬ Integrable (fun ω => X 0 ω ^ 2) P := by
    intro h
    apply gabaix_pareto_not_integrable_pow (ζ := ζ) ht (by linarith) 2 (by norm_num; exact h2)
    rw [← (hmp 0).map_eq, integrable_map_measure (by fun_prop)
      (hmp 0).measurable.aemeasurable]
    exact h
  have hpos0 : ∀ᵐ x ∂(paretoMeasure t ζ), 0 < x := by
    rw [paretoMeasure, ae_withDensity_iff
      (show Measurable (paretoPDF t ζ) from (measurable_paretoPDFReal t ζ).ennreal_ofReal)]
    refine ae_of_all _ fun x hx => ?_
    by_contra hx0
    exact hx (paretoPDF_of_lt (lt_of_le_of_lt (not_lt.1 hx0) ht))
  exact gabaix_iid_infinite_variance X hint hsq (fun i j hij => hindep.indepFun hij) hident
    ((hmp 0).quasiMeasurePreserving.ae hpos0) hσ

/-! ### The deterministic rank-size rule -/

/-- AKMM, (22.33), p. 684: **the deterministic rank-size rule**. Under (22.33) with `χ = 1`,
the fraction of firms larger than `x` is `x^{−ζ}`, so the firm of rank `k` has size
`k^{−1/ζ}` relative to the largest; `gabaixRank ζ i` is the size of the firm of rank `i + 1`.
`ζ = 1` is Zipf's law `Sₖ = 1/k`. -/
noncomputable def gabaixRank (ζ : ℝ) (i : ℕ) : ℝ := ((i : ℝ) + 1) ^ (-(1 / ζ))

/-- Beyond the text: **integral comparison**. For `0 ≤ β < 1`,
`((N+1)^{1−β} − 1)/(1−β) ≤ Σ_{k=1}^N k^{−β} ≤ 1 + ((N+1)^{1−β} − 1)/(1−β)`. -/
theorem gabaix_sum_rpow_bounds {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (N : ℕ) :
    (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) ≤ ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-β) ∧
      ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-β) ≤
        1 + (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-β)) (Set.Icc 1 (1 + (N : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint : ∫ x in (1 : ℝ)..1 + (N : ℝ), x ^ (-β) =
      (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) := by
    rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow, show -β + 1 = 1 - β by ring,
      add_comm (1 : ℝ)]
  refine ⟨?_, ?_⟩
  · have h := hanti.integral_le_sum
    rw [hint] at h
    exact h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => by rw [add_comm (1 : ℝ)]))
  · have h := hanti.sum_le_integral
    rw [hint] at h
    have e : ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-β) =
        ∑ i ∈ Finset.range N, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-β) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [add_comm (1 : ℝ)]
    have hle : ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-β) ≤
        ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-β) := by
      rw [Finset.sum_range_succ]
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1) (-β)
      linarith
    linarith

/-- Beyond the text: for `0 ≤ β < 1`, `Σ_{k=1}^N k^{−β} ∼ N^{1−β}/(1−β)`. -/
theorem gabaix_sum_rpow_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-β)) / (N : ℝ) ^ (1 - β))
      atTop (𝓝 (1 / (1 - β))) := by
  have hc0 : 0 < 1 - β := by linarith
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) ^ (1 - β))⁻¹) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop hc0).comp hN).inv_tendsto_atTop
  have hq : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
    have h2 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hratio : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / N) ^ (1 - β)) atTop (𝓝 1) := by
    simpa using hq.rpow_const (Or.inl one_ne_zero)
  have hlow : Tendsto (fun N : ℕ => ((((N : ℝ) + 1) / N) ^ (1 - β) - ((N : ℝ) ^ (1 - β))⁻¹) /
      (1 - β)) atTop (𝓝 (1 / (1 - β))) := by
    simpa using (hratio.sub hinv).div_const (1 - β)
  have hup : Tendsto (fun N : ℕ => ((N : ℝ) ^ (1 - β))⁻¹ +
      ((((N : ℝ) + 1) / N) ^ (1 - β) - ((N : ℝ) ^ (1 - β))⁻¹) / (1 - β)) atTop
      (𝓝 (1 / (1 - β))) := by
    simpa using hinv.add hlow
  have hb := gabaix_sum_rpow_bounds hβ0 hβ1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNc : 0 < (N : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hNpos _
    rw [Real.div_rpow (by positivity) hNpos.le, le_div_iff₀ hNc]
    calc _ = (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) := by field_simp
      _ ≤ _ := (hb N).1
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNc : 0 < (N : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hNpos _
    rw [Real.div_rpow (by positivity) hNpos.le, div_le_iff₀ hNc]
    calc _ ≤ 1 + (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) := (hb N).2
      _ = _ := by field_simp

/-- Beyond the text: the harmonic numbers satisfy `H_N / log N → 1`. -/
theorem gabaix_harmonic_div_log_tendsto :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((i : ℝ) + 1)⁻¹) / Real.log N) atTop
      (𝓝 1) := by
  have hH : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((i : ℝ) + 1)⁻¹ = harmonic N := fun N => by
    simp [harmonic]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => (Real.log N)⁻¹ + 1) atTop (𝓝 1) := by
    simpa using hlog.inv_tendsto_atTop.add_const 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [le_div_iff₀ hl, one_mul, hH]
    have h1 := log_add_one_le_harmonic N
    have h2 : Real.log N ≤ Real.log ↑(N + 1) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    linarith
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [div_le_iff₀ hl, hH, add_mul, inv_mul_cancel₀ hl.ne', one_mul]
    linarith [harmonic_le_one_add_log N]

/-- AKMM, p. 685, beyond the text: **Zipf's law, `ζ = 1`**. For the rank-size rule
`Sₖ = 1/k`, `log N · σ_Y → σπ/√6`: aggregate volatility is proportional to `1/log N`, the
book's `σ_Y ∼ v_ζσ/log N`, with the deterministic constant `π/√6 = √(Σ 1/k²)`. -/
theorem gabaix_zipf_log_tendsto (σ : ℝ) :
    Tendsto (fun N : ℕ => Real.log N * gabaixVol σ (gabaixRank 1) N) atTop
      (𝓝 (σ * Real.pi / Real.sqrt 6)) := by
  have hr : ∀ i, gabaixRank 1 i = ((i : ℝ) + 1)⁻¹ := fun i => by
    rw [gabaixRank, div_one, Real.rpow_neg_one]
  have hsq : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, gabaixRank 1 i ^ 2) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
    have h' := hasSum_zeta_two.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h'.congr fun N => ?_
    simp only [Function.comp_apply, Finset.sum_range_succ', hr]
    simp
  have hlim := ((hsq.sqrt).const_mul σ).div gabaix_harmonic_div_log_tendsto one_ne_zero
  have hval : σ * Real.sqrt (Real.pi ^ 2 / 6) / 1 = σ * Real.pi / Real.sqrt 6 := by
    rw [div_one, Real.sqrt_div' _ (by norm_num), Real.sqrt_sq Real.pi_pos.le]
    ring
  rw [hval] at hlim
  refine hlim.congr' (Eventually.of_forall fun N => ?_)
  simp only [Pi.div_apply, gabaixVol, hr]
  rw [div_div_eq_mul_div]
  ring

/-- AKMM, p. 685, beyond the text: **the regime `1 < ζ < 2`**. For the rank-size rule
`Sₖ = k^{−1/ζ}`, `N^{1−1/ζ} σ_Y → σ(1 − 1/ζ)√(Σ_k k^{−2/ζ})`: `σ_Y` falls like
`N^{−(1−1/ζ)}`. -/
theorem gabaix_rank_mid_tendsto {ζ : ℝ} (h1 : 1 < ζ) (h2 : ζ < 2) (σ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 1 / ζ) * gabaixVol σ (gabaixRank ζ) N) atTop
      (𝓝 (σ * Real.sqrt (∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ))) * (1 - 1 / ζ))) := by
  have hz : 0 < ζ := by linarith
  have hβ0 : 0 ≤ 1 / ζ := by positivity
  have hβ1 : 1 / ζ < 1 := by rw [div_lt_one hz]; exact h1
  have hp : 1 < 2 / ζ := by rw [lt_div_iff₀ hz]; linarith
  have hsq_eq : ∀ i : ℕ, gabaixRank ζ i ^ 2 = ((i : ℝ) + 1) ^ (-(2 / ζ)) := fun i => by
    rw [gabaixRank, ← Real.rpow_mul_natCast (by positivity)]
    ring_nf
  have hsum : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-(2 / ζ))) := by
    refine ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hp)).congr fun i => ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rfl
  have hsq : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, gabaixRank ζ i ^ 2) atTop
      (𝓝 (∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ)))) := by
    simp only [hsq_eq]
    exact hsum.hasSum.tendsto_sum_nat
  have hc : 0 < 1 - 1 / ζ := by linarith
  have hlim := ((hsq.sqrt).const_mul σ).div (gabaix_sum_rpow_tendsto hβ0 hβ1)
    (one_div_pos.2 hc).ne'
  have hval : σ * Real.sqrt (∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ))) / (1 / (1 - 1 / ζ)) =
      σ * Real.sqrt (∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ))) * (1 - 1 / ζ) := by
    rw [div_div_eq_mul_div, div_one]
  rw [hval] at hlim
  refine hlim.congr' (Eventually.of_forall fun N => ?_)
  simp only [Pi.div_apply, gabaixVol, gabaixRank]
  rw [div_div_eq_mul_div]
  ring

/-- AKMM, p. 685, beyond the text: for `1 < ζ < 2` and `σ > 0`, `√N σ_Y → ∞`: with a fat tail
aggregate volatility falls strictly more slowly than the `1/√N` of the finite-variance case. -/
theorem gabaix_rank_mid_sqrt_tendsto_atTop {ζ : ℝ} (h1 : 1 < ζ) (h2 : ζ < 2) {σ : ℝ}
    (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ (gabaixRank ζ) N) atTop atTop := by
  have hz : 0 < ζ := by linarith
  have he : 0 < 1 / ζ - 1 / 2 := by
    rw [sub_pos, one_div_lt_one_div (by norm_num) hz]; exact h2
  have hc : 0 < 1 - 1 / ζ := by
    have : 1 / ζ < 1 := by rw [div_lt_one hz]; exact h1
    linarith
  have hsum : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-(2 / ζ))) := by
    have hp : 1 < 2 / ζ := by rw [lt_div_iff₀ hz]; linarith
    refine ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hp)).congr fun i => ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rfl
  have hL : 0 < ∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ)) :=
    hsum.tsum_pos (fun i => by positivity) 0 (by norm_num)
  have hC : 0 < σ * Real.sqrt (∑' i : ℕ, ((i : ℝ) + 1) ^ (-(2 / ζ))) * (1 - 1 / ζ) := by
    have := Real.sqrt_pos.2 hL
    positivity
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / ζ - 1 / 2)) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  refine (hpow.atTop_mul_pos hC (gabaix_rank_mid_tendsto h1 h2 σ)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hN0]
  congr 2
  ring

/-- AKMM, p. 685, beyond the text: **the boundary `ζ = 2`**. For the rank-size rule
`Sₖ = k^{−1/2}`, `√(N/log N) σ_Y → σ/2`. -/
theorem gabaix_rank_two_tendsto (σ : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (N / Real.log N) * gabaixVol σ (gabaixRank 2) N) atTop
      (𝓝 (σ / 2)) := by
  have hsq_eq : ∀ i : ℕ, gabaixRank 2 i ^ 2 = ((i : ℝ) + 1)⁻¹ := fun i => by
    rw [gabaixRank, ← Real.rpow_mul_natCast (by positivity)]
    norm_num
    exact Real.rpow_neg_one _
  have hS := gabaix_sum_rpow_tendsto (β := 1 / 2) (by norm_num) (by norm_num)
  have hlim := ((gabaix_harmonic_div_log_tendsto.sqrt).const_mul σ).div hS (by norm_num)
  have hval : σ * Real.sqrt 1 / (1 / (1 - 1 / 2)) = σ / 2 := by norm_num
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsl : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.2 hl
  simp only [Pi.div_apply, gabaixVol, hsq_eq]
  simp only [gabaixRank]
  rw [Real.sqrt_div' _ hl.le, Real.sqrt_div hN0, Real.sqrt_eq_rpow (N : ℝ),
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, div_div_eq_mul_div]
  ring

/-- AKMM, p. 685, beyond the text: **thin tails, `ζ > 2`**. For the rank-size rule
`Sₖ = k^{−1/ζ}`, `√N σ_Y → σ(ζ − 1)/√(ζ(ζ − 2))`: the `1/√N` law of the equal-size case, with
the same constant as for i.i.d. Pareto sizes (`gabaix_pareto_iid`). -/
theorem gabaix_rank_thin_tendsto {ζ : ℝ} (h2 : 2 < ζ) (σ : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt N * gabaixVol σ (gabaixRank ζ) N) atTop
      (𝓝 (σ * (ζ - 1) / Real.sqrt (ζ * (ζ - 2)))) := by
  have hz : 0 < ζ := by linarith
  have hb1 : 1 / ζ < 1 := by rw [div_lt_one hz]; linarith
  have hb2 : 2 / ζ < 1 := by rw [div_lt_one hz]; exact h2
  have hsq_eq : ∀ i : ℕ, gabaixRank ζ i ^ 2 = ((i : ℝ) + 1) ^ (-(2 / ζ)) := fun i => by
    rw [gabaixRank, ← Real.rpow_mul_natCast (by positivity)]
    ring_nf
  have hS1 := gabaix_sum_rpow_tendsto (β := 1 / ζ) (by positivity) hb1
  have hS2 := gabaix_sum_rpow_tendsto (β := 2 / ζ) (by positivity) hb2
  have hc1 : 0 < 1 - 1 / ζ := by linarith
  have hc2 : 0 < 1 - 2 / ζ := by linarith
  have hlim := ((hS2.sqrt).const_mul σ).div hS1 (one_div_pos.2 hc1).ne'
  have hval : σ * Real.sqrt (1 / (1 - 2 / ζ)) / (1 / (1 - 1 / ζ)) =
      σ * (ζ - 1) / Real.sqrt (ζ * (ζ - 2)) := by
    have hz2 : 0 < ζ - 2 := by linarith
    have e2 : 1 / (1 - 2 / ζ) = ζ / (ζ - 2) := by field_simp
    have e1 : 1 / (1 - 1 / ζ) = ζ / (ζ - 1) := by field_simp
    have hsz := Real.sqrt_pos.2 hz
    have hsz2 := Real.sqrt_pos.2 hz2
    rw [e2, e1, Real.sqrt_div' _ hz2.le, Real.sqrt_mul hz.le]
    field_simp
    rw [Real.sq_sqrt hz.le]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNa : 0 < (N : ℝ) ^ (1 - 2 / ζ) := Real.rpow_pos_of_pos hN0 _
  have key : (N : ℝ) ^ (1 - 1 / ζ) = Real.sqrt N * Real.sqrt ((N : ℝ) ^ (1 - 2 / ζ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    ring
  have hsa : 0 < Real.sqrt ((N : ℝ) ^ (1 - 2 / ζ)) := Real.sqrt_pos.2 hNa
  simp only [Pi.div_apply, gabaixVol, hsq_eq]
  simp only [gabaixRank]
  rw [Real.sqrt_div' _ hNa.le, key]
  field_simp

/-! ### The largest firm -/

/-- AKMM, p. 685, beyond the text: **the largest firm bounds volatility from below**. For any
nonnegative sizes and any firm `j < N`, `σ_Y ≥ σ Sⱼ / Σ Sᵢ`, the volatility contributed by firm
`j` alone. -/
theorem gabaix_vol_ge_share {σ : ℝ} (hσ : 0 ≤ σ) {S : ℕ → ℝ} (hS : ∀ i, 0 ≤ S i) {N j : ℕ}
    (hj : j < N) : σ * S j / ∑ i ∈ Finset.range N, S i ≤ gabaixVol σ S N := by
  rw [gabaixVol]
  refine div_le_div_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => hS i)
  refine mul_le_mul_of_nonneg_left ?_ hσ
  rw [← Real.sqrt_sq (hS j)]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => S i ^ 2)
    (fun i _ => sq_nonneg (S i)) (Finset.mem_range.2 hj))

/-- AKMM, p. 682, beyond the text: with nonnegative sizes, `σ_Y ≤ σ` (one firm holding all of
output is the most volatile case). -/
theorem gabaix_vol_le {σ : ℝ} (hσ : 0 ≤ σ) {S : ℕ → ℝ} (hS : ∀ i, 0 ≤ S i) (N : ℕ) :
    gabaixVol σ S N ≤ σ := by
  rw [gabaixVol]
  have hB := Finset.sum_nonneg fun i (_ : i ∈ Finset.range N) => hS i
  rcases hB.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hσ
  · rw [div_le_iff₀ hpos]
    refine mul_le_mul_of_nonneg_left ?_ hσ
    calc Real.sqrt (∑ i ∈ Finset.range N, S i ^ 2)
        ≤ Real.sqrt ((∑ i ∈ Finset.range N, S i) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hS i)
      _ = ∑ i ∈ Finset.range N, S i := Real.sqrt_sq hB

/-- AKMM, p. 685, beyond the text: for the Zipf rank-size rule `Sₖ = 1/k`,
`σ_Y ≥ σ/(1 + log N)` for every `N ≥ 1`: the largest firm alone gives the `1/log N` order. -/
theorem gabaix_zipf_vol_ge {σ : ℝ} (hσ : 0 ≤ σ) {N : ℕ} (hN : 1 ≤ N) :
    σ / (1 + Real.log N) ≤ gabaixVol σ (gabaixRank 1) N := by
  have hr : ∀ i, gabaixRank 1 i = ((i : ℝ) + 1)⁻¹ := fun i => by
    rw [gabaixRank, div_one, Real.rpow_neg_one]
  have h := gabaix_vol_ge_share hσ (S := gabaixRank 1) (fun i => by rw [hr]; positivity)
    (j := 0) hN
  have hH : ∑ i ∈ Finset.range N, gabaixRank 1 i = harmonic N := by
    simp [hr, harmonic]
  rw [hH, hr, Nat.cast_zero, zero_add, inv_one, mul_one] at h
  refine le_trans (div_le_div_of_nonneg_left hσ ?_ (harmonic_le_one_add_log N)) h
  have h1 := log_add_one_le_harmonic N
  have h2 : 0 < Real.log ↑(N + 1) := Real.log_pos (by push_cast; norm_cast; omega)
  linarith

/-- AKMM, p. 685, beyond the text: **i.i.d. Pareto sizes, pathwise**. For i.i.d.
Pareto(`t`, `ζ`) sizes (any `ζ > 0`, in particular Zipf's `ζ = 1`), almost surely every firm
bounds aggregate volatility from below: `σ_Y ≥ σ Sⱼ / Σ Sᵢ` for all `j < N`. -/
theorem gabaix_pareto_vol_ge_share {t ζ : ℝ} (ht : 0 < t)
    [IsProbabilityMeasure (paretoMeasure t ζ)] {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ), ∀ N j : ℕ, j < N →
      σ * ω j / ∑ i ∈ Finset.range N, ω i ≤ gabaixVol σ ω N := by
  have hpos0 : ∀ᵐ x ∂(paretoMeasure t ζ), 0 ≤ x := by
    rw [paretoMeasure, ae_withDensity_iff
      (show Measurable (paretoPDF t ζ) from (measurable_paretoPDFReal t ζ).ennreal_ofReal)]
    refine ae_of_all _ fun x hx => ?_
    by_contra hx0
    exact hx (paretoPDF_of_lt (lt_of_lt_of_le (not_le.1 hx0) ht.le))
  have hall : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => paretoMeasure t ζ), ∀ i, 0 ≤ ω i :=
    ae_all_iff.2 fun i =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => paretoMeasure t ζ)
        i).quasiMeasurePreserving.ae hpos0
  filter_upwards [hall] with ω hω
  exact fun N j hj => gabaix_vol_ge_share hσ hω hj

end AKMM.HeterogeneousFirms
