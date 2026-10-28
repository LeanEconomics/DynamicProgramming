/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.IncrementAnalysis
import VUniformErgodicity.FErgodicModels

/-!
# `V`-uniform ergodicity for regenerative models (MT §16.1.3)

Meyn and Tweedie, §16.1.3, pp. 399–400: random walk on `ℝ₊` (RWHL1),
`Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` with increment law `Γ` (`halfLineWalkKernel Γ`).

* `IsLaplaceFinite Γ γ` (16.18), p. 399: `Γ ∈ G⁺(γ)`, `∫ e^{sw} Γ(dw) < ∞` for `0 < s ≤ γ`.
* `exists_mgf_lt_one`: if `β = ∫ w Γ(dw) < 0` and `Γ ∈ G⁺(γ)`, then `∫ e^{s₀w} Γ(dw) < 1` for
  some `0 < s₀ ≤ γ/2`. This is the book's `s⁻¹ ∫ Γ(dw) [e^{sw} − 1] → β` as `s ↓ 0`, proved by
  dominated convergence with the bound `|w| + (2/γ) e^{γw}`.
* `halfLine_driftV4_exp`: (16.19): `PV(x) ≤ e^{sx} (∫ e^{sw} Γ(dw) + Γ(−∞, −x])` for
  `V(x) = e^{sx}`, so (V4) holds with `C = [0, c]` once `Γ(−∞, −c] ≤ (1 − ∫ e^{s₀w} Γ(dw))/2`.
* `halfLine_vUniformlyErgodic` (p. 400): the walk is `ψ`-irreducible, aperiodic and positive, and
  `e^{s₀x}`-uniformly ergodic with `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞`, when (a) `β < 0` and
  (b) `Γ ∈ G⁺(γ)`.

**Elsewhere.** The forward recurrence time `δ`-skeleton `V⁺_δ` of p. 399 is in
`FwdRecurrenceSkeleton` (`fwdChain_vUniformlyErgodic`, `fwdChain_not_uniformlyErgodic`). The
cited result `E_x[τ_0] ∼ cx` of [69] is not formalised.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology NNReal

/-- **`Γ ∈ G⁺(γ)`** (16.18), MT p. 399: the Laplace–Stieltjes transform converges on `(0, γ]`,
`∫ e^{sw} Γ(dw) < ∞` for `0 < s ≤ γ`. -/
def IsLaplaceFinite (Γ : Measure ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ s, 0 < s → s ≤ γ → Integrable (fun w => Real.exp (s * w)) Γ

/-- `e^{sw}` is integrable for `0 ≤ s ≤ γ` when `e^{γw}` is (it is at most `1 + e^{γw}`). -/
theorem integrable_exp_mul_of_le {Γ : Measure ℝ} [IsProbabilityMeasure Γ] {γ s : ℝ}
    (hs0 : 0 ≤ s) (hsγ : s ≤ γ) (hγ : Integrable (fun w => Real.exp (γ * w)) Γ) :
    Integrable (fun w => Real.exp (s * w)) Γ := by
  refine Integrable.mono' ((integrable_const 1).add hγ) (by fun_prop)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 w with hw | hw
  · have : Real.exp (s * w) ≤ Real.exp (γ * w) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hsγ hw)
    simp only [Pi.add_apply]; linarith
  · have : Real.exp (s * w) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hs0 hw)
    simp only [Pi.add_apply]; linarith [Real.exp_pos (γ * w)]

/-- **A negative mean and `G⁺(γ)` give `∫ e^{s₀w} Γ(dw) < 1`** (MT p. 400): as `s ↓ 0`,
`s⁻¹ ∫ Γ(dw) [e^{sw} − 1] → β < 0`. -/
theorem exists_mgf_lt_one {Γ : Measure ℝ} [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) {γ : ℝ} (hγ : IsLaplaceFinite Γ γ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ γ / 2 ∧ Integrable (fun w => Real.exp (s * w)) Γ ∧
      ∫ w, Real.exp (s * w) ∂Γ < 1 := by
  obtain ⟨hγ0, hγi⟩ := hγ
  have hγI := hγi γ hγ0 le_rfl
  set sq : ℕ → ℝ := fun n => γ / (2 * (n + 1)) with hsq
  have hsq0 : ∀ n, 0 < sq n := fun n => by positivity
  have hsqγ : ∀ n, sq n ≤ γ / 2 := fun n => by
    rw [hsq]; simp only
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsqlim : Tendsto sq atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1))) atTop atTop := by
      refine Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    have h := this.inv_tendsto_atTop.const_mul γ
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [hsq, Pi.inv_apply]
    ring
  have hint : ∀ n, Integrable (fun w => Real.exp (sq n * w)) Γ := fun n =>
    integrable_exp_mul_of_le (hsq0 n).le ((hsqγ n).trans (by linarith)) hγI
  set F : ℕ → ℝ → ℝ := fun n w => (Real.exp (sq n * w) - 1) / sq n with hF
  set G : ℝ → ℝ := fun w => |w| + 2 / γ * Real.exp (γ * w) with hG
  have hGint : Integrable G Γ := hW.abs.add (hγI.const_mul _)
  have hbound : ∀ n w, ‖F n w‖ ≤ G w := fun n w => by
    have hs := hsq0 n
    simp only [hF, hG]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    rcases le_total 0 w with hw | hw
    · -- `e^{sw} − 1 ≤ s w e^{sw}` and `w e^{sw} ≤ (2/γ) e^{γw}`
      have h1 : Real.exp (sq n * w) - 1 ≤ sq n * w * Real.exp (sq n * w) := by
        have h := Real.add_one_le_exp (-(sq n * w))
        have he : Real.exp (sq n * w) * Real.exp (-(sq n * w)) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_pos (sq n * w)).le]
      have h2 : Real.exp (sq n * w) ≤ Real.exp (γ * w / 2) :=
        Real.exp_le_exp.2 (by nlinarith [hsqγ n])
      have h3 : w ≤ 2 / γ * Real.exp (γ * w / 2) := by
        have := Real.add_one_le_exp (γ * w / 2)
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ0]
        nlinarith
      have h4 : Real.exp (γ * w / 2) * Real.exp (γ * w / 2) = Real.exp (γ * w) := by
        rw [← Real.exp_add]; ring_nf
      have hpos : 0 ≤ Real.exp (sq n * w) - 1 := by
        linarith [Real.one_le_exp (mul_nonneg hs.le hw)]
      rw [abs_of_nonneg hpos]
      calc Real.exp (sq n * w) - 1 ≤ sq n * w * Real.exp (sq n * w) := h1
        _ ≤ sq n * (2 / γ * Real.exp (γ * w / 2) * Real.exp (γ * w / 2)) := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul h3 h2 (Real.exp_pos _).le
              (by positivity)) hs.le
        _ = sq n * (2 / γ * Real.exp (γ * w)) := by rw [mul_assoc, h4]
        _ ≤ (|w| + 2 / γ * Real.exp (γ * w)) * sq n := by nlinarith [abs_nonneg w, le_abs_self w]
    · -- `1 − e^{sw} ≤ −sw`
      have h1 : 1 - Real.exp (sq n * w) ≤ -(sq n * w) := by
        linarith [Real.add_one_le_exp (sq n * w)]
      have hneg : Real.exp (sq n * w) - 1 ≤ 0 := by
        linarith [Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hs.le hw)]
      rw [abs_of_nonpos hneg, abs_of_nonpos hw]
      have : 0 ≤ 2 / γ * Real.exp (γ * w) := by positivity
      nlinarith
  have hlim : ∀ w, Tendsto (fun n => F n w) atTop (𝓝 w) := fun w => by
    have hd : HasDerivAt (fun s => Real.exp (s * w)) (Real.exp (0 * w) * w) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).exp
    rw [zero_mul, Real.exp_zero, one_mul] at hd
    have hs := hd.tendsto_slope
    have hsq' : Tendsto sq atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsqlim
        (Eventually.of_forall fun n => (hsq0 n).ne')
    have := hs.comp hsq'
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, slope_def_field, sub_zero, zero_mul, Real.exp_zero, hF]
  have hconv := tendsto_integral_of_dominated_convergence G
    (fun n => (by fun_prop : Measurable (F n)).aestronglyMeasurable) hGint
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hβ)).exists
  have hFn : ∫ w, F n w ∂Γ = (∫ w, Real.exp (sq n * w) ∂Γ - 1) / sq n := by
    rw [hF]; simp only
    rw [integral_div, integral_sub (hint n) (integrable_const 1), integral_const, probReal_univ,
      one_smul]
  rw [hFn, div_lt_iff₀ (hsq0 n), zero_mul] at hn
  exact ⟨sq n, hsq0 n, hsqγ n, hint n, by linarith⟩

/-- **The drift (16.19)** (MT p. 400): for `V(x) = e^{sx}` on `ℝ₊`,
`PV(x) ≤ e^{sx} (∫ e^{sw} Γ(dw) + Γ(−∞, −x])`. -/
theorem lintegral_halfLine_exp_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {s : ℝ}
    (hs : 0 ≤ s) (hint : Integrable (fun w => Real.exp (s * w)) Γ) (x : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂halfLineWalkKernel Γ x ≤
      ENNReal.ofReal (Real.exp (s * x)) *
        (ENNReal.ofReal (∫ w, Real.exp (s * w) ∂Γ) + Γ (Iic (-(x : ℝ)))) := by
  have hm : Measurable fun y : ℝ≥0 => ENNReal.ofReal (Real.exp (s * y)) := by fun_prop
  rw [lintegral_halfLine Γ x hm, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun w => (Real.exp_pos _).le),
    ← lintegral_indicator_one measurableSet_Iic,
    ← lintegral_add_left (by fun_prop),
    ← lintegral_const_mul (f := fun w => ENNReal.ofReal (Real.exp (s * w)) +
      (Iic (-(x : ℝ))).indicator 1 w) _ ((by fun_prop : Measurable fun w : ℝ =>
      ENNReal.ofReal (Real.exp (s * w))).add (measurable_one.indicator measurableSet_Iic))]
  refine lintegral_mono fun w => ?_
  rcases lt_or_ge 0 ((x : ℝ) + w) with hxw | hxw
  · rw [Real.coe_toNNReal _ hxw.le, mul_add, mul_add]
    refine le_add_right (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  · have hmem : w ∈ Iic (-(x : ℝ)) := by simp only [mem_Iic]; linarith
    rw [Real.toNNReal_of_nonpos hxw, NNReal.coe_zero, mul_zero, Real.exp_zero,
      ENNReal.ofReal_one, Set.indicator_of_mem hmem, Pi.one_apply, mul_add, mul_one]
    refine le_add_left ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs x.2))

/-- **(V4) for random walk on `ℝ₊`** (MT p. 400): if `∫ e^{sw} Γ(dw) < 1`, then `V(x) = e^{sx}`
satisfies (V4) with `C = [0, c]` for some `c`. -/
theorem halfLine_driftV4_exp (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {s : ℝ} (hs : 0 ≤ s)
    (hint : Integrable (fun w => Real.exp (s * w)) Γ) (hM : ∫ w, Real.exp (s * w) ∂Γ < 1) :
    ∃ c : ℝ≥0, ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧
      DriftV4 (halfLineWalkKernel Γ) (fun x => ENNReal.ofReal (Real.exp (s * x))) ρ b (Iic c) := by
  set M := ∫ w, Real.exp (s * w) ∂Γ with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun w => (Real.exp_pos _).le
  -- the tail `Γ(−∞, −x] → 0`
  have hanti : Antitone fun x : ℝ => Iic (-x) := fun a b hab =>
    Iic_subset_Iic.2 (neg_le_neg hab)
  have hlim : Tendsto (fun x : ℝ => Γ (Iic (-x))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := Γ)
      (fun x => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have he : (⋂ x : ℝ, Iic (-x)) = ∅ := by
      refine eq_empty_of_forall_notMem fun w hw => ?_
      have := mem_iInter.1 hw (-w + 1)
      simp only [mem_Iic, neg_add_rev, neg_neg] at this
      linarith
    rwa [he, measure_empty] at h
  have hgap : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 - M) / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨x₀, hx₀⟩ := (hlim.eventually (gt_mem_nhds hgap)).exists_forall_of_atTop
  set c : ℝ≥0 := x₀.toNNReal
  refine ⟨c, ENNReal.ofReal ((1 + M) / 2), ENNReal.ofReal (Real.exp (s * c) * (M + 1)),
    ENNReal.ofReal_lt_one.2 (by linarith), ENNReal.ofReal_ne_top, fun x => ?_⟩
  have h := lintegral_halfLine_exp_le Γ hs hint x
  by_cases hx : x ∈ Iic c
  · rw [indicator_of_mem hx]
    refine le_add_left (h.trans ?_)
    have hxc : (x : ℝ) ≤ c := by exact_mod_cast hx
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_add hM0 zero_le_one,
      ENNReal.ofReal_one]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hxc hs))) (add_le_add le_rfl prob_le_one)
  · rw [indicator_of_notMem hx, add_zero]
    have hxc : x₀ ≤ (x : ℝ) := by
      have : c < x := not_le.1 hx
      have h2 : (c : ℝ) < x := by exact_mod_cast this
      exact (Real.le_coe_toNNReal x₀).trans h2.le
    have ht := (hx₀ x hxc).le
    refine h.trans ?_
    rw [mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ENNReal.ofReal M + Γ (Iic (-(x : ℝ))) ≤ ENNReal.ofReal M + ENNReal.ofReal ((1 - M) / 2) :=
          add_le_add le_rfl ht
      _ = ENNReal.ofReal ((1 + M) / 2) := by
          rw [← ENNReal.ofReal_add hM0 (by linarith)]; congr 1; ring

/-- **Random walk on `ℝ₊` is `e^{s₀x}`-uniformly ergodic** (MT p. 400): if (a) the mean increment
`β = ∫ w Γ(dw)` is negative and (b) `Γ ∈ G⁺(γ)`, then for some `0 < s₀ < γ` the walk is
`ψ`-irreducible, aperiodic and positive, and every invariant probability `π` has
`|||Pⁿ − 1 ⊗ π|||_V → 0` and `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞` for `V(x) = e^{s₀x}` and some
`r > 1`. -/
theorem halfLine_vUniformlyErgodic (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) {γ : ℝ} (hγ : IsLaplaceFinite Γ γ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < γ ∧ ∃ ψ : Measure ℝ≥0,
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ ∧ IsAperiodic (halfLineWalkKernel Γ) ψ ∧
      IsPositive (halfLineWalkKernel Γ) ψ ∧
      ∀ (μ : Measure ℝ≥0) [IsProbabilityMeasure μ], IsInvariant (halfLineWalkKernel Γ) μ →
        IsVUniformlyErgodic (fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (s₀ * x)))
          (halfLineWalkKernel Γ) μ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (s₀ * x))) (halfLineWalkKernel Γ) μ n ≠ ∞ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  set P := halfLineWalkKernel Γ with hP
  obtain ⟨s, hs0, hsγ, hint, hM⟩ := exists_mgf_lt_one hW hβ hγ
  obtain ⟨c, ρ, b, hρ, hb, hd⟩ := halfLine_driftV4_exp Γ hs0.le hint hM
  have hneg := halfLine_neg_pos_of_mean_neg Γ hβ
  obtain ⟨_, hψ, -⟩ := halfLine_maximal Γ hneg
  set ψ := (2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0 with hψdef
  have hpet := halfLine_isPetite_Iic Γ hneg c
  have hatom := halfLine_isAccessibleAtom_zero Γ hneg hψ
  have hP0 : 0 < P 0 {0} := by
    rw [hP, halfLineWalkKernel_apply_zero]
    refine lt_of_lt_of_le hneg (measure_mono ?_)
    rw [NNReal.coe_zero, neg_zero]
    exact Set.Iio_subset_Iic_self
  obtain ⟨M, hMC, hMν, -⟩ := exists_minorization_of_le (P := P) (measurableSet_singleton 0)
    ⟨0, rfl⟩ (ν' := P 0) (fun x hx => by rw [mem_singleton_iff.1 hx]) hP0
  have hap : IsAperiodic P ψ := isAperiodic_of_minorization hψ M (by rw [hMC]; exact hatom.2.2)
    (by rw [hMν]; exact one_pos)
  set V : ℝ≥0 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (s * x)) with hV
  have hVm : Measurable V := by fun_prop
  have hV1 : ∀ x, 1 ≤ V x := fun x => by
    rw [hV, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs0.le x.2))
  have hVt : ∀ x, V x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  refine ⟨s, hs0, lt_of_le_of_lt hsγ (by linarith [hγ.1]), ψ, hψ, hap,
    (geometric_ergodic_of_driftV4 hψ hap hVm hV1 hρ hb hpet hd (hVt 0)).1, fun μ _ hμ => ?_⟩
  obtain ⟨hsum, hlim⟩ := theorem_16_1_2 hψ hap hVm hV1 hVt hρ hb hpet hd μ hμ
  exact ⟨⟨hμ, hlim⟩, hsum⟩

end MeynTweedie.VUniformErgodicity
