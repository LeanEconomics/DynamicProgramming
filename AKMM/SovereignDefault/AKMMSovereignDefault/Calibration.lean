/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import CapitalMarketImperfections.DebtOverhangLaffer

/-!
# Calibration formulas and the iso-moment slope (App. 24.A.2–24.A.3)

AKMM, §24.4.1, pp. 742–743; Appendix 24.A.2, (24.A.7) and Table 24.A.1, pp. 901–902; Appendix
24.A.3, footnote 44 and p. 905.

* **CRRA** (p. 901): `u(c) = (c^{1−σ} − 1)/(1 − σ)` has `u′(c) = c^{−σ} > 0`, decreasing, so it
  satisfies the hypotheses of the two-period Euler equation (24.6) (`cal_crra_hasDerivAt`,
  `cal_crra_deriv_pos`, `cal_crra_deriv_antitone`).
* **(24.A.7)**: `φ(Y) = max{Y[λ₀Y + λ₁(Y − E Y)], 0}` is nonnegative, its loss fraction
  `φ(Y)/Y` is nondecreasing in `Y` when `λ₀ + λ₁ ≥ 0` (the assumption of p. 743), equals `λ₀`
  at `Y = E Y = 1` (`λ₀` is "the average fraction"), rises with `λ₀`, and rises with `λ₁`
  above mean income and falls with it below (p. 905) (`cal_phi_*`).
* **Table 24.A.1** (`μ = −σ_ε²/2`): for the AR(1) `log Y_t = (1 − ρ)μ + ρ log Y_{t−1} + ε_t` the
  stationary variance is `σ_ε²/(1 − ρ²)` (`cal_ar1_variance`), and with `log Y` Gaussian
  `E Y = exp(μ + σ_ε²/(2(1 − ρ²)))` (`cal_lognormal_mean`); `E Y = 1` requires
  `μ = −σ_ε²/(2(1 − ρ²))` (`cal_mean_one_iff`), and the printed `μ = −σ_ε²/2` gives `E Y > 1`
  whenever `ρ ≠ 0` (`cal_table_mu_printed_false`).
* **Footnote 44** (`fn_44`, `fn_44_exists`): the iso-moment curve `X(λ₀, λ₁) = X̄` exists near a
  point where `∂X/∂λ₁ ≠ 0` (Mathlib's bivariate implicit function theorem) and has slope
  `dλ₁/dλ₀ = −(∂X/∂λ₀)/(∂X/∂λ₁)`.
-/

namespace AKMM.SovereignDefault

open MeasureTheory ProbabilityTheory Filter Topology

/-- AKMM, p. 901: CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`, `σ ≠ 1`. -/
noncomputable def cal_crra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, p. 901: `u′(c) = c^{−σ}` for `c > 0`. -/
theorem cal_crra_hasDerivAt {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (cal_crra σ) (c ^ (-σ)) c := by
  have h1 : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
    (1 - σ)
  have h2 : HasDerivAt (cal_crra σ) ((1 - σ) * c ^ (1 - σ - 1) / (1 - σ)) c := this
  convert h2 using 1
  rw [show 1 - σ - 1 = -σ by ring]
  field_simp

/-- `u′(c) = c^{−σ} > 0`. -/
theorem cal_crra_deriv_pos {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) : 0 < deriv (cal_crra σ) c := by
  rw [(cal_crra_hasDerivAt hσ hc).deriv]
  exact Real.rpow_pos_of_pos hc _

/-- For `σ > 0`, `u′` is decreasing on `(0, ∞)` (concavity). -/
theorem cal_crra_deriv_antitone {σ : ℝ} (hσ : σ ≠ 1) (hσ0 : 0 < σ) :
    AntitoneOn (deriv (cal_crra σ)) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [(cal_crra_hasDerivAt hσ hb).deriv, (cal_crra_hasDerivAt hσ ha).deriv]
  exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- AKMM, (24.A.7), p. 901: the income cost of default
`φ(Y) = max{Y[λ₀Y + λ₁(Y − E Y)], 0}`. -/
noncomputable def cal_phi (lam0 lam1 EY Yv : ℝ) : ℝ := max (Yv * (lam0 * Yv + lam1 * (Yv - EY))) 0

/-- AKMM, p. 901: the cost of default is nonnegative. -/
theorem cal_phi_nonneg (lam0 lam1 EY Yv : ℝ) : 0 ≤ cal_phi lam0 lam1 EY Yv := le_max_right _ _

/-- The loss fraction: `φ(Y)/Y = max{λ₀Y + λ₁(Y − E Y), 0}` for `Y > 0`. -/
theorem cal_phi_div {lam0 lam1 EY Yv : ℝ} (hY : 0 < Yv) :
    cal_phi lam0 lam1 EY Yv / Yv = max (lam0 * Yv + lam1 * (Yv - EY)) 0 := by
  unfold cal_phi
  rw [div_eq_iff hY.ne', max_mul_of_nonneg _ _ hY.le, zero_mul, mul_comm]

/-- AKMM, p. 743: with `λ₀ + λ₁ ≥ 0`, (24.A.7) makes default proportionally more costly in good
times: `φ(Y)/Y` is nondecreasing in `Y > 0`. -/
theorem cal_phi_div_monotone {lam0 lam1 EY : ℝ} (hlam : 0 ≤ lam0 + lam1) :
    MonotoneOn (fun Yv => cal_phi lam0 lam1 EY Yv / Yv) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only
  rw [cal_phi_div ha, cal_phi_div hb]
  refine max_le_max ?_ le_rfl
  nlinarith

/-- AKMM, p. 901: with `E Y = 1`, at mean income the loss fraction is `λ₀` ("the average
fraction of income lost during defaults"), for `λ₀ ≥ 0`. -/
theorem cal_phi_at_mean {lam0 lam1 : ℝ} (h0 : 0 ≤ lam0) : cal_phi lam0 lam1 1 1 / 1 = lam0 := by
  rw [cal_phi_div one_pos]
  simp [max_eq_left h0]

/-- AKMM, p. 904: a higher `λ₀` raises the cost of default at every income `Y ≥ 0`. -/
theorem cal_phi_mono_lam0 {lam1 EY Yv : ℝ} (hY : 0 ≤ Yv) :
    Monotone fun lam0 => cal_phi lam0 lam1 EY Yv := by
  intro a b hab
  exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl

/-- AKMM, p. 905: a higher `λ₁` makes default less costly below mean income and more costly
above it. -/
theorem cal_phi_lam1 {lam0 EY Yv : ℝ} (hY : 0 ≤ Yv) :
    (Yv ≤ EY → Antitone fun lam1 => cal_phi lam0 lam1 EY Yv) ∧
      (EY ≤ Yv → Monotone fun lam1 => cal_phi lam0 lam1 EY Yv) := by
  constructor
  · intro h a b hab
    exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl
  · intro h a b hab
    exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl

/-- AKMM, p. 742: the stationary variance `s² = σ_ε²/(1 − ρ²)` of
`log Y_t = (1 − ρ)μ + ρ log Y_{t−1} + ε_t` solves `s² = ρ²s² + σ_ε²`, and the stationary mean
`μ` solves `μ = (1 − ρ)μ + ρμ`. -/
theorem cal_ar1_variance {ρ σε μ : ℝ} (hρ : |ρ| < 1) :
    σε ^ 2 / (1 - ρ ^ 2) = ρ ^ 2 * (σε ^ 2 / (1 - ρ ^ 2)) + σε ^ 2 ∧ μ = (1 - ρ) * μ + ρ * μ := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
    linarith
  refine ⟨?_, by ring⟩
  field_simp
  ring

/-- If `log Y ∼ N(μ, s²)` then `E Y = exp(μ + s²/2)`. -/
theorem cal_lognormal_mean {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} {Z : Ω → ℝ} {μ : ℝ}
    {v : NNReal} (hZ : HasLaw Z (gaussianReal μ v) Pm) :
    ∫ ω, Real.exp (Z ω) ∂Pm = Real.exp (μ + v / 2) := by
  have h := mgf_gaussianReal hZ 1
  simp only [mgf, one_mul, one_pow, mul_one] at h
  rw [h]

/-- AKMM, p. 901: "the value for `μ` is chosen so that `E(Y) = 1`": with `log Y` Gaussian with
mean `μ` and the stationary variance `s²`, `E Y = 1` iff `μ = −s²/2`. -/
theorem cal_mean_one_iff {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} {Z : Ω → ℝ} {μ : ℝ}
    {v : NNReal} (hZ : HasLaw Z (gaussianReal μ v) Pm) :
    ∫ ω, Real.exp (Z ω) ∂Pm = 1 ↔ μ = -(v / 2) := by
  rw [cal_lognormal_mean hZ, Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- **AKMM, Table 24.A.1**, p. 902, as printed: `μ = −σ_ε²/2`. With the stationary variance
`s² = σ_ε²/(1 − ρ²)` of the AR(1), this gives `E Y = exp(ρ²σ_ε²/(2(1 − ρ²))) > 1` whenever
`ρ ≠ 0` and `σ_ε ≠ 0`; the mean-one normalisation needs `μ = −σ_ε²/(2(1 − ρ²))`. -/
theorem cal_table_mu_printed_false {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω}
    {Z : Ω → ℝ} {ρ σε : ℝ} (hρ : |ρ| < 1) (hρ0 : ρ ≠ 0) (hσ : σε ≠ 0) {v : NNReal}
    (hv : (v : ℝ) = σε ^ 2 / (1 - ρ ^ 2)) (hZ : HasLaw Z (gaussianReal (-(σε ^ 2 / 2)) v) Pm) :
    1 < ∫ ω, Real.exp (Z ω) ∂Pm := by
  rw [cal_lognormal_mean hZ, hv]
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
    linarith
  have hpos : 0 < -(σε ^ 2 / 2) + σε ^ 2 / (1 - ρ ^ 2) / 2 := by
    have e : -(σε ^ 2 / 2) + σε ^ 2 / (1 - ρ ^ 2) / 2 = ρ ^ 2 * σε ^ 2 / (2 * (1 - ρ ^ 2)) := by
      field_simp; ring
    rw [e]
    exact div_pos (mul_pos (pow_pos (abs_pos.2 hρ0) 2 |>.trans_eq (sq_abs ρ))
      (pow_pos (abs_pos.2 hσ) 2 |>.trans_eq (sq_abs σε))) (by linarith)
  have := Real.exp_lt_exp.2 hpos
  rwa [Real.exp_zero] at this

/-- **AKMM, footnote 44**, p. 903: along a differentiable iso-moment curve
`λ₁ = g(λ₀)` with `X(λ₀, g(λ₀)) = X̄` near `λ₀`, where `X` is differentiable with
`∂X/∂λ₁ ≠ 0`, the slope is `g′(λ₀) = −(∂X/∂λ₀)/(∂X/∂λ₁)`. -/
theorem fn_44 {X : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {g : ℝ → ℝ} {l0 g' Xbar : ℝ}
    (hX : HasFDerivAt X L (l0, g l0)) (hg : HasDerivAt g g' l0)
    (hlev : ∀ᶠ l in 𝓝 l0, X (l, g l) = Xbar) (h1 : L (0, 1) ≠ 0) :
    g' = -(L (1, 0) / L (0, 1)) := by
  have hc := HasFDerivAt.comp_hasDerivAt (f := fun l => (l, g l)) l0 hX
    ((hasDerivAt_id' l0).prodMk hg)
  have hconst : HasDerivAt (fun l => X (l, g l)) 0 l0 :=
    (hasDerivAt_const l0 Xbar).congr_of_eventuallyEq (hlev.mono fun l h => h)
  have h0 := hc.unique hconst
  have : ((1, g') : ℝ × ℝ) = (1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + g' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_mul] at h0
  field_simp
  linarith

/-- **AKMM, footnote 44**, p. 903, existence: if the moment function `X(λ₀, λ₁)` has partial
derivatives `X₀, X₁` near `(λ₀, λ₁)`, continuous there, with `X₁ ≠ 0` at the point, then the
implicit function theorem gives a curve `λ₁ = g(λ₀)` through the point on which `X` is constant
near `λ₀`, differentiable with slope `−X₀/X₁`. -/
theorem fn_44_exists {X X0 X1 : ℝ → ℝ → ℝ} {u : ℝ × ℝ}
    (d0 : ∀ᶠ w in 𝓝 u, HasDerivAt (X · w.2) (X0 w.1 w.2) w.1)
    (d1 : ∀ᶠ w in 𝓝 u, HasDerivAt (X w.1 ·) (X1 w.1 w.2) w.2)
    (c0 : ContinuousAt (Function.uncurry X0) u) (c1 : ContinuousAt (Function.uncurry X1) u)
    (h1 : X1 u.1 u.2 ≠ 0) :
    ∃ g : ℝ → ℝ, Tendsto g (𝓝 u.1) (𝓝 u.2) ∧ (∀ᶠ l in 𝓝 u.1, X l (g l) = X u.1 u.2) ∧
      HasDerivAt g (-(X0 u.1 u.2 / X1 u.1 u.2)) u.1 := by
  set f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b => X0 a b • (1 : ℝ →L[ℝ] ℝ) with hf₁
  set f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b => X1 a b • (1 : ℝ →L[ℝ] ℝ) with hf₂
  have df₁ : ∀ᶠ w in 𝓝 u, HasFDerivAt (X · w.2) (f₁ w.1 w.2) w.1 := by
    filter_upwards [d0] with w hw
    rw [hf₁]
    simp only
    rw [← ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.toSpanSingleton_eq_smul]
    exact hw.hasFDerivAt
  have df₂ : ∀ᶠ w in 𝓝 u, HasFDerivAt (X w.1 ·) (f₂ w.1 w.2) w.2 := by
    filter_upwards [d1] with w hw
    rw [hf₂]
    simp only
    rw [← ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.toSpanSingleton_eq_smul]
    exact hw.hasFDerivAt
  have cf₁ : ContinuousAt ↿f₁ u := c0.smul continuousAt_const
  have cf₂ : ContinuousAt ↿f₂ u := c1.smul continuousAt_const
  have if₂ : (f₂ u.1 u.2).IsInvertible :=
    ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.smul_one_isInvertible h1
  set g := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hten := tendsto_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hlev := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hgd := (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).hasFDerivAt
    |>.hasDerivAt
  refine ⟨g, hten, hlev, ?_⟩
  -- identify the derivative through `fn_44`
  have hg0 : g u.1 = u.2 := by
    have := (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    exact this.1 rfl
  have hXd : HasFDerivAt (Function.uncurry X)
      ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) (u.1, g u.1) := by
    rw [hg0]
    exact (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂).hasFDerivAt
  have hlev' : ∀ᶠ l in 𝓝 u.1, Function.uncurry X (l, g l) = X u.1 u.2 := hlev
  have hne : ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) (0, 1) ≠ 0 := by
    simp [hf₂, h1]
  have hval : (-(f₂ u.1 u.2).inverse ∘SL f₁ u.1 u.2) 1 = -(X0 u.1 u.2 / X1 u.1 u.2) := by
    rw [fn_44 hXd hgd hlev' hne]
    simp [hf₁, hf₂]
  rw [← hval]
  exact hgd

end AKMM.SovereignDefault
