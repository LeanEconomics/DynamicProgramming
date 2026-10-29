/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.LLNApplications
import LimitTheorems.RegularityConverse
import LimitTheorems.LinearInvariant
import LimitTheorems.UniqueInvariant
import LimitTheorems.ModelNonlinearModels
import Mathlib.Probability.Independence.ZeroOne

/-!
# The dependent parameter bilinear model (MT §17.3.3)

Meyn and Tweedie, §17.3.3, pp. 437–440: Proposition 17.3.4 in the book's setting, the backward
LLN (17.26), and Proposition 17.3.5, for the dependent parameter bilinear model (DBL1)–(DBL2),
`θₖ₊₁ = αθₖ + Zₖ₊₁`, `Yₖ₊₁ = θₖYₖ + Wₖ₊₁` (`dblKernel Γz Γw α`, with the parameter process
`ar1Kernel Γz α`).

**Proposition 11.4.2** (copied from `DriftRegularity/DriftExamples.lean`, unchanged):
`logAbs_add_le`, `logAbs_contract`, `exists_small_logAbs`, `proposition_11_4_2` (the simple
linear model with `|α| < 1` and `E log(1 + |W|) < ∞` is regular, with `V(x) = log(1 + ε|x|)`).

**Proposition 17.3.4.** `dblKernel_map_fst`: the parameter process of the bilinear model is the
AR(1) model (2.14). **`proposition_17_3_4_dbl`** (p. 438): `θ` is positive Harris (it is
regular by Proposition 11.4.2, and `IsRegularChain.isPositiveHarris`), and the LLN holds for
every `f` with `π_θ(f⁺) < ∞`, with limit `π_θ(f) ∈ [−∞, ∞)`;
`proposition_17_3_4_dbl_thetaLaw`: its invariant probability is the law `thetaLaw` of the
stationary solution `θ₀ = Σⱼ αʲ Z₋ⱼ`.

**The Bernoulli shift.** `measurePreserving_seqShift`, `seqShift_iterate_apply`,
`infinitePi_seqShift_ergodic` (strictly invariant events of `Γ^{⊗ℕ}` are tail events, so
Kolmogorov's zero–one law applies) and `ae_tendsto_birkhoffAverage_seqShift` (Birkhoff).

**Stationary solutions of random recursions.** `recursionKernel_comp'`;
`isInvariant_recursionKernel_map`: if `X(w) = F(X(θw), w₀)` a.s. under `Γ^{⊗ℕ}`, the law of `X`
is invariant for `Xₖ₊₁ = F(Xₖ, Wₖ₊₁)`. `tsum_measure_lt_ne_top` and `ae_eventually_log_le`
(Borel–Cantelli: `log(1 + |ζⱼ|) ≤ jκ` eventually).

**The stationary parameter process and (17.26).** `thetaSeries α ζ = Σⱼ αʲ ζⱼ` (the
innovations `ζⱼ = Z₋ⱼ` of the two-sided stationary version, so that `θ₋ₖ = thetaSeries α (θᵏζ)`),
`ae_summable_thetaSeries`, `thetaSeries_cons` ((2.14) backwards), `thetaLaw`,
`isInvariant_thetaLaw`, `eq_thetaLaw_of_isInvariant`. **The backward LLN (17.26)**
(`theorem_17_26_integrable`, `theorem_17_26`): `(1/N) Σ_{k=1}^N f(θ₋ₖ) → π_θ(f)` almost surely,
for `π_θ(f⁺) < ∞` (limit `−∞` when `π_θ(f⁻) = ∞`).

**Proposition 17.3.5.** `fstSeq`, `infinitePi_map_fstSeq`, `infinitePi_map_sndSeq`; `ySeries`,
`yTerm` (the stationary output `Y₀ = Σⱼ (θ₋₁ ⋯ θ₋ⱼ) W₋ⱼ` of (17.28)), `yTerm_succ`,
`ySeries_cons` ((2.13) backwards), `abs_prod_le_exp_sum_log`; `ae_summable_yTerm` (the root test
of p. 440, from (17.29)); `exists_truncation_neg`; `dblStationaryLaw`.
**`proposition_17_3_5`** (p. 438): under (DBL1), the moments of (DBL2) and (17.27), the law of
`(θ₀, Y₀)` is an invariant probability for `Φ = (θ, Y)` with first marginal `π_θ`, so `Φ` is
positive and recurrent when it is `ψ`-irreducible. `condition_17_27_of_integral_abs_lt_one`: the
remark that `E_π|θ| < 1` implies (17.27).

**Proofs that differ from the book.** The book proves Proposition 17.3.5 by showing that the laws
of `Y` are tight from `π_θ × δ_y` (bounds (17.30)) and then invoking the Feller property and
Theorem 12.1.2. Here the same estimates ((17.29) and the root test) are used to show that the
stationary series `Y₀` converges, which gives the invariant probability directly. The two-sided
stationary parameter process of (17.26) is realised through its past innovations: `θ₋ₖ` depends
only on `Z₋ₖ, Z₋ₖ₋₁, …`, so the backward LLN is Birkhoff's theorem for the one-sided Bernoulli
shift.

**Hypotheses.**
* `ψ`-irreducibility and petiteness of compact sets of `θ` (Proposition 17.3.4), and
  `ψ`-irreducibility of `Φ` (Proposition 17.3.5), are hypotheses: the book takes them from
  Proposition 7.4.1 (T-chains, through the lower semicontinuous densities of (DBL2)), which is
  formalised in the `NonlinearStateSpace` project, not in this one. For `Φ` it needs the extra
  condition (7.24) there.
* (DBL2) is used only through `E log(1 + |Z|) < ∞` and `E log(1 + |W|) < ∞` (the book assumes
  `E W² < ∞`, which implies the latter); the densities are not needed for the stationary
  solution.
* (17.27) is stated for `π_θ = thetaLaw`, in the extended sense `∫ log⁺|x| dπ_θ < ∞` and
  `∫ log⁺|x| dπ_θ < ∫ log⁻|x| dπ_θ` (so `∫ log|x| dπ_θ = −∞` is allowed, as in
  Proposition 17.3.4); `thetaLaw` is the invariant probability `π_θ` of the book whenever `θ` is
  Harris (`eq_thetaLaw_of_isInvariant`). With Lean's `log 0 = 0`, the remark
  `E_π|θ| < 1 ⇒ (17.27)` needs `π_θ{0} = 0`.

**Not formalised.** The aperiodicity of `Φ` claimed in Proposition 17.3.5 (it comes from
Proposition 7.4.1 under (7.24)); the tightness bound (17.30) itself; the simulation remarks of
p. 440.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### Proposition 11.4.2 (copied from `DriftRegularity`) -/

/-- `log(1 + ε|x|)` is subadditive. -/
theorem logAbs_add_le {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    Real.log (1 + ε * |a + b|) ≤ Real.log (1 + ε * |a|) + Real.log (1 + ε * |b|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have := abs_add_le a b
  nlinarith [mul_nonneg hε (abs_nonneg a), mul_nonneg hε (abs_nonneg b),
    mul_nonneg (mul_nonneg hε (abs_nonneg a)) (mul_nonneg hε (abs_nonneg b))]

/-- For `0 < ρ < 1`, `log(1 + ερ|x|) ≤ log(1 + ε|x|) + ½ log ρ` once `|x|` is large. -/
theorem logAbs_contract {ε ρ : ℝ} (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ r : ℝ, ∀ x : ℝ, r ≤ |x| →
      Real.log (1 + ε * (ρ * |x|)) ≤ Real.log (1 + ε * |x|) + Real.log ρ / 2 := by
  set s := Real.sqrt ρ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hρ0
  have hs1 : s < 1 := by rw [hs, Real.sqrt_lt' one_pos]; simpa using hρ1
  have hss : s * s = ρ := Real.mul_self_sqrt hρ0.le
  have hρs : ρ < s := by nlinarith
  refine ⟨(1 - s) / (ε * (s - ρ)), fun x hx => ?_⟩
  have hden : 0 < ε * (s - ρ) := mul_pos hε (by linarith)
  rw [div_le_iff₀ hden] at hx
  have hkey : 1 + ε * (ρ * |x|) ≤ s * (1 + ε * |x|) := by nlinarith
  have hlog : Real.log ρ / 2 = Real.log s := by
    rw [hs, Real.log_sqrt hρ0.le]
  rw [hlog, ← Real.log_mul (by positivity) hs0.ne']
  refine Real.log_le_log (by positivity) ?_
  linarith [mul_comm s (1 + ε * |x|)]

/-- For an integrable `log(1 + |W|)`, `E log(1 + ε|W|) < η` for a small `ε ∈ (0, 1]`. -/
theorem exists_small_logAbs (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => Real.log (1 + |w|)) Γ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∫ w, Real.log (1 + ε * |w|) ∂Γ < η := by
  have hc : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => ∫ w, Real.log (1 + 1 / ((n : ℝ) + 1) * |w|) ∂Γ) atTop
      (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂Γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => Real.log (1 + |w|))
      (fun n => (Real.measurable_log.comp (measurable_const.add (measurable_const.mul
        (measurable_id.norm : Measurable fun w : ℝ => ‖w‖)))).aestronglyMeasurable) hW
      (fun n => Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w => ?_)
    · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1)) (abs_nonneg w)
        linarith))]
      refine Real.log_le_log (by positivity) ?_
      have := mul_le_of_le_one_left (abs_nonneg w) h1
      linarith
    · have : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) * |w|) atTop (𝓝 (1 + 0 * |w|)) :=
        tendsto_const_nhds.add (hc.mul tendsto_const_nhds)
      simpa using this.log (by norm_num)
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hη)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, hn⟩
  rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **Proposition 11.4.2** (MT p. 273): for the simple linear model `Xₙ = αXₙ₋₁ + Wₙ` with
`|α| < 1` and `E log(1 + |W|) < ∞`, every compact set is regular and the chain is regular. The test
function is `V(x) = log(1 + ε|x|)`, subadditive (`logAbs_add_le`) with
`V(x) − V(ρx) ≥ −½ log ρ` for large `|x|` (`logAbs_contract`, `ρ = max(|α|, ½)`) and
`E V(W) < −¼ log ρ` for small `ε` (`exists_small_logAbs`). The `ψ`-irreducibility and the
petiteness of compact sets, which the book takes from Proposition 6.3.5 (non-singular `W`), are
hypotheses. -/
theorem proposition_11_4_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW : Integrable (fun w => Real.log (1 + |w|)) Γ) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hpet : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (ar1Kernel Γ α) ψ K) ∧
      IsRegularChain (ar1Kernel Γ α) ψ := by
  have := isMarkovKernel_ar1Kernel Γ α
  set ρ := max |α| 2⁻¹ with hρdef
  have hρ0 : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hρ1 : ρ < 1 := max_lt hα (by norm_num)
  have hαρ : |α| ≤ ρ := le_max_left _ _
  set L := -Real.log ρ with hLdef
  have hL : 0 < L := by rw [hLdef, neg_pos]; exact Real.log_neg hρ0 hρ1
  obtain ⟨ε, hε0, hε1, hεW⟩ := exists_small_logAbs Γ hW (η := L / 4) (by positivity)
  obtain ⟨r, hr⟩ := logAbs_contract hε0 hρ0 hρ1
  set V : ℝ → ℝ := fun x => Real.log (1 + ε * |x|) with hVdef
  have hVm : Measurable V := Real.measurable_log.comp (measurable_const.add
    (measurable_const.mul (measurable_id.norm : Measurable fun w : ℝ => ‖w‖)))
  have hV0 : ∀ x, 0 ≤ V x := fun x => Real.log_nonneg (by
    have := mul_nonneg hε0.le (abs_nonneg x); linarith)
  have hVmono : ∀ x y, |x| ≤ |y| → V x ≤ V y := fun x y h =>
    Real.log_le_log (by positivity) (by nlinarith)
  -- `V(W)` is integrable
  have hVW : Integrable (fun w => V w) Γ := by
    refine Integrable.mono' hW hVm.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 w)]
    refine Real.log_le_log (by positivity) ?_
    have := mul_le_of_le_one_left (abs_nonneg w) hε1
    linarith
  -- the one-step law
  have hker : ∀ x, ar1Kernel Γ α x = Γ.map fun w => α * x + w := fun x =>
    recursionKernel_apply Γ (measurable_ar1Step α) x
  have hstepm : ∀ x : ℝ, Measurable fun w : ℝ => α * x + w := fun x =>
    measurable_const.add measurable_id
  have hint : ∀ x, Integrable (fun w => V (α * x + w)) Γ := fun x => by
    refine Integrable.mono' ((integrable_const (V (α * x))).add hVW)
      (hVm.comp (hstepm x)).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 _)]
    exact logAbs_add_le hε0.le _ _
  have hPV : ∀ x, ∫ y, V y ∂ar1Kernel Γ α x ≤ V (α * x) + L / 4 := fun x => by
    rw [hker, integral_map (hstepm x).aemeasurable hVm.aestronglyMeasurable]
    calc ∫ w, V (α * x + w) ∂Γ ≤ ∫ w, (V (α * x) + V w) ∂Γ :=
          integral_mono (hint x) ((integrable_const _).add hVW)
            fun w => logAbs_add_le hε0.le _ _
      _ = V (α * x) + ∫ w, V w ∂Γ := by
          rw [integral_add (integrable_const _) hVW, integral_const]; simp
      _ ≤ V (α * x) + L / 4 := by linarith
  -- the drift off `C = [−r', r']`
  set r' := max r 0
  have hoff : ∀ x, r' < |x| → ∫ y, V y ∂ar1Kernel Γ α x ≤ V x - L / 4 := fun x hx => by
    have h1 : V (α * x) ≤ Real.log (1 + ε * (ρ * |x|)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right hαρ (abs_nonneg x)]
    have h2 := hr x ((le_max_left _ _).trans hx.le)
    have h3 := hPV x
    rw [hLdef] at h3 ⊢
    simp only [hVdef] at h1 h2 h3 ⊢
    linarith
  -- the scaled test function
  set c₄ := 4 / L with hc₄
  have hc₄pos : 0 < c₄ := by positivity
  set W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (V x * c₄) with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (hVm.mul_const _)
  have hPW : ∀ x, ∫⁻ y, W y ∂ar1Kernel Γ α x =
      ENNReal.ofReal ((∫ y, V y ∂ar1Kernel Γ α x) * c₄) := fun x => by
    have hiV : Integrable V (ar1Kernel Γ α x) := by
      rw [hker, integrable_map_measure hVm.aestronglyMeasurable (hstepm x).aemeasurable]
      exact hint x
    rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal (hiV.mul_const _)
      (Eventually.of_forall fun y => mul_nonneg (hV0 y) hc₄pos.le)]
  set C := Icc (-r') r' with hCdef
  have hmemC : ∀ x, x ∈ C ↔ |x| ≤ r' := fun x => by rw [hCdef, mem_Icc, abs_le]
  have hCpet : IsPetite (ar1Kernel Γ α) C := hpet C isCompact_Icc
  set K := V r' + L / 4 with hKdef
  set b := ENNReal.ofReal (K * c₄) + 1 with hbdef
  have hb : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hdrift : DriftV2 (ar1Kernel Γ α) W b C := by
    intro x
    rw [hPW x]
    have hI0 : 0 ≤ ∫ y, V y ∂ar1Kernel Γ α x := integral_nonneg hV0
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx]
      refine le_trans ?_ le_add_self
      refine add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hc₄pos.le))
        le_rfl
      have hx' := (hmemC x).1 hx
      have : V (α * x) ≤ V r' := hVmono _ _ (by
        rw [abs_mul, abs_of_nonneg (le_max_right r 0)]
        nlinarith [abs_nonneg x, abs_nonneg α, hα])
      rw [hKdef]
      linarith [hPV x]
    · rw [indicator_of_notMem hx, add_zero]
      have hx' : r' < |x| := not_le.1 fun h => hx ((hmemC x).2 h)
      have h1 := hoff x hx'
      have hVx : 1 ≤ V x * c₄ := by
        rw [hc₄, ← mul_div_assoc, le_div_iff₀ hL]; linarith
      calc ENNReal.ofReal ((∫ y, V y ∂ar1Kernel Γ α x) * c₄) + 1
          ≤ ENNReal.ofReal (V x * c₄ - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]
            refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have : (∫ y, V y ∂ar1Kernel Γ α x) * c₄ ≤ (V x - L / 4) * c₄ :=
              mul_le_mul_of_nonneg_right h1 hc₄pos.le
            have h4 : L / 4 * c₄ = 1 := by rw [hc₄]; field_simp
            rw [sub_mul, h4] at this
            linarith
        _ = W x := by rw [← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
  have hWfin : ∀ x, W x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  refine ⟨fun K' hK' => ?_, (theorem_11_3_15 hψ).1.2 ⟨C, W, b, hCpet, hWm, hb, hWfin, hdrift⟩⟩
  obtain ⟨c, hc⟩ := hK'.isBounded.exists_norm_le
  exact theorem_11_3_11_i_regular hψ hWm hb hCpet hdrift hK'.measurableSet
    (M := ENNReal.ofReal (V c * c₄)) ENNReal.ofReal_ne_top fun y hy =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hVmono _ _ (by
        have := hc y hy; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self c)))
        hc₄pos.le)

/-! ### Proposition 17.3.4 for the parameter process -/

/-- The parameter process of the dependent parameter bilinear model is the AR(1) model
`θₖ₊₁ = αθₖ + Zₖ₊₁` (2.14): the first coordinate of one step of `Φ = (θ, Y)` has law
`P_θ(θ, ·)`. -/
theorem dblKernel_map_fst (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] (α : ℝ) (q : ℝ × ℝ) :
    (dblKernel Γz Γw α q).map Prod.fst = ar1Kernel Γz α q.1 := by
  have hF := (contDiff_dblStep α).continuous.measurable
  have hs : Measurable fun w : ℝ × ℝ => dblStep α (q, w) := hF.comp measurable_prodMk_left
  rw [dblKernel, recursionKernel_apply _ hF, Measure.map_map measurable_fst hs, ar1Kernel,
    recursionKernel_apply Γz (measurable_ar1Step α)]
  have e : (Prod.fst ∘ fun w : ℝ × ℝ => dblStep α (q, w)) =
      (fun z : ℝ => α * (q.1, z).1 + (q.1, z).2) ∘ Prod.fst := rfl
  have hg : Measurable fun z : ℝ => α * (q.1, z).1 + (q.1, z).2 :=
    (measurable_ar1Step α).comp measurable_prodMk_left
  rw [e, ← Measure.map_map hg measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

/-- **Proposition 17.3.4** (MT p. 438) in the book's setting: under (DBL1) (`|α| < 1`) and the
moment condition of (DBL2) (`E log(1 + |Z|) < ∞`), the parameter process `θ` is positive Harris
(Proposition 11.4.2: it is regular), and for its invariant probability `π_θ` and every `f` with
`π_θ(f⁺) < ∞`, `(1/N) Σ_{k=1}^N f(θₖ) → π_θ(f)` almost surely from every initial state, the limit
being `−∞` when `π_θ(f⁻) = ∞`. The `ψ`-irreducibility and the petiteness of compact sets, which
the book takes from Proposition 7.4.1 (a T-chain), are hypotheses. -/
theorem proposition_17_3_4_dbl (Γz : Measure ℝ) [IsProbabilityMeasure Γz] {α : ℝ}
    (hα : |α| < 1) (hZ : Integrable (fun z => Real.log (1 + |z|)) Γz) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γz α; IsMaximalIrreducibility (ar1Kernel Γz α) ψ)
    (hpet : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γz α) K) :
    haveI := isMarkovKernel_ar1Kernel Γz α
    IsPositiveHarris (ar1Kernel Γz α) ψ ∧
    ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (ar1Kernel Γz α) π →
      ∀ f : ℝ → ℝ, Measurable f → ∫⁻ x, ENNReal.ofReal (f x) ∂π ≠ ∞ → ∀ x,
        (Integrable f π → ∀ᵐ ω ∂pathKernel (ar1Kernel Γz α) x,
          Tendsto (fun n => pathSum f n ω / n) atTop (𝓝 (∫ y, f y ∂π))) ∧
        (∫⁻ y, ENNReal.ofReal (-f y) ∂π = ∞ → ∀ᵐ ω ∂pathKernel (ar1Kernel Γz α) x,
          Tendsto (fun n => pathSum f n ω / n) atTop atBot) := by
  have := isMarkovKernel_ar1Kernel Γz α
  have hph := (proposition_11_4_2 Γz hα hZ hψ hpet).2.isPositiveHarris hψ
  refine ⟨hph, fun π _ hπ f hfm hpos x => ⟨fun hfi => lln_of_harris hph.1 hπ hfm hfi x,
    fun hneg => proposition_17_3_4 hph.1 hπ hfm hpos hneg x⟩⟩

/-! ### The Bernoulli shift -/

variable {W : Type*} [MeasurableSpace W]

/-- The shift preserves `Γ^{⊗ℕ}`. -/
theorem measurePreserving_seqShift (Γ : Measure W) [IsProbabilityMeasure Γ] :
    MeasurePreserving seqShift (Measure.infinitePi fun _ : ℕ => Γ)
      (Measure.infinitePi fun _ : ℕ => Γ) :=
  ⟨measurable_seqShift, infinitePi_map_seqShift Γ⟩

omit [MeasurableSpace W] in
/-- `θⁿ(w)ⱼ = w_{j+n}` for the shift on sequences. -/
theorem seqShift_iterate_apply (k : ℕ) (w : ℕ → W) (j : ℕ) :
    seqShift^[k] w j = w (j + k) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    change w (j + k + 1) = w (j + (k + 1))
    rw [Nat.add_assoc]

/-- **The Bernoulli shift is ergodic**: a strictly invariant event of `Γ^{⊗ℕ}` lies in the tail
σ-algebra, so it has probability `0` or `1` (Kolmogorov's zero–one law). -/
theorem infinitePi_seqShift_ergodic (Γ : Measure W) [IsProbabilityMeasure Γ]
    {E : Set (ℕ → W)} (hEm : MeasurableSet E) (hE : seqShift ⁻¹' E = E) :
    (Measure.infinitePi fun _ : ℕ => Γ) E = 0 ∨ (Measure.infinitePi fun _ : ℕ => Γ) E = 1 := by
  set s : ℕ → MeasurableSpace (ℕ → W) :=
    fun i => MeasurableSpace.comap (fun w : ℕ → W => w i) inferInstance with hs
  have hle : ∀ i, s i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  refine measure_zero_or_one_of_measurableSet_limsup_atTop hle (iIndep_coords' Γ) ?_
  rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro n
  have hcomap : MeasurableSpace.comap (seqShift^[n] : (ℕ → W) → ℕ → W) MeasurableSpace.pi ≤
      ⨆ i ≥ n, s i := by
    simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro j
    have e : (fun w : ℕ → W => seqShift^[n] w j) = fun w => w (j + n) :=
      funext fun w => seqShift_iterate_apply n w j
    rw [e]
    exact le_iSup₂ (f := fun i (_ : i ≥ n) => s i) (j + n) (Nat.le_add_left n j)
  have hpre : seqShift^[n] ⁻¹' E = E := by
    ext w; exact iterate_mem_iff hE n w
  rw [← hpre]
  exact hcomap _ ⟨E, hEm, rfl⟩

/-- **Birkhoff's theorem for the Bernoulli shift**: for `f ∈ L¹(Γ^{⊗ℕ})`,
`(1/n) Σ_{k<n} f(θᵏw) → ∫ f` almost surely. -/
theorem ae_tendsto_birkhoffAverage_seqShift (Γ : Measure W) [IsProbabilityMeasure Γ]
    {f : (ℕ → W) → ℝ} (hfm : Measurable f)
    (hf : Integrable f (Measure.infinitePi fun _ : ℕ => Γ)) :
    ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => Γ), Tendsto (fun n => birkhoffAverage ℝ seqShift f n w)
      atTop (𝓝 (∫ w, f w ∂(Measure.infinitePi fun _ : ℕ => Γ))) :=
  ae_tendsto_birkhoffAverage_of_ergodic (measurePreserving_seqShift Γ) hfm hf
    fun _ hEm hE => infinitePi_seqShift_ergodic Γ hEm hE

/-! ### Stationary solutions of random recursions -/

/-- `μP = (μ ⊗ Γ) ∘ F⁻¹` for a random recursion `Xₖ₊₁ = F(Xₖ, Wₖ₊₁)`. -/
theorem recursionKernel_comp' {S : Type*} [MeasurableSpace S] (Γ : Measure W)
    [IsProbabilityMeasure Γ] {F : S × W → S} (hF : Measurable F) (π : Measure S) [SFinite π] :
    recursionKernel Γ F ∘ₘ π = (π.prod Γ).map F := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), Measure.map_apply hF hA,
    Measure.prod_apply (hF hA)]
  refine lintegral_congr fun x => ?_
  rw [recursionKernel_apply' Γ hF x hA]
  rfl

/-- **Stationary solutions** (the construction of MT §10.5.4): if `X(w) = F(X(θw), w₀)` almost
surely under `Γ^{⊗ℕ}`, then the law of `X` is invariant for the recursion `Xₖ₊₁ = F(Xₖ, Wₖ₊₁)`. -/
theorem isInvariant_recursionKernel_map {S : Type*} [MeasurableSpace S] (Γ : Measure W)
    [IsProbabilityMeasure Γ] {F : S × W → S} (hF : Measurable F) {X : (ℕ → W) → S}
    (hX : Measurable X)
    (hcons : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => Γ), X w = F (X (seqShift w), w 0)) :
    IsInvariant (recursionKernel Γ F) ((Measure.infinitePi fun _ : ℕ => Γ).map X) := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ with hμ
  unfold IsInvariant
  have hprod : (μ.map X).prod Γ = (μ.prod Γ).map (Prod.map X id) := by
    rw [← Measure.map_prod_map μ Γ hX measurable_id, Measure.map_id]
  rw [recursionKernel_comp' Γ hF, hprod, Measure.map_map hF (hX.prodMap measurable_id)]
  have hc : μ = (Γ.prod μ).map (fun q => consSeq q.1 q.2) := (prod_map_consSeq Γ).symm
  have hae : ∀ᵐ q ∂(Γ.prod μ), X (consSeq q.1 q.2) = F (X q.2, q.1) := by
    have h0 := hcons
    rw [hc] at h0
    exact ae_of_ae_map measurable_consSeq.aemeasurable h0
  conv_rhs => rw [hc]
  rw [Measure.map_map hX measurable_consSeq,
    show (X ∘ fun q : W × (ℕ → W) => consSeq q.1 q.2) = fun q => X (consSeq q.1 q.2) from rfl,
    Measure.map_congr hae, ← Measure.prod_swap,
    Measure.map_map (hF.comp (hX.prodMap measurable_id)) measurable_swap]
  rfl

/-! ### A Borel–Cantelli bound -/

/-- For `X ≥ 0` integrable under a finite measure, `Σⱼ ν{X > j} < ∞`. -/
theorem tsum_measure_lt_ne_top {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [IsFiniteMeasure ν] {X : β → ℝ} (hXm : Measurable X) (hX0 : ∀ x, 0 ≤ X x)
    (hXi : Integrable X ν) : ∑' j : ℕ, ν {x | (j : ℝ) < X x} ≠ ∞ := by
  have hpt : ∀ x, ∑' j : ℕ, {y | (j : ℝ) < X y}.indicator (1 : β → ℝ≥0∞) x ≤
      ENNReal.ofReal (X x) + 1 := fun x => by
    have e : ∑' j : ℕ, {y | (j : ℝ) < X y}.indicator (1 : β → ℝ≥0∞) x =
        ∑ j ∈ Finset.range ⌈X x⌉₊, (1 : ℝ≥0∞) := by
      rw [tsum_eq_sum (s := Finset.range ⌈X x⌉₊) fun j hj => by
        rw [Finset.mem_range, Nat.lt_ceil] at hj
        exact indicator_of_notMem (s := {y | (j : ℝ) < X y}) (a := x) hj 1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range, Nat.lt_ceil] at hj
      exact indicator_of_mem (s := {y | (j : ℝ) < X y}) (a := x) hj 1
    rw [e, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h1 : (⌈X x⌉₊ : ℝ) ≤ X x + 1 := (Nat.ceil_lt_add_one (hX0 x)).le
    calc (⌈X x⌉₊ : ℝ≥0∞) = ENNReal.ofReal (⌈X x⌉₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (X x + 1) := ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal (X x) + ENNReal.ofReal 1 := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (X x) + 1 := by rw [ENNReal.ofReal_one]
  have hmeas : ∀ j : ℕ, MeasurableSet {y | (j : ℝ) < X y} := fun j =>
    measurableSet_lt measurable_const hXm
  have e2 : ∑' j : ℕ, ν {x | (j : ℝ) < X x} =
      ∫⁻ x, ∑' j : ℕ, {y | (j : ℝ) < X y}.indicator (1 : β → ℝ≥0∞) x ∂ν := by
    rw [lintegral_tsum fun j => (measurable_one.indicator (hmeas j)).aemeasurable]
    exact tsum_congr fun j => (lintegral_indicator_one (hmeas j)).symm
  rw [e2]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_right _ measurable_const, lintegral_const]
  exact ENNReal.add_ne_top.2 ⟨(hasFiniteIntegral_iff_ofReal (Eventually.of_forall hX0)).1
    hXi.2 |>.ne, ENNReal.mul_ne_top ENNReal.one_ne_top (measure_ne_top _ _)⟩

/-- **Borel–Cantelli for an i.i.d. sequence**: if `E log(1 + |ζ|) < ∞`, then for every `κ > 0`,
almost surely `log(1 + |ζⱼ|) ≤ jκ` for all large `j`. -/
theorem ae_eventually_log_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hZ : Integrable (fun z => Real.log (1 + |z|)) Γ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ζ ∂(Measure.infinitePi fun _ : ℕ => Γ), ∀ᶠ j : ℕ in atTop,
      Real.log (1 + |ζ j|) ≤ j * κ := by
  set X : ℝ → ℝ := fun z => Real.log (1 + |z|) / κ with hX
  have hXm : Measurable X :=
    (Real.measurable_log.comp (measurable_const.add continuous_abs.measurable)).div_const κ
  have hX0 : ∀ z, 0 ≤ X z := fun z =>
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg z])) hκ.le
  have hsum := tsum_measure_lt_ne_top hXm hX0 (hZ.div_const κ)
  have hset : ∀ j : ℕ, (Measure.infinitePi fun _ : ℕ => Γ) {ζ | (j : ℝ) < X (ζ j)} =
      Γ {z | (j : ℝ) < X z} := fun j => by
    rw [show {ζ : ℕ → ℝ | (j : ℝ) < X (ζ j)} = (fun ζ : ℕ → ℝ => ζ j) ⁻¹' {z | (j : ℝ) < X z}
      from rfl, ← Measure.map_apply (measurable_pi_apply j) (measurableSet_lt measurable_const
      hXm), Measure.infinitePi_map_eval]
  have h := ae_eventually_notMem (μ := Measure.infinitePi fun _ : ℕ => Γ)
    (s := fun j : ℕ => {ζ : ℕ → ℝ | (j : ℝ) < X (ζ j)}) (by simp_rw [hset]; exact hsum)
  filter_upwards [h] with ζ hζ
  filter_upwards [hζ] with j hj
  have h1 : X (ζ j) ≤ j := not_lt.1 hj
  rwa [hX, div_le_iff₀ hκ] at h1

/-! ### The stationary parameter process and the backward LLN (17.26) -/

/-- The stationary solution of (2.14), `θ₀ = Σⱼ αʲ Z₋ⱼ`, as a function of the past innovations
`ζⱼ = Z₋ⱼ` (zero when the series diverges). -/
noncomputable def thetaSeries (α : ℝ) (ζ : ℕ → ℝ) : ℝ := ∑' j, α ^ j * ζ j

/-- `θ₀` is measurable. -/
theorem measurable_thetaSeries (α : ℝ) : Measurable (thetaSeries α) :=
  Measurable.tsum fun j => measurable_const.mul (measurable_pi_apply j)

/-- Under (DBL1) and `E log(1 + |Z|) < ∞` the series `Σⱼ αʲ ζⱼ` converges absolutely almost
surely: `|ζⱼ| ≤ βʲ` eventually, for `β = 2/(1 + |α|)`, by Borel–Cantelli. -/
theorem ae_summable_thetaSeries (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hα : |α| < 1) (hZ : Integrable (fun z => Real.log (1 + |z|)) Γ) :
    ∀ᵐ ζ ∂(Measure.infinitePi fun _ : ℕ => Γ), Summable fun j => |α ^ j * ζ j| := by
  set β : ℝ := 2 / (1 + |α|) with hβ
  have hα0 := abs_nonneg α
  have hβ1 : 1 < β := by rw [hβ, lt_div_iff₀ (by positivity)]; linarith
  have hαβ : |α| * β < 1 := by
    rw [hβ, mul_div_assoc', div_lt_one (by positivity)]; nlinarith
  filter_upwards [ae_eventually_log_le Γ hZ (Real.log_pos hβ1)] with ζ hζ
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by positivity) hαβ) ?_
  filter_upwards [hζ] with j hj
  have h1 : 1 + |ζ j| ≤ β ^ j := by
    have := Real.exp_le_exp.2 hj
    rwa [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by linarith)] at this
  rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hα0 j)

/-- The recursion (2.14) for the stationary solution: `θ₀ = α θ₋₁ + Z₀`. -/
theorem thetaSeries_cons {α : ℝ} {ζ : ℕ → ℝ} (hs : Summable fun j => |α ^ j * ζ j|) :
    thetaSeries α ζ = α * thetaSeries α (seqShift ζ) + ζ 0 := by
  have hs' : Summable fun j => α ^ j * ζ j := hs.of_abs
  rw [thetaSeries, hs'.tsum_eq_zero_add, pow_zero, one_mul, add_comm, thetaSeries,
    ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ]
  change α ^ j * α * ζ (j + 1) = α * (α ^ j * ζ (j + 1))
  ring

/-- The law `π_θ` of the stationary solution `θ₀ = Σⱼ αʲ Z₋ⱼ`. -/
noncomputable def thetaLaw (Γ : Measure ℝ) (α : ℝ) : Measure ℝ :=
  (Measure.infinitePi fun _ : ℕ => Γ).map (thetaSeries α)

/-- `π_θ` is a probability measure. -/
theorem isProbabilityMeasure_thetaLaw (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ) :
    IsProbabilityMeasure (thetaLaw Γ α) := by
  unfold thetaLaw; infer_instance

/-- `π_θ` is invariant for the parameter process `θₖ₊₁ = αθₖ + Zₖ₊₁`. -/
theorem isInvariant_thetaLaw (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hZ : Integrable (fun z => Real.log (1 + |z|)) Γ) :
    IsInvariant (ar1Kernel Γ α) (thetaLaw Γ α) :=
  isInvariant_recursionKernel_map Γ (measurable_ar1Step α) (measurable_thetaSeries α)
    ((ae_summable_thetaSeries Γ hα hZ).mono fun _ hζ => thetaSeries_cons hζ)

/-- For a Harris parameter process, `π_θ` is its only invariant probability. -/
theorem eq_thetaLaw_of_isInvariant (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hα : |α| < 1) (hZ : Integrable (fun z => Real.log (1 + |z|)) Γ) {ψ : Measure ℝ}
    (hH : haveI := isMarkovKernel_ar1Kernel Γ α; IsHarris (ar1Kernel Γ α) ψ)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : IsInvariant (ar1Kernel Γ α) π) : π = thetaLaw Γ α := by
  have := isMarkovKernel_ar1Kernel Γ α
  have := isProbabilityMeasure_thetaLaw Γ α
  obtain ⟨c, -, hc⟩ := hH.isRecurrentChain.exists_eq_smul (μ := π) (ν := thetaLaw Γ α)
    ⟨inferInstance, le_of_eq hπ⟩ ⟨inferInstance, le_of_eq (isInvariant_thetaLaw Γ hα hZ)⟩
    (IsProbabilityMeasure.ne_zero _)
  have h1 := congrArg (fun m : Measure ℝ => m univ) hc
  simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] at h1
  rw [hc, ← h1, one_smul]

/-- `θ₋ₖ = θ₀ ∘ θᵏ`, the stationary parameter at time `−k`. -/
theorem thetaSeries_iterate_succ (α : ℝ) (k : ℕ) (ζ : ℕ → ℝ) :
    thetaSeries α (seqShift^[k + 1] ζ) = (fun ζ => thetaSeries α (seqShift ζ)) (seqShift^[k] ζ) :=
  by rw [Function.iterate_succ_apply']

/-- The Birkhoff averages of `f(θ₋₁), f(θ₋₂), …`. -/
theorem birkhoffAverage_thetaSeries (α : ℝ) (f : ℝ → ℝ) (N : ℕ) (ζ : ℕ → ℝ) :
    birkhoffAverage ℝ seqShift (fun ζ => f (thetaSeries α (seqShift ζ))) N ζ =
      (∑ k ∈ Finset.range N, f (thetaSeries α (seqShift^[k + 1] ζ))) / N := by
  rw [birkhoffAverage_eq_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.iterate_succ_apply']

/-- **The backward LLN (17.26)** (MT p. 438), integrable case: for the stationary parameter
process `θ₋ₖ = Σⱼ αʲ Z₋ₖ₋ⱼ` built from i.i.d. past innovations, and `f ∈ L¹(π_θ)`,
`(1/N) Σ_{k=1}^N f(θ₋ₖ) → π_θ(f)` almost surely (Birkhoff's theorem for the ergodic Bernoulli
shift). -/
theorem theorem_17_26_integrable (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ)
    {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f (thetaLaw Γ α)) :
    ∀ᵐ ζ ∂(Measure.infinitePi fun _ : ℕ => Γ),
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, f (thetaSeries α (seqShift^[k + 1] ζ))) / N)
        atTop (𝓝 (∫ x, f x ∂thetaLaw Γ α)) := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hθ := measurable_thetaSeries α
  have hT := measurePreserving_seqShift Γ
  have hg : Measurable fun ζ => f (thetaSeries α (seqShift ζ)) :=
    hfm.comp (hθ.comp measurable_seqShift)
  have hfθ : Integrable (fun ζ => f (thetaSeries α ζ)) μ :=
    (integrable_map_measure hfm.aestronglyMeasurable hθ.aemeasurable).1 hfi
  have hgi : Integrable (fun ζ => f (thetaSeries α (seqShift ζ))) μ :=
    hT.integrable_comp_of_integrable hfθ
  have hint : ∫ ζ, f (thetaSeries α (seqShift ζ)) ∂μ = ∫ x, f x ∂thetaLaw Γ α := by
    rw [thetaLaw, integral_map hθ.aemeasurable hfm.aestronglyMeasurable]
    have h := integral_map (μ := μ) hT.measurable.aemeasurable
      (f := fun ζ => f (thetaSeries α ζ)) (hfm.comp hθ).aestronglyMeasurable
    rw [hT.map_eq] at h
    exact h.symm
  filter_upwards [ae_tendsto_birkhoffAverage_seqShift Γ hg hgi] with ζ hζ
  rw [hint] at hζ
  simpa only [birkhoffAverage_thetaSeries] using hζ

/-- **The backward LLN (17.26)** (MT p. 438), in the form of Proposition 17.3.4: for `f` with
`π_θ(f⁺) < ∞`, `(1/N) Σ_{k=1}^N f(θ₋ₖ) → π_θ(f)` almost surely, the limit being `−∞` when
`π_θ(f⁻) = ∞` (truncation `max(f, −M)` and `theorem_17_26_integrable`). -/
theorem theorem_17_26 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ) {f : ℝ → ℝ}
    (hfm : Measurable f) (hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂thetaLaw Γ α ≠ ∞) :
    (Integrable f (thetaLaw Γ α) → ∀ᵐ ζ ∂(Measure.infinitePi fun _ : ℕ => Γ),
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, f (thetaSeries α (seqShift^[k + 1] ζ))) / N)
        atTop (𝓝 (∫ x, f x ∂thetaLaw Γ α))) ∧
    (∫⁻ x, ENNReal.ofReal (-f x) ∂thetaLaw Γ α = ∞ →
      ∀ᵐ ζ ∂(Measure.infinitePi fun _ : ℕ => Γ),
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, f (thetaSeries α (seqShift^[k + 1] ζ))) / N)
        atTop atBot) := by
  refine ⟨theorem_17_26_integrable Γ α hfm, fun hneg => ?_⟩
  have := isProbabilityMeasure_thetaLaw Γ α
  have hfMm : ∀ M : ℕ, Measurable fun y => max (f y) (-(M : ℝ)) := fun M =>
    hfm.max measurable_const
  have hfMi : ∀ M : ℕ, Integrable (fun y => max (f y) (-(M : ℝ))) (thetaLaw Γ α) := fun M => by
    refine ⟨(hfMm M).aestronglyMeasurable, ?_⟩
    have hb : ∀ y, ‖max (f y) (-(M : ℝ))‖ₑ ≤ ENNReal.ofReal (f y) + M := fun y => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      calc ENNReal.ofReal |max (f y) (-(M : ℝ))| ≤ ENNReal.ofReal (max (f y) 0 + M) := by
            refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
            · have := le_max_right (f y) (-(M : ℝ)); linarith [le_max_right (f y) 0]
            · rcases le_total (f y) (-(M : ℝ)) with h | h
              · rw [max_eq_right h]; linarith [le_max_right (f y) 0]
              · rw [max_eq_left h]; linarith [le_max_left (f y) 0]
        _ = ENNReal.ofReal (max (f y) 0) + ENNReal.ofReal M :=
            ENNReal.ofReal_add (le_max_right _ _) hM0
        _ ≤ ENNReal.ofReal (f y) + M := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
              ENNReal.ofReal_natCast]
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, ENNReal.mul_lt_top
      (ENNReal.natCast_lt_top M) (measure_lt_top _ _)⟩
  have hall := ae_all_iff.2 fun M : ℕ => theorem_17_26_integrable Γ α (hfMm M) (hfMi M)
  filter_upwards [hall] with ζ hζ
  rw [tendsto_atBot]
  intro L
  obtain ⟨M, hM⟩ := exists_integral_max_lt hfm hpos hneg L
  filter_upwards [(hζ M).eventually (gt_mem_nhds hM)] with N hN
  refine le_trans ?_ hN.le
  have hle : ∑ k ∈ Finset.range N, f (thetaSeries α (seqShift^[k + 1] ζ)) ≤
      ∑ k ∈ Finset.range N, max (f (thetaSeries α (seqShift^[k + 1] ζ))) (-(M : ℝ)) :=
    Finset.sum_le_sum fun k _ => le_max_left _ _
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg N)

/-! ### Proposition 17.3.5: the stationary solution of the bilinear model -/

/-- The innovations `ζⱼ = Z₋ⱼ` of the parameter process, from the joint innovations
`ξⱼ = (Z₋ⱼ, W₋ⱼ)`. -/
def fstSeq (ξ : ℕ → ℝ × ℝ) : ℕ → ℝ := fun j => (ξ j).1

/-- `fstSeq` is measurable. -/
theorem measurable_fstSeq : Measurable fstSeq :=
  measurable_pi_iff.2 fun j => measurable_fst.comp (measurable_pi_apply j)

/-- The `Z`-innovations of `(Γz ⊗ Γw)^{⊗ℕ}` are i.i.d. `Γz`. -/
theorem infinitePi_map_fstSeq (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] :
    (Measure.infinitePi fun _ : ℕ => Γz.prod Γw).map fstSeq =
      Measure.infinitePi fun _ : ℕ => Γz := by
  rw [show fstSeq = fun (ξ : ℕ → ℝ × ℝ) (j : ℕ) => (ξ j).1 from rfl,
    Measure.infinitePi_map_pi (fun _ => Γz.prod Γw) (fun _ => measurable_fst)]
  congr 1
  funext j
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The `W`-innovations of `(Γz ⊗ Γw)^{⊗ℕ}` are i.i.d. `Γw`. -/
theorem infinitePi_map_sndSeq (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] :
    (Measure.infinitePi fun _ : ℕ => Γz.prod Γw).map (fun (ξ : ℕ → ℝ × ℝ) (j : ℕ) => (ξ j).2) =
      Measure.infinitePi fun _ : ℕ => Γw := by
  rw [Measure.infinitePi_map_pi (fun _ => Γz.prod Γw) (fun _ => measurable_snd)]
  congr 1
  funext j
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The stationary output of (2.13), `Y₀ = Σⱼ (θ₋₁ ⋯ θ₋ⱼ) W₋ⱼ` (17.28), as a function of the past
innovations (zero when the series diverges). -/
noncomputable def ySeries (α : ℝ) (ξ : ℕ → ℝ × ℝ) : ℝ :=
  ∑' j, (∏ i ∈ Finset.range j, thetaSeries α (seqShift^[i + 1] (fstSeq ξ))) * (ξ j).2

/-- The terms of `Y₀`. -/
noncomputable def yTerm (α : ℝ) (ξ : ℕ → ℝ × ℝ) (j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, thetaSeries α (seqShift^[i + 1] (fstSeq ξ))) * (ξ j).2

/-- The terms of `Y₀` are measurable. -/
theorem measurable_yTerm (α : ℝ) (j : ℕ) : Measurable fun ξ => yTerm α ξ j :=
  (Finset.measurable_prod _ fun i _ => (measurable_thetaSeries α).comp
    ((measurable_seqShift.iterate (i + 1)).comp measurable_fstSeq)).mul
    (measurable_snd.comp (measurable_pi_apply j))

/-- `Y₀` is measurable. -/
theorem measurable_ySeries (α : ℝ) : Measurable (ySeries α) :=
  Measurable.tsum fun j => measurable_yTerm α j

/-- The recursion of the terms: the term `j + 1` at `ξ` is `θ₋₁` times the term `j` at `θξ`. -/
theorem yTerm_succ (α : ℝ) (ξ : ℕ → ℝ × ℝ) (j : ℕ) :
    yTerm α ξ (j + 1) = thetaSeries α (fstSeq (seqShift ξ)) * yTerm α (seqShift ξ) j := by
  unfold yTerm
  rw [Finset.prod_range_succ', mul_comm _ (thetaSeries α _), mul_assoc]
  have e : ∀ i, seqShift^[i + 1 + 1] (fstSeq ξ) = seqShift^[i + 1] (fstSeq (seqShift ξ)) :=
    fun i => by rw [Function.iterate_succ_apply]; rfl
  simp_rw [e]
  rfl

/-- The recursion (2.13) for the stationary solution: `Y₀ = θ₋₁ Y₋₁ + W₀`. -/
theorem ySeries_cons {α : ℝ} {ξ : ℕ → ℝ × ℝ} (hs : Summable fun j => yTerm α ξ j) :
    ySeries α ξ = thetaSeries α (fstSeq (seqShift ξ)) * ySeries α (seqShift ξ) + (ξ 0).2 := by
  change ∑' j, yTerm α ξ j = _ * ∑' j, yTerm α (seqShift ξ) j + _
  rw [hs.tsum_eq_zero_add, add_comm, ← tsum_mul_left]
  simp_rw [yTerm_succ]
  congr 1
  simp [yTerm]

/-- `|Πᵢ xᵢ| ≤ exp(Σᵢ log|xᵢ|)` (with Lean's `log 0 = 0`, a zero factor only helps). -/
theorem abs_prod_le_exp_sum_log (s : Finset ℕ) (x : ℕ → ℝ) :
    |∏ i ∈ s, x i| ≤ Real.exp (∑ i ∈ s, Real.log |x i|) := by
  rw [Finset.abs_prod, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  by_cases hx : x i = 0
  · rw [hx, abs_zero]; exact (Real.exp_pos _).le
  · rw [Real.exp_log (abs_pos.2 hx)]

/-- (17.29)–(17.30): under (17.27), in the truncated form `π_θ(max(log|x|, −M)) < 0` for some
`M`, and `E log(1 + |W|) < ∞`, the series `Y₀ = Σⱼ (θ₋₁ ⋯ θ₋ⱼ) W₋ⱼ` converges absolutely almost
surely: by the backward LLN, `θ₋₁ ⋯ θ₋ⱼ` decays like `e^{−2κj}` while `|W₋ⱼ| ≤ e^{κj}`
eventually (the book's root test). -/
theorem ae_summable_yTerm (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] (α : ℝ) (hW : Integrable (fun w => Real.log (1 + |w|)) Γw)
    {M : ℝ} (hMi : Integrable (fun x => max (Real.log |x|) (-M)) (thetaLaw Γz α))
    (hMneg : ∫ x, max (Real.log |x|) (-M) ∂thetaLaw Γz α < 0) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => Γz.prod Γw), Summable fun j => |yTerm α ξ j| := by
  set lam := ∫ x, max (Real.log |x|) (-M) ∂thetaLaw Γz α with hlam
  set κ := -lam / 4 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hfm : Measurable fun x : ℝ => max (Real.log |x|) (-M) :=
    (Real.measurable_log.comp continuous_abs.measurable).max measurable_const
  have hlln := theorem_17_26_integrable Γz α hfm hMi
  rw [← infinitePi_map_fstSeq Γz Γw] at hlln
  have hlln' := ae_of_ae_map measurable_fstSeq.aemeasurable hlln
  have hbc := ae_eventually_log_le Γw hW hκ
  rw [← infinitePi_map_sndSeq Γz Γw] at hbc
  have hbc' := ae_of_ae_map (measurable_pi_iff.2 fun j =>
    measurable_snd.comp (measurable_pi_apply j)).aemeasurable hbc
  filter_upwards [hlln', hbc'] with ξ h1 h2
  have h3 := h1.eventually (gt_mem_nhds (show lam < lam / 2 by linarith))
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (Real.exp_pos (-κ)).le (Real.exp_lt_one_iff.2 (by linarith))) ?_
  filter_upwards [h2, h3, eventually_gt_atTop 0] with j hj2 hj3 hj0
  have hj0' : (0 : ℝ) < j := by exact_mod_cast hj0
  have hsum : ∑ i ∈ Finset.range j, Real.log |thetaSeries α (seqShift^[i + 1] (fstSeq ξ))| ≤
      j * (lam / 2) := by
    rw [div_lt_iff₀ hj0'] at hj3
    refine le_trans (Finset.sum_le_sum fun i _ => le_max_left _ (-M)) ?_
    linarith
  have hW' : |(ξ j).2| ≤ Real.exp (j * κ) := by
    change Real.log (1 + |(ξ j).2|) ≤ j * κ at hj2
    have := Real.exp_le_exp.2 hj2
    rw [Real.exp_log (by positivity)] at this
    linarith
  calc ‖|yTerm α ξ j|‖
      = |∏ i ∈ Finset.range j, thetaSeries α (seqShift^[i + 1] (fstSeq ξ))| * |(ξ j).2| := by
        rw [Real.norm_eq_abs, abs_abs, yTerm, abs_mul]
    _ ≤ Real.exp (∑ i ∈ Finset.range j,
          Real.log |thetaSeries α (seqShift^[i + 1] (fstSeq ξ))|) * Real.exp (j * κ) :=
        mul_le_mul (abs_prod_le_exp_sum_log _ _) hW' (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (j * (lam / 2)) * Real.exp (j * κ) := by gcongr
    _ = Real.exp (-κ) ^ j := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        rw [hκdef]
        ring

/-- The stationary law of `Φ = (θ, Y)`: the law of `(θ₀, Y₀)`. -/
noncomputable def dblStationaryLaw (Γz Γw : Measure ℝ) (α : ℝ) : Measure (ℝ × ℝ) :=
  (Measure.infinitePi fun _ : ℕ => Γz.prod Γw).map
    fun ξ => (thetaSeries α (fstSeq ξ), ySeries α ξ)

/-- The truncated form of (17.27): if `π(f⁺) < ∞` and `π(f) < 0` in the extended sense
(`∫ f⁺ < ∫ f⁻`, possibly `∫ f⁻ = ∞`), then `π(max(f, −M)) < 0` for some `M`, and `max(f, −M)`
is integrable. -/
theorem exists_truncation_neg {π : Measure ℝ} [IsProbabilityMeasure π] {f : ℝ → ℝ}
    (hfm : Measurable f) (hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂π ≠ ∞)
    (hlt : ∫⁻ x, ENNReal.ofReal (f x) ∂π < ∫⁻ x, ENNReal.ofReal (-f x) ∂π) :
    ∃ M : ℝ, Integrable (fun x => max (f x) (-M)) π ∧ ∫ x, max (f x) (-M) ∂π < 0 := by
  have hfMi : ∀ M : ℕ, Integrable (fun y => max (f y) (-(M : ℝ))) π := fun M => by
    refine ⟨(hfm.max measurable_const).aestronglyMeasurable, ?_⟩
    have hb : ∀ y, ‖max (f y) (-(M : ℝ))‖ₑ ≤ ENNReal.ofReal (f y) + M := fun y => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      calc ENNReal.ofReal |max (f y) (-(M : ℝ))| ≤ ENNReal.ofReal (max (f y) 0 + M) := by
            refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
            · have := le_max_right (f y) (-(M : ℝ)); linarith [le_max_right (f y) 0]
            · rcases le_total (f y) (-(M : ℝ)) with h | h
              · rw [max_eq_right h]; linarith [le_max_right (f y) 0]
              · rw [max_eq_left h]; linarith [le_max_left (f y) 0]
        _ = ENNReal.ofReal (max (f y) 0) + ENNReal.ofReal M :=
            ENNReal.ofReal_add (le_max_right _ _) hM0
        _ ≤ ENNReal.ofReal (f y) + M := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
              ENNReal.ofReal_natCast]
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, ENNReal.mul_lt_top
      (ENNReal.natCast_lt_top M) (measure_lt_top _ _)⟩
  by_cases hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂π = ∞
  · obtain ⟨M, hM⟩ := exists_integral_max_lt hfm hpos hneg 0
    exact ⟨M, hfMi M, hM⟩
  · -- `f` is integrable with `∫ f < 0`; dominated convergence in `M`
    have hfi : Integrable f π := by
      refine ⟨hfm.aestronglyMeasurable, ?_⟩
      change ∫⁻ x, ‖f x‖ₑ ∂π < ∞
      have hle : ∀ x, ‖f x‖ₑ ≤ ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) := fun x => by
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (f x) with h | h
        · rw [abs_of_nonneg h]; exact le_self_add
        · rw [abs_of_nonpos h]; exact le_add_self
      refine lt_of_le_of_lt (lintegral_mono hle) ?_
      rw [lintegral_add_left hfm.ennreal_ofReal]
      exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, lt_top_iff_ne_top.2 hneg⟩
    have hint : ∫ x, f x ∂π < 0 := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi, sub_neg]
      exact (ENNReal.toReal_lt_toReal hpos hneg).2 hlt
    have hlim : Tendsto (fun M : ℕ => ∫ x, max (f x) (-(M : ℝ)) ∂π) atTop
        (𝓝 (∫ x, f x ∂π)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
        (fun M => (hfm.max measurable_const).aestronglyMeasurable) hfi.abs
        (fun M => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := neg_abs_le (f x); linarith [le_max_left (f x) (-(M : ℝ))]
        · rcases le_total (f x) (-(M : ℝ)) with h | h
          · rw [max_eq_right h]; have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
            linarith [abs_nonneg (f x)]
          · rw [max_eq_left h]; exact le_abs_self _
      · obtain ⟨N, hN⟩ := exists_nat_ge (-f x)
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun M hM => ?_⟩)
        have : -(M : ℝ) ≤ f x := by
          have : (N : ℝ) ≤ M := by exact_mod_cast hM
          linarith
        change f x = max (f x) (-(M : ℝ))
        rw [max_eq_left this]
    obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds hint)).exists
    exact ⟨M, hfMi M, hM⟩

/-- **Proposition 17.3.5** (MT p. 438): under (DBL1)–(DBL2) (`|α| < 1`, `E log(1 + |Z|) < ∞`,
`E log(1 + |W|) < ∞`, the last implied by the book's `E W² < ∞`) and (17.27), the joint process
`Φ = (θ, Y)` has the invariant probability `dblStationaryLaw`, the law of the stationary solution
`(θ₀, Y₀)` of (17.28), whose first marginal is `π_θ`; hence, when `Φ` is `ψ`-irreducible, it is
positive and recurrent. (17.27) is taken in the extended sense `∫ log⁺|x| dπ_θ < ∞` and
`∫ log⁺|x| dπ_θ < ∫ log⁻|x| dπ_θ`, which allows `∫ log|x| dπ_θ = −∞`. -/
theorem proposition_17_3_5 (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] {α : ℝ} (hα : |α| < 1)
    (hZ : Integrable (fun z => Real.log (1 + |z|)) Γz)
    (hW : Integrable (fun w => Real.log (1 + |w|)) Γw)
    (hpos : ∫⁻ x, ENNReal.ofReal (Real.log |x|) ∂thetaLaw Γz α ≠ ∞)
    (h27 : ∫⁻ x, ENNReal.ofReal (Real.log |x|) ∂thetaLaw Γz α <
      ∫⁻ x, ENNReal.ofReal (-Real.log |x|) ∂thetaLaw Γz α) :
    haveI := isMarkovKernel_dblKernel Γz Γw α
    IsProbabilityMeasure (dblStationaryLaw Γz Γw α) ∧
    IsInvariant (dblKernel Γz Γw α) (dblStationaryLaw Γz Γw α) ∧
    (dblStationaryLaw Γz Γw α).map Prod.fst = thetaLaw Γz α ∧
    ∀ ψ : Measure (ℝ × ℝ), IsMaximalIrreducibility (dblKernel Γz Γw α) ψ →
      IsPositive (dblKernel Γz Γw α) ψ ∧ IsRecurrentChain (dblKernel Γz Γw α) ψ := by
  have := isMarkovKernel_dblKernel Γz Γw α
  have := isProbabilityMeasure_thetaLaw Γz α
  set μ := Measure.infinitePi fun _ : ℕ => Γz.prod Γw with hμ
  have hXm : Measurable fun ξ : ℕ → ℝ × ℝ => (thetaSeries α (fstSeq ξ), ySeries α ξ) :=
    ((measurable_thetaSeries α).comp measurable_fstSeq).prodMk (measurable_ySeries α)
  have hprob : IsProbabilityMeasure (dblStationaryLaw Γz Γw α) := by
    unfold dblStationaryLaw; infer_instance
  obtain ⟨M, hMi, hMneg⟩ := exists_truncation_neg
    (Real.measurable_log.comp continuous_abs.measurable) hpos h27
  have hθ := ae_summable_thetaSeries Γz hα hZ
  rw [← infinitePi_map_fstSeq Γz Γw] at hθ
  have hθ' := ae_of_ae_map measurable_fstSeq.aemeasurable hθ
  have hy := ae_summable_yTerm Γz Γw α hW hMi hMneg
  have hinv : IsInvariant (dblKernel Γz Γw α) (dblStationaryLaw Γz Γw α) := by
    refine isInvariant_recursionKernel_map (Γz.prod Γw) (contDiff_dblStep α).continuous.measurable
      hXm ?_
    filter_upwards [hθ', hy] with ξ h1 h2
    refine Prod.ext ?_ ?_
    · change thetaSeries α (fstSeq ξ) = α * thetaSeries α (fstSeq (seqShift ξ)) + (ξ 0).1
      exact thetaSeries_cons h1
    · change ySeries α ξ = thetaSeries α (fstSeq (seqShift ξ)) * ySeries α (seqShift ξ) + (ξ 0).2
      exact ySeries_cons h2.of_abs
  have hmarg : (dblStationaryLaw Γz Γw α).map Prod.fst = thetaLaw Γz α := by
    rw [dblStationaryLaw, Measure.map_map measurable_fst hXm, thetaLaw,
      ← infinitePi_map_fstSeq Γz Γw, Measure.map_map (measurable_thetaSeries α)
      measurable_fstSeq]
    rfl
  refine ⟨hprob, hinv, hmarg, fun ψ hψ => ?_⟩
  have hp : IsPositive (dblKernel Γz Γw α) ψ := ⟨hψ, _, hprob, hinv⟩
  exact ⟨hp, proposition_10_1_1 hp⟩

/-- The parameter process with the law `π_θ` of its stationary solution: under the hypotheses of
`proposition_17_3_4_dbl`, `π_θ = thetaLaw` is the unique invariant probability of `θ`. -/
theorem proposition_17_3_4_dbl_thetaLaw (Γz : Measure ℝ) [IsProbabilityMeasure Γz] {α : ℝ}
    (hα : |α| < 1) (hZ : Integrable (fun z => Real.log (1 + |z|)) Γz) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γz α; IsMaximalIrreducibility (ar1Kernel Γz α) ψ)
    (hpet : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γz α) K) :
    IsInvariant (ar1Kernel Γz α) (thetaLaw Γz α) ∧
      ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (ar1Kernel Γz α) π →
        π = thetaLaw Γz α := by
  have := isMarkovKernel_ar1Kernel Γz α
  have hph := (proposition_17_3_4_dbl Γz hα hZ hψ hpet).1
  exact ⟨isInvariant_thetaLaw Γz hα hZ, fun π _ hπ => eq_thetaLaw_of_isInvariant Γz hα hZ hph.1 hπ⟩

/-- The remark before Proposition 17.3.5 (MT p. 438): if `E_π|θ| < 1` then (17.27) holds (Jensen's
inequality; here `log y ≤ y − 1`). With Lean's `log 0 = 0` the remark needs `π{0} = 0`, which holds
when `π` has no atom at `0`. -/
theorem condition_17_27_of_integral_abs_lt_one {π : Measure ℝ} [IsProbabilityMeasure π]
    (h0 : π {0} = 0) (hi : Integrable (fun x => |x|) π) (h1 : ∫ x, |x| ∂π < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.log |x|) ∂π ≠ ∞ ∧
      ∫⁻ x, ENNReal.ofReal (Real.log |x|) ∂π < ∫⁻ x, ENNReal.ofReal (-Real.log |x|) ∂π := by
  have hle : ∀ x : ℝ, Real.log |x| ≤ |x| := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · have := Real.log_le_sub_one_of_pos (abs_pos.2 hx); linarith
  have hpos : ∫⁻ x, ENNReal.ofReal (Real.log |x|) ∂π ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => abs_nonneg x)]
    exact ENNReal.ofReal_ne_top
  refine ⟨hpos, ?_⟩
  have hlm : Measurable fun x : ℝ => Real.log |x| :=
    Real.measurable_log.comp continuous_abs.measurable
  by_cases hneg : ∫⁻ x, ENNReal.ofReal (-Real.log |x|) ∂π = ∞
  · rw [hneg]; exact lt_top_iff_ne_top.2 hpos
  · have hfi : Integrable (fun x => Real.log |x|) π := by
      refine ⟨hlm.aestronglyMeasurable, ?_⟩
      change ∫⁻ x, ‖Real.log |x|‖ₑ ∂π < ∞
      have hb : ∀ x : ℝ, ‖Real.log |x|‖ₑ ≤
          ENNReal.ofReal (Real.log |x|) + ENNReal.ofReal (-Real.log |x|) := fun x => by
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (Real.log |x|) with h | h
        · rw [abs_of_nonneg h]; exact le_self_add
        · rw [abs_of_nonpos h]; exact le_add_self
      refine lt_of_le_of_lt (lintegral_mono hb) ?_
      rw [lintegral_add_left hlm.ennreal_ofReal]
      exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, lt_top_iff_ne_top.2 hneg⟩
    have hae : ∀ᵐ x ∂π, Real.log |x| ≤ |x| - 1 := by
      have : ∀ᵐ x ∂π, x ≠ 0 := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with x hx
      exact Real.log_le_sub_one_of_pos (abs_pos.2 hx)
    have hint : ∫ x, Real.log |x| ∂π < 0 := by
      have hsub : Integrable (fun x : ℝ => |x| - 1) π := hi.sub (integrable_const 1)
      have := integral_mono_ae hfi hsub hae
      rw [integral_sub hi (integrable_const 1), integral_const, probReal_univ, one_smul] at this
      linarith
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi, sub_neg] at hint
    exact (ENNReal.toReal_lt_toReal hpos hneg).1 hint

end MeynTweedie.LimitTheorems
