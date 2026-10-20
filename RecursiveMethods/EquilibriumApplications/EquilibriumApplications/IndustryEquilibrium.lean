/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.IndustryModel

/-!
# Industry equilibrium and surplus maximisation (SLP §16.4, Exercise 16.4(b)–(c))

SLP §16.4, pp. 489–490. `(Ω, μ)` is a probability space with filtration `ℱ` (the shock
histories `z^t`), `z_t` the demand shock (`IndustryShocks`), `r > 0` the interest rate.

* `industryPV μ r g = Σ_t (1 + r)⁻ᵗ ∫ g_t dμ`, the expected discounted value
  `E{Σ_t (1 + r)⁻ᵗ g_t}`; on uniformly bounded measurable processes (`IndustryBdd`) it is a positive
  linear functional (`industryPV_add`, `industryPV_sub`, `industryPV_const_mul`,
  `industryPV_mono`) and continuous under bounded pointwise convergence (`industryPV_tendsto`).
* `industrySurplus` (`E Σ (1 + r)⁻ᵗ [U(q_t, z_t) − I_t]`) and `industryProfit`
  (`E Σ (1 + r)⁻ᵗ [p_t q_t − I_t]`).
* `IndustryEquilibrium` (p. 489): (I1) `(q, I) ∈ Y`; prices `p_t ∈ L¹₊(ℱ_t)`; (I2)
  `p_t = D(q_t, z_t)`; (I3) `(q, I)` maximises expected discounted profit over `Y`.
* `IndustrySurplusMax` (p. 489): (I1) and (I4), `(q, I)` maximises expected discounted surplus
  over `Y`.
* **Exercise 16.4(b)** (`ex_16_4b`): every industry equilibrium allocation is surplus maximising
  (the concavity inequality of the hint, `surplusFn_le`).
* **Exercise 16.4(c)** (`ex_16_4c`): a surplus-maximising `(q, I)` with `p_t = D(q_t, z_t)` is an
  industry equilibrium (the hint's first-order condition at `θ = 0`: the difference quotients
  `[f(θ) − f(0)]/θ` dominate `E Σ (1 + r)⁻ᵗ [D(q^θ_t, z_t)(q′_t − q_t) − (I′_t − I_t)]`, which
  converges to the profit difference by dominated convergence).

**Comments.** All series and integrals converge absolutely (bounded plans, `D ≤ D̄ = D(0, z̄)`,
`r > 0`); the book takes this for granted. The convexity of `Y` used in (c)
(`industryTech_combo`) is proved in `IndustryModel`. `k₀ > 0` is assumed (see `IndustryModel`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The **expected discounted value** `E{Σ_t (1 + r)⁻ᵗ g_t} = Σ_t (1 + r)⁻ᵗ ∫ g_t dμ`. -/
noncomputable def industryPV (μ : Measure Ω) (r : ℝ) (g : ℕ → Ω → ℝ) : ℝ :=
  ∑' t, ((1 + r)⁻¹) ^ t * ∫ ω, g t ω ∂μ

/-- A uniformly bounded, measurable process. -/
def IndustryBdd (μ : Measure Ω) (g : ℕ → Ω → ℝ) : Prop :=
  (∀ t, AEStronglyMeasurable (g t) μ) ∧ ∃ B, ∀ t ω, |g t ω| ≤ B

/-- The **demand shock process**: `z_t` is `ℱ_t`-measurable with values in `Z = [z̲, z̄]`. -/
structure IndustryShocks (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ) (zlo zhi : ℝ) : Prop where
  adapted : ∀ t, StronglyMeasurable[ℱ t] (z t)
  mem : ∀ t ω, z t ω ∈ Icc zlo zhi

/-- The discount factor `(1 + r)⁻¹ ∈ [0, 1)`. -/
theorem industry_disc {r : ℝ} (hr : 0 < r) : 0 ≤ (1 + r)⁻¹ ∧ (1 + r)⁻¹ < 1 :=
  ⟨inv_nonneg.2 (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

variable {μ : Measure Ω}

/-- Bounded measurable processes are integrable in each period. -/
theorem IndustryBdd.integrable [IsFiniteMeasure μ] {g : ℕ → Ω → ℝ} (h : IndustryBdd μ g)
    (t : ℕ) : Integrable (g t) μ := by
  obtain ⟨hm, B, hB⟩ := h
  exact Integrable.of_bound (hm t) B (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hB t ω)

/-- Uniform bound on the period expectations. -/
theorem IndustryBdd.integral_le [IsProbabilityMeasure μ] {g : ℕ → Ω → ℝ} (h : IndustryBdd μ g) :
    ∃ B, ∀ t, ‖∫ ω, g t ω ∂μ‖ ≤ B := by
  obtain ⟨-, B, hB⟩ := h
  refine ⟨B, fun t => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g t) (C := B)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB t ω)
  rwa [probReal_univ, mul_one] at this

/-- The discounted series converges for a bounded measurable process. -/
theorem IndustryBdd.summable [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {g : ℕ → Ω → ℝ}
    (h : IndustryBdd μ g) : Summable fun t => ((1 + r)⁻¹) ^ t * ∫ ω, g t ω ∂μ := by
  obtain ⟨B, hB⟩ := h.integral_le
  obtain ⟨h0, h1⟩ := industry_disc hr
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right B)
    fun t => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (hB t) (pow_nonneg h0 t)

/-- Sums of bounded measurable processes. -/
theorem IndustryBdd.add {g g' : ℕ → Ω → ℝ} (h : IndustryBdd μ g) (h' : IndustryBdd μ g') :
    IndustryBdd μ fun t ω => g t ω + g' t ω := by
  obtain ⟨hm, B, hB⟩ := h
  obtain ⟨hm', B', hB'⟩ := h'
  exact ⟨fun t => (hm t).add (hm' t), B + B', fun t ω =>
    (abs_add_le _ _).trans (add_le_add (hB t ω) (hB' t ω))⟩

/-- Differences of bounded measurable processes. -/
theorem IndustryBdd.sub {g g' : ℕ → Ω → ℝ} (h : IndustryBdd μ g) (h' : IndustryBdd μ g') :
    IndustryBdd μ fun t ω => g t ω - g' t ω := by
  obtain ⟨hm, B, hB⟩ := h
  obtain ⟨hm', B', hB'⟩ := h'
  exact ⟨fun t => (hm t).sub (hm' t), B + B', fun t ω =>
    (abs_sub _ _).trans (add_le_add (hB t ω) (hB' t ω))⟩

/-- Scalar multiples of bounded measurable processes. -/
theorem IndustryBdd.const_mul {g : ℕ → Ω → ℝ} (h : IndustryBdd μ g) (a : ℝ) :
    IndustryBdd μ fun t ω => a * g t ω := by
  obtain ⟨hm, B, hB⟩ := h
  exact ⟨fun t => (hm t).const_mul a, |a| * B, fun t ω => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg a)⟩

/-- Products of bounded measurable processes. -/
theorem IndustryBdd.mul {g g' : ℕ → Ω → ℝ} (h : IndustryBdd μ g) (h' : IndustryBdd μ g') :
    IndustryBdd μ fun t ω => g t ω * g' t ω := by
  obtain ⟨hm, B, hB⟩ := h
  obtain ⟨hm', B', hB'⟩ := h'
  exact ⟨fun t => (hm t).mul (hm' t), B * B', fun t ω => by
    rw [abs_mul]
    exact mul_le_mul (hB t ω) (hB' t ω) (abs_nonneg _) ((abs_nonneg _).trans (hB t ω))⟩

/-- `industryPV` is additive. -/
theorem industryPV_add [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {g g' : ℕ → Ω → ℝ}
    (h : IndustryBdd μ g) (h' : IndustryBdd μ g') :
    industryPV μ r (fun t ω => g t ω + g' t ω) = industryPV μ r g + industryPV μ r g' := by
  unfold industryPV
  rw [← (h.summable hr).tsum_add (h'.summable hr)]
  congr 1
  funext t
  rw [integral_add (h.integrable t) (h'.integrable t), mul_add]

/-- `industryPV` of a difference. -/
theorem industryPV_sub [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {g g' : ℕ → Ω → ℝ}
    (h : IndustryBdd μ g) (h' : IndustryBdd μ g') :
    industryPV μ r (fun t ω => g t ω - g' t ω) = industryPV μ r g - industryPV μ r g' := by
  unfold industryPV
  rw [← (h.summable hr).tsum_sub (h'.summable hr)]
  congr 1
  funext t
  rw [integral_sub (h.integrable t) (h'.integrable t), mul_sub]

/-- `industryPV` is homogeneous. -/
theorem industryPV_const_mul (r a : ℝ) (g : ℕ → Ω → ℝ) :
    industryPV μ r (fun t ω => a * g t ω) = a * industryPV μ r g := by
  unfold industryPV
  rw [← tsum_mul_left]
  congr 1
  funext t
  rw [integral_const_mul]
  ring

/-- `industryPV` is monotone. -/
theorem industryPV_mono [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {g g' : ℕ → Ω → ℝ}
    (h : IndustryBdd μ g) (h' : IndustryBdd μ g') (hle : ∀ t ω, g t ω ≤ g' t ω) :
    industryPV μ r g ≤ industryPV μ r g' := by
  refine (h.summable hr).tsum_le_tsum (fun t => ?_) (h'.summable hr)
  exact mul_le_mul_of_nonneg_left (integral_mono (h.integrable t) (h'.integrable t)
    fun ω => hle t ω) (pow_nonneg (industry_disc hr).1 t)

/-- **Dominated convergence** for `industryPV`: uniformly bounded measurable processes converging
pointwise. -/
theorem industryPV_tendsto [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℕ → Ω → ℝ} {f : ℕ → Ω → ℝ} {B : ℝ} (hm : ∀ n t, AEStronglyMeasurable (F n t) μ)
    (hB : ∀ n t ω, |F n t ω| ≤ B) (hlim : ∀ t ω, Tendsto (fun n => F n t ω) atTop (𝓝 (f t ω))) :
    Tendsto (fun n => industryPV μ r (F n)) atTop (𝓝 (industryPV μ r f)) := by
  obtain ⟨h0, h1⟩ := industry_disc hr
  refine tendsto_tsum_of_dominated_convergence (bound := fun t => ((1 + r)⁻¹) ^ t * B)
    ((summable_geometric_of_lt_one h0 h1).mul_right B) (fun t => ?_)
    (Eventually.of_forall fun n t => ?_)
  · refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => hm n t) (integrable_const B) (fun n => ae_of_all _ fun ω => ?_)
      (ae_of_all _ fun ω => hlim t ω))
    rw [Real.norm_eq_abs]
    exact hB n t ω
  · rw [norm_mul, norm_pow, Real.norm_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 t)
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := F n t) (C := B)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB n t ω)
    rwa [probReal_univ, mul_one] at this

/-- The expected discounted **surplus** `E Σ (1 + r)⁻ᵗ [U(q_t, z_t) − I_t]` ((I4)). -/
noncomputable def industrySurplus (μ : Measure Ω) (r : ℝ) (D : ℝ → ℝ → ℝ) (z q I : ℕ → Ω → ℝ) :
    ℝ :=
  industryPV μ r fun t ω => surplusFn D (q t ω) (z t ω) - I t ω

/-- The expected discounted **profit** `E Σ (1 + r)⁻ᵗ [p_t q_t − I_t]` ((I3)). -/
noncomputable def industryProfit (μ : Measure Ω) (r : ℝ) (p q I : ℕ → Ω → ℝ) : ℝ :=
  industryPV μ r fun t ω => p t ω * q t ω - I t ω

/-- An **industry equilibrium** `(q, I, p)` (p. 489): (I1) `(q, I) ∈ Y`; `p_t ∈ L¹₊(ℱ_t)`;
(I2) `p_t = D(q_t, z_t)`; (I3) `(q, I)` maximises expected discounted profit on `Y`. -/
def IndustryEquilibrium (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℝ → ℝ → ℝ)
    (z : ℕ → Ω → ℝ) (c : ℝ → ℝ) (δ k0 r : ℝ) (q I p : ℕ → Ω → ℝ) : Prop :=
  (q, I) ∈ IndustryTech ℱ c δ k0 ∧
    (∀ t, StronglyMeasurable[ℱ t] (p t) ∧ Integrable (p t) μ ∧ ∀ ω, 0 ≤ p t ω) ∧
    (∀ t ω, p t ω = D (q t ω) (z t ω)) ∧
    ∀ q' I', (q', I') ∈ IndustryTech ℱ c δ k0 →
      industryProfit μ r p q' I' ≤ industryProfit μ r p q I

/-- A **surplus-maximising allocation** (p. 489): (I1) and (I4). -/
def IndustrySurplusMax (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℝ → ℝ → ℝ)
    (z : ℕ → Ω → ℝ) (c : ℝ → ℝ) (δ k0 r : ℝ) (q I : ℕ → Ω → ℝ) : Prop :=
  (q, I) ∈ IndustryTech ℱ c δ k0 ∧
    ∀ q' I', (q', I') ∈ IndustryTech ℱ c δ k0 →
      industrySurplus μ r D z q' I' ≤ industrySurplus μ r D z q I

variable {ℱ : Filtration ℕ mΩ} {D : ℝ → ℝ → ℝ} {zlo zhi : ℝ} {z : ℕ → Ω → ℝ}

/-- A common bound for two plans in `L`. -/
theorem IndustryAdapted.bound₂ {q I q' I' : ℕ → Ω → ℝ}
    (h : IndustryAdapted ℱ q I) (h' : IndustryAdapted ℱ q' I') :
    ∃ B, 0 ≤ B ∧ ∀ t ω, |q t ω| ≤ B ∧ |I t ω| ≤ B ∧ |q' t ω| ≤ B ∧ |I' t ω| ≤ B := by
  obtain ⟨-, B, hB⟩ := h
  obtain ⟨-, B', hB'⟩ := h'
  refine ⟨max (max B B') 0, le_max_right _ _, fun t ω => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hB t ω).1.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hB t ω).2.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hB' t ω).1.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hB' t ω).2.trans ((le_max_right _ _).trans (le_max_left _ _))

/-- `q` and `I` of a plan in `L`, as bounded measurable processes. -/
theorem IndustryAdapted.bdd {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) :
    IndustryBdd μ q ∧ IndustryBdd μ I := by
  obtain ⟨hm, B, hB⟩ := h
  exact ⟨⟨fun t => ((hm t).1.mono (ℱ.le t)).aestronglyMeasurable, B, fun t ω => (hB t ω).1⟩,
    ⟨fun t => ((hm t).2.mono (ℱ.le t)).aestronglyMeasurable, B, fun t ω => (hB t ω).2⟩⟩

/-- The market-clearing price `D(q_t, z_t)` is `ℱ_t`-measurable. -/
theorem industry_D_meas (hD : IndustryDemand D zlo zhi) (hz : IndustryShocks ℱ z zlo zhi)
    {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) (t : ℕ) :
    StronglyMeasurable[ℱ t] fun ω => D (q t ω) (z t ω) :=
  hD.cont.comp_stronglyMeasurable ((h.1 t).1.prodMk (hz.adapted t))

/-- The market-clearing price process is bounded and measurable, `0 ≤ D(q_t, z_t) ≤ D̄`. -/
theorem industry_D_bdd (hD : IndustryDemand D zlo zhi) (hz : IndustryShocks ℱ z zlo zhi)
    {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) (hq : ∀ t ω, 0 ≤ q t ω) :
    IndustryBdd μ (fun t ω => D (q t ω) (z t ω)) ∧
      ∀ t ω, 0 ≤ D (q t ω) (z t ω) ∧ D (q t ω) (z t ω) ≤ D 0 zhi := by
  have hb : ∀ t ω, 0 ≤ D (q t ω) (z t ω) ∧ D (q t ω) (z t ω) ≤ D 0 zhi := fun t ω =>
    ⟨hD.nonneg _ _ (hq t ω) (hz.mem t ω), D_le_bar hD (hq t ω) (hz.mem t ω)⟩
  refine ⟨⟨fun t => ((industry_D_meas hD hz h t).mono (ℱ.le t)).aestronglyMeasurable, D 0 zhi,
    fun t ω => ?_⟩, hb⟩
  rw [abs_of_nonneg (hb t ω).1]
  exact (hb t ω).2

/-- The surplus integrand `U(q_t, z_t) − I_t` of a nonnegative plan in `L` is bounded and
measurable. -/
theorem industry_surplus_bdd (hD : IndustryDemand D zlo zhi) (hz : IndustryShocks ℱ z zlo zhi)
    {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) (hq : ∀ t ω, 0 ≤ q t ω) :
    IndustryBdd μ fun t ω => surplusFn D (q t ω) (z t ω) - I t ω := by
  have hU : IndustryBdd μ fun t ω => surplusFn D (q t ω) (z t ω) := by
    obtain ⟨hm, B, hB⟩ := h
    refine ⟨fun t => ((surplusFn_continuous hD).comp_stronglyMeasurable
      (((hm t).1.mono (ℱ.le t)).prodMk ((hz.adapted t).mono (ℱ.le t)))).aestronglyMeasurable,
      D 0 zhi * B, fun t ω => ?_⟩
    exact surplusFn_abs_le hD (hq t ω) ((le_abs_self _).trans (hB t ω).1) (hz.mem t ω)
  exact hU.sub h.bdd.2

/-- The profit integrand `p_t q_t − I_t` for a bounded measurable price is bounded and
measurable. -/
theorem industry_profit_bdd {p q I : ℕ → Ω → ℝ} (hp : IndustryBdd μ p) (h : IndustryAdapted ℱ q I) :
    IndustryBdd μ fun t ω => p t ω * q t ω - I t ω :=
  (hp.mul h.bdd.1).sub h.bdd.2

/-- **Exercise 16.4(b)**: if `(q, I, p)` is an industry equilibrium, then `(q, I)` is surplus
maximising. -/
theorem ex_16_4b [IsProbabilityMeasure μ] {c : ℝ → ℝ} {δ k0 r : ℝ} (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) {q I p : ℕ → Ω → ℝ}
    (hE : IndustryEquilibrium μ ℱ D z c δ k0 r q I p) :
    IndustrySurplusMax μ ℱ D z c δ k0 r q I := by
  obtain ⟨hY, -, hI2, hI3⟩ := hE
  refine ⟨hY, fun q' I' hY' => ?_⟩
  have hA : IndustryAdapted ℱ q I := hY.1
  have hA' : IndustryAdapted ℱ q' I' := hY'.1
  have hq := fun t ω => (hY.2.1 t ω).1
  have hq' := fun t ω => (hY'.2.1 t ω).1
  have hpB : IndustryBdd μ p := by
    have := (industry_D_bdd (μ := μ) hD hz hA hq).1
    have he : p = fun t ω => D (q t ω) (z t ω) := funext fun t => funext fun ω => hI2 t ω
    rwa [he]
  have hS := industry_surplus_bdd (μ := μ) hD hz hA hq
  have hS' := industry_surplus_bdd (μ := μ) hD hz hA' hq'
  have hP := industry_profit_bdd hpB hA
  have hP' := industry_profit_bdd hpB hA'
  have hpt := hI3 q' I' hY'
  have hmono := industryPV_mono hr hS' (hS.add (hP'.sub hP)) fun t ω => by
    have := surplusFn_le hD (hq t ω) (hq' t ω) (hz.mem t ω)
    rw [← hI2 t ω] at this
    linarith
  rw [industryPV_add hr hS (hP'.sub hP), industryPV_sub hr hP' hP] at hmono
  unfold industrySurplus
  unfold industryProfit at hpt
  linarith

/-- **Exercise 16.4(c)**: if `(q, I)` is surplus maximising and `p_t = D(q_t, z_t)` ((I2)), then
`(q, I, p)` is an industry equilibrium. -/
theorem ex_16_4c [IsProbabilityMeasure μ] {c : ℝ → ℝ} {δ k0 r : ℝ}
    (hD : IndustryDemand D zlo zhi) (hc : IndustryCost c δ) (hz : IndustryShocks ℱ z zlo zhi)
    (hr : 0 < r) (hk0 : 0 < k0) {q I : ℕ → Ω → ℝ}
    (hS : IndustrySurplusMax μ ℱ D z c δ k0 r q I) :
    IndustryEquilibrium μ ℱ D z c δ k0 r q I fun t ω => D (q t ω) (z t ω) := by
  obtain ⟨hY, hmax⟩ := hS
  have hA : IndustryAdapted ℱ q I := hY.1
  have hq := fun t ω => (hY.2.1 t ω).1
  obtain ⟨hpB, hpb⟩ := industry_D_bdd (μ := μ) hD hz hA hq
  refine ⟨hY, fun t => ⟨industry_D_meas hD hz hA t, hpB.integrable t, fun ω => (hpb t ω).1⟩,
    fun t ω => rfl, fun q' I' hY' => ?_⟩
  set p : ℕ → Ω → ℝ := fun t ω => D (q t ω) (z t ω)
  have hA' : IndustryAdapted ℱ q' I' := hY'.1
  have hq' := fun t ω => (hY'.2.1 t ω).1
  obtain ⟨B, hB0, hB⟩ := hA.bound₂ hA'
  set θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hθ0 : ∀ n, 0 < θ n := fun n => by positivity
  have hθ1 : ∀ n, θ n ≤ 1 := fun n => by
    simp only [θ]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set qn : ℕ → ℕ → Ω → ℝ := fun n t ω => (1 - θ n) * q t ω + θ n * q' t ω
  set In : ℕ → ℕ → Ω → ℝ := fun n t ω => (1 - θ n) * I t ω + θ n * I' t ω
  have hYn : ∀ n, (qn n, In n) ∈ IndustryTech ℱ c δ k0 := fun n =>
    industryTech_combo hc hk0 hY hY' (by linarith [hθ1 n]) (hθ0 n).le (by ring)
  have hqn : ∀ n t ω, 0 ≤ qn n t ω := fun n t ω => ((hYn n).2.1 t ω).1
  set G : ℕ → ℕ → Ω → ℝ := fun n t ω =>
    D (qn n t ω) (z t ω) * (q' t ω - q t ω) - (I' t ω - I t ω)
  set G0 : ℕ → Ω → ℝ := fun t ω => p t ω * (q' t ω - q t ω) - (I' t ω - I t ω)
  have hdiff : IndustryBdd μ fun t ω => q' t ω - q t ω := hA'.bdd.1.sub hA.bdd.1
  have hdiffI : IndustryBdd μ fun t ω => I' t ω - I t ω := hA'.bdd.2.sub hA.bdd.2
  have hGb : ∀ n, IndustryBdd μ (G n) := fun n =>
    ((industry_D_bdd (μ := μ) hD hz (hYn n).1 (hqn n)).1.mul hdiff).sub hdiffI
  have hS0 := industry_surplus_bdd (μ := μ) hD hz hA hq
  -- the first-order inequality for each `θ_n`
  have hGle : ∀ n, industryPV μ r (G n) ≤ 0 := by
    intro n
    have hSn := industry_surplus_bdd (μ := μ) hD hz (hYn n).1 (hqn n)
    have hle := industryPV_mono hr ((hGb n).const_mul (θ n)) (hSn.sub hS0) fun t ω => by
      have h := surplusFn_le hD (hqn n t ω) (hq t ω) (hz.mem t ω)
      simp only [G, qn, In] at h ⊢
      have e : q t ω - ((1 - θ n) * q t ω + θ n * q' t ω) = -(θ n * (q' t ω - q t ω)) := by
        ring
      rw [e] at h
      nlinarith
    rw [industryPV_const_mul, industryPV_sub hr hSn hS0] at hle
    have hW := hmax (qn n) (In n) (hYn n)
    unfold industrySurplus at hW
    by_contra hpos
    push Not at hpos
    have := mul_pos (hθ0 n) hpos
    linarith
  -- passage to the limit `θ_n → 0`
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => industryPV μ r (G n)) atTop (𝓝 (industryPV μ r G0)) := by
    obtain ⟨-, Bd, hBd⟩ := hdiff
    obtain ⟨-, Bi, hBi⟩ := hdiffI
    refine industryPV_tendsto hr (B := D 0 zhi * Bd + Bi) (fun n t => (hGb n).1 t)
      (fun n t ω => ?_) (fun t ω => ?_)
    · obtain ⟨h0, h1⟩ := (industry_D_bdd (μ := μ) hD hz (hYn n).1 (hqn n)).2 t ω
      calc |G n t ω| ≤ |D (qn n t ω) (z t ω) * (q' t ω - q t ω)| + |I' t ω - I t ω| :=
            abs_sub _ _
        _ ≤ D 0 zhi * Bd + Bi := by
          rw [abs_mul, abs_of_nonneg h0]
          exact add_le_add (mul_le_mul h1 (hBd t ω) (abs_nonneg _) (h0.trans h1)) (hBi t ω)
    · have hq_lim : Tendsto (fun n => qn n t ω) atTop (𝓝 (q t ω)) := by
        have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hθlim).mul
          (tendsto_const_nhds (x := q t ω)) |>.add (hθlim.mul (tendsto_const_nhds (x := q' t ω)))
        simpa using this
      have hDlim : Tendsto (fun n => D (qn n t ω) (z t ω)) atTop (𝓝 (D (q t ω) (z t ω))) :=
        ((hD.cont.tendsto (q t ω, z t ω)).comp (hq_lim.prodMk_nhds tendsto_const_nhds))
      exact (hDlim.mul tendsto_const_nhds).sub tendsto_const_nhds
  have hG0 : industryPV μ r G0 ≤ 0 := le_of_tendsto' hlim hGle
  have hP := industry_profit_bdd hpB hA
  have hP' := industry_profit_bdd hpB hA'
  have hG0eq : industryPV μ r G0 = industryProfit μ r p q' I' - industryProfit μ r p q I := by
    unfold industryProfit
    rw [← industryPV_sub hr hP' hP]
    congr 1
    funext t ω
    simp only [G0]
    ring
  linarith

end StokeyLucasPrescott.EquilibriumApplications
