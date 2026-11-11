/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.JDEndogenous
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Endogenous job destruction: steady state, comparative statics, dynamics (Miao §18.2)

Miao, *Economic Dynamics in Discrete Time*, §18.2, pp. 604–607. With
`Φ(c) = ∫_c^∞ (z − c) dG` (`jd_Phi`), the steady-state job creation (JC) and job destruction (JD)
conditions are

  (18.44) `κ / q(θ) = β (1 − η) A Φ(z*)`  (`jd_JC`),
  (18.45) `η θ κ = (1 − η)(A z* − b) + β (1 − ρˣ)(1 − η) A Φ(z*)`  (`jd_JD`).

Proved:

* JC slopes down (`eq_18_44`), JD slopes up (`eq_18_45`) in the `(θ, z*)` plane;
* **existence and uniqueness** of the steady state `(θ*, z̄*)` with `θ* > 0`
  (`jd_steady_state_unique`, `jd_steady_state_exists`, `jd_steady_state_existsUnique`) when `q`
  is positive, continuous and strictly decreasing on `(0, ∞)` with `q(θ) → ∞` as `θ ↓ 0`, and
  `G(b/A) < 1` (some matches are worth more than unemployment benefits); a concrete instance
  (Cobb–Douglas `q`, degenerate `G`) is `jd_example_steady_state`;
* the Beveridge curve with `ρ = ρˣ + (1 − ρˣ) G(z̄*)`: steady-state unemployment
  `u = ρ / (ρ + q(θ) θ)` (`jd_jc_eq_jd_of_steady`), the curve slopes down
  (`jd_beveridge_downward`) and shifts down when `ρ` falls (`jd_beveridge_shift`);
* comparative statics in `A`: with fixed `κ`, tightness rises (`jd_compstat_A_theta`; the book
  says the effect on `z*` is ambiguous, not formalised); with posting cost `κ A`, `A` cancels from
  JC (`jd_JC_kappaA_iff`), the reservation productivity falls and tightness rises
  (`jd_compstat_kappaA`), the job destruction rate does not rise (`jd_compstat_kappaA_jd`), and
  unemployment and the steady-state job creation rate fall (`jd_compstat_kappaA_u`);
* transitional dynamics: the linearised JC/JD system reduces to `dz_t = ψ dz_{t+1}` with
  `ψ = β (1 − G(z̄*)) ((1 − ρˣ) − η q(θ*) θ* / ξ(θ*))` (`jd_linear_psi`); when `|ψ| < 1` (in
  particular under the analogue of the §18.1 condition `1 − ρˣ − η q θ / ξ ≥ 0`,
  `jd_psi_abs_lt_one`) the only bounded solution has `dz ≡ dθ ≡ 0` and unemployment converges
  (`jd_saddle`), the saddle-point property; after a permanent rise in `A` unemployment falls
  monotonically and the job creation rate falls to the constant job destruction rate
  (`jd_transition_unemployment`). The slopes used are `Φ′ = −(1 − G)` (`jd_Phi_hasDerivAt`) and
  `(κ/q)′ = −κ q′/q²` (`jd_kappa_div_q_hasDerivAt`).

**Departure.** The book's claim that `z*` and `θ` are "constant over time" reads off its printed
(18.41)–(18.42), whose integrals start at `z*_t`; with the correct timing (`eq_18_41`,
`eq_18_42`) constancy is the saddle-path selection proved in `jd_saddle` (linearised).
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- Miao, (18.44), p. 604: the steady-state job creation condition
`κ / q(θ) = β (1 − η) A Φ(z*)`. -/
def jd_JC (μ : Measure ℝ) (q : ℝ → ℝ) (β η κ A θ c : ℝ) : Prop :=
  κ / q θ = β * (1 - η) * A * jd_Phi μ c

/-- Miao, (18.45), p. 604: the steady-state job destruction condition
`η θ κ = (1 − η)(A z* − b) + β (1 − ρˣ)(1 − η) A Φ(z*)`. -/
def jd_JD (μ : Measure ℝ) (β ρx η κ A b θ c : ℝ) : Prop :=
  η * θ * κ = (1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c

/-- The JD curve as a function of `z*`: `θ_JD(c) = [(1 − η)(A c − b) + β(1 − ρˣ)(1 − η) A Φ(c)]
/ (η κ)`. -/
noncomputable def jd_thetaJD (μ : Measure ℝ) (β ρx η κ A b c : ℝ) : ℝ :=
  ((1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c) / (η * κ)

/-- `c ↦ c + β(1 − ρˣ) Φ(c)` is strictly increasing when `0 ≤ β(1 − ρˣ) < 1`. -/
theorem jd_h_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    StrictMono fun c => c + k * jd_Phi μ c := by
  intro c c' h
  have h1 := jd_Phi_sub_le hint h.le
  simp only
  nlinarith

/-- Miao, (18.45), p. 604: `JD(θ, c) ↔ θ = θ_JD(c)`. -/
theorem jd_JD_iff {μ : Measure ℝ} {β ρx η κ A b θ c : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    jd_JD μ β ρx η κ A b θ c ↔ θ = jd_thetaJD μ β ρx η κ A b c := by
  unfold jd_JD jd_thetaJD
  rw [eq_div_iff (mul_pos hη hκ).ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 604: `θ_JD` is strictly increasing in `z*` (the JD curve slopes up). -/
theorem jd_thetaJD_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {β ρx η κ A b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A) :
    StrictMono (jd_thetaJD μ β ρx η κ A b) := by
  intro c c' h
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hh := jd_h_strictMono hint hk0 hk1 h
  simp only at hh
  unfold jd_thetaJD
  apply div_lt_div_of_pos_right _ (mul_pos hη0 hκ)
  have hc : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have : (1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c
      = (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) - (1 - η) * b := by ring
  have h' : (1 - η) * (A * c' - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c'
      = (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ c') - (1 - η) * b := by ring
  rw [this, h']
  nlinarith

/-- `θ_JD` is continuous. -/
theorem jd_thetaJD_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (β ρx η κ A b : ℝ) :
    Continuous (jd_thetaJD μ β ρx η κ A b) := by
  unfold jd_thetaJD
  have := jd_Phi_continuous hint
  fun_prop

/-- **The job creation curve slopes down** (Miao, (18.44), p. 604). If `(θ₁, c₁)` and
`(θ₂, c₂)` satisfy (18.44) with `θᵢ > 0` and `c₁ < c₂`, then `θ₂ < θ₁`. -/
theorem eq_18_44 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : Integrable (fun z => z) μ)
    {q : ℝ → ℝ} {β η κ A θ₁ θ₂ c₁ c₂ : ℝ} (hβ : 0 < β) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (hqpos : ∀ θ, 0 < θ → 0 < q θ) (hqanti : StrictAntiOn q (Set.Ioi 0))
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (h₁ : jd_JC μ q β η κ A θ₁ c₁) (h₂ : jd_JC μ q β η κ A θ₂ c₂)
    (hc : c₁ < c₂) : θ₂ < θ₁ := by
  unfold jd_JC at h₁ h₂
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ (by linarith)) hA
  have hq₁ := hqpos θ₁ hθ₁
  have hq₂ := hqpos θ₂ hθ₂
  have hPhi₁ : 0 < jd_Phi μ c₁ := by
    have : 0 < κ / q θ₁ := div_pos hκ hq₁
    rw [h₁] at this
    exact pos_of_mul_pos_right this hK.le
  have hlt : jd_Phi μ c₂ < jd_Phi μ c₁ := jd_Phi_strictAnti_of_pos hint hc hPhi₁
  have : κ / q θ₂ < κ / q θ₁ := by rw [h₁, h₂]; exact mul_lt_mul_of_pos_left hlt hK
  rw [div_lt_div_iff_of_pos_left hκ hq₂ hq₁] at this
  by_contra hne
  rcases (not_lt.mp hne).lt_or_eq with h | h
  · have := hqanti (Set.mem_Ioi.mpr hθ₁) (Set.mem_Ioi.mpr hθ₂) h; linarith
  · rw [h] at this; linarith

/-- **The job destruction curve slopes up** (Miao, (18.45), p. 604). If `(θ₁, c₁)` and
`(θ₂, c₂)` satisfy (18.45) and `c₁ < c₂`, then `θ₁ < θ₂`. -/
theorem eq_18_45 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : Integrable (fun z => z) μ)
    {β ρx η κ A b θ₁ θ₂ c₁ c₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (h₁ : jd_JD μ β ρx η κ A b θ₁ c₁) (h₂ : jd_JD μ β ρx η κ A b θ₂ c₂) (hc : c₁ < c₂) :
    θ₁ < θ₂ := by
  rw [jd_JD_iff hη0 hκ] at h₁ h₂
  rw [h₁, h₂]
  exact jd_thetaJD_strictMono hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hc

/-- **Uniqueness of the steady state** (Miao, p. 604, Figure 18.5): the JC and JD curves cross at
most once in `θ > 0`. -/
theorem jd_steady_state_unique {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b θ₁ θ₂ c₁ c₂ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hC₁ : jd_JC μ q β η κ A θ₁ c₁) (hD₁ : jd_JD μ β ρx η κ A b θ₁ c₁)
    (hC₂ : jd_JC μ q β η κ A θ₂ c₂) (hD₂ : jd_JD μ β ρx η κ A b θ₂ c₂) :
    θ₁ = θ₂ ∧ c₁ = c₂ := by
  have hc : c₁ = c₂ := by
    rcases lt_trichotomy c₁ c₂ with h | h | h
    · have := eq_18_44 hint hβ0 hη1 hκ hA hqpos hqanti hθ₁ hθ₂ hC₁ hC₂ h
      have := eq_18_45 hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hD₁ hD₂ h
      linarith
    · exact h
    · have := eq_18_44 hint hβ0 hη1 hκ hA hqpos hqanti hθ₂ hθ₁ hC₂ hC₁ h
      have := eq_18_45 hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hD₂ hD₁ h
      linarith
  refine ⟨?_, hc⟩
  rw [jd_JD_iff hη0 hκ] at hD₁ hD₂
  rw [hD₁, hD₂, hc]

/-- **Existence of the steady state** (Miao, p. 604, Figure 18.5). If `q` is positive, continuous
and strictly decreasing on `(0, ∞)` with `q(θ) → ∞` as `θ ↓ 0`, and `G(b/A) < 1`, then the JC
and JD curves cross at some `(θ*, z̄*)` with `θ* > 0`. -/
theorem jd_steady_state_exists {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hqcont : ContinuousOn q (Set.Ioi 0))
    (hq0 : Tendsto q (𝓝[>] 0) atTop) (hG : 0 < μ (Set.Ioi (b / A))) :
    ∃ θ c, 0 < θ ∧ jd_JC μ q β η κ A θ c ∧ jd_JD μ β ρx η κ A b θ c := by
  set T := jd_thetaJD μ β ρx η κ A b with hT
  have hTmono : StrictMono T := jd_thetaJD_strictMono hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA
  have hTcont : Continuous T := jd_thetaJD_continuous hint β ρx η κ A b
  have hPcont := jd_Phi_continuous hint (μ := μ)
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ0 (by linarith)) hA
  have hηκ : 0 < η * κ := mul_pos hη0 hκ
  set F : ℝ → ℝ := fun c => κ / q (T c) - β * (1 - η) * A * jd_Phi μ c with hF
  -- Step 1: at `c₁ = b / A` the JD curve is above zero
  set c₁ := b / A with hc₁
  have hP₁ : 0 < jd_Phi μ c₁ := (jd_Phi_pos_iff hint c₁).mpr hG
  have hT₁ : 0 < T c₁ := by
    rw [hT]; unfold jd_thetaJD
    have : A * c₁ - b = 0 := by rw [hc₁]; field_simp; ring
    rw [this]
    apply div_pos _ hηκ
    have : 0 < β * (1 - ρx) * (1 - η) * A :=
      mul_pos (mul_pos (mul_pos hβ0 (by linarith)) (by linarith)) hA
    nlinarith
  -- Step 2: a `c₂ ≥ c₁` with `F c₂ > 0`
  have hm : 0 < κ / q (T c₁) := div_pos hκ (hqpos _ hT₁)
  have hlow : ∀ c, c₁ ≤ c → κ / q (T c₁) ≤ κ / q (T c) := by
    intro c hc
    have hTc : T c₁ ≤ T c := hTmono.monotone hc
    have hTc0 : 0 < T c := lt_of_lt_of_le hT₁ hTc
    have hqle : q (T c) ≤ q (T c₁) := hqanti.antitoneOn (Set.mem_Ioi.mpr hT₁)
      (Set.mem_Ioi.mpr hTc0) hTc
    exact div_le_div_of_nonneg_left hκ.le (hqpos _ hTc0) hqle
  have hev : ∀ᶠ c in atTop, β * (1 - η) * A * jd_Phi μ c < κ / q (T c₁) := by
    have := ((jd_Phi_tendsto_atTop hint).const_mul (β * (1 - η) * A))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hm)
  obtain ⟨c₂, hc₂F, hc₂⟩ := (hev.and (eventually_ge_atTop c₁)).exists
  have hF₂ : 0 < F c₂ := by
    simp only [hF]; linarith [hlow c₂ hc₂]
  -- Step 3: the zero `c₀` of the JD curve
  set k := β * (1 - ρx) with hk
  have hk0 : 0 ≤ k := mul_nonneg hβ0.le (by linarith)
  have hk1 : k < 1 := by rw [hk]; nlinarith
  set cn := min 0 ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k))) with hcn
  have hAk : 0 < A * (1 - k) := mul_pos hA (by linarith)
  have hTn : T cn < 0 := by
    rw [hT]; unfold jd_thetaJD
    apply div_neg_of_neg_of_pos _ hηκ
    have hcn0 : cn ≤ 0 := min_le_left _ _
    have hcn1 : A * (1 - k) * cn ≤ b - k * A * jd_Phi μ 0 - 1 := by
      have := min_le_right 0 ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k)))
      rw [← hcn] at this
      calc A * (1 - k) * cn ≤ A * (1 - k) * ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k))) :=
            mul_le_mul_of_nonneg_left this hAk.le
        _ = b - k * A * jd_Phi μ 0 - 1 := mul_div_cancel₀ _ hAk.ne'
    have hP := jd_Phi_sub_le hint hcn0
    have : β * (1 - ρx) * (1 - η) * A * jd_Phi μ cn = (1 - η) * (k * A * jd_Phi μ cn) := by
      rw [hk]; ring
    rw [this]
    have hkA : 0 ≤ k * A := mul_nonneg hk0 hA.le
    have : k * A * jd_Phi μ cn ≤ k * A * (jd_Phi μ 0 - cn) :=
      mul_le_mul_of_nonneg_left (by linarith) hkA
    have h1η : 0 < 1 - η := by linarith
    nlinarith
  have hcn₁ : cn ≤ c₁ := by
    by_contra h
    have := hTmono.monotone (not_le.mp h).le
    linarith
  obtain ⟨c₀, ⟨hc₀l, hc₀r⟩, hT₀⟩ : ∃ c₀ ∈ Set.Icc cn c₁, T c₀ = 0 :=
    intermediate_value_Icc hcn₁ hTcont.continuousOn ⟨hTn.le, hT₁.le⟩
  have hc₀₁ : c₀ < c₁ := by
    rcases hc₀r.lt_or_eq with h | h
    · exact h
    · rw [h] at hT₀; linarith
  have hP₀ : 0 < jd_Phi μ c₀ := lt_of_lt_of_le hP₁ (jd_Phi_antitone hint hc₀₁.le)
  -- Step 4: just above `c₀`, `F < 0`
  have hTlim : Tendsto T (𝓝[>] c₀) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (hTcont.tendsto c₀).mono_left (nhdsWithin_le_nhds (s := Set.Ioi c₀))
      rwa [hT₀] at this
    · filter_upwards [self_mem_nhdsWithin] with c hc
      rw [Set.mem_Ioi, ← hT₀]
      exact hTmono hc
  have hFlim : Tendsto F (𝓝[>] c₀) (𝓝 (0 - β * (1 - η) * A * jd_Phi μ c₀)) := by
    refine Tendsto.sub ?_ ?_
    · exact tendsto_const_nhds.div_atTop (hq0.comp hTlim)
    · exact ((hPcont.tendsto c₀).mono_left nhdsWithin_le_nhds).const_mul _
  have hneg : 0 - β * (1 - η) * A * jd_Phi μ c₀ < 0 := by
    have := mul_pos hK hP₀; linarith
  have hev2 := hFlim.eventually (gt_mem_nhds hneg)
  have hc₀₂ : c₀ < c₂ := lt_of_lt_of_le hc₀₁ hc₂
  obtain ⟨cl, hclF, hcl⟩ := (hev2.and (Ioo_mem_nhdsGT hc₀₂)).exists
  -- Step 5: intermediate value theorem on `[cl, c₂]`
  have hpos : ∀ c ∈ Set.Icc cl c₂, 0 < T c := by
    intro c hc
    rw [← hT₀]
    exact hTmono (lt_of_lt_of_le hcl.1 hc.1)
  have hFcont : ContinuousOn F (Set.Icc cl c₂) := by
    simp only [hF]
    refine ContinuousOn.sub ?_ (continuous_const.mul hPcont).continuousOn
    refine continuousOn_const.div (hqcont.comp hTcont.continuousOn fun c hc => hpos c hc) ?_
    intro c hc
    exact (hqpos _ (hpos c hc)).ne'
  obtain ⟨cs, hcs, hFcs⟩ : ∃ cs ∈ Set.Icc cl c₂, F cs = 0 :=
    intermediate_value_Icc hcl.2.le hFcont ⟨hclF.le, hF₂.le⟩
  refine ⟨T cs, cs, hpos cs hcs, ?_, ?_⟩
  · unfold jd_JC
    simp only [hF] at hFcs
    linarith
  · rw [jd_JD_iff hη0 hκ]

/-- **Existence and uniqueness of the steady state** (Miao, p. 604, Figure 18.5): under the
hypotheses of `jd_steady_state_exists` there is exactly one `(θ*, z̄*)` with `θ* > 0` solving
(18.44)–(18.45). -/
theorem jd_steady_state_existsUnique {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hqcont : ContinuousOn q (Set.Ioi 0))
    (hq0 : Tendsto q (𝓝[>] 0) atTop) (hG : 0 < μ (Set.Ioi (b / A))) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ jd_JC μ q β η κ A p.1 p.2 ∧ jd_JD μ β ρx η κ A b p.1 p.2 := by
  obtain ⟨θ, c, h0, h1, h2⟩ :=
    jd_steady_state_exists hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti hqcont hq0 hG
  refine ⟨(θ, c), ⟨h0, h1, h2⟩, ?_⟩
  rintro ⟨θ', c'⟩ ⟨h0', h1', h2'⟩
  obtain ⟨e1, e2⟩ := jd_steady_state_unique hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti
    h0' h0 h1' h2' h1 h2
  exact Prod.ext e1 e2

/-- A concrete instance of `jd_steady_state_existsUnique` (non-vacuity): Cobb–Douglas
`q(θ) = θ^(−1/2)`, degenerate `G` at the mean `1`, `b < A`. -/
theorem jd_example_steady_state {β ρx η κ A b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (hb : b < A) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ jd_JC (Measure.dirac 1) (fun θ => θ ^ (-(1 / 2 : ℝ))) β η κ A p.1 p.2
      ∧ jd_JD (Measure.dirac 1) β ρx η κ A b p.1 p.2 := by
  refine jd_steady_state_existsUnique (integrable_dirac (by simp)) hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA
    (fun θ hθ => Real.rpow_pos_of_pos hθ _) ?_ ?_ (tendsto_rpow_neg_nhdsGT_zero (by norm_num)) ?_
  · intro x hx y hy hxy
    exact Real.rpow_lt_rpow_of_neg hx hxy (by norm_num)
  · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  · have : (1 : ℝ) ∈ Set.Ioi (b / A) := by
      rw [Set.mem_Ioi, div_lt_one hA]; exact hb
    simp [Measure.dirac_apply' _ measurableSet_Ioi, this]

/-- Miao, p. 605: with the posting cost `κ A`, `A` cancels from the job creation condition:
`κ A / q(θ) = β (1 − η) A Φ(z*) ↔ κ / q(θ) = β (1 − η) Φ(z*)`. -/
theorem jd_JC_kappaA_iff {μ : Measure ℝ} {q : ℝ → ℝ} {β η κ A θ c : ℝ} (hA : 0 < A) :
    jd_JC μ q β η (κ * A) A θ c ↔ κ / q θ = β * (1 - η) * jd_Phi μ c := by
  unfold jd_JC
  have hA0 := hA.ne'
  constructor
  · intro h
    have : κ * A / q θ = κ / q θ * A := by ring
    rw [this] at h
    have h2 : κ / q θ * A = (β * (1 - η) * jd_Phi μ c) * A := by rw [h]; ring
    exact mul_right_cancel₀ hA0 h2
  · intro h
    have : κ * A / q θ = κ / q θ * A := by ring
    rw [this, h]; ring

/-- **Comparative statics in `A`, fixed `κ`** (Miao, pp. 604–605): a permanent rise in
productivity `A < A′` raises steady-state market tightness (for `b ≥ 0`). -/
theorem jd_compstat_A_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A A' b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hAA : A < A') (hb : 0 ≤ b) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ q β η κ A' θ' c') (hD' : jd_JD μ β ρx η κ A' b θ' c') : θ < θ' := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  by_contra hne
  have hle : θ' ≤ θ := not_lt.mp hne
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  have hqq : q θ ≤ q θ' := hqanti.antitoneOn (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) hle
  have h1 : κ / q θ' ≤ κ / q θ := div_le_div_of_nonneg_left hκ.le hq hqq
  have hb1 : 0 < β * (1 - η) := mul_pos hβ0 (by linarith)
  have hP : 0 < jd_Phi μ c := by
    have : 0 < κ / q θ := div_pos hκ hq
    rw [hC] at this
    exact pos_of_mul_pos_right this (mul_pos hb1 hA).le
  have h2 : A' * jd_Phi μ c' ≤ A * jd_Phi μ c := by
    rw [hC, hC'] at h1
    have : β * (1 - η) * (A' * jd_Phi μ c') ≤ β * (1 - η) * (A * jd_Phi μ c) := by linarith
    exact le_of_mul_le_mul_left this hb1
  have h3 : jd_Phi μ c' < jd_Phi μ c := by
    have : A * jd_Phi μ c < A' * jd_Phi μ c := mul_lt_mul_of_pos_right hAA hP
    have hA' : 0 < A' := by linarith
    by_contra h4
    have : A' * jd_Phi μ c ≤ A' * jd_Phi μ c' := mul_le_mul_of_nonneg_left (not_lt.mp h4) hA'.le
    linarith
  have hcc : c < c' := by
    by_contra h4
    have := jd_Phi_antitone hint (not_lt.mp h4)
    linarith
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hh := jd_h_strictMono hint hk0 hk1 hcc
  simp only at hh
  set h₀ := c + β * (1 - ρx) * jd_Phi μ c
  set h₁ := c' + β * (1 - ρx) * jd_Phi μ c'
  have h1η : 0 < 1 - η := by linarith
  have eD : η * θ * κ = (1 - η) * (A * h₀ - b) := by rw [hD]; ring
  have eD' : η * θ' * κ = (1 - η) * (A' * h₁ - b) := by rw [hD']; ring
  have hpos : 0 < η * θ * κ := mul_pos (mul_pos hη0 hθ) hκ
  have hh0 : 0 < h₀ := by
    have : 0 < A * h₀ - b := by
      rw [eD] at hpos; exact pos_of_mul_pos_right hpos h1η.le
    by_contra h5
    have : A * h₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le (not_lt.mp h5)
    linarith
  have : A * h₀ < A' * h₁ := by nlinarith
  have : η * θ * κ < η * θ' * κ := by rw [eD, eD']; nlinarith
  have : θ < θ' := by
    have hηκ : 0 < η * κ := mul_pos hη0 hκ
    nlinarith
  linarith

/-- **Comparative statics in `A`, posting cost `κ A`** (Miao, pp. 605–607): for `b > 0` and
`A < A′`, the reservation productivity falls and market tightness rises. -/
theorem jd_compstat_kappaA {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A A' b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hAA : A < A') (hb : 0 < b) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hC : jd_JC μ q β η (κ * A) A θ c) (hD : jd_JD μ β ρx η (κ * A) A b θ c)
    (hC' : jd_JC μ q β η (κ * A') A' θ' c') (hD' : jd_JD μ β ρx η (κ * A') A' b θ' c') :
    c' < c ∧ θ < θ' := by
  have hA' : 0 < A' := by linarith
  rw [jd_JC_kappaA_iff hA] at hC
  rw [jd_JC_kappaA_iff hA'] at hC'
  unfold jd_JD at hD hD'
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  have hb1 : 0 < β * (1 - η) := mul_pos hβ0 (by linarith)
  have h1η : 0 < 1 - η := by linarith
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  -- JD divided by `A`
  have eD : η * θ * κ = (1 - η) * ((c + β * (1 - ρx) * jd_Phi μ c) - b / A) := by
    field_simp; linarith
  have eD' : η * θ' * κ = (1 - η) * ((c' + β * (1 - ρx) * jd_Phi μ c') - b / A') := by
    field_simp; linarith
  have hbA : b / A' < b / A := div_lt_div_of_pos_left hb hA hAA
  have hcc : c' < c := by
    by_contra h
    have hle : c ≤ c' := not_lt.mp h
    have hP := jd_Phi_antitone hint hle
    have h1 : κ / q θ' ≤ κ / q θ := by rw [hC, hC']; exact mul_le_mul_of_nonneg_left hP hb1.le
    have hqq : q θ ≤ q θ' := by
      rw [div_le_div_iff_of_pos_left hκ hq' hq] at h1; exact h1
    have hθθ : θ' ≤ θ := by
      by_contra h2
      have := hqanti (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr hθ') (not_le.mp h2)
      linarith
    have hh := (jd_h_strictMono hint hk0 hk1).monotone hle
    beta_reduce at hh
    have : η * θ' * κ ≤ η * θ * κ := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθθ hη0.le) hκ.le
      linarith
    rw [eD, eD'] at this
    have := le_of_mul_le_mul_left this h1η
    linarith
  refine ⟨hcc, ?_⟩
  have hP : 0 < jd_Phi μ c := by
    have : 0 < κ / q θ := div_pos hκ hq
    rw [hC] at this
    exact pos_of_mul_pos_right this hb1.le
  have hm := (jd_Phi_pos_iff_real hint c).mp hP
  have hgap := jd_Phi_gap hint hcc.le
  have hlt : jd_Phi μ c < jd_Phi μ c' := by nlinarith
  have h1 : κ / q θ < κ / q θ' := by rw [hC, hC']; exact mul_lt_mul_of_pos_left hlt hb1
  rw [div_lt_div_iff_of_pos_left hκ hq hq'] at h1
  by_contra h2
  rcases (not_lt.mp h2).lt_or_eq with h3 | h3
  · have := hqanti (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) h3; linarith
  · rw [h3] at h1; linarith

/-- Miao, p. 606: with posting cost `κ A`, a rise in `A` does not raise the job destruction rate
`ρˣ + (1 − ρˣ) G(z̄*)` (it falls weakly, strictly if `G` puts mass on `(z̄*′, z̄*]`). -/
theorem jd_compstat_kappaA_jd {μ : Measure ℝ} [IsProbabilityMeasure μ] {ρx c c' : ℝ}
    (hρ1 : ρx ≤ 1) (hcc : c' < c) : jd_jdRate μ ρx c' ≤ jd_jdRate μ ρx c :=
  jd_sepRate_mono μ hρ1 hcc.le

/-- Miao, p. 607: steady-state unemployment `u = ρ / (ρ + f)` falls when the separation rate
does not rise and the job-finding rate `f = q(θ) θ` rises: `ρ′ ≤ ρ`, `f < f′` ⇒ `u′ < u`. -/
theorem jd_compstat_kappaA_u {ρ ρ' f f' : ℝ} (hρ : 0 < ρ) (hρ' : 0 ≤ ρ') (hρρ : ρ' ≤ ρ)
    (hf : 0 ≤ f) (hff : f < f') : ρ' / (ρ' + f') < ρ / (ρ + f) := by
  have hf' : 0 < f' := lt_of_le_of_lt hf hff
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Miao, p. 604 ("it is downward sloping"): if the matching function `M` is nondecreasing in
`u` and in `v`, two points `(u₁, v₁)`, `(u₂, v₂)` of the Beveridge curve `ρ (1 − u) = M(u, v)`
with `ρ > 0` and `u₁ < u₂` have `v₂ < v₁`. (Convexity is the §18.1 claim and is not repeated.) -/
theorem jd_beveridge_downward {M : ℝ → ℝ → ℝ} {ρ u₁ u₂ v₁ v₂ : ℝ}
    (hMu : ∀ v, Monotone fun u => M u v) (hMv : ∀ u, Monotone (M u)) (hρ : 0 < ρ)
    (h₁ : ρ * (1 - u₁) = M u₁ v₁) (h₂ : ρ * (1 - u₂) = M u₂ v₂) (hu : u₁ < u₂) : v₂ < v₁ := by
  by_contra h
  have hv : v₁ ≤ v₂ := not_lt.mp h
  have e1 : M u₁ v₁ ≤ M u₁ v₂ := hMv u₁ hv
  have e2 : M u₁ v₂ ≤ M u₂ v₂ := hMu v₂ hu.le
  nlinarith

/-- Miao, p. 604 and Figure 18.6: the Beveridge curve `ρ (1 − u) = M(u, v) = v q(v/u)` shifts
down when the separation rate falls: at given `u ∈ (0, 1)`, if `θ ↦ θ q(θ)` is strictly
increasing on `(0, ∞)` and `ρ′ < ρ`, the vacancies on the new curve are lower. -/
theorem jd_beveridge_shift {q : ℝ → ℝ} {ρ ρ' u v v' : ℝ}
    (hf : StrictMonoOn (fun θ => θ * q θ) (Set.Ioi 0)) (hu0 : 0 < u) (hu1 : u < 1)
    (hv : 0 < v) (hv' : 0 < v') (hρρ : ρ' < ρ)
    (hBC : ρ * (1 - u) = v * q (v / u)) (hBC' : ρ' * (1 - u) = v' * q (v' / u)) : v' < v := by
  have e : ∀ x, x * q (x / u) = u * ((x / u) * q (x / u)) := by
    intro x; field_simp
  rw [e] at hBC hBC'
  have hlt : u * ((v' / u) * q (v' / u)) < u * ((v / u) * q (v / u)) := by
    rw [← hBC, ← hBC']; nlinarith
  have hlt' := lt_of_mul_lt_mul_left hlt hu0.le
  have : v' / u < v / u := by
    by_contra h
    have := hf.monotoneOn (Set.mem_Ioi.mpr (div_pos hv hu0)) (Set.mem_Ioi.mpr (div_pos hv' hu0))
      (not_lt.mp h)
    beta_reduce at this
    linarith
  exact (div_lt_div_iff_of_pos_right hu0).mp this

/-- **Transitional dynamics after a permanent rise in `A`** (Miao, p. 607). Tightness and the
reservation productivity jump to their new steady state; then `u_{t+1} = (1 − ρ − f) u_t + ρ`
with constant `ρ` and `f = q(θ) θ`. If `0 ≤ 1 − ρ − f`, `f > 0` and `u₀ ≥ ū = ρ/(ρ + f)`,
unemployment falls monotonically to `ū`, and the job creation rate `f u_t /(1 − u_t)` falls
monotonically to the constant job destruction rate `ρ`. -/
theorem jd_transition_unemployment {ρ f : ℝ} {u : ℕ → ℝ} (hρ : 0 ≤ ρ) (hf : 0 < f)
    (ha : 0 ≤ 1 - ρ - f) (hu : ∀ t, u (t + 1) = (1 - ρ - f) * u t + ρ)
    (h0 : ρ / (ρ + f) ≤ u 0) (h01 : u 0 < 1) :
    Antitone u ∧ Tendsto u atTop (𝓝 (ρ / (ρ + f))) ∧
      Antitone (fun t => f * u t / (1 - u t)) ∧ (∀ t, ρ ≤ f * u t / (1 - u t)) ∧
      Tendsto (fun t => f * u t / (1 - u t)) atTop (𝓝 ρ) := by
  have hpos : 0 < ρ + f := by linarith
  have e : ρ / (1 - (1 - ρ - f)) = ρ / (ρ + f) := by congr 1; ring
  have ha1 : 1 - ρ - f < 1 := by linarith
  have hu' : ∀ t, u (t + 1) = (1 - ρ - f) * u t + ρ := hu
  obtain ⟨hanti, hge⟩ := jd_affine_antitone ha ha1 hu' (by rw [e]; exact h0)
  rw [e] at hge
  have hlim : Tendsto u atTop (𝓝 (ρ / (ρ + f))) := by
    have := jd_affine_tendsto (abs_lt.mpr ⟨by linarith, ha1⟩) hu'
    rwa [e] at this
  have hlt1 : ∀ t, u t < 1 := fun t => lt_of_le_of_lt (hanti (Nat.zero_le t)) h01
  have hus1 : ρ / (ρ + f) < 1 := by rw [div_lt_one hpos]; linarith
  have hjc : ∀ t, ρ ≤ f * u t / (1 - u t) := by
    intro t
    have h1 : 0 < 1 - u t := by linarith [hlt1 t]
    rw [le_div_iff₀ h1]
    have := hge t
    rw [div_le_iff₀ hpos] at this
    nlinarith
  refine ⟨hanti, hlim, ?_, hjc, ?_⟩
  · intro s t hst
    have h1 : 0 < 1 - u t := by linarith [hlt1 t]
    have h2 : 0 < 1 - u s := by linarith [hlt1 s]
    have hus := hanti hst
    simp only
    rw [div_le_div_iff₀ h1 h2]
    nlinarith
  · have hcont : Tendsto (fun x => f * x / (1 - x)) (𝓝 (ρ / (ρ + f)))
        (𝓝 (f * (ρ / (ρ + f)) / (1 - ρ / (ρ + f)))) := by
      refine Tendsto.div (tendsto_const_nhds.mul tendsto_id) (tendsto_const_nhds.sub tendsto_id) ?_
      linarith
    have := hcont.comp hlim
    have e2 : f * (ρ / (ρ + f)) / (1 - ρ / (ρ + f)) = ρ := by
      field_simp
      ring_nf
      field_simp
    rw [e2] at this
    exact this

/-- Miao, p. 607 (linearising (18.41)): `θ ↦ κ / q(θ)` has derivative `−κ q′(θ)/q(θ)²`. -/
theorem jd_kappa_div_q_hasDerivAt {q : ℝ → ℝ} {κ θ q' : ℝ} (hq : HasDerivAt q q' θ)
    (hq0 : q θ ≠ 0) : HasDerivAt (fun x => κ / q x) (-(κ * q') / q θ ^ 2) θ := by
  have h := (hasDerivAt_const θ κ).div hq hq0
  have e : (fun x => κ / q x) = (fun _ => κ) / q := rfl
  rw [e]
  convert h using 1
  ring

/-- Miao, p. 607 (the linearised system): if `D = (κ/q)′(θ*) > 0` and `g = 1 − G(z̄*)`, the
linearised (18.41) `D dθ_t = −β (1 − η) A g dz_{t+1}` and (18.42)
`η κ dθ_t = (1 − η) A dz_t − β (1 − ρˣ)(1 − η) A g dz_{t+1}` give
`dz_t = ψ dz_{t+1}` with `ψ = β g ((1 − ρˣ) − η κ / D)`. With `D = κ ξ/(θ q)`, `ξ = −θ q′/q`,
this is `ψ = β g ((1 − ρˣ) − η q θ / ξ)`. -/
theorem jd_linear_psi {β ρx η κ A g D : ℝ} {dz dθ : ℕ → ℝ} (hη1 : η < 1) (hA : 0 < A)
    (hD : 0 < D)
    (hJC : ∀ t, D * dθ t = -(β * (1 - η) * A * g) * dz (t + 1))
    (hJD : ∀ t, η * κ * dθ t = (1 - η) * A * dz t - β * (1 - ρx) * (1 - η) * A * g * dz (t + 1))
    (t : ℕ) : dz t = β * g * ((1 - ρx) - η * κ / D) * dz (t + 1) := by
  have h1 := hJC t
  have h2 := hJD t
  have hD0 := hD.ne'
  have hc : (1 - η) * A ≠ 0 := (mul_pos (by linarith) hA).ne'
  have hθ : dθ t = -(β * (1 - η) * A * g) * dz (t + 1) / D := by
    field_simp; linarith
  rw [hθ] at h2
  apply mul_left_cancel₀ hc
  field_simp at h2 ⊢
  linarith

/-- Miao, p. 607: under the analogue of the §18.1 condition, `(1 − ρˣ) − η κ / D ≥ 0`, and
`0 ≤ g ≤ 1`, `0 < β < 1`, the coefficient satisfies `0 ≤ ψ < 1`. -/
theorem jd_psi_abs_lt_one {β ρx η κ g D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx)
    (hη0 : 0 < η) (hκ : 0 < κ) (hD : 0 < D) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hcond : 0 ≤ (1 - ρx) - η * κ / D) : |β * g * ((1 - ρx) - η * κ / D)| < 1 := by
  have hpos : 0 < η * κ / D := div_pos (mul_pos hη0 hκ) hD
  have h1 : (1 - ρx) - η * κ / D < 1 := by linarith
  have h0 : 0 ≤ β * g * ((1 - ρx) - η * κ / D) := mul_nonneg (mul_nonneg hβ0.le hg0) hcond
  rw [abs_of_nonneg h0]
  have : β * g ≤ β := by nlinarith
  calc β * g * ((1 - ρx) - η * κ / D) ≤ β * ((1 - ρx) - η * κ / D) :=
        mul_le_mul_of_nonneg_right this hcond
    _ < 1 := by nlinarith

/-- **The steady state is a saddle point** (Miao, p. 607). In the linearised system
`dz_t = ψ dz_{t+1}` (`jd_linear_psi`), `D dθ_t = −β (1 − η) A g dz_{t+1}` and
`du_{t+1} = a dz_t + a' dθ_t + (1 − ρ − f) du_t` (from (18.43)), with `|ψ| < 1` and
`|1 − ρ − f| < 1`, every bounded solution has `dz_t = dθ_t = 0` for all `t` (the jump variables
sit at their steady state), and `du_t = (1 − ρ − f)ᵗ du₀ → 0`. -/
theorem jd_saddle {β η A g D ψ a a' ρ f : ℝ} {dz dθ du : ℕ → ℝ} (hD : 0 < D) (hψ : |ψ| < 1)
    (hr : |1 - ρ - f| < 1) (hz : ∀ t, dz t = ψ * dz (t + 1))
    (hJC : ∀ t, D * dθ t = -(β * (1 - η) * A * g) * dz (t + 1))
    (hu : ∀ t, du (t + 1) = a * dz t + a' * dθ t + (1 - ρ - f) * du t)
    (hbdd : ∃ M, ∀ t, |dz t| ≤ M) :
    (∀ t, dz t = 0) ∧ (∀ t, dθ t = 0) ∧ (∀ t, du t = (1 - ρ - f) ^ t * du 0) ∧
      Tendsto du atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hbdd
  have hz0 : ∀ t, dz t = 0 := by
    intro t
    have hpow : ∀ n, |dz t| ≤ |ψ| ^ n * M := by
      intro n
      induction n generalizing t with
      | zero => simpa using hM t
      | succ n ih =>
        have := ih (t + 1)
        rw [hz t, abs_mul, pow_succ]
        have h0 : 0 ≤ |ψ| := abs_nonneg ψ
        calc |ψ| * |dz (t + 1)| ≤ |ψ| * (|ψ| ^ n * M) := mul_le_mul_of_nonneg_left this h0
          _ = |ψ| ^ n * |ψ| * M := by ring
    have hlim : Tendsto (fun n : ℕ => |ψ| ^ n * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ψ) hψ).mul_const M
    have : |dz t| ≤ 0 := ge_of_tendsto' hlim hpow
    exact abs_nonpos_iff.mp this
  have hθ0 : ∀ t, dθ t = 0 := by
    intro t
    have := hJC t
    rw [hz0 (t + 1), mul_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hD.ne'
    · exact h
  have hu' : ∀ t, du (t + 1) = (1 - ρ - f) * du t + 0 := by
    intro t; rw [hu t, hz0 t, hθ0 t]; ring
  have hsol : ∀ t, du t = (1 - ρ - f) ^ t * du 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hu' n, ih, pow_succ]; ring
  refine ⟨hz0, hθ0, hsol, ?_⟩
  have := jd_affine_tendsto hr hu'
  simpa using this

end Miao.SearchAndMatching
