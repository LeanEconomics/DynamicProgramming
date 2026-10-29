/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.FNorm
import VUniformErgodicity.SpecificKernels

/-!
# The continuous-time key renewal theorem: the measure-theoretic steps (MT §14.5)

Meyn and Tweedie, §14.5, pp. 354–358. For measures `ρ` on `ℝ` (in the book `ρ = Γ₀ ∗ U`, with
`U = Σₙ Γ^{n∗}` the renewal measure `renewalMeasure Γ`) write `ρ ∗ g(t) = ∫ g(t − u) ρ(du)`
(`convAt`), as in (14.34).

**Results.**
* `convSupDiff_le`: if `ρ₁ − ρ₂` has finite total variation in the form `ρ₁ + σ₂ = ρ₂ + σ₁` with
  `σ₁, σ₂` finite (the conclusion (14.42) of Proposition 14.5.3), then
  `sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)| ≤ ∫ f(t − u) (σ₁ + σ₂)(du)`, the bound (14.47).
* **Proposition 14.5.4** (`proposition_14_5_4`, p. 357), (14.45), given (14.42): for a bounded
  measurable `f ≥ 0` with `f(t) → 0` ((14.37) and (14.39); the integrability (14.38) is not
  needed), `sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)| → 0` (dominated convergence for `σ₁ + σ₂`).
* **Theorem 14.5.2 (ii) from (i)** (`theorem_14_5_2_ii_of_i`, p. 355, "a simple consequence"):
  the uniform convergence (14.36) for `f = 1_{[0, b−a]}` gives (14.40), by the reflected test
  functions `g(s) = 1_B(b − s)` and the times `t + b`.

**Not formalised.** Theorem 14.5.1 (Blackwell's renewal theorem, quoted from Feller), Theorem
14.5.2 (i) and (iii), Proposition 14.5.3 and Proposition 14.5.5. They rest on (i) the
continuous-time regeneration identity (14.43), `Γ₀ ∗ U(A) = Γ₀Pˢ ∗ U(A − s)` for `A ⊆ [s, ∞)`,
relating the renewal measure to the forward recurrence time chain `V⁺_δ` (`fwdSkelKernel`);
(ii) the ergodic theory of `V⁺_δ`: its `ψ`-irreducibility (left implicit in the book, and not
available here), positive Harris recurrence and regularity under (V2) with `V(x) = x`
(Theorems 11.3.15, 11.3.12), and the sum bound (14.41) from Theorem 13.4.4; (iii) the finiteness
of `U[0, δ)`; (iv) for Proposition 14.5.5 the equilibrium identity `Γₑ ∗ U = β⁻¹ μ_Leb` and the
truncation (14.48)–(14.49); (v) for (iii) the absolute continuity of `(Γ₁ + Γ₂) ∗ U`. The discrete
analogues on `ℤ₊` are in `KeyRenewal`.

**Corrections.** None. The book's derivation of (14.40) from (14.36) needs the test functions to be
reflected, `g(s) = 1_B(b − s)` on `[0, b − a]`, since `ρ ∗ g(t)` integrates `g` at `t − u`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `ρ ∗ g(t) = ∫ g(t − u) ρ(du)` (MT (14.34), with `ρ = Γ₀ ∗ U`). -/
noncomputable def convAt (ρ : Measure ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u, g (t - u) ∂ρ

/-- `sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)|` (MT (14.45)), valued in `[0, ∞]`. -/
noncomputable def convSupDiff (f : ℝ → ℝ) (ρ₁ ρ₂ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (g : ℝ → ℝ) (_ : Measurable g ∧ ∀ s, |g s| ≤ f s),
    ENNReal.ofReal |convAt ρ₁ g t - convAt ρ₂ g t|

/-- **The bound (14.47)**: if `ρ₁ + σ₂ = ρ₂ + σ₁` (finite total variation of `ρ₁ − ρ₂` when
`σ₁, σ₂` are finite) and `f(t − ·)` is `ρᵢ`-integrable, then
`sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)| ≤ ∫ f(t − u) σ₁(du) + ∫ f(t − u) σ₂(du)`. -/
theorem convSupDiff_le {ρ₁ ρ₂ σ₁ σ₂ : Measure ℝ} (heq : ρ₁ + σ₂ = ρ₂ + σ₁) {f : ℝ → ℝ}
    {t : ℝ} (h₁ : ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂ρ₁ ≠ ∞)
    (h₂ : ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂ρ₂ ≠ ∞) :
    convSupDiff f ρ₁ ρ₂ t ≤
      ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ₁ + ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ₂ := by
  have hsub : Measurable fun u : ℝ => t - u := measurable_const.sub measurable_id
  refine iSup₂_le fun g hg => ?_
  have hGm : Measurable fun u => g (t - u) := hg.1.comp hsub
  have hGb : ∀ u, ENNReal.ofReal |g (t - u)| ≤ ENNReal.ofReal (f (t - u)) := fun u =>
    ENNReal.ofReal_le_ofReal (hg.2 _)
  have htest : IsFTest (fun u => ENNReal.ofReal (f (t - u))) ρ₁ ρ₂ (fun u => g (t - u)) :=
    ⟨hGm, hGb, integrable_of_ofReal_abs_le hGm hGb h₁, integrable_of_ofReal_abs_le hGm hGb h₂⟩
  exact (ofReal_abs_integral_sub_le_fNorm htest).trans (fNorm_le_of_add_eq heq)

/-- **Proposition 14.5.4** (MT p. 357), (14.45), from the finite total variation (14.42) of
Proposition 14.5.3: if `ρ₁ + σ₂ = ρ₂ + σ₁` with `σ₁, σ₂` finite, `f ≥ 0` is measurable and
bounded (14.37), `f(t) → 0` as `t → ∞` (14.39), and `f(t − ·)` is `ρᵢ`-integrable for every `t`,
then `sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)| → 0`. -/
theorem proposition_14_5_4 {ρ₁ ρ₂ σ₁ σ₂ : Measure ℝ} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    (heq : ρ₁ + σ₂ = ρ₂ + σ₁) {f : ℝ → ℝ} (hf : Measurable f) {d : ℝ} (hfd : ∀ s, f s ≤ d)
    (hlim : Tendsto f atTop (𝓝 0))
    (hloc : ∀ t, ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂ρ₁ ≠ ∞ ∧
      ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂ρ₂ ≠ ∞) :
    Tendsto (convSupDiff f ρ₁ ρ₂) atTop (𝓝 0) := by
  -- dominated convergence for a finite measure
  have hdct : ∀ σ : Measure ℝ, IsFiniteMeasure σ →
      Tendsto (fun t => ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂σ) atTop (𝓝 0) := fun σ _ => by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := σ) (l := atTop)
      (F := fun t u => ENNReal.ofReal (f (t - u))) (f := fun _ => 0) (fun _ => ENNReal.ofReal d)
      (Eventually.of_forall fun t =>
        ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub measurable_id)))
      (Eventually.of_forall fun t => Eventually.of_forall fun u => ENNReal.ofReal_le_ofReal (hfd _))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (Eventually.of_forall fun u => by
        have h1 : Tendsto (fun t : ℝ => t - u) atTop atTop := by
          simp_rw [sub_eq_add_neg]
          exact tendsto_atTop_add_const_right _ _ tendsto_id
        have h2 := ENNReal.tendsto_ofReal (hlim.comp h1)
        rw [ENNReal.ofReal_zero] at h2
        exact h2)
    rw [lintegral_zero] at h
    exact h
  have hsum := (hdct σ₁ inferInstance).add (hdct σ₂ inferInstance)
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun t => convSupDiff_le heq (hloc t).1 (hloc t).2

/-- **Theorem 14.5.2 (ii) from (i)** (MT p. 355): if `ρ` satisfies the uniform convergence (14.36)
for `f = 1_{[0, b−a]}`, then (14.40) holds on `[a, b]`:
`sup_{B ⊆ [a, b]} |ρ(t + B) − β⁻¹ μ_Leb(B)| → 0`. -/
theorem theorem_14_5_2_ii_of_i (ρ : Measure ℝ) (β : ℝ) {a b : ℝ}
    (h : Tendsto (fun t => ⨆ (g : ℝ → ℝ) (_ : Measurable g ∧
      ∀ s, |g s| ≤ (Icc 0 (b - a)).indicator 1 s),
        ENNReal.ofReal |convAt ρ g t - β⁻¹ * ∫ s, g s|) atTop (𝓝 0)) :
    Tendsto (fun t => ⨆ (B : Set ℝ) (_ : MeasurableSet B ∧ B ⊆ Icc a b),
      ENNReal.ofReal |ρ.real {u | u - t ∈ B} - β⁻¹ * volume.real B|) atTop (𝓝 0) := by
  have hshift : Tendsto (fun t : ℝ => t + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h.comp hshift)
    (fun _ => zero_le) fun t => iSup₂_le fun B hB => ?_
  -- the reflected test function `g(s) = 1_B(b − s)`
  set g : ℝ → ℝ := {s | b - s ∈ B}.indicator 1 with hg
  have hrefl : MeasurableSet {s : ℝ | b - s ∈ B} :=
    (measurable_const.sub measurable_id) hB.1
  have hgm : Measurable g := measurable_one.indicator hrefl
  have hgb : ∀ s, |g s| ≤ (Icc 0 (b - a)).indicator 1 s := fun s => by
    by_cases hs : b - s ∈ B
    · have hab := hB.2 hs
      rw [hg, indicator_of_mem (show s ∈ {s | b - s ∈ B} from hs),
        indicator_of_mem (show s ∈ Icc 0 (b - a) from ⟨by linarith [hab.2], by linarith [hab.1]⟩)]
      simp only [Pi.one_apply, abs_one, le_refl]
    · rw [hg, indicator_of_notMem (show s ∉ {s | b - s ∈ B} from hs), abs_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) s
  have hconv : convAt ρ g (t + b) = ρ.real {u | u - t ∈ B} := by
    have e : (fun u => g (t + b - u)) = {u : ℝ | u - t ∈ B}.indicator 1 := by
      funext u
      have : b - (t + b - u) = u - t := by ring
      by_cases hu : u - t ∈ B
      · rw [hg, indicator_of_mem (show t + b - u ∈ {s | b - s ∈ B} by
          change b - (t + b - u) ∈ B; rw [this]; exact hu),
          indicator_of_mem (show u ∈ {u : ℝ | u - t ∈ B} from hu)]
        rfl
      · rw [hg, indicator_of_notMem (show t + b - u ∉ {s | b - s ∈ B} by
          change ¬ b - (t + b - u) ∈ B; rw [this]; exact hu),
          indicator_of_notMem (show u ∉ {u : ℝ | u - t ∈ B} from hu)]
    rw [convAt, e, integral_indicator_one
      (show MeasurableSet {u : ℝ | u - t ∈ B} from (measurable_id.sub measurable_const) hB.1)]
  have hleb : ∫ s, g s = volume.real B := by
    rw [hg, integral_indicator_one hrefl]
    have e : {s : ℝ | b - s ∈ B} = Neg.neg ⁻¹' ((fun h => b + h) ⁻¹' B) := by
      ext s
      simp only [mem_ofPred_eq, mem_preimage, ← sub_eq_add_neg]
    rw [measureReal_def, measureReal_def, e, Measure.measure_preimage_neg, measure_preimage_add]
  have hle := le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : Measurable g ∧
      ∀ s, |g s| ≤ (Icc 0 (b - a)).indicator 1 s) =>
        ENNReal.ofReal |convAt ρ g (t + b) - β⁻¹ * ∫ s, g s|) g ⟨hgm, hgb⟩
  rw [hconv, hleb] at hle
  exact hle

end MeynTweedie.VUniformErgodicity
