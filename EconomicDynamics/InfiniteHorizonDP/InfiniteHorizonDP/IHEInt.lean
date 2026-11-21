/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.MDPObjective
import InfiniteHorizonDP.IHExtendedReals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Integrals of extended-real functions

Tools for Miao, §7.1, pp. 194–203. The integrals of Lemma 7.1.1 and of the Bellman equation (7.2)
are integrals of functions with values in `[−∞, +∞]` (the objective `J` and the value function
`V` may be infinite). We use the usual extended integral
`ih_eint μ f = ∫ f⁺ dμ − ∫ f⁻ dμ ∈ [−∞, +∞]`, with `f⁺ = max(f, 0)`, `f⁻ = max(−f, 0)` integrated
as lower integrals in `[0, ∞]` and the convention `∞ − ∞ = −∞` of `EReal`.

* `ih_eint_mono`: it is monotone (no measurability or integrability is needed).
* `ih_eint_coe`: for an integrable real function it is the Bochner integral;
  `ih_eint_of_nonneg`, `ih_eint_of_nonpos`: for functions of one sign it is `±∫⁻`.
* `ih_eint_le_add`: if `g ≤ f + ε` then `∫ g ≤ ∫ f + 2ε` (probability measures).
* The three limit theorems behind Lemma 7.1.1: monotone convergence for nonnegative increasing
  sequences (`ih_tendsto_eint_nonneg`), for nonpositive decreasing ones
  (`ih_tendsto_eint_nonpos`), and dominated convergence for uniformly bounded ones
  (`ih_tendsto_eint_bounded`).
* `ih_ae_eq_of_eint_eq`: if `f ≤ v`, `v` is integrable and `∫ f = ∫ v`, then `f = v` a.e.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The integral `∫ f dμ = ∫ f⁺ dμ − ∫ f⁻ dμ ∈ [−∞, +∞]` of an extended-real function. -/
noncomputable def ih_eint (μ : Measure X) (f : X → EReal) : EReal :=
  ((∫⁻ x, (f x).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ x, (-f x).toENNReal ∂μ : ℝ≥0∞) : EReal)

/-- The extended integral is monotone. -/
theorem ih_eint_mono (μ : Measure X) {f g : X → EReal} (h : ∀ x, f x ≤ g x) :
    ih_eint μ f ≤ ih_eint μ g :=
  EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x)))
    (EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h x))))

/-- For an integrable real function the extended integral is the Bochner integral. -/
theorem ih_eint_coe {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ) :
    ih_eint μ (fun x => (f x : EReal)) = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  simp only [ih_eint, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  have h2 := hf.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at h2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    EReal.coe_ennreal_toReal hf.lintegral_lt_top.ne, EReal.coe_ennreal_toReal h2.ne]

/-- For a nonnegative function, `∫ f = ∫⁻ f`. -/
theorem ih_eint_of_nonneg (μ : Measure X) {f : X → EReal} (hf : ∀ x, 0 ≤ f x) :
    ih_eint μ f = ((∫⁻ x, (f x).toENNReal ∂μ : ℝ≥0∞) : EReal) := by
  have : ∀ x, (-f x).toENNReal = 0 := fun x =>
    EReal.toENNReal_of_nonpos (by rw [← neg_zero]; exact EReal.neg_le_neg_iff.2 (hf x))
  simp only [ih_eint, this, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

/-- For a nonpositive function, `∫ f = −∫⁻ (−f)`. -/
theorem ih_eint_of_nonpos (μ : Measure X) {f : X → EReal} (hf : ∀ x, f x ≤ 0) :
    ih_eint μ f = -((∫⁻ x, (-f x).toENNReal ∂μ : ℝ≥0∞) : EReal) := by
  have : ∀ x, (f x).toENNReal = 0 := fun x => EReal.toENNReal_of_nonpos (hf x)
  simp only [ih_eint, this, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]

theorem ih_toENNReal_le_add {g f : EReal} {ε : ℝ} (hε : 0 ≤ ε) (h : g ≤ f + ε) :
    g.toENNReal ≤ f.toENNReal + ENNReal.ofReal ε := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_add, EReal.coe_toENNReal_eq_max,
    EReal.coe_toENNReal_eq_max, EReal.coe_ennreal_ofReal, max_eq_left hε]
  refine max_le (add_nonneg (le_max_left _ _) (EReal.coe_nonneg.2 hε)) ?_
  exact h.trans (add_le_add (le_max_right _ _) le_rfl)

theorem ih_neg_le_add {g f : EReal} {ε : ℝ} (h : g ≤ f + ε) : -f ≤ -g + ε := by
  induction f using EReal.rec with
  | bot =>
    have hg : g = ⊥ := le_bot_iff.1 (by simpa using h)
    simp [hg]
  | top => simp
  | coe r =>
    induction g using EReal.rec with
    | bot => simp
    | top => exact absurd h (by rw [← EReal.coe_add]; exact not_le.2 (EReal.coe_lt_top _))
    | coe q =>
      rw [← EReal.coe_add] at h
      rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
      have := EReal.coe_le_coe_iff.1 h
      exact EReal.coe_le_coe_iff.2 (by linarith)

theorem ih_ereal_sub_le {P₁ N₁ P₂ N₂ : ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : P₁ ≤ P₂ + ENNReal.ofReal ε) (h₂ : N₂ ≤ N₁ + ENNReal.ofReal ε) :
    (P₁ : EReal) - N₁ ≤ (P₂ : EReal) - N₂ + ((2 * ε : ℝ) : EReal) := by
  by_cases hN₁ : N₁ = ⊤
  · rw [hN₁, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hN₂ : N₂ ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hN₁, ENNReal.ofReal_ne_top⟩) h₂
  by_cases hP₂ : P₂ = ⊤
  · rw [hP₂, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hN₂, EReal.top_sub_coe,
      EReal.top_add_coe]
    exact le_top
  have hP₁ : P₁ ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hP₂, ENNReal.ofReal_ne_top⟩) h₁
  have e₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP₂, ENNReal.ofReal_ne_top⟩) h₁
  have e₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hN₁, ENNReal.ofReal_ne_top⟩) h₂
  rw [ENNReal.toReal_add hP₂ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε] at e₁
  rw [ENNReal.toReal_add hN₁ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε] at e₂
  rw [← EReal.coe_ennreal_toReal hN₁, ← EReal.coe_ennreal_toReal hN₂,
    ← EReal.coe_ennreal_toReal hP₁, ← EReal.coe_ennreal_toReal hP₂, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.2 (by linarith)

/-- If `g ≤ f + ε` pointwise, then `∫ g dμ ≤ ∫ f dμ + 2ε` for a probability measure `μ`. -/
theorem ih_eint_le_add {μ : Measure X} [IsProbabilityMeasure μ] {f g : X → EReal} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x, g x ≤ f x + ε) :
    ih_eint μ g ≤ ih_eint μ f + ((2 * ε : ℝ) : EReal) := by
  have hc : ∫⁻ _ : X, ENNReal.ofReal ε ∂μ = ENNReal.ofReal ε := by
    rw [lintegral_const, measure_univ, mul_one]
  refine ih_ereal_sub_le hε ?_ ?_
  · refine (lintegral_mono fun x => ih_toENNReal_le_add hε (h x)).trans ?_
    rw [lintegral_add_right _ measurable_const, hc]
  · refine (lintegral_mono fun x => ih_toENNReal_le_add hε (ih_neg_le_add (h x))).trans ?_
    rw [lintegral_add_right _ measurable_const, hc]

/-- **Monotone convergence** for the extended integral: nonnegative integrable functions
increasing to `g` have integrals tending to `∫ g`. -/
theorem ih_tendsto_eint_nonneg {μ : Measure X} {f : ℕ → X → ℝ} {g : X → EReal}
    (hint : ∀ n, Integrable (f n) μ) (hf0 : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ x, Monotone fun n => f n x)
    (hlim : ∀ x, Tendsto (fun n => (f n x : EReal)) atTop (𝓝 (g x))) :
    Tendsto (fun n => ((∫ x, f n x ∂μ : ℝ) : EReal)) atTop (𝓝 (ih_eint μ g)) := by
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    ge_of_tendsto' (hlim x) fun n => EReal.coe_nonneg.2 (hf0 n x)
  rw [ih_eint_of_nonneg μ hg0]
  have e : ∀ n, ((∫ x, f n x ∂μ : ℝ) : EReal) =
      ((∫⁻ x, ENNReal.ofReal (f n x) ∂μ : ℝ≥0∞) : EReal) := fun n => by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hf0 n)) (hint n).1,
      EReal.coe_ennreal_toReal (hint n).lintegral_lt_top.ne]
  simp only [e]
  refine (continuous_coe_ennreal_ereal.tendsto _).comp ?_
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hint n).1.aemeasurable.ennreal_ofReal)
    (ae_of_all _ fun x m n hmn => ENNReal.ofReal_le_ofReal (hmono x hmn)) (ae_of_all _ fun x => ?_)
  have := (EReal.continuous_toENNReal.tendsto _).comp (hlim x)
  simpa only [Function.comp_def, EReal.real_coe_toENNReal] using this

/-- **Monotone convergence** for nonpositive decreasing sequences. -/
theorem ih_tendsto_eint_nonpos {μ : Measure X} {f : ℕ → X → ℝ} {g : X → EReal}
    (hint : ∀ n, Integrable (f n) μ) (hf0 : ∀ n x, f n x ≤ 0)
    (hanti : ∀ x, Antitone fun n => f n x)
    (hlim : ∀ x, Tendsto (fun n => (f n x : EReal)) atTop (𝓝 (g x))) :
    Tendsto (fun n => ((∫ x, f n x ∂μ : ℝ) : EReal)) atTop (𝓝 (ih_eint μ g)) := by
  have hg0 : ∀ x, g x ≤ 0 := fun x =>
    le_of_tendsto' (hlim x) fun n => EReal.coe_nonpos.2 (hf0 n x)
  have h := ih_tendsto_eint_nonneg (μ := μ) (f := fun n x => -f n x) (g := fun x => -g x)
    (fun n => (hint n).neg) (fun n x => neg_nonneg.2 (hf0 n x))
    (fun x m n hmn => neg_le_neg (hanti x hmn))
    (fun x => by
      have := (continuous_neg.tendsto _).comp (hlim x)
      simpa only [Function.comp_def, EReal.coe_neg] using this)
  rw [ih_eint_of_nonneg μ fun x => EReal.neg_nonneg.2 (hg0 x)] at h
  rw [ih_eint_of_nonpos μ hg0]
  have h2 := (continuous_neg.tendsto _).comp h
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, integral_neg, EReal.coe_neg, neg_neg]

/-- **Dominated convergence** for the extended integral: integrable functions bounded by a
constant `C` and converging to `g` (pointwise in `[−∞, +∞]`). The limit is real-valued, bounded
by `C` and integrable, and the integrals converge to its integral. -/
theorem ih_tendsto_eint_bounded {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ}
    {g : X → EReal} {C : ℝ} (hint : ∀ n, Integrable (f n) μ) (hb : ∀ n x, |f n x| ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (f n x : EReal)) atTop (𝓝 (g x))) :
    (∀ x, g x = ((g x).toReal : EReal)) ∧ (∀ x, |(g x).toReal| ≤ C) ∧
      Integrable (fun x => (g x).toReal) μ ∧
      ih_eint μ g = ((∫ x, (g x).toReal ∂μ : ℝ) : EReal) ∧
      Tendsto (fun n => ((∫ x, f n x ∂μ : ℝ) : EReal)) atTop (𝓝 (ih_eint μ g)) := by
  have hg : ∀ x, g x = ((g x).toReal : EReal) := fun x => by
    have h1 : ((-C : ℝ) : EReal) ≤ g x := ge_of_tendsto' (hlim x) fun n =>
      EReal.coe_le_coe_iff.2 (neg_le_of_abs_le (hb n x))
    have h2 : g x ≤ (C : EReal) := le_of_tendsto' (hlim x) fun n =>
      EReal.coe_le_coe_iff.2 (le_of_abs_le (hb n x))
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top C) h2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)).symm
  have hlim' : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x).toReal) := fun x => by
    have := hlim x
    rw [hg x] at this
    exact EReal.tendsto_coe.1 this
  have hbd : ∀ x, |(g x).toReal| ≤ C := fun x =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hlim' x)) fun n => hb n x
  have hmeas : AEStronglyMeasurable (fun x => (g x).toReal) μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hint n).1) (ae_of_all _ hlim')
  have hgi : Integrable (fun x => (g x).toReal) μ :=
    Integrable.mono' (integrable_const C) hmeas (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hbd x)
  have he : ih_eint μ g = ((∫ x, (g x).toReal ∂μ : ℝ) : EReal) := by
    rw [← ih_eint_coe hgi]
    exact congrArg (ih_eint μ) (funext hg)
  refine ⟨hg, hbd, hgi, he, ?_⟩
  rw [he]
  refine EReal.tendsto_coe.2 ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => (hint n).1)
    (integrable_const C) (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ hlim')
  rw [Real.norm_eq_abs]
  exact hb n x

/-- A pointwise limit of a.e.-measurable real functions has a.e.-measurable positive and
negative parts. -/
theorem ih_aemeasurable_parts {μ : Measure X} {f : ℕ → X → ℝ} {g : X → EReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ x, Tendsto (fun n => (f n x : EReal)) atTop (𝓝 (g x))) :
    AEMeasurable (fun x => (g x).toENNReal) μ ∧ AEMeasurable (fun x => (-g x).toENNReal) μ := by
  refine ⟨aemeasurable_of_tendsto_metrizable_ae' (fun n => (hf n).ennreal_ofReal)
    (ae_of_all _ fun x => ?_), aemeasurable_of_tendsto_metrizable_ae'
      (fun n => (hf n).neg.ennreal_ofReal) (ae_of_all _ fun x => ?_)⟩
  · have := (EReal.continuous_toENNReal.tendsto _).comp (hlim x)
    simpa only [Function.comp_def, EReal.real_coe_toENNReal] using this
  · have := (EReal.continuous_toENNReal.tendsto _).comp ((continuous_neg.tendsto _).comp (hlim x))
    simpa only [Function.comp_def, ← EReal.coe_neg, EReal.real_coe_toENNReal, Pi.neg_apply]
      using this

theorem ih_eq_of_parts {x : EReal} {r : ℝ} (h₁ : x.toENNReal = ENNReal.ofReal r)
    (h₂ : (-x).toENNReal = ENNReal.ofReal (-r)) : x = r := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.neg_bot, EReal.toENNReal_top] at h₂
    exact absurd h₂.symm ENNReal.ofReal_ne_top
  | top =>
    rw [EReal.toENNReal_top] at h₁
    exact absurd h₁.symm ENNReal.ofReal_ne_top
  | coe q =>
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal] at h₂
    rw [EReal.real_coe_toENNReal] at h₁
    have a₁ := congrArg ENNReal.toReal h₁
    have a₂ := congrArg ENNReal.toReal h₂
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at a₁ a₂
    congr 1
    rw [← max_zero_sub_max_neg_zero_eq_self q, ← max_zero_sub_max_neg_zero_eq_self r, a₁, a₂]

/-- If `f ≤ v` pointwise, `v` is integrable, the parts of `f` are a.e.-measurable and
`∫ f dμ = ∫ v dμ`, then `f = v` almost everywhere. -/
theorem ih_ae_eq_of_eint_eq {μ : Measure X} {f : X → EReal} {v : X → ℝ} (hv : Integrable v μ)
    (hle : ∀ x, f x ≤ v x)
    (hf : AEMeasurable (fun x => (f x).toENNReal) μ ∧ AEMeasurable (fun x => (-f x).toENNReal) μ)
    (heq : ih_eint μ f = ih_eint μ (fun x => (v x : EReal))) : ∀ᵐ x ∂μ, f x = v x := by
  rw [ih_eint_coe hv] at heq
  set Pf := ∫⁻ x, (f x).toENNReal ∂μ
  set Nf := ∫⁻ x, (-f x).toENNReal ∂μ
  set Pv := ∫⁻ x, ENNReal.ofReal (v x) ∂μ
  set Nv := ∫⁻ x, ENNReal.ofReal (-v x) ∂μ
  have hPv : Pv ≠ ⊤ := hv.lintegral_lt_top.ne
  have hNv : Nv ≠ ⊤ := hv.neg.lintegral_lt_top.ne
  have l₁ : ∀ x, (f x).toENNReal ≤ ENNReal.ofReal (v x) := fun x =>
    EReal.toENNReal_le_toENNReal (hle x)
  have l₂ : ∀ x, ENNReal.ofReal (-v x) ≤ (-f x).toENNReal := fun x => by
    have := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hle x))
    rwa [← EReal.coe_neg, EReal.real_coe_toENNReal] at this
  have hPle : Pf ≤ Pv := lintegral_mono l₁
  have hNle : Nv ≤ Nf := lintegral_mono l₂
  have hPf : Pf ≠ ⊤ := ne_top_of_le_ne_top hPv hPle
  have hNf : Nf ≠ ⊤ := by
    intro h
    change (Pf : EReal) - Nf = _ at heq
    rw [h, EReal.coe_ennreal_top, EReal.sub_top] at heq
    exact EReal.coe_ne_bot _ heq.symm
  have hint := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hv
  change (Pf : EReal) - Nf = _ at heq
  rw [hint, ← EReal.coe_ennreal_toReal hPf, ← EReal.coe_ennreal_toReal hNf, ← EReal.coe_sub]
    at heq
  have hr := EReal.coe_eq_coe_iff.1 heq
  have t₁ := ENNReal.toReal_mono hPv hPle
  have t₂ := ENNReal.toReal_mono hNf hNle
  have eP : Pv ≤ Pf := by
    rw [← ENNReal.toReal_le_toReal hPv hPf]; linarith
  have eN : Nf ≤ Nv := by
    rw [← ENNReal.toReal_le_toReal hNf hNv]; linarith
  have a₁ := ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ l₁) hPf hv.1.aemeasurable.ennreal_ofReal
    eP
  have a₂ := ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ l₂) hNv hf.2 eN
  filter_upwards [a₁, a₂] with x h₁ h₂
  exact ih_eq_of_parts h₁ h₂.symm

end Miao.InfiniteHorizonDP
