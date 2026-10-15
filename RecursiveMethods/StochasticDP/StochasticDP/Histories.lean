/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.StochasticKernels

/-!
# Measures on spaces of finite histories

SLP §8.2–8.3, pp. 220–234. For a transition function `Q` and an initial state `z₀`, the
probability measure `μᵗ(z₀, ·)` on histories `zᵗ = (z₁, …, z_t) ∈ Zᵗ` (`hist Q t`), built as the
book does: first `z₁ ~ Q(z₀, ·)`, then the history from `z₁` (`hist_succ_lintegral`).

* Theorem 8.8: `∫ F dμᵗ(z₀, ·)` is the iterated integral
  `∫ Q(z₀, dz₁) ∫ Q(z₁, dz₂) ⋯ ∫ Q(z_{t−1}, dz_t) F(z₁, …, z_t)` (`iterLInt`, `theorem_8_8`, and
  `iterInt`, `theorem_8_8_integrable` for integrable `F`).
* Exercise 8.5: on rectangles `μᵗ` is given by that formula, it is countably additive and
  `μᵗ(z₀, Zᵗ) = 1` (`ex_8_5`).
* Exercise 8.8: `μᵗ(·, ·)` is a stochastic kernel (`ex_8_8a`); `Q × μᵗ⁻¹ = μᵗ = μᵗ⁻¹ × Q`, i.e. the
  history splits at its first or at its last date (`hist_succ_eq_cons`, `ex_8_8b`); and the
  integral splits accordingly, (1a) and (1b) (`ex_8_8c_last`, `ex_8_8c_first`).

`lastState z₀ zᵗ` is the most recent state: `z₀` if `t = 0`, otherwise `z_t`.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

theorem measurable_cons (t : ℕ) :
    Measurable fun p : Z × (Fin t → Z) => (Fin.cons p.1 p.2 : Fin (t + 1) → Z) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_snoc (t : ℕ) :
    Measurable fun p : (Fin t → Z) × Z => (Fin.snoc p.1 p.2 : Fin (t + 1) → Z) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The most recent state of a history started at `z₀`: `z₀` for the empty history, otherwise
the last entry. -/
def lastState (z₀ : Z) : {t : ℕ} → (Fin t → Z) → Z
  | 0, _ => z₀
  | t + 1, h => h (Fin.last t)

theorem measurable_lastState (z₀ : Z) (t : ℕ) : Measurable (lastState z₀ (t := t)) := by
  cases t with
  | zero => exact measurable_const
  | succ t => exact measurable_pi_apply _

omit [MeasurableSpace Z] in
theorem lastState_cons (z₀ z₁ : Z) {t : ℕ} (h : Fin t → Z) :
    lastState z₀ (Fin.cons z₁ h : Fin (t + 1) → Z) = lastState z₁ h := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [lastState]
    rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace Z] in
theorem lastState_snoc (z₀ z : Z) {t : ℕ} (h : Fin t → Z) :
    lastState z₀ (Fin.snoc h z : Fin (t + 1) → Z) = z := by
  simp [lastState]

variable (Q : Kernel Z Z) [IsMarkovKernel Q]

/-- `μᵗ(z₀, ·)`: the distribution of the history `(z₁, …, z_t)` (SLP p. 221). -/
noncomputable def hist (Q : Kernel Z Z) : (t : ℕ) → Kernel Z (Fin t → Z)
  | 0 => Kernel.const Z (Measure.dirac Fin.elim0)
  | t + 1 => ((Kernel.id ×ₖ hist Q t).map fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → Z)) ∘ₖ Q

/-- **Exercise 8.8a.** `μᵗ` is a stochastic kernel on `{Z, 𝒵ᵗ}`. -/
theorem ex_8_8a (t : ℕ) : IsMarkovKernel (hist Q t) := by
  induction t with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.const Z _))
  | succ t ih =>
    have : IsMarkovKernel ((Kernel.id ×ₖ hist Q t).map fun p =>
        (Fin.cons p.1 p.2 : Fin (t + 1) → Z)) :=
      Kernel.IsMarkovKernel.map _ (measurable_cons t)
    exact inferInstanceAs (IsMarkovKernel (_ ∘ₖ Q))

omit [IsMarkovKernel Q] in
theorem hist_zero_lintegral (z₀ : Z) (f : (Fin 0 → Z) → ℝ≥0∞) :
    ∫⁻ h, f h ∂hist Q 0 z₀ = f Fin.elim0 := by
  simp [hist, lintegral_dirac]

/-- **The first-date decomposition** (SLP p. 221, and the identity `μᵗ = Q × μᵗ⁻¹` of
Exercise 8.8b): `∫ f dμᵗ⁺¹(z₀, ·) = ∫ [∫ f(z₁, zᵗ) μᵗ(z₁, dzᵗ)] Q(z₀, dz₁)`. -/
theorem hist_succ_lintegral (t : ℕ) (z₀ : Z) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂hist Q (t + 1) z₀ = ∫⁻ z₁, ∫⁻ h, f (Fin.cons z₁ h) ∂hist Q t z₁ ∂Q z₀ := by
  have := ex_8_8a Q t
  rw [hist, Kernel.lintegral_comp _ _ _ hf]
  refine lintegral_congr fun z₁ => ?_
  rw [Kernel.lintegral_map _ (measurable_cons t) _ hf, Kernel.lintegral_prod _ _ _
    (g := fun p : Z × (Fin t → Z) => f (Fin.cons p.1 p.2)) (hf.comp (measurable_cons t)),
    Kernel.id_apply, lintegral_dirac']
  exact (hf.comp (measurable_cons t)).lintegral_prod_right'

/-- The iterated integral `∫ Q(z₀, dz₁) ∫ Q(z₁, dz₂) ⋯ ∫ Q(z_{t−1}, dz_t) F(z₁, …, z_t)`. -/
noncomputable def iterLInt : (t : ℕ) → ((Fin t → Z) → ℝ≥0∞) → Z → ℝ≥0∞
  | 0, F, _ => F Fin.elim0
  | t + 1, F, z₀ => ∫⁻ z₁, iterLInt t (fun h => F (Fin.cons z₁ h)) z₁ ∂Q z₀

/-- **Theorem 8.8** (nonnegative functions). -/
theorem theorem_8_8 (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂hist Q t z₀ = iterLInt Q t F z₀ := by
  induction t generalizing z₀ with
  | zero => exact hist_zero_lintegral Q z₀ F
  | succ t ih =>
    rw [hist_succ_lintegral Q t z₀ hF, iterLInt]
    refine lintegral_congr fun z₁ => ?_
    exact ih z₁ (hF.comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id)))

/-- **Exercise 8.5.** On a measurable rectangle `A₁ × ⋯ × A_t`, `μᵗ(z₀, ·)` is the iterated
integral of its indicator; `μᵗ(z₀, ·)` is countably additive on rectangles; and
`μᵗ(z₀, Zᵗ) = 1`. -/
theorem ex_8_5 (t : ℕ) (z₀ : Z) {A : Fin t → Set Z} (hA : ∀ i, MeasurableSet (A i)) :
    hist Q t z₀ (Set.pi univ A) = iterLInt Q t ((Set.pi univ A).indicator 1) z₀ ∧
      (∀ C : ℕ → Set (Fin t → Z), (∀ n, MeasurableSet (C n)) →
        Pairwise (Function.onFun Disjoint C) →
          hist Q t z₀ (⋃ n, C n) = ∑' n, hist Q t z₀ (C n)) ∧
      hist Q t z₀ univ = 1 := by
  have := ex_8_8a Q t
  have hpi : MeasurableSet (Set.pi univ A) := MeasurableSet.univ_pi hA
  refine ⟨?_, fun C hC hd => measure_iUnion hd hC, measure_univ⟩
  rw [← theorem_8_8 Q t z₀ (measurable_one.indicator hpi), lintegral_indicator_one hpi]

/-- The kernel `zᵗ ↦ Q(z_t, ·)` of the next state given a history started at `z₀`. -/
noncomputable def nextKernel (z₀ : Z) (t : ℕ) : Kernel (Fin t → Z) Z :=
  Q.comap (lastState z₀) (measurable_lastState z₀ t)

theorem isMarkovKernel_nextKernel (z₀ : Z) (t : ℕ) : IsMarkovKernel (nextKernel Q z₀ t) := by
  unfold nextKernel
  infer_instance

omit [IsMarkovKernel Q] in
theorem nextKernel_apply (z₀ : Z) (t : ℕ) (h : Fin t → Z) :
    nextKernel Q z₀ t h = Q (lastState z₀ h) := rfl

/-- **The last-date decomposition** (the identity `μᵗ = μᵗ⁻¹ × Q` of Exercise 8.8b):
`∫ f dμᵗ⁺¹(z₀, ·) = ∫ [∫ f(zᵗ, z′) Q(z_t, dz′)] μᵗ(z₀, dzᵗ)`. -/
theorem hist_succ_lintegral_last (t : ℕ) (z₀ : Z) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂hist Q (t + 1) z₀ =
      ∫⁻ h, ∫⁻ z', f (Fin.snoc h z') ∂Q (lastState z₀ h) ∂hist Q t z₀ := by
  induction t generalizing z₀ with
  | zero =>
    rw [hist_succ_lintegral Q 0 z₀ hf, hist_zero_lintegral]
    refine lintegral_congr fun z₁ => ?_
    rw [hist_zero_lintegral]
    congr 1
    funext i
    fin_cases i
    rfl
  | succ t ih =>
    have hfc : ∀ z₁ : Z, Measurable fun h : Fin (t + 1) → Z => f (Fin.cons z₁ h) := fun z₁ =>
      hf.comp ((measurable_cons (t + 1)).comp (measurable_const.prodMk measurable_id))
    have := isMarkovKernel_nextKernel Q z₀ (t + 1)
    have hg : Measurable fun h : Fin (t + 1) → Z =>
        ∫⁻ z', f (Fin.snoc h z') ∂Q (lastState z₀ h) := by
      have := (hf.comp (measurable_snoc (t + 1))).lintegral_kernel_prod_right'
        (κ := nextKernel Q z₀ (t + 1))
      exact this
    rw [hist_succ_lintegral Q (t + 1) z₀ hf, hist_succ_lintegral Q t z₀ hg]
    refine lintegral_congr fun z₁ => ?_
    rw [ih z₁ (hfc z₁)]
    refine lintegral_congr fun h' => ?_
    rw [lastState_cons]
    refine lintegral_congr fun z' => ?_
    rw [Fin.cons_snoc_eq_snoc_cons]

/-- **Exercise 8.8b** as an identity of measures: `μᵗ⁺¹(z₀, ·)` is the image under
`(zᵗ, z′) ↦ (zᵗ, z′)` of `μᵗ(z₀, ·) ⊗ Q(z_t, ·)`. -/
theorem ex_8_8b (t : ℕ) (z₀ : Z) :
    hist Q (t + 1) z₀ =
      ((hist Q t z₀) ⊗ₘ nextKernel Q z₀ t).map fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → Z) := by
  have := ex_8_8a Q t
  have := isMarkovKernel_nextKernel Q z₀ t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [hist_succ_lintegral_last Q t z₀ hf, lintegral_map hf (measurable_snoc t),
    Measure.lintegral_compProd (f := fun p : (Fin t → Z) × Z => f (Fin.snoc p.1 p.2))
      (hf.comp (measurable_snoc t))]
  rfl

/-- The first-date decomposition as an identity of measures: `μᵗ⁺¹(z₀, ·)` is the image under
`(z₁, zᵗ) ↦ (z₁, zᵗ)` of `Q(z₀, ·) ⊗ μᵗ(z₁, ·)`. -/
theorem hist_succ_eq_cons (t : ℕ) (z₀ : Z) :
    hist Q (t + 1) z₀ =
      ((Q z₀) ⊗ₘ hist Q t).map fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → Z) := by
  have := ex_8_8a Q t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [hist_succ_lintegral Q t z₀ hf, lintegral_map hf (measurable_cons t),
    Measure.lintegral_compProd (f := fun p : Z × (Fin t → Z) => f (Fin.cons p.1 p.2))
      (hf.comp (measurable_cons t))]

/-- **Exercise 8.8c, (1a).** For `μᵗ⁺¹(z₀, ·)`-integrable `F`,
`∫ F dμᵗ⁺¹ = ∫ [∫ F(zᵗ, z′) Q(z_t, dz′)] μᵗ(z₀, dzᵗ)`. -/
theorem ex_8_8c_last (t : ℕ) (z₀ : Z) {F : (Fin (t + 1) → Z) → ℝ}
    (hF : Integrable F (hist Q (t + 1) z₀)) :
    ∫ h, F h ∂hist Q (t + 1) z₀ =
      ∫ h, ∫ z', F (Fin.snoc h z') ∂Q (lastState z₀ h) ∂hist Q t z₀ := by
  have := ex_8_8a Q t
  have := isMarkovKernel_nextKernel Q z₀ t
  rw [ex_8_8b Q t z₀] at hF ⊢
  have hF' := (integrable_map_measure hF.1 (measurable_snoc t).aemeasurable).1 hF
  rw [integral_map (measurable_snoc t).aemeasurable hF.1,
    Measure.integral_compProd (f := fun p : (Fin t → Z) × Z => F (Fin.snoc p.1 p.2)) hF']
  rfl

/-- **Exercise 8.8c, (1b).** For `μᵗ⁺¹(z₀, ·)`-integrable `F`,
`∫ F dμᵗ⁺¹ = ∫ [∫ F(z₁, zᵗ) μᵗ(z₁, dzᵗ)] Q(z₀, dz₁)`. -/
theorem ex_8_8c_first (t : ℕ) (z₀ : Z) {F : (Fin (t + 1) → Z) → ℝ}
    (hF : Integrable F (hist Q (t + 1) z₀)) :
    ∫ h, F h ∂hist Q (t + 1) z₀ = ∫ z₁, ∫ h, F (Fin.cons z₁ h) ∂hist Q t z₁ ∂Q z₀ := by
  have := ex_8_8a Q t
  rw [hist_succ_eq_cons Q t z₀] at hF ⊢
  have hF' := (integrable_map_measure hF.1 (measurable_cons t).aemeasurable).1 hF
  rw [integral_map (measurable_cons t).aemeasurable hF.1,
    Measure.integral_compProd (f := fun p : Z × (Fin t → Z) => F (Fin.cons p.1 p.2)) hF']

/-- The iterated integral of a real function. -/
noncomputable def iterInt : (t : ℕ) → ((Fin t → Z) → ℝ) → Z → ℝ
  | 0, F, _ => F Fin.elim0
  | t + 1, F, z₀ => ∫ z₁, iterInt t (fun h => F (Fin.cons z₁ h)) z₁ ∂Q z₀

/-- **Theorem 8.8** (integrable functions). -/
theorem theorem_8_8_integrable (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : Integrable F (hist Q t z₀)) : ∫ h, F h ∂hist Q t z₀ = iterInt Q t F z₀ := by
  induction t generalizing z₀ with
  | zero => simp [hist, iterInt]
  | succ t ih =>
    have := ex_8_8a Q t
    rw [ex_8_8c_first Q t z₀ hF, iterInt]
    rw [hist_succ_eq_cons Q t z₀] at hF
    have hF' := (integrable_map_measure hF.1 (measurable_cons t).aemeasurable).1 hF
    have hae := (Measure.integrable_compProd_iff hF'.1).1 hF'
    refine integral_congr_ae (hae.1.mono fun z₁ hz₁ => ?_)
    exact ih z₁ hz₁

end StokeyLucasPrescott.StochasticDP
