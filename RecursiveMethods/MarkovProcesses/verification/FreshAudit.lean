import Mathlib
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`theorem_8_1`, `theorem_8_1_cor`), Exercise 8.1 (`ex_8_1`),
Theorem 8.2 (`theorem_8_2`), Exercise 8.2 (`ex_8_2`), Theorem 8.3 and its corollary
(`theorem_8_3`, `theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`ex_8_3`), the
`n`-step transition functions and Exercise 8.4 (`kpow`, `ex_8_4a`, `ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
    IsTransitionFunction Q ↔
      ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ ∀ z A, MeasurableSet A → κ z A = Q z A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμQ using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun z => μ z A) = fun z => Q z A := funext fun z => hμQ z A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun z => hμ z⟩, fun z A hA => hμQ z A hA⟩
  · rintro ⟨κ, hκ, hQ⟩
    refine ⟨fun z => ⟨κ z, inferInstance, fun A hA => hQ z A hA⟩, fun A hA => ?_⟩
    have : (fun z => Q z A) = fun z => κ z A := funext fun z => (hQ z A hA).symm
    rw [this]
    exact κ.measurable_coe hA

variable (κ : Kernel Z Z)

/-- The **Markov operator** on nonnegative functions (SLP (1), p. 213):
`(Tf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def markovOp (f : Z → ℝ≥0∞) (z : Z) : ℝ≥0∞ := ∫⁻ z', f z' ∂κ z

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- The **adjoint** `T*` (SLP (2), p. 213): `(T*λ)(A) = ∫ Q(z, A) λ(dz)`. -/
noncomputable def adjointOp (lam : Measure Z) : Measure Z := lam.bind κ

theorem markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (markovOp_indicator κ hs c)
    rw [this]
    exact measurable_const.mul (κ.measurable_coe hs)
  · intro f g hfg hf hg ihf ihg
    have : markovOp κ (f + g) = fun z => markovOp κ f z + markovOp κ g z := funext fun z =>
      lintegral_add_left hf _
    rw [this]
    exact ihf.add ihg
  · intro f hf hmono ih
    have : markovOp κ (fun x => ⨆ n, f n x) = fun z => ⨆ n, markovOp κ (f n) z :=
      funext fun z => lintegral_iSup hf hmono
    rw [this]
    exact Measurable.iSup ih

variable [IsMarkovKernel κ]

theorem integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM)
    rw [heq]
    exact (theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((integrable_of_bounded hf hfM).const_mul α)
    ((integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
  have hTf := theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => integrable_of_bounded (theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    theorem_8_3 κ lam hf.ennreal_ofReal,
    theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    pairing (fun z => a * f z + b * g z) lam = a * pairing f lam + b * pairing g lam ∧
      pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * pairing f lam + (1 - α) * pairing f μ := by
  constructor
  · simp only [pairing]
    rw [integral_add ((integrable_of_bounded hf hfM).const_mul a)
      ((integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [pairing]
    rw [integral_add_measure ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [kpow_add, markovOp_comp _ _ hf]
  · rw [add_comm, kpow_add, adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end StokeyLucasPrescott.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic kernels and iterated integrals

SLP §8.3, pp. 225–234. A stochastic kernel on `{X, 𝒴}` (`IsStochasticKernel`) is a Markov
kernel from `X` to `Y` (`isStochasticKernel_iff`). Theorem 8.4 and its corollary
(`theorem_8_4`, `theorem_8_4_cor`); the direct product `P₁ × P₂` of Theorem 8.5 (`directProd`,
`theorem_8_5`, `theorem_8_5_unique`); the iterated integral formula (4) of Theorem 8.6 and its
corollary (`theorem_8_6`, `theorem_8_6_cor`) and Theorem 8.7 for integrable functions
(`theorem_8_7`); and Exercise 8.9 (`ex_8_9a`, `ex_8_9b`).

The book proves Theorems 8.4–8.6 with the Monotone Class Lemma, starting from measurable
rectangles; the same argument, in π-λ form, is Mathlib's for its kernel composition.
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

/-- A **stochastic kernel** on `{X, 𝒴}` (SLP p. 226): each `P(x, ·)` is a probability measure on
`Y` and each `P(·, B)` is measurable. -/
def IsStochasticKernel (P : X → Set Y → ℝ≥0∞) : Prop :=
  (∀ x, ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ B, MeasurableSet B → μ B = P x B) ∧
    ∀ B, MeasurableSet B → Measurable fun x => P x B

/-- Stochastic kernels are Mathlib's Markov kernels. -/
theorem isStochasticKernel_iff (P : X → Set Y → ℝ≥0∞) :
    IsStochasticKernel P ↔
      ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ ∀ x B, MeasurableSet B → κ x B = P x B := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμP using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun B hB => by
      have : (fun x => μ x B) = fun x => P x B := funext fun x => hμP x B hB
      rw [this]
      exact h2 B hB
    exact ⟨⟨μ, hm⟩, ⟨fun x => hμ x⟩, fun x B hB => hμP x B hB⟩
  · rintro ⟨κ, hκ, hP⟩
    refine ⟨fun x => ⟨κ x, inferInstance, fun B hB => hP x B hB⟩, fun B hB => ?_⟩
    have : (fun x => P x B) = fun x => κ x B := funext fun x => (hP x B hB).symm
    rw [this]
    exact κ.measurable_coe hB

/-- **Theorem 8.4.** For `F ≥ 0` measurable on `X × Y`, `(TF)(x) = ∫ F(x, y) P(x, dy)` is
measurable. -/
theorem theorem_8_4 (P : Kernel X Y) [IsSFiniteKernel P] {F : X × Y → ℝ≥0∞}
    (hF : Measurable F) : Measurable fun x => ∫⁻ y, F (x, y) ∂P x :=
  hF.lintegral_kernel_prod_right'

/-- **Corollary to Theorem 8.4.** For bounded measurable `F`, `TF` is bounded and measurable. -/
theorem theorem_8_4_cor (P : Kernel X Y) [IsMarkovKernel P] {F : X × Y → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ p, |F p| ≤ M) :
    Measurable (fun x => ∫ y, F (x, y) ∂P x) ∧ ∀ x, |∫ y, F (x, y) ∂P x| ≤ M := by
  refine ⟨(hF.stronglyMeasurable.integral_kernel_prod_right' (κ := P)).measurable, fun x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := P x) (C := M) (f := fun y => F (x, y))
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM (x, y))
  simpa [Real.norm_eq_abs, measureReal_def] using this

/-- The **direct product** `P₃ = P₁ × P₂` (SLP p. 229): `P₃(w, ·)` is the law of `(x, y)` when
`x ~ P₁(w, ·)` and then `y ~ P₂(x, ·)`. -/
noncomputable def directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) : Kernel W (X × Y) :=
  P₁ ⊗ₖ Kernel.prodMkLeft W P₂

theorem isMarkovKernel_directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] : IsMarkovKernel (directProd P₁ P₂) := by
  unfold directProd
  infer_instance

/-- **Theorem 8.5.** `P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`, and `P₃` is a stochastic kernel on
`{W, 𝒳 × 𝒴}`. -/
theorem theorem_8_5 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    directProd P₁ P₂ w (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w ∧
      IsMarkovKernel (directProd P₁ P₂) := by
  refine ⟨?_, isMarkovKernel_directProd P₁ P₂⟩
  rw [directProd, Kernel.compProd_apply_prod hA hB]
  rfl

/-- **Theorem 8.5, uniqueness.** A probability measure on `X × Y` with the values (3) on
measurable rectangles is `P₃(w, ·)`. -/
theorem theorem_8_5_unique (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {ν : Measure (X × Y)} [IsProbabilityMeasure ν]
    (hν : ∀ A B, MeasurableSet A → MeasurableSet B → ν (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w) :
    ν = directProd P₁ P₂ w := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [hν A B hA hB, (theorem_8_5 P₁ P₂ w hA hB).1]
  · have := isMarkovKernel_directProd P₁ P₂
    simp

/-- **Theorem 8.6.** For `F ≥ 0` measurable on `X × Y`,
`∫ F dP₃(w, ·) = ∫_X [∫_Y F(x, y) P₂(x, dy)] P₁(w, dx)`. -/
theorem theorem_8_6 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂directProd P₁ P₂ w = ∫⁻ x, ∫⁻ y, F (x, y) ∂P₂ x ∂P₁ w :=
  Kernel.lintegral_compProd _ _ w hF

/-- **Theorem 8.7.** (4) holds for every `F` integrable for `P₃(ŵ, ·)`. -/
theorem theorem_8_7 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ} (hF : Integrable F (directProd P₁ P₂ w)) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w :=
  integral_compProd hF

/-- **Corollary to Theorem 8.6.** (4) holds for bounded measurable `F`. -/
theorem theorem_8_6_cor (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {F : X × Y → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ p, |F p| ≤ M) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w := by
  have := isMarkovKernel_directProd P₁ P₂
  exact theorem_8_7 P₁ P₂ w (integrable_of_bounded hF hM)

/-- **Exercise 8.9a (Product Measure Theorem).** For probability spaces `(X, μ)` and `(Y, ν)`
there is a unique probability measure `λ` on `X × Y` with `λ(A × B) = μ(A)ν(B)`. -/
theorem ex_8_9a (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (IsProbabilityMeasure (μ.prod ν) ∧
      ∀ A B, MeasurableSet A → MeasurableSet B → μ.prod ν (A ×ˢ B) = μ A * ν B) ∧
      ∀ lam : Measure (X × Y), (∀ A B, MeasurableSet A → MeasurableSet B →
        lam (A ×ˢ B) = μ A * ν B) → lam = μ.prod ν :=
  ⟨⟨inferInstance, fun A B _ _ => Measure.prod_prod A B⟩,
    fun _ h => (Measure.prod_eq h).symm⟩

/-- **Exercise 8.9b (Tonelli and Fubini).** The two iterated integrals of a nonnegative
measurable, or a `λ`-integrable, function equal its integral. -/
theorem ex_8_9b (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∀ F : X × Y → ℝ≥0∞, Measurable F →
      ∫⁻ p, F p ∂μ.prod ν = ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ ∧
        ∫⁻ p, F p ∂μ.prod ν = ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν) ∧
      ∀ F : X × Y → ℝ, Integrable F (μ.prod ν) →
        ∫ p, F p ∂μ.prod ν = ∫ x, ∫ y, F (x, y) ∂ν ∂μ ∧
          ∫ p, F p ∂μ.prod ν = ∫ y, ∫ x, F (x, y) ∂μ ∂ν :=
  ⟨fun F hF => ⟨lintegral_prod F hF.aemeasurable, lintegral_prod_symm F hF.aemeasurable⟩,
    fun F hF => ⟨integral_prod F hF, integral_prod_symm F hF⟩⟩

end StokeyLucasPrescott.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

namespace StokeyLucasPrescott.MarkovProcesses

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

end StokeyLucasPrescott.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite histories and Markov processes

SLP §8.2, pp. 220–225. The measure `μ^∞(z₀, ·)` on infinite paths, which the book obtains from
the measures on finite rectangles with an omitted proof of countable additivity (the
Ionescu-Tulcea theorem, here Mathlib's `trajMeasure`): `pathMeasure Q z₀` is the law of the path
`(z₀, z₁, z₂, …)`. Its finite-dimensional distributions are the measures `μᵗ(z₀, ·)` of the finite
histories (`pathMeasure_marginal`), which determine it (`pathMeasure_unique`).

Stochastic processes (`IsStochasticProcess`); the canonical process is one
(`canonical_isStochasticProcess`). The Markov property and stationary transitions of
Exercise 8.6a–b, in the rigorous form: the joint law of the history up to `t` and the next state
is the law of the history composed with `Q(z_t, ·)` (`ex_8_6ab`), so that `Q(z_t, ·)` is a
regular conditional distribution of `z_{t+1}` given `(z₀, …, z_t)` (`ex_8_6ab_condDistrib`);
the book's conditional probabilities given the point events `{σ_τ = a_τ}` are not defined in
general. Exercise 8.6c: shocks drawn independently from `λ` form a stationary process
(`ex_8_6c`). Exercise 8.7: coin tossing (`ex_8_7a`, `ex_8_7b`, `ex_8_7c`).
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- The kernels `(z₀, …, z_n) ↦ Q(z_n, ·)` that drive the path. -/
noncomputable def trajKernel (Q : Kernel Z Z) (n : ℕ) : Kernel (Π _ : Finset.Iic n, Z) Z :=
  Q.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem isMarkovKernel_trajKernel (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    IsMarkovKernel (trajKernel Q n) := by
  unfold trajKernel
  infer_instance

/-- The law of the path `(z₀, z₁, z₂, …)` started at `z₀` (the book's `μ^∞(z₀, ·)`, with the
initial state included as coordinate `0`). -/
noncomputable def pathMeasure (Q : Kernel Z Z) [IsMarkovKernel Q] (z₀ : Z) : Measure (ℕ → Z) :=
  have := isMarkovKernel_trajKernel Q
  Kernel.trajMeasure (X := fun _ => Z) (Measure.dirac z₀) (trajKernel Q)

variable (Q : Kernel Z Z) [IsMarkovKernel Q]

theorem isProbabilityMeasure_pathMeasure (z₀ : Z) : IsProbabilityMeasure (pathMeasure Q z₀) := by
  have := isMarkovKernel_trajKernel Q
  unfold pathMeasure
  infer_instance

/-- The history `(z₁, …, z_T)` of a path. -/
def prefixHist (T : ℕ) (ω : ℕ → Z) : Fin T → Z := fun i => ω (i + 1)

theorem measurable_prefixHist (T : ℕ) : Measurable (prefixHist (Z := Z) T) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The path starts at `z₀`: the law of `z₀` under the path measure is `δ_{z₀}`. -/
theorem pathMeasure_map_zero (z₀ : Z) : (pathMeasure Q z₀).map (frestrictLe 0) =
    Measure.dirac ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm z₀) := by
  have := isMarkovKernel_trajKernel Q
  rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_dirac' (MeasurableEquiv.measurable _)]

/-- **The finite-dimensional distributions of the path are the measures `μᵗ(z₀, ·)`** (SLP
p. 222: `μ^∞(z₀, A₁ × ⋯ × A_T × Z × ⋯) = μᵀ(z₀, A₁ × ⋯ × A_T)`). -/
theorem pathMeasure_marginal (z₀ : Z) (T : ℕ) :
    (pathMeasure Q z₀).map (prefixHist T) = hist Q T z₀ := by
  have := isMarkovKernel_trajKernel Q
  have hP := isProbabilityMeasure_pathMeasure Q z₀
  induction T with
  | zero =>
    have := ex_8_8a Q 0
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have hc : ∀ h : Fin 0 → Z, f h = f Fin.elim0 := fun h => by congr 1; funext i; exact i.elim0
    simp_rw [hc]
    simp
  | succ T ih =>
    have := ex_8_8a Q T
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    let rT : (Π _ : Finset.Iic T, Z) → Fin T → Z := fun y i =>
      y ⟨i + 1, Finset.mem_Iic.2 (by omega)⟩
    have hrT : Measurable rT := measurable_pi_iff.2 fun _ => measurable_pi_apply _
    have hsplit : ∀ ω : ℕ → Z, prefixHist (T + 1) ω =
        Fin.snoc (rT (frestrictLe T ω)) (ω (T + 1)) := by
      intro ω
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [prefixHist]
      · simp [prefixHist, rT, frestrictLe]
    have hmeas : Measurable fun ω : ℕ → Z => (frestrictLe T ω, ω (T + 1)) :=
      (measurable_frestrictLe T).prodMk (measurable_pi_apply _)
    have hG : Measurable fun p : (Π _ : Finset.Iic T, Z) × Z => g (Fin.snoc (rT p.1) p.2) :=
      hg.comp ((measurable_snoc T).comp (hrT.prodMap measurable_id))
    have hkey := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Z) (μ₀ := Measure.dirac z₀) (κ := trajKernel Q) (a := T)
    have hΦ : Measurable fun h : Fin T → Z => ∫⁻ z, g (Fin.snoc h z) ∂Q (lastState z₀ h) := by
      have := isMarkovKernel_nextKernel Q z₀ T
      exact (hg.comp (measurable_snoc T)).lintegral_kernel_prod_right' (κ := nextKernel Q z₀ T)
    rw [lintegral_map hg (measurable_prefixHist _), hist_succ_lintegral_last Q T z₀ hg, ← ih,
      lintegral_map hΦ (measurable_prefixHist _)]
    simp_rw [hsplit]
    rw [← lintegral_map (f := fun p : (Π _ : Finset.Iic T, Z) × Z => g (Fin.snoc (rT p.1) p.2))
      hG hmeas]
    change ∫⁻ p, _ ∂((pathMeasure Q z₀).map _) = _
    rw [pathMeasure] at *
    rw [← hkey, Measure.lintegral_compProd hG]
    have hprefix : ∀ ω : ℕ → Z, prefixHist T ω = rT (frestrictLe T ω) := fun ω => rfl
    simp_rw [hprefix]
    rw [← lintegral_map (f := fun y => ∫⁻ z, g (Fin.snoc (rT y) z) ∂Q (lastState z₀ (rT y)))
      (hΦ.comp hrT) (measurable_frestrictLe T)]
    cases T with
    | zero =>
      have h0 := pathMeasure_map_zero Q z₀
      rw [pathMeasure] at h0
      rw [h0, lintegral_dirac' _ (hG.lintegral_kernel_prod_right' (κ := trajKernel Q 0)),
        lintegral_dirac' (f := fun a => ∫⁻ z, g (Fin.snoc (rT a) z) ∂Q (lastState z₀ (rT a))) _
          (hΦ.comp hrT)]
      rfl
    | succ T =>
      refine lintegral_congr fun y => ?_
      rfl

/-- The book's `μ^∞(z₀, ·)` on the paths `(z₁, z₂, …)` of future states. -/
noncomputable def muInf (z₀ : Z) : Measure (ℕ → Z) :=
  (pathMeasure Q z₀).map fun ω n => ω (n + 1)

/-- `μ^∞(z₀, A₁ × ⋯ × A_T × Z × ⋯) = μᵀ(z₀, A₁ × ⋯ × A_T)` (SLP p. 222). -/
theorem muInf_marginal (z₀ : Z) (T : ℕ) :
    (muInf Q z₀).map (fun ω (i : Fin T) => ω i) = hist Q T z₀ := by
  have h1 : Measurable fun (ω : ℕ → Z) (i : Fin T) => ω (i : ℕ) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have h2 : Measurable fun (ω : ℕ → Z) (n : ℕ) => ω (n + 1) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  rw [muInf, Measure.map_map h1 h2, ← pathMeasure_marginal Q z₀ T]
  rfl

/-- **Uniqueness of `μ^∞`** (SLP p. 222): probability measures on paths with the same
finite-dimensional distributions are equal. -/
theorem pathMeasure_unique {ν ν' : Measure (ℕ → Z)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν']
    (h : ∀ T, ν.map (fun ω (i : Fin T) => ω i) = ν'.map (fun ω (i : Fin T) => ω i)) : ν = ν' := by
  let C : Set (Set (ℕ → Z)) :=
    {S | ∃ T, ∃ B : Set (Fin T → Z), MeasurableSet B ∧ S = (fun ω (i : Fin T) => ω i) ⁻¹' B}
  have hproj : ∀ T, Measurable fun ω : ℕ → Z => fun i : Fin T => ω i := fun T =>
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  refine ext_of_generate_finite C ?_ ?_ ?_ (by simp)
  · apply le_antisymm
    · refine iSup_le fun n => MeasurableSpace.comap_le_iff_le_map.2 fun s hs => ?_
      refine MeasurableSpace.measurableSet_generateFrom ⟨n + 1, (fun x => x ⟨n, by omega⟩) ⁻¹' s,
        measurable_pi_apply _ hs, rfl⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨T, B, hB, rfl⟩
      exact hproj T hB
  · rintro _ ⟨T, B, hB, rfl⟩ _ ⟨T', B', hB', rfl⟩ _
    refine ⟨max T T', (fun x (i : Fin T) => x ⟨i, by omega⟩) ⁻¹' B ∩
      (fun x (i : Fin T') => x ⟨i, by omega⟩) ⁻¹' B', ?_, rfl⟩
    exact ((measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB).inter
      ((measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB')
  · rintro _ ⟨T, B, hB, rfl⟩
    rw [← Measure.map_apply (hproj T) hB, ← Measure.map_apply (hproj T) hB, h T]

/-- A **stochastic process** (SLP p. 223): an increasing sequence of sub-σ-algebras `𝓕ₜ` and
`𝓕ₜ`-measurable functions `σₜ`. -/
def IsStochasticProcess {Ω : Type*} [m : MeasurableSpace Ω] (F : ℕ → MeasurableSpace Ω)
    (σ : ℕ → Ω → Z) : Prop :=
  Monotone F ∧ (∀ t, F t ≤ m) ∧ ∀ t, Measurable[F t] (σ t)

/-- The σ-algebra of the first `t` coordinates of a path. -/
abbrev prefixSigma (t : ℕ) : MeasurableSpace (ℕ → Z) :=
  MeasurableSpace.comap (fun ω (i : Fin t) => ω i) inferInstance

theorem prefixSigma_mono : Monotone (prefixSigma (Z := Z)) := by
  intro s t hst
  refine MeasurableSpace.comap_le_iff_le_map.2 fun B hB => ?_
  refine ⟨(fun x (i : Fin s) => x ⟨i, by omega⟩) ⁻¹' B,
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB, rfl⟩

theorem prefixSigma_le (t : ℕ) : prefixSigma (Z := Z) t ≤ MeasurableSpace.pi :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).comap_le

/-- The canonical process `z̃_t(ω) = ω_t` with `𝓕_t` generated by the first `t` coordinates is a
stochastic process (SLP p. 224). -/
theorem canonical_isStochasticProcess :
    IsStochasticProcess (prefixSigma (Z := Z) ∘ (· + 1)) fun t (ω : ℕ → Z) => ω t := by
  refine ⟨fun s t hst => prefixSigma_mono (Nat.add_le_add_right hst 1),
    fun t => prefixSigma_le _, fun t => ?_⟩
  change Measurable[prefixSigma (t + 1)] ((fun x : Fin (t + 1) → Z => x ⟨t, by omega⟩) ∘
    fun ω (i : Fin (t + 1)) => ω i)
  exact (measurable_pi_apply _).comp (comap_measurable _)

/-- **Exercise 8.6a–b: the Markov property with stationary transitions.** The joint law of the
history `(z₀, …, z_t)` and the next state `z_{t+1}` is the law of the history composed with
`Q(z_t, ·)`: the distribution of `z_{t+1}` given the past depends only on `z_t`, through the same
transition function `Q` at every date. -/
theorem ex_8_6ab (z₀ : Z) (t : ℕ) :
    (pathMeasure Q z₀).map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      (pathMeasure Q z₀).map (frestrictLe t) ⊗ₘ trajKernel Q t := by
  have := isMarkovKernel_trajKernel Q
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure).symm

/-- **Exercise 8.6a–b, conditional form.** `Q(z_t, ·)` is a regular conditional distribution of
`z_{t+1}` given `(z₀, …, z_t)`. -/
theorem ex_8_6ab_condDistrib [StandardBorelSpace Z] [Nonempty Z] (z₀ : Z) (t : ℕ) :
    have := isProbabilityMeasure_pathMeasure Q z₀
    condDistrib (fun ω : ℕ → Z => ω (t + 1)) (frestrictLe t) (pathMeasure Q z₀)
      =ᵐ[(pathMeasure Q z₀).map (frestrictLe t)] trajKernel Q t := by
  have := isMarkovKernel_trajKernel Q
  have := isProbabilityMeasure_pathMeasure Q z₀
  exact Kernel.condDistrib_trajMeasure

/-- With shocks drawn independently from `λ`, `μᵗ(z₀, ·)` does not depend on `z₀`. -/
theorem hist_const (lam : Measure Z) [IsProbabilityMeasure lam] (t : ℕ) (z₀ z₀' : Z) :
    hist (Kernel.const Z lam) t z₀ = hist (Kernel.const Z lam) t z₀' := by
  cases t with
  | zero => rfl
  | succ t => rw [hist_succ_eq_cons, hist_succ_eq_cons]; rfl

/-- The window `(z_{t+1}, …, z_{t+n})` of a history of length `n + t`. -/
def window (t n : ℕ) (h : Fin (n + t) → Z) : Fin n → Z := fun i => h ⟨t + i, by omega⟩

theorem measurable_window (t n : ℕ) : Measurable (window (Z := Z) t n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- **Exercise 8.6c.** If `Q(a, A) = λ(A)` for all `a`, the process is stationary: the law of
`(z_{t+1}, …, z_{t+n})` does not depend on `t`. -/
theorem ex_8_6c (lam : Measure Z) [IsProbabilityMeasure lam] (z₀ : Z) (t n : ℕ) :
    (hist (Kernel.const Z lam) (n + t) z₀).map (window t n) = hist (Kernel.const Z lam) n z₀ := by
  induction t generalizing z₀ with
  | zero =>
    rw [show window (Z := Z) 0 n = id by funext h i; simp [window], Measure.map_id]
    rfl
  | succ t ih =>
    have := ex_8_8a (Kernel.const Z lam) (n + t)
    change ((hist (Kernel.const Z lam) ((n + t) + 1) z₀).map (window (t + 1) n)) = _
    rw [hist_succ_eq_cons,
      Measure.map_map (measurable_window (t + 1) n) (measurable_cons (n + t))]
    have hw : window (t + 1) n ∘ (fun p : Z × (Fin (n + t) → Z) =>
        (Fin.cons p.1 p.2 : Fin (n + t + 1) → Z)) = window t n ∘ Prod.snd := by
      funext p i
      simp only [Function.comp_apply, window]
      have : (⟨t + 1 + i, by omega⟩ : Fin (n + t + 1)) = Fin.succ ⟨t + i, by omega⟩ := by
        ext
        simp
        omega
      rw [this, Fin.cons_succ]
    rw [hw, ← Measure.map_map (measurable_window _ _) measurable_snd]
    change Measure.map (window t n) ((_ ⊗ₘ _).snd) = _
    rw [Measure.snd_compProd]
    have hc : (hist (Kernel.const Z lam) (n + t)) ∘ₘ (Kernel.const Z lam z₀) =
        hist (Kernel.const Z lam) (n + t) z₀ := by
      ext A hA
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
      simp_rw [hist_const lam (n + t) _ z₀]
      simp
    rw [hc, ih]

/-- **Exercise 8.7a.** The σ-algebra `𝓕_t` consists of all sets determined by the first `t`
tosses: `{ω : (ω₁, …, ω_t) ∈ B}` for arbitrary `B ⊆ {H, T}ᵗ`. -/
theorem ex_8_7a (t : ℕ) (S : Set (ℕ → Bool)) :
    MeasurableSet[prefixSigma t] S ↔
      ∃ B : Set (Fin t → Bool), S = (fun ω (i : Fin t) => ω i) ⁻¹' B := by
  constructor
  · rintro ⟨B, -, rfl⟩
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨B, (Set.to_countable B).measurableSet, rfl⟩

/-- The indicator of heads at toss `t` (`t ≥ 1`). -/
def headsAt (t : ℕ) (ω : ℕ → Bool) : ℝ := if t = 0 then 0 else if ω (t - 1) then 1 else 0

/-- **Exercise 8.7b.** `σ_t(ω) = 1` if the `t`-th toss is heads, `0` otherwise, is a stochastic
process. -/
theorem ex_8_7b : IsStochasticProcess (Z := ℝ) prefixSigma headsAt := by
  refine ⟨prefixSigma_mono, prefixSigma_le, fun t => ?_⟩
  unfold headsAt
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact measurable_const
  · simp only [ht, ↓reduceIte]
    have hm : Measurable[prefixSigma t] fun ω : ℕ → Bool => ω (t - 1) := by
      change Measurable[prefixSigma t] ((fun x : Fin t → Bool => x ⟨t - 1, by omega⟩) ∘
        fun ω (i : Fin t) => ω i)
      exact (measurable_pi_apply _).comp (comap_measurable _)
    exact Measurable.ite (hm (measurableSet_singleton true)) measurable_const measurable_const

/-- **Exercise 8.7c.** The number of heads `g_t = Σ_{s ≤ t} σ_s` is a stochastic process. -/
theorem ex_8_7c : IsStochasticProcess (Z := ℝ) prefixSigma
    fun t ω => ∑ s ∈ Finset.range (t + 1), headsAt s ω := by
  refine ⟨prefixSigma_mono, prefixSigma_le, fun t => ?_⟩
  refine Finset.measurable_sum _ fun s hs => ?_
  exact (ex_8_7b.2.2 s).mono (prefixSigma_mono (by simp at hs; omega)) le_rfl

end StokeyLucasPrescott.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transitions defined by stochastic difference equations

SLP §8.4, pp. 234–237. Theorem 8.9: a stochastic difference equation `z_{t+1} = g(z_t, w_t)`
with i.i.d. shocks `w_t ~ μ` defines the transition function `Q(z, A) = μ{w : g(z, w) ∈ A}`
(`theorem_8_9`; its kernel is `sdeKernel`). Exercise 8.10: if `g` is continuous, `Q` has the
Feller property (`ex_8_10`). Exercise 8.11: a second-order process is a first-order process on
the expanded state space `W × W` (`ex_8_11`).
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

/-- **Theorem 8.9.** For a probability measure `μ` on `W` and measurable `g : Z × W → Z`,
`Q(z, A) = μ{w : g(z, w) ∈ A}` is a transition function. The book's proof: `Q(z, ·)` is the
image of `μ` under `g(z, ·)`, and `z ↦ μ([Γ(A)]_z)` is measurable because sections of measurable
sets have measurable measure (a monotone class argument). -/
theorem theorem_8_9 (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) : IsTransitionFunction fun z A => μ {w | g (z, w) ∈ A} := by
  refine ⟨fun z => ⟨μ.map fun w => g (z, w), inferInstance, fun A hA => ?_⟩, fun A hA => ?_⟩
  · have hgz : Measurable fun w => g (z, w) := hg.comp measurable_prodMk_left
    rw [Measure.map_apply hgz hA]
    rfl
  · exact measurable_measure_prodMk_left (hg hA)

/-- The transition kernel of the difference equation `z′ = g(z, w)`, `w ~ μ`. -/
noncomputable def sdeKernel (μ : Measure W) (g : Z × W → Z) : Kernel Z Z :=
  ((Kernel.deterministic id measurable_id) ×ₖ Kernel.const Z μ).map g

theorem sdeKernel_apply (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) (z : Z) : sdeKernel μ g z = μ.map fun w => g (z, w) := by
  rw [sdeKernel, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
  rfl

theorem isMarkovKernel_sdeKernel (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) : IsMarkovKernel (sdeKernel μ g) := by
  unfold sdeKernel
  exact Kernel.IsMarkovKernel.map _ hg

/-- **Exercise 8.10.** If `g` is continuous (on separable metric spaces with their Borel sets),
`Q` has the Feller property: `(Tf)(z) = ∫ f[g(z, w)] μ(dw)`, and `zₙ → z` gives
`∫ f[g(zₙ, w)] μ(dw) → ∫ f[g(z, w)] μ(dw)` by dominated convergence. -/
theorem ex_8_10 [TopologicalSpace Z] [TopologicalSpace W] [SecondCountableTopology Z]
    [SecondCountableTopology W] [BorelSpace Z] [BorelSpace W] (μ : Measure W)
    [IsProbabilityMeasure μ] {g : Z × W → Z} (hg : Continuous g) :
    IsFeller (sdeKernel μ g) := by
  intro f hf ⟨M, hM⟩
  have hgm : Measurable g := hg.measurable
  have heq : markovOpR (sdeKernel μ g) f = fun z => ∫ w, f (g (z, w)) ∂μ := by
    funext z
    have hgz : Measurable fun w => g (z, w) := hgm.comp measurable_prodMk_left
    rw [markovOpR, sdeKernel_apply μ hgm z, integral_map hgz.aemeasurable
      hf.measurable.aestronglyMeasurable]
  rw [heq]
  refine continuous_of_dominated (bound := fun _ => M) (fun z => ?_) (fun z => ?_)
    (integrable_const M) (Eventually.of_forall fun w => ?_)
  · exact (hf.measurable.comp (hgm.comp measurable_prodMk_left)).aestronglyMeasurable
  · exact Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hM _
  · exact hf.comp (hg.comp (continuous_id.prodMk continuous_const))

open Classical in
/-- **Exercise 8.11.** A second-order process `P(w, w′, ·)` on `W` is a first-order process on
`Z = W × W`: there is a unique transition function `Q` on `W × W` with
`Q[(w, w′), A × B] = P(w, w′, B)` if `w′ ∈ A` and `0` otherwise. -/
theorem ex_8_11 (P : Kernel (W × W) W) [IsMarkovKernel P] :
    ∃ κ : Kernel (W × W) (W × W), IsMarkovKernel κ ∧
      (∀ w w' A B, MeasurableSet A → MeasurableSet B →
        κ (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0) ∧
      ∀ κ' : Kernel (W × W) (W × W), IsMarkovKernel κ' →
        (∀ w w' A B, MeasurableSet A → MeasurableSet B →
          κ' (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0) → κ' = κ := by
  let κ : Kernel (W × W) (W × W) := Kernel.deterministic Prod.snd measurable_snd ×ₖ P
  have hκ : IsMarkovKernel κ := inferInstance
  have hval : ∀ w w' A B, MeasurableSet A → MeasurableSet B →
      κ (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0 := by
    intro w w' A B hA hB
    rw [Kernel.prod_apply_prod, Kernel.deterministic_apply' _ _ hA]
    by_cases h : w' ∈ A <;> simp [h]
  refine ⟨κ, hκ, hval, fun κ' hκ' hval' => ?_⟩
  ext ⟨w, w'⟩ : 1
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨A, hA, B, hB, rfl⟩
  rw [hval' w w' A B hA hB, hval w w' A B hA hB]

end StokeyLucasPrescott.MarkovProcesses

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.MarkovProcesses.IsTransitionFunction
#print axioms StokeyLucasPrescott.MarkovProcesses.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.MarkovProcesses.markovOp
#print axioms StokeyLucasPrescott.MarkovProcesses.markovOpR
#print axioms StokeyLucasPrescott.MarkovProcesses.adjointOp
#print axioms StokeyLucasPrescott.MarkovProcesses.markovOp_indicator
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_1
#print axioms StokeyLucasPrescott.MarkovProcesses.integrable_of_bounded
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_1_cor
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_1
#print axioms StokeyLucasPrescott.MarkovProcesses.adjointOp_apply
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_2
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_2
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_3
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_3_cor
#print axioms StokeyLucasPrescott.MarkovProcesses.pairing
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_3
#print axioms StokeyLucasPrescott.MarkovProcesses.kpow
#print axioms StokeyLucasPrescott.MarkovProcesses.kpow_one
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_4a
#print axioms StokeyLucasPrescott.MarkovProcesses.kpow_add
#print axioms StokeyLucasPrescott.MarkovProcesses.markovOp_comp
#print axioms StokeyLucasPrescott.MarkovProcesses.adjointOp_comp
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_4b
#print axioms StokeyLucasPrescott.MarkovProcesses.adjointOp_iterate
#print axioms StokeyLucasPrescott.MarkovProcesses.IsFeller
#print axioms StokeyLucasPrescott.MarkovProcesses.IsMonotoneTF
#print axioms StokeyLucasPrescott.MarkovProcesses.IsStochasticKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.isStochasticKernel_iff
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_4
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_4_cor
#print axioms StokeyLucasPrescott.MarkovProcesses.directProd
#print axioms StokeyLucasPrescott.MarkovProcesses.isMarkovKernel_directProd
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_5
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_5_unique
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_6
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_7
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_6_cor
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_9a
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_9b
#print axioms StokeyLucasPrescott.MarkovProcesses.measurable_cons
#print axioms StokeyLucasPrescott.MarkovProcesses.measurable_snoc
#print axioms StokeyLucasPrescott.MarkovProcesses.lastState
#print axioms StokeyLucasPrescott.MarkovProcesses.measurable_lastState
#print axioms StokeyLucasPrescott.MarkovProcesses.lastState_cons
#print axioms StokeyLucasPrescott.MarkovProcesses.lastState_snoc
#print axioms StokeyLucasPrescott.MarkovProcesses.hist
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_8a
#print axioms StokeyLucasPrescott.MarkovProcesses.hist_zero_lintegral
#print axioms StokeyLucasPrescott.MarkovProcesses.hist_succ_lintegral
#print axioms StokeyLucasPrescott.MarkovProcesses.iterLInt
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_8
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_5
#print axioms StokeyLucasPrescott.MarkovProcesses.nextKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.isMarkovKernel_nextKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.nextKernel_apply
#print axioms StokeyLucasPrescott.MarkovProcesses.hist_succ_lintegral_last
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_8b
#print axioms StokeyLucasPrescott.MarkovProcesses.hist_succ_eq_cons
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_8c_last
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_8c_first
#print axioms StokeyLucasPrescott.MarkovProcesses.iterInt
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_8_integrable
#print axioms StokeyLucasPrescott.MarkovProcesses.trajKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.isMarkovKernel_trajKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.pathMeasure
#print axioms StokeyLucasPrescott.MarkovProcesses.isProbabilityMeasure_pathMeasure
#print axioms StokeyLucasPrescott.MarkovProcesses.prefixHist
#print axioms StokeyLucasPrescott.MarkovProcesses.measurable_prefixHist
#print axioms StokeyLucasPrescott.MarkovProcesses.pathMeasure_map_zero
#print axioms StokeyLucasPrescott.MarkovProcesses.pathMeasure_marginal
#print axioms StokeyLucasPrescott.MarkovProcesses.muInf
#print axioms StokeyLucasPrescott.MarkovProcesses.muInf_marginal
#print axioms StokeyLucasPrescott.MarkovProcesses.pathMeasure_unique
#print axioms StokeyLucasPrescott.MarkovProcesses.IsStochasticProcess
#print axioms StokeyLucasPrescott.MarkovProcesses.prefixSigma
#print axioms StokeyLucasPrescott.MarkovProcesses.prefixSigma_mono
#print axioms StokeyLucasPrescott.MarkovProcesses.prefixSigma_le
#print axioms StokeyLucasPrescott.MarkovProcesses.canonical_isStochasticProcess
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_6ab
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_6ab_condDistrib
#print axioms StokeyLucasPrescott.MarkovProcesses.hist_const
#print axioms StokeyLucasPrescott.MarkovProcesses.window
#print axioms StokeyLucasPrescott.MarkovProcesses.measurable_window
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_6c
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_7a
#print axioms StokeyLucasPrescott.MarkovProcesses.headsAt
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_7b
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_7c
#print axioms StokeyLucasPrescott.MarkovProcesses.theorem_8_9
#print axioms StokeyLucasPrescott.MarkovProcesses.sdeKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.sdeKernel_apply
#print axioms StokeyLucasPrescott.MarkovProcesses.isMarkovKernel_sdeKernel
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_10
#print axioms StokeyLucasPrescott.MarkovProcesses.ex_8_11
