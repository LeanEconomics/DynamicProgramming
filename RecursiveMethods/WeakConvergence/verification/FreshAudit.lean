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

namespace StokeyLucasPrescott.WeakConvergence

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

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence: basic tools

SLP §12.1, pp. 353–358. `(S, ρ)` is a metric space with its Borel sets.

* **Exercise 12.1** (`ex_12_1`): for a Borel `S ⊆ ℝˡ`, the Borel sets of `S` are the Borel sets of
  `ℝˡ` contained in `S`; relatively open sets are traces of open sets; relative interiors are
  relatively open; and an open set is its own interior.
* **Exercise 12.2** (`ex_12_2`): the distance `ρ(s, A)` is `1`-Lipschitz, hence uniformly
  continuous, and `Ā = {s : ρ(s, A) = 0}` for nonempty `A`.
* `ConvWeak` (p. 354): `λₙ ⇒ λ` if `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f`.
* **Lemma 12.1** (`lemma_12_1`): for a closed `F` the continuous functions
  `fₙ(s) = max(0, 1 − n ρ(s, F))` decrease, equal `1` on `F`, lie in `[0, 1]`, and
  `∫ fₙ dλ → λ(F)` for every probability measure `λ`. The book proves the limit with the sets
  `Fₙ = {ρ(·, F) ≤ 1/n}`; here dominated convergence is used.
* **Lemma 12.2** (`lemma_12_2`): for measurable `a ≤ f < b`, the sets `Fᵢ = {f ≥ a + ic/k}` give
  `a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. The `Fᵢ` are
  closed if `f` is continuous. The book sums by parts; here the pointwise inequality
  `m/k ≤ g < (m + 1)/k`, with `m = #{i ≤ k : i/k ≤ g}`, is integrated.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-- **Exercise 12.1.** For a Borel set `S ⊆ ℝˡ`: (a) the Borel sets of `S` are the Borel subsets
of `ℝˡ` contained in `S`; (b) the relatively open sets are the traces `A′ ∩ S` of open sets;
(c) relative interiors are relatively open; (d) a relatively open set is its own interior. -/
theorem ex_12_1 {l : ℕ} {S : Set (Fin l → ℝ)} (hS : MeasurableSet S) :
    (∀ A : Set S, MeasurableSet A ↔ MeasurableSet (Subtype.val '' A)) ∧
      (∀ A : Set S, IsOpen A ↔ ∃ A' : Set (Fin l → ℝ), IsOpen A' ∧ Subtype.val ⁻¹' A' = A) ∧
      (∀ A : Set S, IsOpen (interior A)) ∧ ∀ A : Set S, IsOpen A → interior A = A := by
  refine ⟨fun A => ⟨fun hA => hS.subtype_image hA, fun hA => ?_⟩, fun A => isOpen_induced_iff,
    fun A => isOpen_interior, fun A hA => hA.interior_eq⟩
  have := (measurable_subtype_coe (p := fun x => x ∈ S)) hA
  rwa [Subtype.val_injective.preimage_image] at this

variable {S : Type*} [MetricSpace S]

/-- **Exercise 12.2.** (a) `|ρ(x, A) − ρ(y, A)| ≤ ρ(x, y)`; (b) `ρ(·, A)` is uniformly
continuous; (c) for nonempty `A`, `Ā = {s : ρ(s, A) = 0}`. -/
theorem ex_12_2 (A : Set S) :
    (∀ x y, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y) ∧
      UniformContinuous (fun s => Metric.infDist s A) ∧
      (A.Nonempty → closure A = {s | Metric.infDist s A = 0}) := by
  refine ⟨fun x y => ?_, (Metric.lipschitz_infDist_pt A).uniformContinuous, fun hA => ?_⟩
  · have := (Metric.lipschitz_infDist_pt A).dist_le_mul x y
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
  · ext s; exact Metric.mem_closure_iff_infDist_zero hA

/-- The functions of Lemma 12.1: `fₙ(s) = max(0, 1 − (n + 1) ρ(s, F))`. -/
noncomputable def bump (F : Set S) (n : ℕ) (s : S) : ℝ :=
  max 0 (1 - (n + 1) * Metric.infDist s F)

theorem continuous_bump (F : Set S) (n : ℕ) : Continuous (bump F n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (Metric.continuous_infDist_pt F)))

theorem bump_mem (F : Set S) (n : ℕ) (s : S) : 0 ≤ bump F n s ∧ bump F n s ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by
    have := Metric.infDist_nonneg (x := s) (s := F)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩

theorem bump_eq_one {F : Set S} {s : S} (hs : s ∈ F) (n : ℕ) : bump F n s = 1 := by
  simp [bump, Metric.infDist_zero_of_mem hs]

theorem bump_antitone (F : Set S) (s : S) : Antitone fun n => bump F n s := fun m n hmn => by
  refine max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_right ?_
    Metric.infDist_nonneg) 1)
  exact_mod_cast Nat.succ_le_succ hmn

/-- `fₙ → 1_F` pointwise for closed nonempty `F`. -/
theorem tendsto_bump {F : Set S} (hF : IsClosed F) (hne : F.Nonempty) (s : S) :
    Tendsto (fun n => bump F n s) atTop (𝓝 (F.indicator 1 s)) := by
  by_cases hs : s ∈ F
  · simp [bump_eq_one hs, indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hpos : 0 < Metric.infDist s F :=
      (hF.notMem_iff_infDist_pos hne).1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist s F)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have : 1 ≤ (n + 1) * Metric.infDist s F := by
      rw [div_lt_iff₀ hpos] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp only [bump]
    exact (max_eq_left (by linarith)).symm

variable [MeasurableSpace S] [BorelSpace S]

/-- `λₙ` **converges weakly** to `λ` (p. 354): `∫ f dλₙ → ∫ f dλ` for every bounded continuous
`f`. -/
def ConvWeak (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- **Lemma 12.1.** For a closed set `F` there are continuous `fₙ`, decreasing in `n`, with
`fₙ = 1` on `F`, `0 ≤ fₙ ≤ 1`, and `∫ fₙ dλ → λ(F)` for every probability measure `λ`. -/
theorem lemma_12_1 {F : Set S} (hF : IsClosed F) :
    ∃ f : ℕ → S → ℝ, (∀ n, Continuous (f n)) ∧ (∀ s, Antitone fun n => f n s) ∧
      (∀ n, ∀ s ∈ F, f n s = 1) ∧ (∀ n s, 0 ≤ f n s ∧ f n s ≤ 1) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        Tendsto (fun n => ∫ s, f n s ∂μ) atTop (𝓝 (μ.real F)) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ _ _ _ => le_rfl, fun _ s hs => hs.elim,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, fun μ _ => by simp⟩
  refine ⟨bump F, continuous_bump F, bump_antitone F, fun n s hs => bump_eq_one hs n,
    bump_mem F, fun μ _ => ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := bump F)
    (f := F.indicator 1) (fun _ => 1)
    (fun n => (continuous_bump F n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (bump_mem F n s).1]; exact (bump_mem F n s).2)
    (Eventually.of_forall fun s => tendsto_bump hF hne s)
  rwa [integral_indicator_one hF.measurableSet] at hlim

/-- For `0 ≤ g < 1` and `m = #{1 ≤ i ≤ k : i/k ≤ g}`: `m/k ≤ g < (m + 1)/k`. -/
theorem count_bounds {k : ℕ} (hk : 1 ≤ k) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card : ℝ) / k ≤ g ∧
      g < (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card + 1 : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkg : 0 ≤ k * g := mul_nonneg hk'.le hg0
  have hfloor : ⌊(k : ℝ) * g⌋₊ ≤ k := by
    have : (k : ℝ) * g < k := by nlinarith
    exact_mod_cast (Nat.floor_le hkg).trans this.le
  have hset : ((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g) =
      Finset.Icc 1 ⌊(k : ℝ) * g⌋₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [div_le_iff₀ hk', mul_comm g, ← Nat.le_floor_iff hkg]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hfloor⟩, h3⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  constructor
  · rw [div_le_iff₀ hk']; have := Nat.floor_le hkg; linarith [mul_comm (k : ℝ) g]
  · rw [lt_div_iff₀ hk', mul_comm]; exact Nat.lt_floor_add_one _

omit [BorelSpace S] in
/-- **Lemma 12.2.** For measurable `f` with `a ≤ f < b`, `c = b − a`, and `ε > 0`, there are `k ≥ 1`
and sets `Fᵢ = {f ≥ a + ic/k}`, `1 ≤ i ≤ k`, independent of `μ`, with
`a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. If `f` is
continuous the `Fᵢ` are closed. -/
theorem lemma_12_2 {f : S → ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ s, a ≤ f s ∧ f s < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ F : ℕ → Set S, (∀ i, MeasurableSet (F i)) ∧
      (Continuous f → ∀ i, IsClosed (F i)) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) ≤ ∫ s, f s ∂μ ∧
          ∫ s, f s ∂μ ≤ a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) + ε := by
  set k := ⌈(b - a) / ε⌉₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set F : ℕ → Set S := fun i => {s | a + (b - a) * i / k ≤ f s}
  refine ⟨k, hk, F, fun i => measurableSet_le measurable_const hf,
    fun hc i => isClosed_le continuous_const hc, fun μ _ => ?_⟩
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hba : 0 < b - a := by have := hab s₀; linarith
  have hck : (b - a) / k ≤ ε := by
    rw [div_le_iff₀ hk']
    have := Nat.le_ceil ((b - a) / ε)
    rw [div_le_iff₀ hε] at this
    have : (⌈(b - a) / ε⌉₊ : ℝ) ≤ k := by simp [k]
    nlinarith
  -- the pointwise inequality, with `g = (f − a)/(b − a)`
  set cnt : S → ℝ := fun s => ∑ i ∈ Finset.Icc 1 k, (F i).indicator 1 s
  have hcnt : ∀ s, cnt s = (((Finset.Icc 1 k).filter fun i : ℕ =>
      (i : ℝ) / k ≤ (f s - a) / (b - a)).card : ℝ) := fun s => by
    simp only [cnt, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : a + (b - a) * i / k ≤ f s ↔ (i : ℝ) / k ≤ (f s - a) / (b - a) := by
      have e : (b - a) * (i : ℝ) / k = (i : ℝ) / k * (b - a) := by ring
      rw [le_div_iff₀ hba, ← e]; constructor <;> intro h <;> linarith
    by_cases h : a + (b - a) * i / k ≤ f s
    · have hm : s ∈ F i := h
      simp [Set.indicator_of_mem hm, this.1 h]
    · have hm : s ∉ F i := h
      have h2 : ¬ ((i : ℝ) / k ≤ (f s - a) / (b - a)) := fun h' => h (this.2 h')
      simp [Set.indicator_of_notMem hm, h2]
  have hpt : ∀ s, (b - a) / k * cnt s ≤ f s - a ∧ f s - a ≤ (b - a) / k * cnt s + (b - a) / k := by
    intro s
    obtain ⟨h1, h2⟩ := hab s
    obtain ⟨c1, c2⟩ := count_bounds hk (g := (f s - a) / (b - a)) (div_nonneg (by linarith) hba.le)
      ((div_lt_one hba).2 (by linarith))
    rw [hcnt]
    constructor
    · calc (b - a) / k * _ = (b - a) * (_ / k) := by ring
        _ ≤ (b - a) * ((f s - a) / (b - a)) := mul_le_mul_of_nonneg_left c1 hba.le
        _ = f s - a := by field_simp
    · calc f s - a = (b - a) * ((f s - a) / (b - a)) := by field_simp
        _ ≤ (b - a) * ((_ + 1) / k) := mul_le_mul_of_nonneg_left c2.le hba.le
        _ = _ := by ring
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable (|a| + |b|)
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; obtain ⟨h1, h2⟩ := hab s
      constructor <;> linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b])
  have hci : Integrable cnt μ := integrable_finsetSum _ fun i _ =>
    (integrable_const 1).indicator (measurableSet_le measurable_const hf)
  have hint_cnt : ∫ s, cnt s ∂μ = ∑ i ∈ Finset.Icc 1 k, μ.real (F i) := by
    rw [integral_finsetSum _ fun i _ => (integrable_const 1).indicator
      (measurableSet_le measurable_const hf)]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one
      (measurableSet_le measurable_const hf)
  have hfa : Integrable (fun s => f s - a) μ := hfi.sub (integrable_const a)
  have hca : Integrable (fun s => (b - a) / k * cnt s + (b - a) / k) μ :=
    (hci.const_mul _).add (integrable_const _)
  have hlo := integral_mono (hci.const_mul ((b - a) / k)) hfa fun s => (hpt s).1
  have hhi := integral_mono hfa hca fun s => (hpt s).2
  rw [integral_const_mul, hint_cnt, integral_sub hfi (integrable_const a)] at hlo
  rw [integral_add (hci.const_mul _) (integrable_const _), integral_const_mul, hint_cnt,
    integral_sub hfi (integrable_const a)] at hhi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlo hhi
  constructor <;> linarith

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Characterizations of weak convergence

SLP §12.1, Theorem 12.3, pp. 358–360. For probability measures `λₙ`, `λ` on a metric space the
following are equivalent (`theorem_12_3`):

* (a) `λₙ ⇒ λ`;
* (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`;
* (c) `liminf λₙ(G) ≥ λ(G)` for open `G`;
* (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`.

`limsup ≤` and `liminf ≥` are written as: for every `ε > 0`, eventually `λₙ(F) < λ(F) + ε`
(`LimsupLe`), respectively `λₙ(G) > λ(G) − ε`. The proofs follow the book: (a) ⇒ (b) by
Lemma 12.1, (b) ⇒ (a) by Lemma 12.2, (b) ⇔ (c) by complements, (b) ⇒ (d) through the interior and
the closure, and (d) ⇒ (b) through thickenings with null boundaries.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- `limsup uₙ ≤ c`, written without `limsup`. -/
def LimsupLe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, u n < c + ε

/-- `liminf uₙ ≥ c`, written without `liminf`. -/
def LiminfGe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, c - ε < u n

theorem tendsto_of_limsup_liminf {u : ℕ → ℝ} {c : ℝ} (h1 : LimsupLe u c) (h2 : LiminfGe u c) :
    Tendsto u atTop (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [h2 (c - a) (by linarith)] with n hn; linarith
  · filter_upwards [h1 (a - c) (by linarith)] with n hn; linarith

/-- A continuous function with values in `[0, 1]` as a bounded continuous function. -/
noncomputable def toBCF {f : S → ℝ} (hc : Continuous f) (h : ∀ s, 0 ≤ f s ∧ f s ≤ 1) : S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hc⟩ 1 fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith [h x, h y]

/-- (a) ⇒ (b). -/
theorem limsup_closed_of_weak {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] (h : ConvWeak ls l) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨f, hc, -, h1, h01, hlim⟩ := lemma_12_1 hF
  obtain ⟨m, hm⟩ := ((hlim l).eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  set g := toBCF (hc m) (h01 m)
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], μ.real F ≤ ∫ s, g s ∂μ := by
    intro μ _
    rw [← integral_indicator_one hF.measurableSet]
    refine integral_mono (integrable_const (1 : ℝ) |>.indicator hF.measurableSet)
      (g.integrable μ) fun s => ?_
    by_cases hs : s ∈ F
    · simp [indicator_of_mem hs, g, toBCF, h1 m s hs]
    · simp [indicator_of_notMem hs, g, toBCF, (h01 m s).1]
  filter_upwards [(h g).eventually (gt_mem_nhds (show ∫ s, g s ∂l < l.real F + ε by
    change ∫ s, f m s ∂l < _; linarith))] with n hn
  exact (hint (ls n)).trans_lt hn

/-- The upper half of (b) ⇒ (a), through Lemma 12.2. -/
theorem limsup_integral_of_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) (g : S →ᵇ ℝ) :
    LimsupLe (fun n => ∫ s, g s ∂ls n) (∫ s, g s ∂l) := by
  intro ε hε
  set a := -‖g‖ - 1
  set b := ‖g‖ + 1
  have hab : ∀ s, a ≤ g s ∧ g s < b := fun s => by
    have := abs_le.1 ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm s)
    constructor <;> linarith
  have hc : 0 < b - a := by simp only [a, b]; linarith [norm_nonneg g]
  obtain ⟨k, hk, F, -, hFc, hF⟩ :=
    lemma_12_2 g.continuous.measurable hab (ε := ε / 3) (by positivity)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set δ := ε / (3 * (b - a))
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc 1 k, (ls n).real (F i) < l.real (F i) + δ :=
    (Filter.eventually_all_finset _).2 fun i _ => hb (F i) (hFc g.continuous i) δ hδ
  filter_upwards [hev] with n hn
  obtain ⟨-, hup⟩ := hF (ls n)
  obtain ⟨hlo, -⟩ := hF l
  have hsum : ∑ i ∈ Finset.Icc 1 k, (ls n).real (F i) ≤
      ∑ i ∈ Finset.Icc 1 k, l.real (F i) + k * δ := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 k, (l.real (F i) + δ) :=
          Finset.sum_le_sum fun i hi => (hn i hi).le
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hkδ : (b - a) / k * (k * δ) = ε / 3 := by
    simp only [δ]; field_simp
  have := mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hk'.le)
  rw [mul_add, hkδ] at this
  linarith

/-- (b) ⇒ (a). -/
theorem weak_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) : ConvWeak ls l := by
  intro g
  refine tendsto_of_limsup_liminf (limsup_integral_of_closed hb g) fun ε hε => ?_
  filter_upwards [limsup_integral_of_closed hb (-g) ε hε] with n hn
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, integral_neg] at hn
  linarith

/-- (b) ⇒ (c), by complements. -/
theorem liminf_open_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {G : Set S}
    (hG : IsOpen G) : LiminfGe (fun n => (ls n).real G) (l.real G) := by
  intro ε hε
  filter_upwards [hb Gᶜ hG.isClosed_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hG.measurableSet,
    probReal_compl_eq_one_sub hG.measurableSet] at hn
  linarith

/-- (c) ⇒ (b), by complements. -/
theorem limsup_closed_of_liminf_open {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hc : ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  filter_upwards [hc Fᶜ hF.isOpen_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hF.measurableSet,
    probReal_compl_eq_one_sub hF.measurableSet] at hn
  linarith

/-- (b) ⇒ (d): `λ(Å) = λ(A) = λ(Ā)` when `λ(∂A) = 0`. -/
theorem tendsto_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {A : Set S}
    (h0 : l (frontier A) = 0) :
    Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A)) := by
  have hcl : l.real (closure A) ≤ l.real (interior A) := by
    rw [closure_eq_interior_union_frontier]
    refine (measureReal_union_le _ _).trans ?_
    rw [measureReal_def (s := frontier A), h0, ENNReal.toReal_zero, add_zero]
  have h1 : l.real (interior A) ≤ l.real A := measureReal_mono interior_subset
  have h2 : l.real A ≤ l.real (closure A) := measureReal_mono subset_closure
  refine tendsto_of_limsup_liminf (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [hb _ isClosed_closure ε hε] with n hn
    have := measureReal_mono (μ := ls n) (subset_closure (s := A))
    linarith
  · filter_upwards [liminf_open_of_limsup_closed hb isOpen_interior ε hε] with n hn
    have := measureReal_mono (μ := ls n) (interior_subset (s := A))
    linarith

/-- (d) ⇒ (b), through thickenings `{ρ(·, F) < r}` with null boundaries. -/
theorem limsup_closed_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hd : ∀ A, MeasurableSet A → l (frontier A) = 0 →
      Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) {F : Set S} (hF : IsClosed F) :
    LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l F
  have hlim :=
    tendsto_measure_thickening_of_isClosed (μ := l) ⟨1, one_pos, measure_ne_top _ _⟩ hF
  have hrs' : Tendsto rs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hrs, Eventually.of_forall fun n => (hpos n).1⟩
  have hlim' : Tendsto (fun n => l.real (Metric.thickening (rs n) F)) atTop (𝓝 (l.real F)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hlim.comp hrs')
  obtain ⟨m, hm⟩ := (hlim'.eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  have hA := hd _ Metric.isOpen_thickening.measurableSet (hpos m).2
  filter_upwards [hA.eventually (gt_mem_nhds (show l.real (Metric.thickening (rs m) F) <
    l.real (Metric.thickening (rs m) F) + ε / 2 by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (Metric.self_subset_thickening (hpos m).1 F)
  linarith

/-- **Theorem 12.3.** For probability measures on a metric space, the following are equivalent:
(a) `λₙ ⇒ λ`; (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`; (c) `liminf λₙ(G) ≥ λ(G)` for open
`G`; (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`. -/
theorem theorem_12_3 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    (ConvWeak ls l ↔ ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) ∧
      (ConvWeak ls l ↔ ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) ∧
      (ConvWeak ls l ↔ ∀ A, MeasurableSet A → l (frontier A) = 0 →
        Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) := by
  refine ⟨⟨fun h F hF => limsup_closed_of_weak h hF, weak_of_limsup_closed⟩, ⟨fun h G hG =>
    liminf_open_of_limsup_closed (fun F hF => limsup_closed_of_weak h hF) hG,
    fun hc => weak_of_limsup_closed fun F hF => limsup_closed_of_liminf_open hc hF⟩,
    ⟨fun h A _ h0 => tendsto_of_null_frontier (fun F hF => limsup_closed_of_weak h hF) h0,
    fun hd => weak_of_limsup_closed fun F hF => limsup_closed_of_null_frontier hd hF⟩⟩

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence-determining families and uniqueness

SLP §12.1, Theorems 12.4–12.6 and their corollaries, pp. 360–364.

* **Theorem 12.4** (`theorem_12_4`): if `𝒜` is closed under finite intersections and every open
  set is a countable union of members of `𝒜`, then `λₙ(A) → λ(A)` on `𝒜` gives `λₙ ⇒ λ`.
  Finite unions converge by inclusion–exclusion (`tendsto_finite_union`), and then condition (c)
  of Theorem 12.3 holds.
* **Theorem 12.5** (`theorem_12_5`): in a second countable metric space, it suffices that every
  ball `b(x, ε)` contain some `A ∈ 𝒜` with `x ∈ Å`. The book takes `S` a Borel subset of `ℝˡ`;
  every subset of `ℝˡ` is second countable, so the theorem applies to it.
* **Corollary** (`theorem_12_5_cor`): finite intersections of open balls with `λ`-null
  boundaries form a convergence-determining class (`IsConvDetermining`).
* **Theorem 12.6** (`theorem_12_6`): every Borel set lies between a closed and an open set whose
  measures differ by less than `ε`. Proved from Mathlib's regularity of finite measures on
  metric spaces.
* **Corollaries 1–2** (`theorem_12_6_cor1`, `theorem_12_6_cor2`): two probability measures that
  agree on closed sets, or on integrals of bounded continuous functions, are equal; so weak
  limits are unique (`convWeak_unique`), and a convergence-determining class determines measures
  (`IsConvDetermining.eq`, the book's "(Why?)" on p. 362).
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [BorelSpace S] in
/-- Finite unions `⋃_{j<m} Aⱼ` of members of `𝒜` converge, by inclusion–exclusion. -/
theorem tendsto_finite_union {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) :
    ∀ m (A : ℕ → Set S), (∀ i, A i ∈ 𝒜) →
      Tendsto (fun n => (ls n).real (⋃ j ∈ Finset.range m, A j)) atTop
        (𝓝 (l.real (⋃ j ∈ Finset.range m, A j))) := by
  intro m
  induction m with
  | zero => intro A _; simp
  | succ m ih =>
    intro A hA
    have hU : (⋃ j ∈ Finset.range (m + 1), A j) = (⋃ j ∈ Finset.range m, A j) ∪ A m := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hI : (⋃ j ∈ Finset.range m, A j) ∩ A m = ⋃ j ∈ Finset.range m, (A j ∩ A m) := by
      rw [iUnion₂_inter]
    have hmU : MeasurableSet (⋃ j ∈ Finset.range m, A j) :=
      Finset.measurableSet_biUnion _ fun j _ => hmeas _ (hA j)
    have key : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        μ.real (⋃ j ∈ Finset.range (m + 1), A j) = μ.real (⋃ j ∈ Finset.range m, A j) +
          μ.real (A m) - μ.real (⋃ j ∈ Finset.range m, (A j ∩ A m)) := by
      intro μ _
      rw [hU, ← hI]
      have := measureReal_union_add_inter (μ := μ) (s := ⋃ j ∈ Finset.range m, A j)
        (hmeas _ (hA m)) (measure_ne_top μ _) (measure_ne_top μ _)
      linarith
    simp_rw [key]
    exact ((ih A hA).add (h _ (hA m))).sub
      (ih (fun j => A j ∩ A m) fun j => hinter _ (hA j) _ (hA m))

/-- **Theorem 12.4.** If `𝒜` is closed under finite intersections and every open set is a
countable union of members of `𝒜`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_4 {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hopen : ∀ G, IsOpen G → ∃ T : Set (Set S), T.Countable ∧ T ⊆ 𝒜 ∧ ⋃₀ T = G)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine (theorem_12_3 ls l).2.1.2 fun G hG ε hε => ?_
  obtain ⟨T, hTc, hT𝒜, hTG⟩ := hopen G hG
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · rw [sUnion_empty] at hTG
    subst hTG
    exact Eventually.of_forall fun n => by simp; linarith
  obtain ⟨A, hAeq⟩ := hTc.exists_eq_range hTne
  have hA : ∀ i, A i ∈ 𝒜 := fun i => hT𝒜 (hAeq ▸ mem_range_self i)
  have hGA : G = ⋃ i, A i := by rw [← hTG, hAeq, sUnion_range]
  -- continuity from below
  set U : ℕ → Set S := fun m => ⋃ j ∈ Finset.range m, A j
  have hmono : Monotone U := fun m m' hmm' => biUnion_subset_biUnion_left
    (Finset.coe_subset.2 (Finset.range_subset_range.2 hmm'))
  have hUG : (⋃ m, U m) = G := by
    rw [hGA]
    ext x
    simp only [U, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨_, j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j + 1, j, by omega, hj⟩⟩
  have hlim : Tendsto (fun m => l.real (U m)) atTop (𝓝 (l.real G)) := by
    have := tendsto_measure_iUnion_atTop (μ := l) hmono
    rw [hUG] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds (show l.real G - ε / 2 < l.real G by
    linarith))).exists
  filter_upwards [(tendsto_finite_union hmeas hinter h m A hA).eventually
    (lt_mem_nhds (show l.real (U m) - ε / 2 < l.real (U m) by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (show U m ⊆ G from hUG ▸ subset_iUnion U m)
  simp only [U] at hn hm this
  linarith

/-- **Theorem 12.5.** In a second countable metric space (for instance any Borel `S ⊆ ℝˡ`), if
`𝒜` is closed under finite intersections and every ball `b(x, ε)` contains some `A ∈ 𝒜` with
`x ∈ Å`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_5 [SecondCountableTopology S] {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hball : ∀ x, ∀ ε > 0, ∃ A ∈ 𝒜, x ∈ interior A ∧ A ⊆ Metric.ball x ε)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine theorem_12_4 hmeas hinter (fun G hG => ?_) h
  -- for `x ∈ G` choose `Aₓ ∈ 𝒜` with `x ∈ Åₓ ⊆ Aₓ ⊆ G`
  have hx : ∀ x : G, ∃ A ∈ 𝒜, (x : S) ∈ interior A ∧ A ⊆ G := fun x => by
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hG x x.2
    obtain ⟨A, hA, hxA, hAb⟩ := hball x ε hε
    exact ⟨A, hA, hxA, hAb.trans hεG⟩
  choose A hA hxA hAG using hx
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : G => interior (A x))
    fun _ => isOpen_interior
  have hcover : (⋃ x : G, interior (A x)) = G := by
    refine subset_antisymm (iUnion_subset fun x => interior_subset.trans (hAG x)) fun y hy => ?_
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hxA ⟨y, hy⟩⟩
  refine ⟨A '' T, hTc.image A, image_subset_iff.2 fun x _ => hA x, subset_antisymm ?_ ?_⟩
  · exact sUnion_subset fun _ ⟨x, _, hx⟩ => hx ▸ hAG x
  · intro y hy
    rw [← hcover, ← hTeq] at hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 hy
    exact ⟨A x, ⟨x, hxT, rfl⟩, interior_subset hyx⟩

/-- `𝒜` is a **convergence-determining class** (p. 362): `λₙ(A) → λ(A)` for all `A ∈ 𝒜` with
`λ(∂A) = 0` implies `λₙ ⇒ λ`. -/
def IsConvDetermining (𝒜 : Set (Set S)) : Prop :=
  ∀ (ls : ℕ → Measure S) (l : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
    IsProbabilityMeasure l →
      (∀ A ∈ 𝒜, l (frontier A) = 0 → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) →
        ConvWeak ls l

omit [MeasurableSpace S] [BorelSpace S] in
/-- The boundary of a finite intersection lies in the union of the boundaries. -/
theorem frontier_iInter_fin_subset {m : ℕ} (s : Fin m → Set S) :
    frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  rw [frontier, interior_iInter_of_finite] at hx
  obtain ⟨hcl, hint⟩ := hx
  simp only [mem_iInter, not_forall] at hint
  obtain ⟨i, hi⟩ := hint
  exact mem_iUnion.2 ⟨i, closure_mono (iInter_subset s i) hcl, hi⟩

/-- Finite intersections of open balls. -/
def ballInters (S : Type*) [MetricSpace S] : Set (Set S) :=
  {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ, A = ⋂ i, Metric.ball (c i) (r i)}

/-- **Corollary to Theorem 12.5.** In a second countable metric space, finite intersections of
open balls form a convergence-determining class. -/
theorem theorem_12_5_cor [SecondCountableTopology S] : IsConvDetermining (ballInters S) := by
  intro ls l _ _ h
  -- the finite intersections of balls whose boundaries are `λ`-null
  set 𝒜 : Set (Set S) := {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ,
    (∀ i, l (frontier (Metric.ball (c i) (r i))) = 0) ∧ A = ⋂ i, Metric.ball (c i) (r i)}
  have hfr : ∀ A ∈ 𝒜, l (frontier A) = 0 := by
    rintro A ⟨m, c, r, hnull, rfl⟩
    refine measure_mono_null (frontier_iInter_fin_subset _) ?_
    exact measure_iUnion_null hnull
  refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨m, c, r, _, hA⟩ => hA ▸
    MeasurableSet.iInter fun i => Metric.isOpen_ball.measurableSet) ?_ ?_
    (fun A hA => h A (by obtain ⟨m, c, r, -, hA⟩ := hA; exact ⟨m, c, r, hA⟩) (hfr A hA))
  · rintro A ⟨m, c, r, hn, rfl⟩ B ⟨m', c', r', hn', rfl⟩
    refine ⟨m + m', Fin.append c c', Fin.append r r', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hn i
      · simpa using hn' i
    · ext x
      simp only [mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩ i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa using h1 i
        · simpa using h2 i
      · intro h
        exact ⟨fun i => by simpa using h (Fin.castAdd m' i),
          fun i => by simpa using h (Fin.natAdd m i)⟩
  · intro x ε hε
    obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l {x}
    obtain ⟨n, hn⟩ := (hrs.eventually (gt_mem_nhds hε)).exists
    refine ⟨Metric.ball x (rs n), ⟨1, fun _ => x, fun _ => rs n, fun _ => ?_, ?_⟩, ?_,
      Metric.ball_subset_ball hn.le⟩
    · simpa [Metric.thickening_singleton] using (hpos n).2
    · ext y; simp
    · rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (hpos n).1

/-- **Theorem 12.6.** For a probability measure on a metric space, every Borel set `B` lies
between a closed `A` and an open `C` with `λ(C) − λ(A) < ε`. -/
theorem theorem_12_6 (l : Measure S) [IsProbabilityMeasure l] {B : Set S} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A C, IsClosed A ∧ IsOpen C ∧ A ⊆ B ∧ B ⊆ C ∧ l.real C - l.real A < ε := by
  have hε2 : (ENNReal.ofReal (ε / 2)) ≠ 0 := by simp [hε]
  obtain ⟨A, hAB, hA, hlt⟩ := hB.exists_isClosed_lt_add (measure_ne_top l B) hε2
  obtain ⟨C, hBC, hC, hCl⟩ := B.exists_isOpen_lt_of_lt (l B + ENNReal.ofReal (ε / 2))
    (ENNReal.lt_add_right (measure_ne_top l B) hε2)
  refine ⟨A, C, hA, hC, hAB, hBC, ?_⟩
  have h1 : l.real B < l.real A + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hlt
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have h2 : l.real C < l.real B + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hCl
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Corollary 1 to Theorem 12.6.** Probability measures that agree on closed sets are equal. -/
theorem theorem_12_6_cor1 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ A, IsClosed A → l A = μ A) : l = μ := by
  have hr : ∀ A, IsClosed A → l.real A = μ.real A := fun A hA => by simp [Measure.real, h A hA]
  have hopen : ∀ C, IsOpen C → l.real C = μ.real C := fun C hC => by
    have := hr Cᶜ hC.isClosed_compl
    rwa [probReal_compl_eq_one_sub hC.measurableSet, probReal_compl_eq_one_sub hC.measurableSet,
      sub_right_inj] at this
  ext B hB
  have hle : ∀ (ν₁ ν₂ : Measure S) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      (∀ A, IsClosed A → ν₁.real A = ν₂.real A) → (∀ C, IsOpen C → ν₁.real C = ν₂.real C) →
        ν₁.real B ≤ ν₂.real B := by
    intro ν₁ ν₂ _ _ hc ho
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hlt⟩ := theorem_12_6 ν₂ hB hε
    calc ν₁.real B ≤ ν₁.real C := measureReal_mono hBC
      _ = ν₂.real C := ho C hC
      _ < ν₂.real A + ε := by linarith
      _ ≤ ν₂.real B + ε := by linarith [measureReal_mono (μ := ν₂) hAB]
  have h1 := hle l μ hr hopen
  have h2 := hle μ l (fun A hA => (hr A hA).symm) (fun C hC => (hopen C hC).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (le_antisymm h1 h2)

/-- **Corollary 2 to Theorem 12.6.** Probability measures with the same integrals of all
bounded continuous functions are equal (Lemma 12.1 and Corollary 1). -/
theorem theorem_12_6_cor2 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂l = ∫ s, f s ∂μ) : l = μ := by
  refine theorem_12_6_cor1 fun A hA => ?_
  obtain ⟨f, hc, -, -, h01, hlim⟩ := lemma_12_1 hA
  have heq : ∀ n, ∫ s, f n s ∂l = ∫ s, f n s ∂μ := fun n => h (toBCF (hc n) (h01 n))
  have := tendsto_nhds_unique (hlim l) ((hlim μ).congr fun n => (heq n).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- Weak limits are unique (p. 364). -/
theorem convWeak_unique {ls : ℕ → Measure S} {l μ : Measure S} [IsProbabilityMeasure l]
    [IsProbabilityMeasure μ] (h1 : ConvWeak ls l) (h2 : ConvWeak ls μ) : l = μ :=
  theorem_12_6_cor2 fun f => tendsto_nhds_unique (h1 f) (h2 f)

/-- A convergence-determining class determines probability measures (p. 362, "(Why?)"): apply
the definition to the constant sequence `μ`. -/
theorem IsConvDetermining.eq {𝒜 : Set (Set S)} (h𝒜 : IsConvDetermining 𝒜) {l μ : Measure S}
    [IsProbabilityMeasure l] [IsProbabilityMeasure μ] (h : ∀ A ∈ 𝒜, l A = μ A) : l = μ := by
  have hw : ConvWeak (fun _ => μ) l := h𝒜 (fun _ => μ) l (fun _ => inferInstance) inferInstance
    fun A hA _ => by simp [Measure.real, h A hA]
  exact convWeak_unique hw (fun f => tendsto_const_nhds)

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Distribution functions on `ℝˡ`

SLP §12.2, pp. 364–369. Points of `ℝˡ` are functions `Fin l → ℝ`, ordered coordinatewise. The
distribution function of `λ` is `F(x) = λ((−∞, x])` (`distFun`). The half-open box `(a, b]` is
`∏ᵢ (aᵢ, bᵢ]` (`box`), and for `t ⊆ {1, …, l}` its vertex `a + θₜd` takes `bᵢ` for `i ∈ t` and
`aᵢ` otherwise (`vertex`).

* **Exercise 12.3** (`ex_12_3`): a nondecreasing `F` continuous from above and from below at `x`
  is continuous at `x`.
* **Theorem 12.7a** (`theorem_12_7a`): (D1) `F` is nondecreasing, tends to `0` as any coordinate
  tends to `−∞`, and to `1` as all coordinates tend to `+∞`; (D2) `F` is continuous from above;
  (D3) `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b]) ≥ 0`. (D3) comes from the identity
  `1_{(a,b]} = ∏ᵢ (1[xᵢ ≤ bᵢ] − 1[xᵢ ≤ aᵢ])`, expanded as a sum over `t`.
* **Theorem 12.7b**, uniqueness (`distFun_injective`): the sets `(−∞, x]` form a π-system
  generating the Borel sets of `ℝˡ`, so `F` determines `λ`. Existence is in
  `MultivariateStieltjes`.
* **Theorem 12.7c** (`theorem_12_7c`): `F` is continuous from below at `x` iff `λ(∂(−∞, x]) = 0`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set

variable {l : ℕ}

/-- The distribution function `F(x) = λ((−∞, x])`. -/
noncomputable def distFun (μ : Measure (Fin l → ℝ)) (x : Fin l → ℝ) : ℝ := μ.real (Iic x)

/-- The half-open box `(a, b] = ∏ᵢ (aᵢ, bᵢ]`. -/
def box (a b : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Ioc (a i) (b i)

/-- The vertex of `(a, b]` taking `bᵢ` for `i ∈ t` and `aᵢ` otherwise. -/
def vertex (a b : Fin l → ℝ) (t : Finset (Fin l)) : Fin l → ℝ := fun i => if i ∈ t then b i else a i

/-- The alternating vertex sum `Σₜ (−1)^{l − |t|} F(a + θₜd)` of (D3). -/
def vertexSum (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) : ℝ :=
  ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * F (vertex a b t)

/-- The vector `ε1 = (ε, …, ε)`. -/
def diag (ε : ℝ) : Fin l → ℝ := fun _ => ε

/-- `F` is **continuous from above** at `x`: `F(x + ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromAbove (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x + diag ε)) (𝓝[>] 0) (𝓝 (F x))

/-- `F` is **continuous from below** at `x`: `F(x − ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromBelow (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x - diag ε)) (𝓝[>] 0) (𝓝 (F x))

theorem Iic_eq_pi (x : Fin l → ℝ) : Iic x = Set.pi univ fun i => Iic (x i) := by
  ext y; simp [Pi.le_def]

/-- The product expansion: `1_{(a,b]}(y) = Σₜ (−1)^{l − |t|} 1[y ≤ a + θₜd]` for `a ≤ b`. -/
theorem box_indicator_eq {a b : Fin l → ℝ} (hab : a ≤ b) (y : Fin l → ℝ) :
    (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * (Iic (vertex a b t)).indicator 1 y := by
  classical
  -- `1_{(a,b]}(y) = ∏ᵢ (1[yᵢ ≤ bᵢ] − 1[yᵢ ≤ aᵢ])`
  have hprod : (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∏ i, ((Iic (b i)).indicator (1 : ℝ → ℝ) (y i) + -(Iic (a i)).indicator 1 (y i)) := by
    by_cases hy : y ∈ box a b
    · rw [indicator_of_mem hy, Pi.one_apply]
      symm
      refine Finset.prod_eq_one fun i _ => ?_
      have hi := hy i (mem_univ i)
      rw [indicator_of_mem (show y i ∈ Iic (b i) from hi.2),
        indicator_of_notMem (show y i ∉ Iic (a i) from fun h => (not_le.2 hi.1) h)]
      simp
    · rw [indicator_of_notMem hy]
      simp only [box, Set.mem_pi, mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : y i ≤ a i
      · rw [indicator_of_mem (show y i ∈ Iic (b i) from h1.trans (hab i)),
          indicator_of_mem (show y i ∈ Iic (a i) from h1)]; simp
      · have h2 : ¬ y i ≤ b i := fun h => hi ⟨not_le.1 h1, h⟩
        rw [indicator_of_notMem (show y i ∉ Iic (b i) from h2),
          indicator_of_notMem (show y i ∉ Iic (a i) from h1)]; simp
  rw [hprod, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin]
  -- the product of indicators is the indicator of `(−∞, vertex]`
  have hv : (∏ i ∈ t, (Iic (b i)).indicator (1 : ℝ → ℝ) (y i)) *
      ∏ i ∈ Finset.univ \ t, (Iic (a i)).indicator (1 : ℝ → ℝ) (y i) =
        (Iic (vertex a b t)).indicator 1 y := by
    by_cases hy : y ≤ vertex a b t
    · rw [indicator_of_mem (show y ∈ Iic (vertex a b t) from hy), Pi.one_apply]
      rw [Finset.prod_eq_one fun i hi => ?_, Finset.prod_eq_one fun i hi => ?_, one_mul]
      · have := hy i; simp only [vertex, Finset.mem_sdiff] at this hi
        simp only [hi.2, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (a i) from this)]; rfl
      · have := hy i; simp only [vertex] at this
        simp only [hi, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (b i) from this)]; rfl
    · rw [indicator_of_notMem (show y ∉ Iic (vertex a b t) from hy)]
      rw [Pi.le_def] at hy
      push Not at hy
      obtain ⟨i, hi⟩ := hy
      by_cases hit : i ∈ t
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero hit (indicator_of_notMem (show y i ∉ Iic (b i) from
          not_le.2 hi) _), zero_mul]
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hit⟩)
          (indicator_of_notMem (show y i ∉ Iic (a i) from not_le.2 hi) _), mul_zero]
  rw [← hv]
  ring

theorem measurableSet_box (a b : Fin l → ℝ) : MeasurableSet (box a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- (D3): `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b])`. -/
theorem vertexSum_eq (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] {a b : Fin l → ℝ}
    (hab : a ≤ b) : vertexSum (distFun μ) a b = μ.real (box a b) := by
  rw [← integral_indicator_one (measurableSet_box a b)]
  simp_rw [box_indicator_eq hab]
  rw [integral_finsetSum _ fun t _ =>
    ((integrable_const 1).indicator measurableSet_Iic).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic]
  rfl

theorem distFun_mono (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] : Monotone (distFun μ) :=
  fun _ _ hxy => measureReal_mono (Iic_subset_Iic.2 hxy)

/-- Continuity from above of `F`, as a squeeze along `ε ↓ 0`, given decreasing sets whose
measures converge. -/
theorem contFromAbove_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) : ContFromAbove (distFun μ) x := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x + diag (1 / (n + 1)))
  have hanti : Antitone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.add_apply, diag]
    gcongr
  have hinter : (⋂ n, A n) = Iic x := by
    ext y
    simp only [A, mem_iInter, mem_Iic, Pi.le_def, Pi.add_apply, diag]
    constructor
    · intro h i
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      linarith [h n i]
    · intro h n i
      linarith [h i, show (0 : ℝ) < 1 / (n + 1) by positivity]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (Iic x))) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [ContFromAbove, tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_of_lt_of_le hc (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [show (0 : ℝ) < ε from hε])
  · obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [hε.2]) hn

/-- **Theorem 12.7a.** The distribution function of a probability measure on `ℝˡ` satisfies
(D1): it is nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all
coordinates tend to `+∞`; (D2): it is continuous from above; and (D3): the alternating vertex
sum over any box is `λ((a, b]) ≥ 0`. -/
theorem theorem_12_7a (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    (Monotone (distFun μ) ∧
      (∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → distFun μ x < ε) ∧
      (∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < distFun μ x)) ∧
      (∀ x, ContFromAbove (distFun μ) x) ∧
      ∀ a b, a ≤ b → vertexSum (distFun μ) a b = μ.real (box a b) ∧
        0 ≤ vertexSum (distFun μ) a b := by
  refine ⟨⟨distFun_mono μ, fun i ε hε => ?_, fun ε hε => ?_⟩, contFromAbove_distFun μ,
    fun a b hab => ⟨vertexSum_eq μ hab, vertexSum_eq μ hab ▸ measureReal_nonneg⟩⟩
  · -- the `i`-th marginal of `(−∞, −n]` tends to `0`
    set A : ℕ → Set (Fin l → ℝ) := fun n => {y | y i ≤ -n}
    have hanti : Antitone A := fun m n hmn y hy => by
      simp only [A, mem_ofPred_eq] at hy ⊢
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hempty : (⋂ n, A n) = ∅ := by
      ext y
      simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y i)
      exact ⟨n, by linarith⟩
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hε)).exists
    refine ⟨-n, fun x hx => lt_of_le_of_lt (measureReal_mono fun y hy => ?_) hn⟩
    exact (hy i).trans hx
  · -- the sets `(−∞, n1]` increase to `ℝˡ`
    set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (diag n)
    have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
      simp only [diag]; exact_mod_cast hmn
    have hunion : (⋃ n, A n) = univ := by
      refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌈∑ j, |y j|⌉₊, fun i => ?_⟩
      simp only [diag]
      calc y i ≤ |y i| := le_abs_self _
        _ ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        _ ≤ ⌈∑ j, |y j|⌉₊ := Nat.le_ceil _
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, measure_univ] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 1) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))).exists
    exact ⟨n, fun x hx => lt_of_lt_of_le hn (distFun_mono μ fun i => hx i)⟩

/-- The sets `(−∞, x]` generate the Borel sets of `ℝˡ`. -/
theorem generateFrom_Iic_pi :
    MeasurableSpace.generateFrom (range fun x : Fin l → ℝ => Iic x) =
      (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) := by
  rw [← generateFrom_eq_pi (C := fun _ => range (Iic : ℝ → Set ℝ))
    (fun _ => (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm)
    fun _ => ⟨fun n => Iic (n : ℝ), fun n => mem_range_self _,
      eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩]
  congr 1
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => Iic (x i), fun i _ => ⟨x i, rfl⟩, (Iic_eq_pi x).symm⟩
  · rintro ⟨T, hT, rfl⟩
    choose x hx using fun i => hT i (mem_univ i)
    exact ⟨x, by change Iic x = _; rw [Iic_eq_pi]; congr 1; funext i; exact hx i⟩

/-- **Theorem 12.7b** (uniqueness). A probability measure on `ℝˡ` is determined by its
distribution function. -/
theorem distFun_injective {μ ν : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : distFun μ = distFun ν) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_Iic_pi.symm ?_ ?_ (by simp)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact ⟨x ⊓ y, Iic_inter_Iic.symm⟩
  · rintro _ ⟨x, rfl⟩
    have := congrFun h x
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- The open lower orthant `{y : y < x}` (all coordinates strictly smaller). -/
def lowerOpen (x : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Iio (x i)

theorem frontier_Iic_eq (x : Fin l → ℝ) : frontier (Iic x) = Iic x \ lowerOpen x := by
  rw [frontier, isClosed_Iic.closure_eq, Iic_eq_pi, interior_pi_set finite_univ]
  simp_rw [interior_Iic]
  rfl

theorem lowerOpen_subset (x : Fin l → ℝ) : lowerOpen x ⊆ Iic x := fun _ hy i => (hy i trivial).le

/-- `F(x − ε1) → λ({y < x})` as `ε ↓ 0`. -/
theorem tendsto_distFun_below (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) :
    Tendsto (fun ε => distFun μ (x - diag ε)) (𝓝[>] 0) (𝓝 (μ.real (lowerOpen x))) := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x - diag (1 / (n + 1)))
  have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.sub_apply, diag]
    gcongr
  have hunion : (⋃ n, A n) = lowerOpen x := by
    ext y
    simp only [A, mem_iUnion, mem_Iic, Pi.le_def, Pi.sub_apply, diag, lowerOpen, Set.mem_pi,
      mem_univ, true_implies, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩ i; linarith [hn i, show (0 : ℝ) < 1 / (n + 1) by positivity]
    · intro h
      choose N hN using fun i => exists_nat_one_div_lt (sub_pos.2 (h i))
      refine ⟨Finset.univ.sup N, fun i => ?_⟩
      have hle : (N i : ℝ) ≤ Finset.univ.sup N := by
        exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ i)
      have : 1 / ((Finset.univ.sup N : ℕ) + 1 : ℝ) ≤ 1 / (N i + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hN i]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (lowerOpen x))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_lt_of_le hn (distFun_mono μ fun i => by
      simp only [Pi.sub_apply, diag]; linarith [hε.2])
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine lt_of_le_of_lt (measureReal_mono (s₂ := lowerOpen x) fun y hy i _ => ?_) hc
    have := hy i
    simp only [Pi.sub_apply, diag] at this
    exact lt_of_le_of_lt this (by linarith [show (0 : ℝ) < ε from hε])

/-- **Theorem 12.7c.** `F` is continuous from below at `x` iff the boundary of `(−∞, x]` is
`λ`-null. -/
theorem theorem_12_7c (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] (x : Fin l → ℝ) :
    ContFromBelow (distFun μ) x ↔ μ (frontier (Iic x)) = 0 := by
  have hdiff : μ.real (frontier (Iic x)) = distFun μ x - μ.real (lowerOpen x) := by
    rw [frontier_Iic_eq, measureReal_sdiff (lowerOpen_subset x)
      (MeasurableSet.univ_pi fun _ => measurableSet_Iio)]
    rfl
  have h0 : μ (frontier (Iic x)) = 0 ↔ μ.real (frontier (Iic x)) = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]; simp [measure_ne_top]
  rw [h0, hdiff, sub_eq_zero]
  constructor
  · intro h
    exact tendsto_nhds_unique h (tendsto_distFun_below μ x)
  · intro h
    rw [ContFromBelow, h]
    exact tendsto_distFun_below μ x

/-- **Exercise 12.3.** A nondecreasing `F` that is continuous from above and from below at `x` is
continuous at `x`. -/
theorem ex_12_3 {F : (Fin l → ℝ) → ℝ} (hF : Monotone F) {x : Fin l → ℝ}
    (ha : ContFromAbove F x) (hb : ContFromBelow F x) : ContinuousAt F x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₁, hε₁, h1⟩ := (Metric.tendsto_nhdsWithin_nhds.1 ha) δ hδ
  obtain ⟨ε₂, hε₂, h2⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hb) δ hδ
  set ε := min ε₁ ε₂ / 2
  have hε : 0 < ε := by positivity
  have hu := h1 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_left ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  have hl := h2 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_right ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  rw [Real.dist_eq] at hu hl
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hε] at hy
  have hlo : x - diag ε ≤ y := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.sub_apply, diag]; linarith
  have hhi : y ≤ x + diag ε := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.add_apply, diag]; linarith
  have := hF hlo
  have := hF hhi
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hu hl
  constructor <;> linarith

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence of distribution functions

SLP §12.3, Theorem 12.8 and Exercises 12.4–12.5, pp. 369–372.

* `nullCoord μ i`: the levels `c` with `λ{y : yᵢ = c} = 0`. Its complement is countable
  (`countable_nullCoord_compl`), so it is dense.
* `continuousAt_distFun`: a point whose coordinates are all null levels is a continuity point
  of `F`.
* **Theorem 12.8** (`theorem_12_8`): `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every continuity point `x` of
  `F`. For (⇐), boxes with null-level coordinates satisfy the hypotheses of Theorem 12.5, and
  their measures are alternating sums of `F` at continuity points.
* **Exercise 12.4** (`ex_12_4`): for `S ⊆ ℝˡ` Borel, `λₙ ⇒ λ` on `S` iff the extensions
  `λ̂(A) = λ(A ∩ S)` converge weakly on `ℝˡ`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {l : ℕ}

/-- The levels `c` with `λ{y : yᵢ = c} = 0`. -/
def nullCoord (μ : Measure (Fin l → ℝ)) (i : Fin l) : Set ℝ := {c | μ {y | y i = c} = 0}

theorem countable_nullCoord_compl (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    (nullCoord μ i)ᶜ.Countable := by
  refine (Measure.countable_meas_level_set_pos (μ := μ) (measurable_pi_apply i)).mono ?_
  intro c hc
  exact pos_iff_ne_zero.2 hc

theorem dense_nullCoord (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    Dense (nullCoord μ i) := by
  simpa using (countable_nullCoord_compl μ i).dense_compl ℝ

/-- A point whose coordinates are null levels is a continuity point of `F`. -/
theorem continuousAt_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {v : Fin l → ℝ} (hv : ∀ i, v i ∈ nullCoord μ i) : ContinuousAt (distFun μ) v := by
  refine ex_12_3 (distFun_mono μ) (contFromAbove_distFun μ v) ((theorem_12_7c μ v).2 ?_)
  refine measure_mono_null (t := ⋃ i, {y : Fin l → ℝ | y i = v i}) (fun y hy => ?_)
    (measure_iUnion_null fun i => hv i)
  rw [frontier_Iic_eq] at hy
  obtain ⟨hle, hlt⟩ := hy
  simp only [lowerOpen, Set.mem_pi, mem_univ, true_implies, mem_Iio, not_forall, not_lt] at hlt
  obtain ⟨i, hi⟩ := hlt
  exact mem_iUnion.2 ⟨i, le_antisymm (hle i) hi⟩

/-- A continuity point of `F` has a `λ`-null boundary of `(−∞, x]`. -/
theorem frontier_null_of_continuousAt (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {x : Fin l → ℝ} (h : ContinuousAt (distFun μ) x) : μ (frontier (Iic x)) = 0 := by
  refine (theorem_12_7c μ x).1 ?_
  have hc : Tendsto (fun ε : ℝ => x - diag ε) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun ε : ℝ => x - diag ε) (𝓝 0) (𝓝 (x - diag 0)) :=
      (continuous_const.sub (continuous_pi fun _ => continuous_id)).tendsto 0
    have h0 : x - diag 0 = x := by ext; simp [diag]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h.tendsto.comp hc

theorem box_inter (a b a' b' : Fin l → ℝ) : box a b ∩ box a' b' = box (a ⊔ a') (b ⊓ b') := by
  ext y
  simp only [box, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_Ioc, Pi.sup_apply,
    Pi.inf_apply, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2⟩ i; exact ⟨⟨(h1 i).1, (h2 i).1⟩, (h1 i).2, (h2 i).2⟩
  · intro h; exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩

theorem box_eq_empty {a b : Fin l → ℝ} (h : ¬ a ≤ b) : box a b = ∅ := by
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  ext y
  simp only [box, Set.mem_pi, mem_univ, true_implies, mem_Ioc, mem_empty_iff_false, iff_false,
    not_forall]
  exact ⟨i, fun h => by linarith [h.1, h.2]⟩

/-- **Theorem 12.8.** For probability measures on `ℝˡ`, `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every
continuity point `x` of `F`. -/
theorem theorem_12_8 (ls : ℕ → Measure (Fin l → ℝ)) (μ : Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ∀ x, ContinuousAt (distFun μ) x →
      Tendsto (fun n => distFun (ls n) x) atTop (𝓝 (distFun μ x)) := by
  constructor
  · intro h x hx
    exact (theorem_12_3 ls μ).2.2.1 h (Iic x) measurableSet_Iic
      (frontier_null_of_continuousAt μ hx)
  · intro h
    set 𝒜 : Set (Set (Fin l → ℝ)) := {A | ∃ a b, (∀ i, a i ∈ nullCoord μ i ∧
      b i ∈ nullCoord μ i) ∧ A = box a b}
    refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨a, b, _, hA⟩ => hA ▸ measurableSet_box a b) ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨a', b', hab', rfl⟩
      refine ⟨a ⊔ a', b ⊓ b', fun i => ⟨?_, ?_⟩, box_inter a b a' b'⟩
      · simp only [Pi.sup_apply]; rcases le_total (a i) (a' i) with h1 | h1
        · rw [max_eq_right h1]; exact (hab' i).1
        · rw [max_eq_left h1]; exact (hab i).1
      · simp only [Pi.inf_apply]; rcases le_total (b i) (b' i) with h1 | h1
        · rw [min_eq_left h1]; exact (hab i).2
        · rw [min_eq_right h1]; exact (hab' i).2
    · intro x ε hε
      have hε2 : 0 < ε / 2 := by positivity
      choose a ha hai using fun i => (dense_nullCoord μ i).exists_between
        (show x i - ε / 2 < x i by linarith)
      choose b hb hbi using fun i => (dense_nullCoord μ i).exists_between
        (show x i < x i + ε / 2 by linarith)
      refine ⟨box a b, ⟨a, b, fun i => ⟨ha i, hb i⟩, rfl⟩, ?_, fun y hy => ?_⟩
      · refine mem_interior.2 ⟨Set.pi univ fun i => Ioo (a i) (b i), fun y hy i _ =>
          ⟨(hy i trivial).1, (hy i trivial).2.le⟩,
          isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo, fun i _ => ⟨(hai i).2, (hbi i).1⟩⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro i
        have := hy i trivial
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [(hai i).1, (hbi i).2, this.1, this.2]
    · rintro _ ⟨a, b, hab, rfl⟩
      by_cases hle : a ≤ b
      · simp_rw [← vertexSum_eq _ hle]
        refine tendsto_finsetSum _ fun t _ => (h _ ?_).const_mul _
        refine continuousAt_distFun μ fun i => ?_
        simp only [vertex]
        split_ifs
        · exact (hab i).2
        · exact (hab i).1
      · simp [box_eq_empty hle]

/-- **Exercise 12.4.** For `S ⊆ ℝˡ`, `λₙ ⇒ λ` on `S` iff the extensions `λ̂(A) = λ(A ∩ S)` converge
weakly on `ℝˡ`. (Measurability of `S` is not needed.) -/
theorem ex_12_4 {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ConvWeak (fun n => (ls n).map Subtype.val) (μ.map Subtype.val) := by
  have hmap : ∀ (ν : Measure S) {F : Set (Fin l → ℝ)}, MeasurableSet F →
      (ν.map Subtype.val).real F = ν.real (Subtype.val ⁻¹' F) := fun ν F hF => by
    rw [measureReal_def, Measure.map_apply measurable_subtype_coe hF]; rfl
  rw [(theorem_12_3 ls μ).1, (theorem_12_3 _ _).1]
  constructor
  · intro h F hF
    simp_rw [hmap _ hF.measurableSet]
    exact h _ (hF.preimage continuous_subtype_val)
  · intro h A hA
    obtain ⟨F, hF, rfl⟩ := isClosed_induced_iff.1 hA
    have := h F hF
    simp_rw [hmap _ hF.measurableSet] at this
    exact this

/-- **Exercise 12.5a.** On `S = [a, b] ⊆ ℝˡ`, if `λₙ([a, x]) → λ([a, x])` for every `x ∈ S`, then
`λₙ ⇒ λ` (through Exercise 12.4 and Theorem 12.8). -/
theorem ex_12_5a {a b : Fin l → ℝ} (ls : ℕ → Measure (Icc a b)) (μ : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h : ∀ x ∈ Icc a b, Tendsto (fun n => (ls n).real (Subtype.val ⁻¹' Icc a x)) atTop
      (𝓝 (μ.real (Subtype.val ⁻¹' Icc a x)))) : ConvWeak ls μ := by
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := s₀.2.1.trans s₀.2.2
  refine (ex_12_4 ls μ).2 ((theorem_12_8 _ _).2 fun y _ => ?_)
  have hmap : ∀ (ν : Measure (Icc a b)), distFun (ν.map Subtype.val) y =
      ν.real (Subtype.val ⁻¹' Iic y) := fun ν => by
    rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl
  simp_rw [hmap]
  by_cases hay : a ≤ y
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = Subtype.val ⁻¹' Icc a (y ⊓ b) := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_Icc, le_inf_iff]
      exact ⟨fun hs => ⟨s.2.1, hs, s.2.2⟩, fun hs => hs.2.1⟩
    rw [hpre]
    exact h _ ⟨le_inf hay hab, inf_le_right⟩
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = ∅ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hs => hay (s.2.1.trans hs)
    simp [hpre]

/-- The continuous nondecreasing ramp `gₙ(s) = min 1 (n Σᵢ max 0 (sᵢ - xᵢ))`, which increases to the
indicator of `{s : ¬ s ≤ x}` (used for Exercise 12.5b in place of the book's Lemma 12.1
functions). -/
noncomputable def ramp (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : ℝ :=
  min 1 ((n : ℝ) * ∑ i, max 0 (s i - x i))

theorem continuous_ramp (x : Fin l → ℝ) (n : ℕ) : Continuous (ramp x n) := by
  unfold ramp; fun_prop

theorem ramp_mem (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : 0 ≤ ramp x n s ∧ ramp x n s ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg n.cast_nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)), min_le_left _ _⟩

theorem monotone_ramp (x : Fin l → ℝ) (n : ℕ) : Monotone (ramp x n) := fun s t hst =>
  min_le_min_left _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    max_le_max le_rfl (by linarith [hst i])) n.cast_nonneg)

theorem tendsto_ramp (x s : Fin l → ℝ) :
    Tendsto (fun n => ramp x n s) atTop (𝓝 ((Iic x)ᶜ.indicator 1 s)) := by
  by_cases hs : s ≤ x
  · have : ∀ n, ramp x n s = 0 := fun n => by
      have : ∀ i, max 0 (s i - x i) = 0 := fun i => max_eq_left (by linarith [hs i])
      simp [ramp, this]
    simp only [this, indicator_of_notMem (show s ∉ (Iic x)ᶜ by simpa using hs)]
    exact tendsto_const_nhds
  · obtain ⟨i, hi⟩ : ∃ i, x i < s i := by
      by_contra h; push Not at h; exact hs h
    have hc : s i - x i ≤ ∑ j, max 0 (s j - x j) :=
      (le_max_right _ _).trans (Finset.single_le_sum (f := fun j => max 0 (s j - x j))
        (fun j _ => le_max_left _ _) (Finset.mem_univ i))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (s i - x i))
    rw [indicator_of_mem (show s ∈ (Iic x)ᶜ by simpa using hs)]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hpos : 0 < s i - x i := by linarith
    have : 1 ≤ (n : ℝ) * ∑ j, max 0 (s j - x j) := by
      have h1 : 1 < N * (s i - x i) := by rwa [div_lt_iff₀ hpos] at hN
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp [ramp, min_eq_left this]

/-- **Exercise 12.5b** (corrected). On `S = [a, b]`, probability measures agreeing on the integrals
of all continuous nondecreasing functions are equal. (The book's hint cites "Theorem 12.1", i.e.
Lemma 12.1, whose functions are nonincreasing; nondecreasing functions suffice, which is what
Theorem 12.12 needs.) -/
theorem ex_12_5b {a b : Fin l → ℝ} (lam μ : Measure (Icc a b)) [IsProbabilityMeasure lam]
    [IsProbabilityMeasure μ] (h : ∀ f : Icc a b →ᵇ ℝ, Monotone f → ∫ s, f s ∂lam = ∫ s, f s ∂μ) :
    lam = μ := by
  have hE : ∀ x : Fin l → ℝ, MeasurableSet (Subtype.val ⁻¹' (Iic x)ᶜ : Set (Icc a b)) :=
    fun x => measurableSet_Iic.compl.preimage measurable_subtype_coe
  have hlim : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] (x : Fin l → ℝ),
      Tendsto (fun n => ∫ s, ramp x n (s : Fin l → ℝ) ∂ν) atTop
        (𝓝 (ν.real (Subtype.val ⁻¹' (Iic x)ᶜ))) := fun ν _ x => by
    rw [← integral_indicator_one (hE x)]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => ((continuous_ramp x n).comp continuous_subtype_val).aestronglyMeasurable)
      (integrable_const 1) (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (ramp_mem x n s).1]; exact (ramp_mem x n s).2
    · exact tendsto_ramp x s
  have heq : ∀ x : Fin l → ℝ, lam.real (Subtype.val ⁻¹' (Iic x)ᶜ) =
      μ.real (Subtype.val ⁻¹' (Iic x)ᶜ) := fun x => by
    refine tendsto_nhds_unique (hlim lam x) ?_
    have := hlim μ x
    refine this.congr fun n => (h ⟨⟨fun s => ramp x n s,
      (continuous_ramp x n).comp continuous_subtype_val⟩, ⟨1, fun s t => ?_⟩⟩
      (fun s t hst => monotone_ramp x n hst)).symm
    have := ramp_mem x n s; have := ramp_mem x n t
    simp only [Real.dist_eq, abs_le]; constructor <;> linarith
  have hconv : ConvWeak (fun _ => μ) lam := by
    refine ex_12_5a _ _ fun x _ => ?_
    have hpre : (Subtype.val ⁻¹' Icc a x : Set (Icc a b)) = (Subtype.val ⁻¹' (Iic x)ᶜ)ᶜ := by
      ext s
      simp only [mem_preimage, mem_Icc, mem_compl_iff, mem_Iic, not_not]
      exact ⟨fun hs => hs.2, fun hs => ⟨s.2.1, hs⟩⟩
    rw [hpre, probReal_compl_eq_one_sub (hE x), probReal_compl_eq_one_sub (hE x), heq]
    exact tendsto_const_nhds
  exact convWeak_unique hconv fun _ => tendsto_const_nhds

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence in Theorem 12.7b: multivariate Stieltjes measures (SLP pp. 366–369)

Every `F : ℝˡ → ℝ` with `0 ≤ F ≤ 1` satisfying (D1)–(D3) is the distribution function of a unique
probability measure (`theorem_12_7b`). The book defines `λ` on finite unions of boxes and asserts
countable additivity by ordering the pieces of a countable decomposition of `(a, b]` as
`b = b₁ ≥ a₁ = b₂ ≥ …`, which is not possible in general when `l ≥ 2` (see `docs/corrections.md`).
The proof here is the standard one:

1. the vertex sum `Δ(a, b] = Σₜ (−1)^{l−|t|} F(a + θₜd)` is additive when a box is cut by a
   hyperplane (`vertexSum_split`), hence additive on every partition of a box into boxes
   (`boxContent`, through Mathlib's `BoxIntegral.BoxAdditiveMap.ofMapSplitAdd`);
2. half-open boxes together with `∅` form a semiring of sets (`isSetSemiring_boxes`), on which
   `Δ` is a finitely additive content (`stieltjesContent`);
3. the content is countably subadditive (`isSigmaSubadditive`): shrink the box to a compact set
   and enlarge the covering boxes to open ones using continuity from above (D2), then take a
   finite subcover;
4. Carathéodory's theorem (`AddContent.measure`) gives the measure, and the limits in (D1) give
   `λ((−∞, x]) = F(x)`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {l : ℕ}

/-! ### The vertex sum is additive under cuts -/

/-- Grouping the vertex sum in pairs `u`, `insert i u`. -/
theorem vertexSum_eq_erase (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) (i : Fin l) :
    vertexSum F a b = ∑ u ∈ (Finset.univ.erase i).powerset,
      (-1 : ℝ) ^ (l - (u.card + 1)) * (F (vertex a b (insert i u)) - F (vertex a b u)) := by
  have hu : (Finset.univ : Finset (Fin l)) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [vertexSum, ← Finset.powerset_univ]
  conv_lhs => rw [hu]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu' => ?_
  have hsub := Finset.mem_powerset.1 hu'
  have hiu : i ∉ u := fun h => Finset.notMem_erase i _ (hsub h)
  have hcard : u.card + 1 ≤ l := by
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < l := Fin.pos i
    omega
  rw [Finset.card_insert_of_notMem hiu, show l - u.card = (l - (u.card + 1)) + 1 by omega,
    pow_succ]
  ring

/-- Cutting `(a, b]` by the hyperplane `xᵢ = x` splits the vertex sum. -/
theorem vertexSum_split (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) (i : Fin l) (x : ℝ) :
    vertexSum F a (Function.update b i x) + vertexSum F (Function.update a i x) b =
      vertexSum F a b := by
  rw [vertexSum_eq_erase F a b i, vertexSum_eq_erase F a _ i, vertexSum_eq_erase F _ b i,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu' => ?_
  have hiu : i ∉ u := fun h => Finset.notMem_erase i _ (Finset.mem_powerset.1 hu' h)
  have e1 : vertex a (Function.update b i x) u = vertex a b u := funext fun j => by
    by_cases hj : j ∈ u
    · have hji : j ≠ i := fun h => hiu (h ▸ hj)
      simp [vertex, hj, Function.update_of_ne hji]
    · simp [vertex, hj]
  have e2 : vertex a (Function.update b i x) (insert i u) =
      vertex (Function.update a i x) b u := funext fun j => by
    by_cases hji : j = i
    · subst hji; simp [vertex, hiu]
    · by_cases hj : j ∈ u <;> simp [vertex, hj, hji]
  have e3 : vertex (Function.update a i x) b (insert i u) = vertex a b (insert i u) :=
    funext fun j => by
      by_cases hji : j = i
      · subst hji; simp [vertex]
      · by_cases hj : j ∈ u <;> simp [vertex, hj, hji]
  rw [e1, e2, e3]
  ring

/-- The vertex sum as a box-additive map: additive on every partition of a box into boxes. -/
noncomputable def boxContent (F : (Fin l → ℝ) → ℝ) : BoxIntegral.BoxAdditiveMap (Fin l) ℝ ⊤ :=
  BoxIntegral.BoxAdditiveMap.ofMapSplitAdd (fun I => vertexSum F I.lower I.upper) ⊤
    fun I _ i x hx => by
      rw [BoxIntegral.Box.splitLower_def hx, BoxIntegral.Box.splitUpper_def hx]
      exact vertexSum_split F I.lower I.upper i x

theorem boxContent_apply (F : (Fin l → ℝ) → ℝ) (I : BoxIntegral.Box (Fin l)) :
    boxContent F I = vertexSum F I.lower I.upper := rfl

/-! ### The semiring of boxes -/

/-- Half-open boxes `(a, b]`, together with `∅`. -/
def boxes : Set (Set (Fin l → ℝ)) := insert ∅ (range fun p : (Fin l → ℝ) × (Fin l → ℝ) =>
  box p.1 p.2)

theorem box_mem_boxes (a b : Fin l → ℝ) : box a b ∈ (boxes : Set (Set (Fin l → ℝ))) :=
  mem_insert_of_mem _ ⟨(a, b), rfl⟩

theorem coe_box_eq (I : BoxIntegral.Box (Fin l)) : (I : Set (Fin l → ℝ)) = box I.lower I.upper :=
  BoxIntegral.Box.coe_eq_pi I

/-- A member of `boxes` is empty or a `BoxIntegral` box. -/
theorem eq_empty_or_coe {s : Set (Fin l → ℝ)} (hs : s ∈ (boxes : Set (Set (Fin l → ℝ)))) :
    s = ∅ ∨ ∃ I : BoxIntegral.Box (Fin l), s = I := by
  rcases hs with rfl | ⟨⟨a, b⟩, rfl⟩
  · exact Or.inl rfl
  by_cases h : ∀ i, a i < b i
  · exact Or.inr ⟨⟨a, b, h⟩, (coe_box_eq (⟨a, b, h⟩ : BoxIntegral.Box (Fin l))).symm⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inl (eq_empty_of_forall_notMem fun y hy => by
      have := hy i (mem_univ i); exact absurd (this.1.trans_le this.2) (not_lt.2 hi))

theorem coe_mem_boxes (I : BoxIntegral.Box (Fin l)) :
    (I : Set (Fin l → ℝ)) ∈ (boxes : Set (Set (Fin l → ℝ))) :=
  coe_box_eq I ▸ box_mem_boxes _ _

theorem isSetSemiring_boxes : IsSetSemiring (boxes : Set (Set (Fin l → ℝ))) where
  empty_mem := mem_insert _ _
  inter_mem s hs t ht := by
    rcases hs with rfl | ⟨⟨a, b⟩, rfl⟩
    · rw [empty_inter]; exact mem_insert _ _
    rcases ht with rfl | ⟨⟨c, d⟩, rfl⟩
    · rw [inter_empty]; exact mem_insert _ _
    simp only
    rw [box_inter]; exact box_mem_boxes _ _
  sdiff_eq_sUnion' s hs t ht := by
    classical
    rcases eq_empty_or_coe hs with rfl | ⟨I, rfl⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    have hst : (I : Set (Fin l → ℝ)) ∩ t ∈ (boxes : Set (Set (Fin l → ℝ))) := by
      rcases ht with rfl | ⟨⟨c, d⟩, rfl⟩
      · rw [inter_empty]; exact mem_insert _ _
      rw [coe_box_eq, box_inter]; exact box_mem_boxes _ _
    rw [← sdiff_inter_self_eq_sdiff, inter_comm]
    rcases eq_empty_or_coe hst with h | ⟨J, hJ⟩
    · rw [h, sdiff_empty]
      exact ⟨{(I : Set (Fin l → ℝ))}, by simpa using coe_mem_boxes I, by simp, by simp⟩
    have hJI : J ≤ I := (BoxIntegral.Box.coe_subset_coe).1 (hJ ▸ inter_subset_left)
    set π := (BoxIntegral.Prepartition.single I J hJI).compl
    refine ⟨π.boxes.image (↑), ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hu
      exact coe_mem_boxes K
    · intro u hu v hv huv
      obtain ⟨K₁, hK₁, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨K₂, hK₂, rfl⟩ := Finset.mem_image.1 hv
      exact π.disjoint_coe_of_mem hK₁ hK₂ fun h => huv (h ▸ rfl)
    · rw [hJ, ← BoxIntegral.Prepartition.iUnion_single hJI,
        ← BoxIntegral.Prepartition.iUnion_compl, BoxIntegral.Prepartition.iUnion_def',
        Finset.coe_image, sUnion_image, Finset.set_biUnion_coe]

/-! ### The content -/

variable {F : (Fin l → ℝ) → ℝ}

/-- A box as a set. -/
abbrev boxSet (J : BoxIntegral.Box (Fin l)) : Set (Fin l → ℝ) := J

open Classical in
/-- `Δ` on members of the semiring: `F`'s vertex sum on boxes, `0` on `∅`. -/
noncomputable def boxFun (F : (Fin l → ℝ) → ℝ) (s : Set (Fin l → ℝ)) : ℝ≥0∞ :=
  if h : ∃ I : BoxIntegral.Box (Fin l), (I : Set (Fin l → ℝ)) = s then
    ENNReal.ofReal (boxContent F h.choose) else 0

theorem boxFun_coe (I : BoxIntegral.Box (Fin l)) :
    boxFun F I = ENNReal.ofReal (boxContent F I) := by
  unfold boxFun
  split_ifs with h
  · rw [BoxIntegral.Box.injective_coe h.choose_spec]
  · exact absurd ⟨I, rfl⟩ h

theorem boxFun_of_notMem {s : Set (Fin l → ℝ)} (hs : s ∉ range ((↑) : BoxIntegral.Box (Fin l) →
    Set (Fin l → ℝ))) : boxFun F s = 0 := by
  unfold boxFun
  split_ifs with h
  · obtain ⟨I, hI⟩ := h; exact absurd ⟨I, hI⟩ hs
  · rfl

/-- The vertex sum as a finitely additive content on the semiring of boxes (needs (D3)). -/
noncomputable def stieltjesContent (F : (Fin l → ℝ) → ℝ)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) : AddContent ℝ≥0∞ (boxes : Set (Set (Fin l → ℝ)))
    where
  toFun := boxFun F
  empty' := boxFun_of_notMem fun ⟨I, hI⟩ => I.nonempty_coe.ne_empty hI
  sUnion' I hI hdis hU := by
    classical
    have hinj : InjOn (boxSet (l := l)) (boxSet ⁻¹' (I : Set (Set (Fin l → ℝ)))) :=
      BoxIntegral.Box.injective_coe.injOn
    rw [← Finset.sum_preimage boxSet I hinj (boxFun F) fun u _ hu => boxFun_of_notMem hu]
    have hmem : ∀ J, J ∈ I.preimage boxSet hinj → boxSet J ∈ I := fun J hJ =>
      Finset.mem_preimage.1 hJ
    rcases eq_empty_or_coe hU with h | ⟨I₀, hI₀⟩
    · have hsub : ∀ J ∈ I.preimage boxSet hinj, False := fun J hJ =>
        J.nonempty_coe.ne_empty (subset_empty_iff.1 (h ▸ subset_sUnion_of_mem
          (Finset.mem_coe.2 (hmem J hJ))))
      rw [h, Finset.sum_eq_zero fun J hJ => (hsub J hJ).elim]
      exact boxFun_of_notMem fun ⟨I, hI⟩ => I.nonempty_coe.ne_empty hI
    set π : BoxIntegral.Prepartition I₀ :=
      { boxes := I.preimage boxSet hinj
        le_of_mem' := fun J hJ => BoxIntegral.Box.coe_subset_coe.1
          (hI₀ ▸ subset_sUnion_of_mem (Finset.mem_coe.2 (hmem J hJ)))
        pairwiseDisjoint := fun J₁ hJ₁ J₂ hJ₂ hne =>
          hdis (Finset.mem_coe.2 (hmem J₁ hJ₁)) (Finset.mem_coe.2 (hmem J₂ hJ₂))
            fun h => hne (BoxIntegral.Box.injective_coe h) }
    have hπ : π.IsPartition := by
      rw [BoxIntegral.Prepartition.isPartition_iff_iUnion_eq,
        BoxIntegral.Prepartition.iUnion_def', ← hI₀]
      apply Subset.antisymm
      · exact iUnion₂_subset fun J hJ => subset_sUnion_of_mem (Finset.mem_coe.2 (hmem J hJ))
      · intro y hy
        obtain ⟨u, hu, hyu⟩ := mem_sUnion.1 hy
        rcases eq_empty_or_coe (hI hu) with rfl | ⟨J, rfl⟩
        · exact absurd hyu (notMem_empty y)
        · exact mem_iUnion₂.2 ⟨J, (Finset.mem_preimage (s := I) (f := boxSet) (hf := hinj)).2
            (Finset.mem_coe.1 hu), hyu⟩
    have hsum := (boxContent F).sum_partition_boxes le_top hπ
    rw [hI₀, boxFun_coe, ← hsum, ENNReal.ofReal_sum_of_nonneg (f := fun J => boxContent F J)
      fun J _ => hD3 _ _ fun i => (J.lower_lt_upper i).le]
    exact Finset.sum_congr rfl fun J _ => (boxFun_coe J).symm

theorem stieltjesContent_box (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) {a b : Fin l → ℝ}
    (h : ∀ i, a i < b i) :
    stieltjesContent F hD3 (box a b) = ENNReal.ofReal (vertexSum F a b) := by
  have : box a b = ((⟨a, b, h⟩ : BoxIntegral.Box (Fin l)) : Set (Fin l → ℝ)) :=
    (coe_box_eq (⟨a, b, h⟩ : BoxIntegral.Box (Fin l))).symm
  change boxFun F (box a b) = _
  rw [this, boxFun_coe]; rfl

/-! ### Continuity from above in every nonnegative direction -/

/-- (D2) and monotonicity give `F(y + δe) → F(y)` as `δ ↓ 0` for every `0 ≤ e ≤ 1`. -/
theorem tendsto_shift (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x) (y : Fin l → ℝ)
    {e : Fin l → ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Tendsto (fun δ : ℝ => F (y + δ • e)) (𝓝[>] 0) (𝓝 (F y)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hcont y) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact hmono fun i => by
      have := he0 i; simp only [Pi.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact hmono fun i => by
      have := he1 i; simp only [Pi.one_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, diag]; nlinarith

/-- The indicator vector of a set of coordinates. -/
def indVec (t : Finset (Fin l)) : Fin l → ℝ := fun j => if j ∈ t then 1 else 0

theorem indVec_nonneg (t : Finset (Fin l)) : 0 ≤ indVec t := fun j => by
  simp only [indVec, Pi.zero_apply]; split_ifs <;> norm_num

theorem indVec_le_one (t : Finset (Fin l)) : indVec t ≤ 1 := fun j => by
  simp only [indVec, Pi.one_apply]; split_ifs <;> norm_num

theorem vertex_add_upper (a b : Fin l → ℝ) (t : Finset (Fin l)) (δ : ℝ) :
    vertex a (b + diag δ) t = vertex a b t + δ • indVec t := funext fun j => by
  by_cases hj : j ∈ t <;> simp [vertex, indVec, diag, hj]

theorem vertex_add_lower (a b : Fin l → ℝ) (t : Finset (Fin l)) (δ : ℝ) :
    vertex (a + diag δ) b t = vertex a b t + δ • indVec tᶜ := funext fun j => by
  by_cases hj : j ∈ t <;> simp [vertex, indVec, diag, hj]

theorem tendsto_vertexSum_upper (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (a b : Fin l → ℝ) :
    Tendsto (fun δ : ℝ => vertexSum F a (b + diag δ)) (𝓝[>] 0) (𝓝 (vertexSum F a b)) := by
  simp only [vertexSum, vertex_add_upper]
  exact tendsto_finsetSum _ fun t _ => (tendsto_shift hmono hcont _ (indVec_nonneg t)
    (indVec_le_one t)).const_mul _

theorem tendsto_vertexSum_lower (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (a b : Fin l → ℝ) :
    Tendsto (fun δ : ℝ => vertexSum F (a + diag δ) b) (𝓝[>] 0) (𝓝 (vertexSum F a b)) := by
  simp only [vertexSum, vertex_add_lower]
  exact tendsto_finsetSum _ fun t _ => (tendsto_shift hmono hcont _ (indVec_nonneg tᶜ)
    (indVec_le_one tᶜ)).const_mul _

/-! ### Countable subadditivity -/

theorem ofReal_le_ofReal_add {x y : ℝ} (ε : ℝ≥0) (hy : 0 ≤ y) (h : x ≤ y + ε) :
    ENNReal.ofReal x ≤ ENNReal.ofReal y + ε := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hy ε.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal h

/-- Each member of the semiring lies in an open set inside a slightly larger box. -/
theorem exists_open_cover (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) {s : Set (Fin l → ℝ)}
    (hs : s ∈ (boxes : Set (Set (Fin l → ℝ)))) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ U V : Set (Fin l → ℝ), IsOpen U ∧ s ⊆ U ∧ U ⊆ V ∧ V ∈ (boxes : Set (Set (Fin l → ℝ))) ∧
      stieltjesContent F hD3 V ≤ stieltjesContent F hD3 s + ε := by
  rcases eq_empty_or_coe hs with rfl | ⟨I, rfl⟩
  · exact ⟨∅, ∅, isOpen_empty, subset_rfl, subset_rfl, mem_insert _ _, le_add_right le_rfl⟩
  have hlim := tendsto_vertexSum_upper hmono hcont I.lower I.upper
  obtain ⟨δ, hδlt, hδ0⟩ := ((hlim.eventually (gt_mem_nhds (show vertexSum F I.lower I.upper <
    vertexSum F I.lower I.upper + ε from lt_add_of_pos_right _ (NNReal.coe_pos.2 hε)))).and
    self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ0
  have hlt : ∀ i, I.lower i < (I.upper + diag δ : Fin l → ℝ) i := fun i => by
    simp only [Pi.add_apply, diag]; linarith [I.lower_lt_upper i]
  refine ⟨Set.pi univ fun i => Ioo (I.lower i) (I.upper i + δ), box I.lower (I.upper + diag δ),
    isOpen_set_pi finite_univ fun i _ => isOpen_Ioo, ?_, ?_, box_mem_boxes _ _, ?_⟩
  · rw [coe_box_eq]
    exact fun y hy i _ => ⟨(hy i (mem_univ i)).1, by linarith [(hy i (mem_univ i)).2]⟩
  · exact fun y hy i _ => ⟨(hy i (mem_univ i)).1, by
      simp only [Pi.add_apply, diag]; exact (hy i (mem_univ i)).2.le⟩
  · rw [stieltjesContent_box hD3 hlt]
    change _ ≤ boxFun F I + ε
    rw [boxFun_coe]
    exact ofReal_le_ofReal_add ε (hD3 _ _ fun i => (I.lower_lt_upper i).le) hδlt.le

/-- Each box contains a compact set containing a slightly smaller box. -/
theorem exists_compact_inner (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) (I : BoxIntegral.Box (Fin l)) {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ K W : Set (Fin l → ℝ), IsCompact K ∧ W ⊆ K ∧ K ⊆ I ∧
      W ∈ (boxes : Set (Set (Fin l → ℝ))) ∧
      stieltjesContent F hD3 I ≤ stieltjesContent F hD3 W + ε := by
  have hlim := tendsto_vertexSum_lower hmono hcont I.lower I.upper
  have hgap : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, δ < I.upper i - I.lower i :=
    eventually_all.2 fun i => nhdsWithin_le_nhds (gt_mem_nhds (sub_pos.2 (I.lower_lt_upper i)))
  obtain ⟨δ, ⟨hδlt, hδgap⟩, hδ0⟩ := (((hlim.eventually (lt_mem_nhds (show
    vertexSum F I.lower I.upper - ε < vertexSum F I.lower I.upper by
      exact sub_lt_self _ (NNReal.coe_pos.2 hε)))).and hgap).and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ0
  have hlt : ∀ i, (I.lower + diag δ : Fin l → ℝ) i < I.upper i := fun i => by
    simp only [Pi.add_apply, diag]; linarith [hδgap i]
  refine ⟨Icc (I.lower + diag δ) I.upper, box (I.lower + diag δ) I.upper, isCompact_Icc,
    fun y hy => ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2⟩, ?_,
    box_mem_boxes _ _, ?_⟩
  · rw [coe_box_eq]
    intro y hy i _
    have h1 := hy.1 i; have h2 := hy.2 i
    simp only [Pi.add_apply, diag] at h1
    exact ⟨by linarith, h2⟩
  · rw [stieltjesContent_box hD3 hlt]
    change boxFun F I ≤ _
    rw [boxFun_coe]
    exact ofReal_le_ofReal_add ε (hD3 _ _ fun i => (hlt i).le) (by
      rw [boxContent_apply]; linarith)

/-- The content is countably subadditive. -/
theorem isSigmaSubadditive (hmono : Monotone F) (hcont : ∀ x, ContFromAbove F x)
    (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) :
    (stieltjesContent F hD3).IsSigmaSubadditive := by
  intro f hf hU
  set m := stieltjesContent F hD3
  rcases eq_empty_or_coe hU with h | ⟨I, hI⟩
  · rw [h, addContent_empty]; exact zero_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨ε', hε'0, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 hε2.ne') ℕ
  choose U V hUo hfU hUV hV hmV using fun n => exists_open_cover hmono hcont hD3 (hf n)
    (hε'0 n)
  obtain ⟨K, W, hK, hWK, hKI, hW, hmW⟩ := exists_compact_inner hmono hcont hD3 I hε2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo
    (hKI.trans (hI ▸ iUnion_mono hfU))
  classical
  have hWsub : W ⊆ ⋃₀ ↑(t.image V) := by
    intro y hy
    obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (ht (hWK hy))
    exact mem_sUnion.2 ⟨V n, Finset.mem_coe.2 (Finset.mem_image_of_mem V hn), hUV n hyn⟩
  have h1 : m W ≤ ∑ u ∈ t.image V, m u :=
    addContent_le_sum_of_subset_sUnion isSetSemiring_boxes
      (fun u hu => by
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hu
        exact hV n) hW hWsub
  have h2 : ∑ u ∈ t.image V, m u ≤ ∑ n ∈ t, m (V n) := Finset.sum_image_le_of_nonneg
    fun _ _ => zero_le
  have h3 : ∑ n ∈ t, m (V n) ≤ ∑' n, m (f n) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    calc ∑ n ∈ t, m (V n) ≤ ∑ n ∈ t, (m (f n) + ε' n) := Finset.sum_le_sum fun n _ => hmV n
      _ = ∑ n ∈ t, m (f n) + ∑ n ∈ t, (ε' n : ℝ≥0∞) := Finset.sum_add_distrib
      _ ≤ ∑' n, m (f n) + ∑' n, (ε' n : ℝ≥0∞) :=
          add_le_add (ENNReal.sum_le_tsum t) (ENNReal.sum_le_tsum t)
      _ ≤ ∑' n, m (f n) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hε'sum.le
  rw [hI]
  calc m I ≤ m W + (ε / 2 : ℝ≥0) := hmW
    _ ≤ ∑' n, m (f n) + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) := by
        gcongr; exact h1.trans (h2.trans h3)
    _ = ∑' n, m (f n) + ε := by
        rw [add_assoc, ← ENNReal.coe_add, add_halves]

/-! ### Generation and the measure -/

theorem Iic_eq_iUnion_box (x : Fin l → ℝ) :
    Iic x = ⋃ n : ℕ, box (x - diag ((n : ℝ) + 1)) x := by
  ext y
  simp only [mem_Iic, mem_iUnion, box, Set.mem_pi, mem_univ, true_implies, mem_Ioc,
    Pi.sub_apply, diag]
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, (x i - y i))
    refine ⟨n, fun i => ⟨?_, hy i⟩⟩
    have : x i - y i ≤ ∑ j, (x j - y j) :=
      Finset.single_le_sum (f := fun j => x j - y j) (fun j _ => sub_nonneg.2 (hy j))
        (Finset.mem_univ i)
    linarith
  · rintro ⟨n, hn⟩ i
    exact (hn i).2

theorem borel_eq_generateFrom_boxes :
    (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) =
      MeasurableSpace.generateFrom (boxes : Set (Set (Fin l → ℝ))) := by
  apply le_antisymm
  · rw [← generateFrom_Iic_pi]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨x, rfl⟩
    beta_reduce
    rw [Iic_eq_iUnion_box]
    exact MeasurableSet.iUnion fun n =>
      MeasurableSpace.measurableSet_generateFrom (box_mem_boxes _ _)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ (rfl | ⟨⟨a, b⟩, rfl⟩)
    · exact MeasurableSet.empty
    · exact measurableSet_box a b

/-- `Δ((x - n1, x]) → F(x)` as `n → ∞`, by the limits of (D1). -/
theorem tendsto_vertexSum_Iic (h0 : ∀ x, 0 ≤ F x)
    (hlow : ∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → F x < ε) (x : Fin l → ℝ) :
    Tendsto (fun n : ℕ => vertexSum F (x - diag ((n : ℝ) + 1)) x) atTop (𝓝 (F x)) := by
  have hterm : ∀ t : Finset (Fin l), Tendsto (fun n : ℕ => F (vertex (x - diag ((n : ℝ) + 1)) x t))
      atTop (𝓝 (if t = Finset.univ then F x else 0)) := fun t => by
    split_ifs with ht
    · subst ht
      have : ∀ n : ℕ, vertex (x - diag ((n : ℝ) + 1)) x Finset.univ = x := fun n =>
        funext fun j => by simp [vertex]
      simp only [this]; exact tendsto_const_nhds
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ t := by
        by_contra hne; push Not at hne; exact ht (Finset.eq_univ_iff_forall.2 hne)
      rw [tendsto_order]
      refine ⟨fun c hc => Eventually.of_forall fun n => lt_of_lt_of_le hc (h0 _),
        fun c hc => ?_⟩
      obtain ⟨M, hM⟩ := hlow i c hc
      obtain ⟨N, hN⟩ := exists_nat_gt (x i - M)
      refine eventually_atTop.2 ⟨N, fun n hn => hM _ ?_⟩
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only [vertex, hi, ↓reduceIte, Pi.sub_apply, diag]
      linarith
  have := tendsto_finsetSum Finset.univ fun t _ => (hterm t).const_mul ((-1 : ℝ) ^ (l - t.card))
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul] at this
  exact this

/-- **Theorem 12.7b** (existence and uniqueness). If `F : ℝˡ → [0, 1]` satisfies (D1) (it is
nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all coordinates tend to
`+∞`), (D2) (it is continuous from above) and (D3) (its vertex sums are nonnegative), then `F` is
the distribution function of exactly one probability measure. -/
theorem theorem_12_7b (F : (Fin l → ℝ) → ℝ) (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1)
    (hmono : Monotone F) (hlow : ∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → F x < ε)
    (hup : ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < F x)
    (hcont : ∀ x, ContFromAbove F x) (hD3 : ∀ a b, a ≤ b → 0 ≤ vertexSum F a b) :
    ∃! μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ distFun μ = F := by
  set m := stieltjesContent F hD3
  set μ : Measure (Fin l → ℝ) := m.measure isSetSemiring_boxes borel_eq_generateFrom_boxes.le
    (isSigmaSubadditive hmono hcont hD3)
  have hμbox : ∀ a b : Fin l → ℝ, μ (box a b) = m (box a b) := fun a b =>
    m.measure_eq isSetSemiring_boxes borel_eq_generateFrom_boxes _ (box_mem_boxes a b)
  have hIic : ∀ x, μ (Iic x) = ENNReal.ofReal (F x) := fun x => by
    have hmono' : Monotone fun n : ℕ => box (x - diag ((n : ℝ) + 1)) x := fun m n hmn y hy i _ =>
      ⟨by
        have := (hy i (mem_univ i)).1
        simp only [Pi.sub_apply, diag] at this ⊢
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith, (hy i (mem_univ i)).2⟩
    have hA := tendsto_measure_iUnion_atTop (μ := μ) hmono'
    rw [← Iic_eq_iUnion_box] at hA
    have hB : Tendsto (fun n : ℕ => μ (box (x - diag ((n : ℝ) + 1)) x)) atTop
        (𝓝 (ENNReal.ofReal (F x))) := by
      have : ∀ n : ℕ, μ (box (x - diag ((n : ℝ) + 1)) x) =
          ENNReal.ofReal (vertexSum F (x - diag ((n : ℝ) + 1)) x) := fun n => by
        rw [hμbox, stieltjesContent_box hD3 fun i => by
          simp only [Pi.sub_apply, diag]; linarith [n.cast_nonneg (α := ℝ)]]
      simp only [this]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_vertexSum_Iic h0 hlow x)
    exact tendsto_nhds_unique hA hB
  have hprob : IsProbabilityMeasure μ := by
    constructor
    have hmono' : Monotone fun n : ℕ => Iic (diag (n : ℝ) : Fin l → ℝ) := fun m n hmn =>
      Iic_subset_Iic.2 fun i => by simp only [diag]; exact_mod_cast hmn
    have hU : (⋃ n : ℕ, Iic (diag (n : ℝ) : Fin l → ℝ)) = univ := eq_univ_of_forall fun y => by
      obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, |y i|)
      refine mem_iUnion.2 ⟨n, fun i => ?_⟩
      have : |y i| ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      simp only [diag]; linarith [le_abs_self (y i)]
    have hA := tendsto_measure_iUnion_atTop (μ := μ) hmono'
    rw [hU] at hA
    have hF1 : Tendsto (fun n : ℕ => F (diag (n : ℝ))) atTop (𝓝 1) := by
      rw [tendsto_order]
      refine ⟨fun c hc => ?_, fun c hc => Eventually.of_forall fun n => (h1 _).trans_lt hc⟩
      obtain ⟨M, hM⟩ := hup (1 - c) (by linarith)
      obtain ⟨N, hN⟩ := exists_nat_gt M
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have := hM (diag (n : ℝ)) fun i => by
        simp only [diag]; linarith [show (N : ℝ) ≤ n by exact_mod_cast hn]
      linarith
    have hB : Tendsto (fun n : ℕ => μ (Iic (diag (n : ℝ) : Fin l → ℝ))) atTop (𝓝 1) := by
      simp only [hIic]
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hF1
    exact tendsto_nhds_unique hA hB
  have hdist : distFun μ = F := funext fun x => by
    rw [distFun, measureReal_def, hIic, ENNReal.toReal_ofReal (h0 x)]
  exact ⟨μ, ⟨hprob, hdist⟩, fun ν ⟨_, hν⟩ => distFun_injective (hν.trans hdist.symm)⟩

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375)

* the **support** of a probability measure (p. 371): the intersection of two closed sets of measure
  one is closed of measure one ("(Why?)"), and on a second-countable space the smallest closed set
  of measure one exists (`exists_support`, by Lindelöf — the book's "extends to any family" needs
  separability);
* the general lemma behind every compactness argument of the chapter: a **tight** sequence of
  probability measures on a separable metric space has a weakly convergent subsequence
  (`exists_convWeak_subseq_of_tight`, through Prokhorov's theorem);
* **Theorem 12.9 (Helly)** and its **Corollary 1**, corrected: hypothesis (3), `Fₙ(a̲) = 0` and
  `Fₙ(b̄) = 1`, does not confine the measures to `[a̲, b̄]` when `l ≥ 2`
  (`theorem_12_9_false_hyp`: `δ_{(-n, 0)}` has no weakly convergent subsequence), and the
  conclusion `F(a̲) = 0` fails even for `l = 1` (`theorem_12_9_false_concl`: `δ_{1/(n+1)}`). The
  true statement takes the measures concentrated on `[a̲, b̄]` and concludes the same of the limit
  (`theorem_12_9_cor1`, `theorem_12_9`);
* **Exercise 12.6**: (a) holds for `l = 1` (`ex_12_6a`) and fails for `l = 2`
  (`ex_12_6a_false`); (b), (c) are tightness (`ex_12_6b`, `ex_12_6c`; closedness is not needed);
* **Corollary 2** (corrected): a monotone sequence of distribution functions of measures
  concentrated on `[a̲, b̄]` converges weakly (`theorem_12_9_cor2`).
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-! ### The support of a measure -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- `A` is the **support** of `μ` (SLP p. 371): the smallest closed set of measure one. -/
def IsSupport (μ : Measure X) (A : Set X) : Prop :=
  IsClosed A ∧ μ A = 1 ∧ ∀ B, IsClosed B → μ B = 1 → A ⊆ B

variable [OpensMeasurableSpace X]

/-- The "(Why?)" of p. 371: two closed sets of measure one meet in a closed set of measure one. -/
theorem support_inter (μ : Measure X) [IsProbabilityMeasure μ] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hμA : μ A = 1) (hμB : μ B = 1) : IsClosed (A ∩ B) ∧ μ (A ∩ B) = 1 := by
  refine ⟨hA.inter hB, (prob_compl_eq_zero_iff (hA.inter hB).measurableSet).1 ?_⟩
  rw [compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA.measurableSet).2 hμA)
    ((prob_compl_eq_zero_iff hB.measurableSet).2 hμB)

/-- The support exists and is unique on a second-countable space (SLP p. 371–372; the extension
from two sets to an arbitrary family needs Lindelöf). -/
theorem exists_support [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃! A, IsSupport μ A := by
  set C := {B : Set X | IsClosed B ∧ μ B = 1}
  have hcl : IsClosed (⋂₀ C) := isClosed_sInter fun B hB => hB.1
  have hnull : μ (⋂₀ C)ᶜ = 0 := by
    rw [compl_sInter]
    obtain ⟨T, hTc, hTsub, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable (compl '' C)
      (by rintro _ ⟨B, hB, rfl⟩; exact hB.1.isOpen_compl)
    rw [← hTeq]
    refine (measure_sUnion_null_iff hTc).2 fun U hU => ?_
    obtain ⟨B, hB, rfl⟩ := hTsub hU
    exact (prob_compl_eq_zero_iff hB.1.measurableSet).2 hB.2
  refine ⟨⋂₀ C, ⟨hcl, (prob_compl_eq_zero_iff hcl.measurableSet).1 hnull,
    fun B hB hμB => sInter_subset_of_mem ⟨hB, hμB⟩⟩, fun A hA => ?_⟩
  exact (hA.2.2 _ hcl ((prob_compl_eq_zero_iff hcl.measurableSet).1 hnull)).antisymm
    (sInter_subset_of_mem ⟨hA.1, hA.2.1⟩)

/-! ### Tightness and weakly convergent subsequences -/

/-- A **tight** sequence of probability measures on a separable metric space (for every `ε > 0` a
compact `K` with `λₙ(K) > 1 - ε` for all `n`) has a weakly convergent subsequence. This is the
form in which Helly's theorem is used throughout the chapter (Prokhorov's theorem). -/
theorem exists_convWeak_subseq_of_tight {S : Type*} [MetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S] (ls : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  let P : ℕ → ProbabilityMeasure S := fun n => ⟨ls n, inferInstance⟩
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure S) : Measure S) | μ ∈ range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => hεtop ▸ le_top⟩
    obtain ⟨K, hK, hKn⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    have h1 : (ls n).real Kᶜ ≤ ε.toReal := by
      rw [probReal_compl_eq_one_sub hK.measurableSet]; linarith [hKn n]
    change (ls n) Kᶜ ≤ ε
    rw [← ofReal_measureReal (μ := ls n) (s := Kᶜ), ← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨ν, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨ν, inferInstance, φ, hφ, fun f =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f⟩

/-! ### Helly's theorem -/

variable {l : ℕ}

/-- A weak limit of measures concentrated on a closed set is concentrated on it (Theorem 12.3b). -/
theorem measure_eq_one_of_convWeak {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ls : ℕ → Measure S} {μ : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure μ] (h : ConvWeak ls μ) {F : Set S} (hF : IsClosed F)
    (hls : ∀ n, ls n F = 1) : μ F = 1 := by
  have hlim := (theorem_12_3 ls μ).1.1 h F hF
  have h1 : 1 ≤ μ.real F := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨n, hn⟩ := (hlim ε hε).exists
    have h1n : (ls n).real F = 1 := by rw [measureReal_def, hls n, ENNReal.toReal_one]
    change (ls n).real F < _ at hn
    linarith
  have : μ.real F = 1 := le_antisymm measureReal_le_one h1
  rw [← ofReal_measureReal, this, ENNReal.ofReal_one]

/-- **Corollary 1 to Theorem 12.9** (Helly, measure form), corrected: probability measures on
`ℝˡ` concentrated on `[a̲, b̄]` have a subsequence converging weakly to a probability measure
concentrated on `[a̲, b̄]`. -/
theorem theorem_12_9_cor1 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight ls fun ε hε =>
    ⟨Icc a b, isCompact_Icc, fun n => by
      rw [measureReal_def, h n, ENNReal.toReal_one]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  exact ⟨μ, hμ, measure_eq_one_of_convWeak hconv isClosed_Icc fun n => h (φ n), φ, hφ, hconv⟩

/-- Concentration on `[a̲, b̄]` in terms of the distribution function: `F(x) = 0` whenever some
`xᵢ < a̲ᵢ`, and `F(b̄) = 1`. -/
theorem concentrated_iff {a b : Fin l → ℝ} (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    μ (Icc a b) = 1 ↔ (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 := by
  constructor
  · intro h
    have hc : μ (Icc a b)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 h
    refine ⟨fun x ⟨i, hi⟩ => ?_, ?_⟩
    · have : μ (Iic x) = 0 := measure_mono_null (t := (Icc a b)ᶜ) (fun y hy hyab => by
        exact absurd ((hyab.1 i).trans (hy i)) (not_le.2 hi)) hc
      rw [distFun, measureReal_def, this, ENNReal.toReal_zero]
    · have : μ (Iic b) = 1 :=
        le_antisymm prob_le_one (h ▸ measure_mono fun y hy => hy.2)
      rw [distFun, measureReal_def, this, ENNReal.toReal_one]
  · rintro ⟨h0, h1⟩
    have hb : μ (Iic b)ᶜ = 0 := by
      have : μ.real (Iic b)ᶜ = 0 := by
        rw [probReal_compl_eq_one_sub measurableSet_Iic]; rw [distFun] at h1; linarith
      exact (measureReal_eq_zero_iff).1 this
    have hk : ∀ i (k : ℕ), μ (Iic (Function.update b i (a i - 1 / (k + 1)))) = 0 := fun i k => by
      have := h0 (Function.update b i (a i - 1 / (k + 1))) ⟨i, by
        simp only [Function.update_self]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := k)]⟩
      exact (measureReal_eq_zero_iff).1 this
    refine (prob_compl_eq_zero_iff measurableSet_Icc).1 (measure_mono_null (t := (Iic b)ᶜ ∪
      ⋃ i, ⋃ k : ℕ, Iic (Function.update b i (a i - 1 / (k + 1)))) ?_
      (measure_union_null hb (measure_iUnion_null fun i => measure_iUnion_null (hk i))))
    intro y hy
    by_cases hyb : y ≤ b
    · right
      obtain ⟨i, hi⟩ : ∃ i, y i < a i := by
        by_contra hne; push Not at hne; exact hy ⟨hne, hyb⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hi)
      simp only [mem_iUnion]
      refine ⟨i, k, fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hji
      · simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne hji]; exact hyb j
    · exact Or.inl hyb

/-- **Theorem 12.9 (Helly)**, corrected: distribution functions vanishing whenever some
`xᵢ < a̲ᵢ` and equal to one at `b̄` have a subsequence converging weakly to a distribution
function with the same properties. -/
theorem theorem_12_9 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)]
    (h0 : ∀ n x, (∃ i, x i < a i) → distFun (ls n) x = 0) (h1 : ∀ n, distFun (ls n) b = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ :=
    theorem_12_9_cor1 ls fun n => (concentrated_iff (ls n)).2 ⟨h0 n, h1 n⟩
  exact ⟨μ, hμ, ((concentrated_iff μ).1 hab).1, ((concentrated_iff μ).1 hab).2, φ, hφ, hconv⟩

/-- The distribution function of a unit mass. -/
theorem distFun_dirac (p x : Fin l → ℝ) :
    distFun (Measure.dirac p) x = if p ≤ x then 1 else 0 := by
  rw [distFun, measureReal_def, Measure.dirac_apply' p measurableSet_Iic]
  split_ifs with h
  · rw [indicator_of_mem (show p ∈ Iic x from h)]; simp
  · rw [indicator_of_notMem (show p ∉ Iic x from h)]; simp

/-- The sequence `δ_{(-n, 0)}` on `ℝ²` has no weakly convergent subsequence: its mass escapes
to `-∞` in the first coordinate. -/
theorem not_convWeak_escape (φ : ℕ → ℕ) (hφ : StrictMono φ) (μ : Measure (Fin 2 → ℝ))
    [IsProbabilityMeasure μ] :
    ¬ ConvWeak ((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) μ := by
  intro hconv
  have : ∀ n, IsProbabilityMeasure
      (((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  set G : ℕ → Set (Fin 2 → ℝ) := fun M => {y | -(M : ℝ) < y 0}
  have hG : ∀ M, IsOpen (G M) := fun M => isOpen_lt continuous_const (continuous_apply 0)
  have hnull : ∀ M, μ (G M) = 0 := fun M => by
    have hlim := (theorem_12_3 _ μ).2.1.1 hconv (G M) (hG M)
    have : μ.real (G M) ≤ 0 := le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨n, hn, hnM⟩ := ((hlim ε hε).and (eventually_ge_atTop M)).exists
      have hφn : M ≤ φ n := hnM.trans (hφ.id_le n)
      have : ((Measure.dirac (![-(φ n : ℝ), 0] : Fin 2 → ℝ))).real (G M) = 0 := by
        rw [measureReal_def, Measure.dirac_apply' _ (hG M).measurableSet,
          indicator_of_notMem (by simpa [G] using hφn)]; simp
      simp only [Function.comp_apply] at hn
      linarith
    exact (measureReal_eq_zero_iff).1 (le_antisymm this measureReal_nonneg)
  have hU : (⋃ M, G M) = univ := eq_univ_of_forall fun y => by
    obtain ⟨M, hM⟩ := exists_nat_gt (-(y 0))
    exact mem_iUnion.2 ⟨M, by simp only [G, mem_ofPred]; linarith⟩
  have := measure_iUnion_null hnull
  rw [hU, measure_univ] at this
  exact one_ne_zero this

/-- **Theorem 12.9 / Corollary 1 are false as printed (hypothesis).** On `ℝ²`, `δ_{(-n, 0)}`
satisfies (3) with `a̲ = (0, -1)`, `b̄ = (1, 1)` (`Fₙ(a̲) = 0`, `Fₙ(b̄) = 1`), but no
subsequence converges weakly. -/
theorem theorem_12_9_false_hyp :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ n, distFun (ls n) ![0, -1] = 0 ∧ distFun (ls n) ![1, 1] = 1) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun n => ⟨?_, ?_⟩, fun φ hφ μ _ => not_convWeak_escape φ hφ μ⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 1; norm_num at this
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; fin_cases i <;> simp; linarith [n.cast_nonneg (α := ℝ)]

/-- **Theorem 12.9 / Corollary 1 are false as printed (conclusion).** On `ℝ`, `δ_{1/(n+1)}`
satisfies (3) with `a̲ = 0`, `b̄ = 1`, and does converge weakly, but every weak limit of every
subsequence has `F(a̲) = 1`, not `0`. -/
theorem theorem_12_9_false_concl :
    let ls := fun n : ℕ => Measure.dirac (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)
    (∀ n, distFun (ls n) 0 = 0 ∧ distFun (ls n) 1 = 1) ∧ ConvWeak ls (Measure.dirac 0) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ →
        ConvWeak (ls ∘ φ) μ → distFun μ 0 = 1 := by
  intro ls
  have hconv : ConvWeak ls (Measure.dirac 0) := fun f => by
    simp only [ls, integral_dirac]
    exact (f.continuous.tendsto 0).comp (tendsto_pi_nhds.2 fun _ =>
      tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨fun n => ⟨?_, ?_⟩, hconv, fun φ hφ μ _ h => ?_⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 0; simp only [Pi.zero_apply] at this
    linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; simp only [Pi.one_apply]
    exact (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  · have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
      inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
    have : μ = Measure.dirac 0 :=
      convWeak_unique h fun f => (hconv f).comp hφ.tendsto_atTop
    rw [this, distFun_dirac, ite_eq_left_iff]
    exact fun h => absurd le_rfl h

/-! ### Exercise 12.6 -/

/-- **Exercise 12.6a** (`l = 1`). If for every `ε > 0` there are `a̲, b̄` with
`Fₙ(b̄) - Fₙ(a̲) > 1 - ε` for all `n`, some subsequence converges weakly. -/
theorem ex_12_6a (ls : ℕ → Measure (Fin 1 → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (h : ∀ ε > 0, ∃ a b : Fin 1 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) :
    ∃ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  refine exists_convWeak_subseq_of_tight ls fun ε hε => ?_
  obtain ⟨a, b, hab⟩ := h ε hε
  refine ⟨Icc a b, isCompact_Icc, fun n => (hab n).trans_le ?_⟩
  have hsub : Iic b \ Iic a ⊆ Icc a b := fun y ⟨hyb, hya⟩ => by
    refine ⟨fun i => ?_, hyb⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_contra hlt
    exact hya fun j => (Subsingleton.elim j 0 ▸ (not_le.1 hlt).le)
  exact (le_measureReal_sdiff).trans (measureReal_mono hsub)

/-- **Exercise 12.6a is false for `l ≥ 2`**: `δ_{(-n, 0)}` on `ℝ²` has `Fₙ(b̄) - Fₙ(a̲) = 1` for
`a̲ = (0, -1)`, `b̄ = (1, 1)`, yet no subsequence converges weakly. -/
theorem ex_12_6a_false :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ ε > 0, ∃ a b : Fin 2 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun ε hε => ⟨![0, -1], ![1, 1], fun n => ?_⟩, theorem_12_9_false_hyp.2⟩
  rw [(theorem_12_9_false_hyp.1 n).1, (theorem_12_9_false_hyp.1 n).2]
  linarith

/-- **Exercise 12.6b.** A tight sequence of probability measures on `ℝˡ` has a weakly convergent
subsequence. -/
theorem ex_12_6b (ls : ℕ → Measure (Fin l → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-- **Exercise 12.6c.** The same on `S ⊆ ℝˡ` (the book assumes `S` closed; this is not needed). -/
theorem ex_12_6c {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-! ### Corollary 2: monotone sequences -/

/-- **Corollary 2 to Theorem 12.9**, corrected: a monotone sequence of distribution functions
(`Fₙ₊₁ ≤ Fₙ` for all `n`, or `Fₙ₊₁ ≥ Fₙ` for all `n`) of measures concentrated on `[a̲, b̄]`
converges weakly to a probability measure concentrated on `[a̲, b̄]`. Proof: Helly gives a
subsequential limit `μ`; the whole sequence `Fₙ(x)` converges (bounded and monotone), so at
continuity points of `F_μ` its limit is `F_μ(x)`, and Theorem 12.8 applies. -/
theorem theorem_12_9_cor2 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1)
    (hmono : (∀ n, distFun (ls (n + 1)) ≤ distFun (ls n)) ∨
      (∀ n, distFun (ls n) ≤ distFun (ls (n + 1)))) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧ ConvWeak ls μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ := theorem_12_9_cor1 ls h
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  have hconvx : ∀ x, ∃ c, Tendsto (fun n => distFun (ls n) x) atTop (𝓝 c) := fun x => by
    have hbdd : ∀ n, 0 ≤ distFun (ls n) x ∧ distFun (ls n) x ≤ 1 := fun n =>
      ⟨measureReal_nonneg, measureReal_le_one⟩
    rcases hmono with hm | hm
    · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => hm n x)
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (hbdd n).1⟩⟩
    · exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hm n x)
        ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbdd n).2⟩⟩
  refine ⟨μ, hμ, hab, (theorem_12_8 ls μ).2 fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hconvx x
  have hsub := (theorem_12_8 (ls ∘ φ) μ).1 hconv x hx
  rwa [tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hsub] at hc

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378)

* **Exercise 12.7**: on any metric space, the Feller property `T[C(S)] ⊆ C(S)` is equivalent to
  `sₙ → s ⇒ P(sₙ, ·) ⇒ P(s, ·)` and to `λₙ ⇒ λ ⇒ T*λₙ ⇒ T*λ` (`ex_12_7`);
* **Exercise 12.8**: the cycle `s ↦ 1 - s` on `[0, 1]` is Feller; from `δ_s`, `s ≠ 1/2`, the even
  and odd iterates converge to the distinct non-invariant `δ_s`, `δ_{1-s}`; the invariant
  measures are exactly the measures symmetric about `1/2` (`ex_12_8a`–`ex_12_8c`);
* the limit step shared by Theorems 12.10 and 12.12 and Exercise 12.12 (`invariant_of_convWeak`):
  if `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
  invariant;
* **Theorem 12.10**: on a compact metric space a Feller transition function has an invariant
  probability measure, through the Cesàro averages of `T*ⁿδ_s` and Prokhorov's theorem. (The book
  works on compact `S ⊆ ℝˡ` and invokes Helly on `ℝˡ`; any compact metric space works. `S` must be
  nonempty.)
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
/-- Bounded continuous functions are bounded by their sup norm. -/
theorem bcf_abs_le_norm (f : S →ᵇ ℝ) (s : S) : |f s| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s

/-- Point masses at a convergent sequence converge weakly. -/
theorem convWeak_dirac {s : ℕ → S} {s₀ : S} (hs : Tendsto s atTop (𝓝 s₀)) :
    ConvWeak (fun n => Measure.dirac (s n)) (Measure.dirac s₀) := fun f => by
  simp only [integral_dirac]
  exact (f.continuous.tendsto s₀).comp hs

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [MetricSpace S] [BorelSpace S] [IsMarkovKernel κ] in
theorem adjointOp_dirac (s : S) : adjointOp κ (Measure.dirac s) = κ s :=
  Measure.dirac_bind κ.measurable s

/-- `∫ Tf dλ = ∫ f d(T*λ)` for bounded continuous `f` (Theorem 8.3). -/
theorem integral_markovOpR (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovOpR κ f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  theorem_8_3_cor κ lam f.continuous.measurable (bcf_abs_le_norm f)

/-- Under the Feller property, `Tf` as a bounded continuous function. -/
noncomputable def fellerBCF {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) :
    S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨markovOpR κ f, hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩⟩ (2 * ‖f‖) fun x y => by
      have hx := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 x
      have hy := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      linarith [abs_sub (markovOpR κ f x) (markovOpR κ f y)]

theorem fellerBCF_apply {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : fellerBCF hF f s = markovOpR κ f s := rfl

/-- **Exercise 12.7.** On a metric space the following are equivalent: (a) the Feller property;
(b) `sₙ → s` implies `P(sₙ, ·) ⇒ P(s, ·)`; (c) `λₙ ⇒ λ` implies `T*λₙ ⇒ T*λ`. -/
theorem ex_12_7 :
    (IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀)) ∧
    (IsFeller κ ↔ ∀ (ls : ℕ → Measure S) (lam : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
      IsProbabilityMeasure lam → ConvWeak ls lam →
        ConvWeak (fun n => adjointOp κ (ls n)) (adjointOp κ lam)) := by
  have hab : IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀) := by
    constructor
    · intro hF s s₀ hs f
      exact ((hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩).tendsto s₀).comp hs
    · intro h f hf ⟨M, hM⟩
      rw [continuous_iff_seqContinuous]
      intro s s₀ hs
      exact h s s₀ hs (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        linarith [abs_sub (f x) (f y), hM x, hM y])
  refine ⟨hab, ⟨fun hF ls lam hls hlam h f => ?_, fun h => hab.2 fun s s₀ hs => ?_⟩⟩
  · rw [← integral_markovOpR κ lam f]
    exact (h (fellerBCF hF f)).congr fun n => integral_markovOpR κ (ls n) f
  · have := h _ _ (fun n => inferInstance) inferInstance (convWeak_dirac hs)
    simpa only [adjointOp_dirac] using this

/-! ### Exercise 12.8: the cycle `s ↦ 1 - s` -/

/-- The transition function of `sₜ₊₁ = 1 - sₜ` on `[0, 1]`: `P(s, ·) = δ_{1-s}`. -/
noncomputable def flipKernel : Kernel unitInterval unitInterval :=
  Kernel.deterministic unitInterval.symm unitInterval.continuous_symm.measurable

theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel := by
  unfold flipKernel; infer_instance

theorem adjointOp_flip (μ : Measure unitInterval) :
    adjointOp flipKernel μ = μ.map unitInterval.symm :=
  Measure.deterministic_comp_eq_map _

theorem adjointOp_flip_dirac (s : unitInterval) :
    adjointOp flipKernel (Measure.dirac s) = Measure.dirac (unitInterval.symm s) := by
  rw [adjointOp_flip, Measure.map_dirac' unitInterval.continuous_symm.measurable]

/-- **Exercise 12.8a.** `P(s, ·) = δ_{1-s}`, and `P` has the Feller property. -/
theorem ex_12_8a : (∀ s, flipKernel s = Measure.dirac (unitInterval.symm s)) ∧
    IsFeller flipKernel := by
  have hP : ∀ s, flipKernel s = Measure.dirac (unitInterval.symm s) := fun s =>
    Kernel.deterministic_apply _ s
  refine ⟨hP, fun f hf _ => ?_⟩
  have : markovOpR flipKernel f = f ∘ unitInterval.symm := funext fun s => by
    simp only [markovOpR, hP, integral_dirac, Function.comp_apply]
  rw [this]
  exact hf.comp unitInterval.continuous_symm

theorem iterate_flip_dirac (s : unitInterval) (n : ℕ) :
    (adjointOp flipKernel)^[2 * n] (Measure.dirac s) = Measure.dirac s ∧
      (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s) =
        Measure.dirac (unitInterval.symm s) := by
  induction n with
  | zero => exact ⟨rfl, adjointOp_flip_dirac s⟩
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h2, Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac, unitInterval.symm_symm,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac,
      unitInterval.symm_symm, adjointOp_flip_dirac]
    exact ⟨rfl, rfl⟩

theorem symm_ne_self {s : unitInterval} (hs : (s : ℝ) ≠ 1 / 2) : unitInterval.symm s ≠ s := by
  intro h
  have := congrArg Subtype.val h
  rw [unitInterval.coe_symm_eq] at this
  exact hs (by linarith)

/-- **Exercise 12.8b.** From `δ_s` with `s ≠ 1/2`, the even iterates converge to `δ_s` and the odd
ones to `δ_{1-s}`; the two limits differ and neither is invariant. -/
theorem ex_12_8b (s : unitInterval) (hs : (s : ℝ) ≠ 1 / 2) :
    ConvWeak (fun n => (adjointOp flipKernel)^[2 * n] (Measure.dirac s)) (Measure.dirac s) ∧
      ConvWeak (fun n => (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s))
        (Measure.dirac (unitInterval.symm s)) ∧
      Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) ∧
      adjointOp flipKernel (Measure.dirac s) ≠ Measure.dirac s ∧
      adjointOp flipKernel (Measure.dirac (unitInterval.symm s)) ≠
        Measure.dirac (unitInterval.symm s) := by
  have hne : Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) := fun h =>
    symm_ne_self hs (dirac_eq_dirac_iff.1 h).symm
  refine ⟨fun f => ?_, fun f => ?_, hne, ?_, ?_⟩
  · simp only [fun n => (iterate_flip_dirac s n).1]; exact tendsto_const_nhds
  · simp only [fun n => (iterate_flip_dirac s n).2]; exact tendsto_const_nhds
  · rw [adjointOp_flip_dirac]; exact hne.symm
  · rw [adjointOp_flip_dirac, unitInterval.symm_symm]; exact hne

/-- **Exercise 12.8c.** The invariant measures are exactly the measures symmetric about `1/2`;
among them are `δ_{1/2}` and `½(δ_s + δ_{1-s})` for every `s`, so there are infinitely many. -/
theorem ex_12_8c :
    (∀ μ : Measure unitInterval, adjointOp flipKernel μ = μ ↔ μ.map unitInterval.symm = μ) ∧
      ∀ s : unitInterval, adjointOp flipKernel
        ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s))) =
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s)) := by
  refine ⟨fun μ => by rw [adjointOp_flip], fun s => ?_⟩
  have hm := unitInterval.continuous_symm.measurable
  rw [adjointOp_flip, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm, unitInterval.symm_symm, add_comm]
  exact hm.aemeasurable

/-! ### Invariant limits and Theorem 12.10 -/

variable {κ}

omit [MetricSpace S] [BorelSpace S] in
theorem isProbabilityMeasure_iterate (lam : Measure S) [IsProbabilityMeasure lam] (n : ℕ) :
    IsProbabilityMeasure ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (theorem_8_2 κ _).1

/-- If `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
invariant under a Feller `P` (the limit step of Theorem 12.10). -/
theorem invariant_of_convWeak (hF : IsFeller κ) {ν : ℕ → Measure S}
    [∀ n, IsProbabilityMeasure (ν n)] {μ : Measure S} [IsProbabilityMeasure μ]
    (hconv : ConvWeak ν μ)
    (hdiff : ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ν n - ∫ s, f s ∂adjointOp κ (ν n))
      atTop (𝓝 0)) : adjointOp κ μ = μ := by
  have : IsProbabilityMeasure (adjointOp κ μ) := (theorem_8_2 κ μ).1
  refine theorem_12_6_cor2 fun f => ?_
  rw [← integral_markovOpR κ μ f]
  have h1 : Tendsto (fun n => ∫ s, f s ∂adjointOp κ (ν n)) atTop (𝓝 (∫ s, f s ∂μ)) := by
    have := (hconv f).sub (hdiff f)
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  exact tendsto_nhds_unique ((hconv (fellerBCF hF f)).congr fun n =>
    integral_markovOpR κ (ν n) f) h1

/-- **Theorem 12.10.** On a nonempty compact metric space, a transition function with the Feller
property has an invariant probability measure. -/
theorem theorem_12_10 [CompactSpace S] [Nonempty S] (hF : IsFeller κ) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  have : TopologicalSpace.SeparableSpace S := inferInstance
  set lam₀ := Measure.dirac (Classical.arbitrary S)
  set L : ℕ → Measure S := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  set avg : ℕ → Measure S := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul, c]
    push_cast
    exact ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)⟩
  have hint : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← integral_markovOpR κ (avg N) g]
    change ∫ s, fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← integral_markovOpR κ (L n) g]
    rfl
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight avg fun ε hε =>
    ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, invariant_of_convWeak hF hconv fun f => ?_⟩
  have hdiff : ∀ N, ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * (∫ s, f s ∂L 0 - ∫ s, f s ∂L (N + 1)) := fun N => by
    rw [hint, hintT, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hbd : ∀ n, |∫ s, f s ∂L n| ≤ ‖f‖ := fun n => by
    rw [← Real.norm_eq_abs]
    exact f.norm_integral_le_norm (L n)
  have hlim : Tendsto (fun N : ℕ => ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N)) atTop
      (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖)) (fun N => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
      linarith [abs_sub (∫ s, f s ∂L 0) (∫ s, f s ∂L (N + 1)), hbd 0, hbd (N + 1)]
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).mul_const (2 * ‖f‖)
  exact hlim.comp hφ.tendsto_atTop

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monotone Markov processes (SLP §12.4, pp. 378–383)

* **dominance** `μ ≥ λ` (p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for all bounded measurable nondecreasing `f`;
* **Exercise 12.9**: dominance orders distribution functions the other way (`ex_12_9a`); on `ℝ`
  the converse holds (`ex_12_9b`, via the layer-cake formula and the classification of lower
  sets of `ℝ`); on `ℝ²` it fails (`ex_12_9c`, `μ = ½(δ_{(1,0)} + δ_{(0,1)})`,
  `λ = ½(δ_{(0,0)} + δ_{(1,1)})`);
* **Exercise 12.10**: squeezing between dominance-ordered weakly convergent sequences (for any
  `S ⊆ ℝˡ`, not only rectangles);
* **Exercise 12.11**: `P` monotone ⇔ `T*` preserves dominance ⇔ `s ≥ s′ ⇒ P(s, ·) ≥ P(s′, ·)`;
* monotone sequences of measures on `[a, b]` converge weakly (`convWeak_of_dominance_mono`, from
  Corollary 2 to Helly);
* **Exercise 12.12**: `T*ⁿδ_a` increases and `T*ⁿδ_b` decreases, and both converge to invariant
  measures;
* **Assumption 12.1**, **Exercise 12.14**, **Lemma 12.11** and **Theorem 12.12** (a monotone Feller
  process satisfying the mixing condition has a unique invariant measure, which is globally
  stable). The proof of Theorem 12.12 supplies the two steps the book leaves implicit: the lower
  bound `(Tⁿf)(b) - (Tⁿf)(a) ≥ 0`, and uniqueness from global convergence.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

/-! ### Dominance -/

variable {S : Type*} [MeasurableSpace S] [Preorder S]

/-- `μ` **dominates** `λ` (SLP p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for every bounded measurable
nondecreasing `f`. -/
def Dominates (μ lam : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ M, ∀ s, |f s| ≤ M) → Monotone f → ∫ s, f s ∂lam ≤ ∫ s, f s ∂μ

theorem Dominates.trans {μ ν lam : Measure S} (h1 : Dominates μ ν) (h2 : Dominates ν lam) :
    Dominates μ lam := fun f hf hb hm => (h2 f hf hb hm).trans (h1 f hf hb hm)

/-- Dominance compares the masses of measurable upper sets. -/
theorem Dominates.real_le {μ lam : Measure S} (h : Dominates μ lam) {U : Set S}
    (hU : MeasurableSet U) (hup : IsUpperSet U) : lam.real U ≤ μ.real U := by
  have hm : Monotone (U.indicator (1 : S → ℝ)) := fun s t hst => by
    by_cases hs : s ∈ U
    · simp [hs, hup hst hs]
    · rw [indicator_of_notMem hs]; exact indicator_nonneg (fun _ _ => zero_le_one) t
  have := h (U.indicator 1) (measurable_const.indicator hU) ⟨1, fun s => by
    by_cases hs : s ∈ U
    · rw [indicator_of_mem hs, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem hs, abs_zero]; exact zero_le_one⟩ hm
  rwa [integral_indicator_one hU, integral_indicator_one hU] at this

variable {l : ℕ}

/-- **Exercise 12.9a.** If `μ ≥ λ` on `ℝˡ` then `F_μ ≤ F_λ`. -/
theorem ex_12_9a {μ lam : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    distFun μ x ≤ distFun lam x := by
  have := h.real_le measurableSet_Iic.compl (isLowerSet_Iic x).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  simp only [distFun]; linarith

/-- **Exercise 12.9a** on `S ⊆ ℝˡ`: if `μ ≥ λ` then `μ(S ∩ (-∞, x]) ≤ λ(S ∩ (-∞, x])` for every
`x ∈ ℝˡ`. -/
theorem ex_12_9a_subtype {S : Set (Fin l → ℝ)} {μ lam : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    μ.real (Subtype.val ⁻¹' Iic x) ≤ lam.real (Subtype.val ⁻¹' Iic x) := by
  have hm : MeasurableSet (Subtype.val ⁻¹' Iic x : Set S) :=
    measurableSet_Iic.preimage measurable_subtype_coe
  have := h.real_le hm.compl (fun s t (hst : (s : Fin l → ℝ) ≤ t) hs ht => hs (hst.trans ht))
  rw [probReal_compl_eq_one_sub hm, probReal_compl_eq_one_sub hm] at this
  linarith

/-- On `ℝ`, `F_μ ≤ F_λ` gives `μ(L) ≤ λ(L)` for every lower set `L`: `L` is `∅`, `ℝ`,
`(-∞, c]` or `(-∞, c)`. -/
theorem measure_lower_le {μ lam : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) {L : Set ℝ} (hL : IsLowerSet L) :
    μ L ≤ lam L := by
  have hE : ∀ x, μ (Iic x) ≤ lam (Iic x) := fun x =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (h x)
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  by_cases hbdd : BddAbove L
  · by_cases hc : sSup L ∈ L
    · have : L = Iic (sSup L) :=
        Subset.antisymm (fun y hy => le_csSup hbdd hy) (fun y hy => hL hy hc)
      rw [this]; exact hE _
    · have hLc : L = ⋃ n : ℕ, Iic (sSup L - 1 / ((n : ℝ) + 1)) := by
        ext y
        simp only [mem_iUnion, mem_Iic]
        constructor
        · intro hy
          have hlt : y < sSup L := lt_of_le_of_ne (le_csSup hbdd hy) fun h => hc (h ▸ hy)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩
          have := Nat.one_div_pos_of_nat (α := ℝ) (n := n)
          obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y < sSup L by linarith)
          exact hL hyz.le hz
      have hmono : Monotone fun n : ℕ => Iic (sSup L - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
        Iic_subset_Iic.2 (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
              linarith)) _)
      rw [hLc]
      exact le_of_tendsto_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
        (tendsto_measure_iUnion_atTop hmono) fun n => hE _
  · have : L = univ := eq_univ_of_forall fun y => by
      obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.1 hbdd y
      exact hL hyz.le hz
    rw [this, measure_univ, measure_univ]

/-- **Exercise 12.9b.** On `ℝ`, `F_μ ≤ F_λ` implies `μ ≥ λ`. -/
theorem ex_12_9b (μ lam : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) : Dominates μ lam := by
  intro f hf ⟨M, hM⟩ hmono
  set g := fun s => f s + M
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    have := hM s; rw [abs_le] at this; simp only [g]; linarith
  have hgM : ∀ s, |g s| ≤ 2 * M := fun s => by
    have := hM s; rw [abs_le] at this
    rw [abs_of_nonneg (hg0 s)]; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const M
  have hshift : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ s, f s ∂ν = ∫ s, g s ∂ν - M :=
    fun ν _ => by
      simp only [g]
      rw [integral_add (integrable_of_bounded hf hM) (integrable_const M), integral_const,
        probReal_univ, one_smul]
      ring
  have hlc : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫ s, g s ∂ν = (∫⁻ t in Ioi 0, ν {s | t < g s}).toReal := fun ν _ => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hgm.aemeasurable]
  have hup : ∀ t, IsUpperSet {s | t < g s} := fun t s s' hss' (hs : t < g s) =>
    show t < g s' from lt_of_lt_of_le hs (add_le_add_left (hmono hss') M)
  have hle : ∀ t, lam {s | t < g s} ≤ μ {s | t < g s} := fun t => by
    have hmeas : MeasurableSet {s | t < g s} := measurableSet_lt measurable_const hgm
    have := measure_lower_le h (hup t).compl
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 this
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hmeas,
      probReal_compl_eq_one_sub hmeas] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (by
      rw [← measureReal_def, ← measureReal_def]; linarith)
  have hfin : ∫⁻ t in Ioi 0, μ {s | t < g s} ≠ ⊤ := by
    rw [← lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hgm.aemeasurable]
    exact (integrable_of_bounded hgm hgM (μ := μ)).lintegral_lt_top.ne
  rw [hshift lam, hshift μ, hlc lam, hlc μ]
  linarith [ENNReal.toReal_mono hfin (lintegral_mono hle)]

/-- The mass of a measurable set under `½(δ_p + δ_q)`. -/
theorem real_half_dirac {α : Type*} [MeasurableSpace α] (p q : α) {A : Set α}
    (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac p + Measure.dirac q)).real A =
      (A.indicator (1 : α → ℝ) p + A.indicator (1 : α → ℝ) q) / 2 := by
  rw [measureReal_def, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' p hA,
    Measure.dirac_apply' q hA, smul_eq_mul]
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;>
    simp [hp, hq, ENNReal.toReal_inv, ENNReal.toReal_add]
  all_goals norm_num

/-- **Exercise 12.9c.** On `ℝ²` the converse of Exercise 12.9a fails:
`μ = ½(δ_{(1,0)} + δ_{(0,1)})` and `λ = ½(δ_{(0,0)} + δ_{(1,1)})` have `F_μ ≤ F_λ`, but the
nondecreasing indicator of `{x ≥ (1, 1)}` integrates to `0` under `μ` and to `½` under `λ`. -/
theorem ex_12_9c :
    let μ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![1, 0] : Fin 2 → ℝ) + Measure.dirac ![0, 1])
    let lam := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![0, 0] : Fin 2 → ℝ) + Measure.dirac ![1, 1])
    (∀ x, distFun μ x ≤ distFun lam x) ∧ ¬ Dominates μ lam := by
  intro μ lam
  have hle : ∀ (a b : ℝ) (x : Fin 2 → ℝ), (![a, b] : Fin 2 → ℝ) ≤ x ↔ a ≤ x 0 ∧ b ≤ x 1 :=
    fun a b x => by simp [Pi.le_def, Fin.forall_fin_two]
  have hle2 : ∀ a b c d : ℝ, (![a, b] : Fin 2 → ℝ) ≤ ![c, d] ↔ a ≤ c ∧ b ≤ d :=
    fun a b c d => by simp [Pi.le_def, Fin.forall_fin_two]
  refine ⟨fun x => ?_, fun h => ?_⟩
  · have i1 : ∀ p : Fin 2 → ℝ, 0 ≤ (Iic x).indicator (1 : (Fin 2 → ℝ) → ℝ) p := fun p =>
      indicator_nonneg (fun _ _ => zero_le_one) p
    have hA : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨by linarith [h.1], h.2⟩
    have hB : (![0, 1] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨h.1, by linarith [h.2]⟩
    have hC : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 1] : Fin 2 → ℝ) ∈ Iic x →
        (![1, 1] : Fin 2 → ℝ) ∈ Iic x := fun h h' => by
      rw [mem_Iic, hle] at h h' ⊢; exact ⟨h.1, h'.2⟩
    simp only [distFun, μ, lam, real_half_dirac _ _ measurableSet_Iic]
    by_cases h1 : (![1, 0] : Fin 2 → ℝ) ∈ Iic x <;> by_cases h2 : (![0, 1] : Fin 2 → ℝ) ∈ Iic x
    · simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (hA h1),
        indicator_of_mem (hC h1 h2), Pi.one_apply, le_refl]
    · simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_mem (hA h1),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem (hB h2),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2]
      linarith [i1 ![0, 0], i1 ![1, 1]]
  · have hU : MeasurableSet (Ici (![1, 1] : Fin 2 → ℝ)) := measurableSet_Ici
    have := h.real_le hU (isUpperSet_Ici _)
    have n00 : (![0, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have n10 : (![1, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.2]
    have n01 : (![0, 1] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have m11 : (![1, 1] : Fin 2 → ℝ) ∈ Ici ![1, 1] := mem_Ici.2 le_rfl
    simp only [μ, lam, real_half_dirac _ _ hU, indicator_of_notMem n00, indicator_of_notMem n10,
      indicator_of_notMem n01, indicator_of_mem m11, Pi.one_apply] at this
    linarith

/-! ### Exercise 12.10 -/

theorem distFun_map_val {S : Set (Fin l → ℝ)} (ν : Measure S) (x : Fin l → ℝ) :
    distFun (ν.map Subtype.val) x = ν.real (Subtype.val ⁻¹' Iic x) := by
  rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl

/-- **Exercise 12.10.** If `μ₁ₙ ≤ λₙ ≤ μ₂ₙ` and `μ₁ₙ ⇒ μ`, `μ₂ₙ ⇒ μ`, then `λₙ ⇒ μ`. (The book
states it for `S = [a, b]`; the argument through Exercise 12.4 and Theorem 12.8 works for any
`S ⊆ ℝˡ`.) -/
theorem ex_12_10 {S : Set (Fin l → ℝ)} (μ₁ μ₂ ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (μ₁ n)] [∀ n, IsProbabilityMeasure (μ₂ n)]
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h₁ : ∀ n, Dominates (ls n) (μ₁ n)) (h₂ : ∀ n, Dominates (μ₂ n) (ls n))
    (hc₁ : ConvWeak μ₁ μ) (hc₂ : ConvWeak μ₂ μ) : ConvWeak ls μ := by
  rw [ex_12_4, theorem_12_8] at hc₁ hc₂ ⊢
  intro x hx
  have e1 := hc₁ x hx
  have e2 := hc₂ x hx
  simp only [distFun_map_val] at e1 e2 ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le e2 e1
    (fun n => ex_12_9a_subtype (h₂ n) x) (fun n => ex_12_9a_subtype (h₁ n) x)

/-! ### Exercise 12.11 and iterates -/

variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Exercise 12.11.** The following are equivalent: (a) `P` is monotone; (b) `μ ≥ λ` implies
`T*μ ≥ T*λ`; (c) `s ≥ s′` implies `P(s, ·) ≥ P(s′, ·)`. -/
theorem ex_12_11 :
    (IsMonotoneTF κ ↔ ∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) ∧
    (IsMonotoneTF κ ↔ ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) := by
  have hab : IsMonotoneTF κ → ∀ (μ lam : Measure S), IsProbabilityMeasure μ →
      IsProbabilityMeasure lam → Dominates μ lam →
        Dominates (adjointOp κ μ) (adjointOp κ lam) := fun hM μ lam _ _ h f hf hb hm => by
    obtain ⟨M, hMb⟩ := hb
    rw [← theorem_8_3_cor κ lam hf hMb, ← theorem_8_3_cor κ μ hf hMb]
    have := theorem_8_1_cor κ hf hMb
    exact h _ this.1 ⟨M, this.2⟩ (hM f hf ⟨M, hMb⟩ hm)
  have hbc : (∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) →
        ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s') := fun h s s' hss' => by
    have := h (Measure.dirac s) (Measure.dirac s') inferInstance inferInstance
      (fun f hf _ hm => by
        rw [integral_dirac' f s' hf.stronglyMeasurable, integral_dirac' f s hf.stronglyMeasurable]
        exact hm hss')
    rwa [adjointOp_dirac, adjointOp_dirac] at this
  have hca : (∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) → IsMonotoneTF κ :=
    fun h f hf hb hm s' s hss' => h s s' hss' f hf hb hm
  exact ⟨⟨hab, fun h => hca (hbc h)⟩, ⟨fun h => hbc (hab h), hca⟩⟩

omit [Preorder S] [IsMarkovKernel κ] in
theorem markovOpR_kpow_zero {f : S → ℝ} (hf : Measurable f) : markovOpR (kpow κ 0) f = f := by
  funext s
  simp only [markovOpR, kpow, Kernel.id_apply]
  exact integral_dirac' f s hf.stronglyMeasurable

omit [Preorder S] in
/-- `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem markovOpR_kpow_add (n m : ℕ) {f : S → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ s, |f s| ≤ M) :
    markovOpR (kpow κ (n + m)) f = markovOpR (kpow κ n) (markovOpR (kpow κ m) f) := by
  have := ex_8_4a κ m
  have := ex_8_4a κ n
  funext s
  rw [kpow_add]
  exact Kernel.integral_comp (integrable_of_bounded hf hM)

/-- The iterates of a monotone transition function are monotone. -/
theorem isMonotoneTF_kpow {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (n : ℕ) :
    IsMonotoneTF (kpow κ n) := by
  induction n with
  | zero => intro f hf _ hm; rw [markovOpR_kpow_zero κ hf]; exact hm
  | succ n ih =>
    intro f hf ⟨M, hb⟩ hm
    have := ex_8_4a κ n
    rw [add_comm, markovOpR_kpow_add κ 1 n hf hb, kpow_one]
    have := theorem_8_1_cor (kpow κ n) hf hb
    exact hM _ this.1 ⟨M, this.2⟩ (ih f hf ⟨M, hb⟩ hm)

omit [Preorder S] [IsMarkovKernel κ] in
theorem iterate_dirac (n : ℕ) (s : S) :
    (adjointOp κ)^[n] (Measure.dirac s) = kpow κ n s := by
  rw [adjointOp_iterate, adjointOp_dirac]

/-- `T*ⁿ` preserves dominance for monotone `P`. -/
theorem dominates_iterate {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    {μ lam : Measure S} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : Dominates μ lam) (n : ℕ) :
    Dominates ((adjointOp κ)^[n] μ) ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (ex_12_11 κ).1.1 hM _ _ (isProbabilityMeasure_iterate μ n)
      (isProbabilityMeasure_iterate lam n) ih

/-! ### Monotone processes on `[a, b]` -/

variable {a b : Fin l → ℝ}

/-- The bottom `a` of `[a, b]`. -/
def IccBot (hab : a ≤ b) : Icc a b := ⟨a, left_mem_Icc.2 hab⟩

/-- The top `b` of `[a, b]`. -/
def IccTop (hab : a ≤ b) : Icc a b := ⟨b, right_mem_Icc.2 hab⟩

theorem IccBot_le (hab : a ≤ b) (s : Icc a b) : IccBot hab ≤ s := s.2.1

theorem le_IccTop (hab : a ≤ b) (s : Icc a b) : s ≤ IccTop hab := s.2.2

/-- Every probability measure dominates `δ_a` and is dominated by `δ_b`. -/
theorem dominates_dirac_bot_top (hab : a ≤ b) (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    Dominates ν (Measure.dirac (IccBot hab)) ∧ Dominates (Measure.dirac (IccTop hab)) ν := by
  refine ⟨fun f hf ⟨M, hM⟩ hm => ?_, fun f hf ⟨M, hM⟩ hm => ?_⟩
  · rw [integral_dirac]
    have := integral_mono (integrable_const (f (IccBot hab))) (integrable_of_bounded hf hM (μ := ν))
      fun s => hm (IccBot_le hab s)
    rwa [integral_const, probReal_univ, one_smul] at this
  · rw [integral_dirac]
    have := integral_mono (integrable_of_bounded hf hM (μ := ν))
      (integrable_const (f (IccTop hab))) fun s => hm (le_IccTop hab s)
    rwa [integral_const, probReal_univ, one_smul] at this

/-- A probability measure on `ℝˡ` concentrated on `[a, b]` is the extension of a probability
measure on `[a, b]`. -/
theorem exists_subtype_measure (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (h : μ (Icc a b) = 1) :
    ∃ ν : Measure (Icc a b), IsProbabilityMeasure ν ∧ ν.map Subtype.val = μ := by
  have hmap : (μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc]
    exact Measure.restrict_eq_self_of_ae_mem
      (mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 h))
  refine ⟨μ.comap Subtype.val, ?_, hmap⟩
  have : IsProbabilityMeasure ((μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ)) := by
    rw [hmap]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).1 this

theorem map_val_Icc (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    ν.map Subtype.val (Icc a b) = 1 := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc]
  have : (Subtype.val ⁻¹' Icc a b : Set (Icc a b)) = univ := eq_univ_of_forall fun s => s.2
  rw [this, measure_univ]

/-- A **monotone sequence of measures** on `[a, b]` (SLP p. 379) converges weakly (Corollary 2 to
Helly, through Exercise 12.9a and Exercise 12.4). -/
theorem convWeak_of_dominance_mono (ν : ℕ → Measure (Icc a b)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmono : (∀ n, Dominates (ν (n + 1)) (ν n)) ∨ (∀ n, Dominates (ν n) (ν (n + 1)))) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ ConvWeak ν μ := by
  obtain ⟨μ', hμ', hab', hconv⟩ := theorem_12_9_cor2 (a := a) (b := b)
    (fun n => (ν n).map Subtype.val) (fun n => map_val_Icc (ν n)) (by
      rcases hmono with h | h
      · exact Or.inl fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x
      · exact Or.inr fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x)
  obtain ⟨μ, hμ, hmap⟩ := exists_subtype_measure μ' hab'
  refine ⟨μ, hμ, (ex_12_4 ν μ).2 ?_⟩
  rw [hmap]; exact hconv

/-- **Exercise 12.12.** For monotone Feller `P` on `[a, b]`, `T*ⁿδ_a` is increasing and `T*ⁿδ_b`
decreasing, and each converges weakly to an invariant measure. -/
theorem ex_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) :
    (∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab)))) ∧
    (∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab)))) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccBot hab))) μ ∧
      adjointOp κ μ = μ) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccTop hab))) μ ∧
      adjointOp κ μ = μ) := by
  have hP : ∀ (lam : Measure (Icc a b)) [IsProbabilityMeasure lam],
      IsProbabilityMeasure (adjointOp κ lam) := fun lam _ => (theorem_8_2 κ lam).1
  have hbot : ∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).1 n
  have htop : ∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).2 n
  have hlim : ∀ s : Icc a b, ((∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac s))
      ((adjointOp κ)^[n] (Measure.dirac s))) ∨ (∀ n, Dominates ((adjointOp κ)^[n]
        (Measure.dirac s)) ((adjointOp κ)^[n + 1] (Measure.dirac s)))) →
      ∃ μ, IsProbabilityMeasure μ ∧
        ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac s)) μ ∧ adjointOp κ μ = μ :=
    fun s hs => by
      have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] (Measure.dirac s)) := fun n =>
        isProbabilityMeasure_iterate _ n
      obtain ⟨μ, hμ, hconv⟩ := convWeak_of_dominance_mono _ hs
      refine ⟨μ, hμ, hconv, invariant_of_convWeak hF hconv fun f => ?_⟩
      have := (hconv f).sub ((hconv f).comp (tendsto_add_atTop_nat 1))
      rw [sub_self] at this
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  exact ⟨hbot, htop, hlim _ (Or.inl hbot), hlim _ (Or.inr htop)⟩

/-! ### Assumption 12.1, Exercise 12.14, Lemma 12.11 and Theorem 12.12 -/

/-- **Assumption 12.1.** There are `c ∈ [a, b]`, `ε > 0` and `N ≥ 1` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε`. -/
def Assumption12_1 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) (c : Icc a b) (ε : ℝ)
    (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (IccBot hab)).real (Ici c) ∧
    ε ≤ (kpow κ N (IccTop hab)).real (Iic c)

/-- **Exercise 12.14.** Under monotonicity, Assumption 12.1 holds from every starting point:
`Pᴺ(s, [a, c]) ≥ ε` and `Pᴺ(s, [c, b]) ≥ ε`. -/
theorem ex_12_14 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    (s : Icc a b) : ε ≤ (kpow κ N s).real (Iic c) ∧ ε ≤ (kpow κ N s).real (Ici c) := by
  have := ex_8_4a κ N
  have hdom := (ex_12_11 (kpow κ N)).2.1 (isMonotoneTF_kpow hM N)
  refine ⟨?_, hA.2.2.1.trans ((hdom s _ (IccBot_le hab s)).real_le measurableSet_Ici
    (isUpperSet_Ici c))⟩
  have := (hdom _ s (le_IccTop hab s)).real_le measurableSet_Iic.compl (isLowerSet_Iic c).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  linarith [hA.2.2.2]

/-- **Lemma 12.11.** Under monotonicity and Assumption 12.1, for bounded measurable
nondecreasing `f`: `εf(c) + (1 - ε)f(a) ≤ (Tᴺf)(s) ≤ εf(c) + (1 - ε)f(b)`. -/
theorem lemma_12_11 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    {f : Icc a b → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ s, |f s| ≤ M) (hm : Monotone f)
    (s : Icc a b) :
    ε * f c + (1 - ε) * f (IccBot hab) ≤ markovOpR (kpow κ N) f s ∧
      markovOpR (kpow κ N) f s ≤ ε * f c + (1 - ε) * f (IccTop hab) := by
  have := ex_8_4a κ N
  obtain ⟨hp, hq⟩ := ex_12_14 hM hA s
  set ν := kpow κ N s
  have hfi : Integrable f ν := integrable_of_bounded hf hb
  have hI : ∀ (A : Set (Icc a b)), MeasurableSet A → Integrable (A.indicator (1 : Icc a b → ℝ)) ν :=
    fun A hA => by exact (integrable_const (1 : ℝ)).indicator hA
  constructor
  · have hle : ∀ t, f (IccBot hab) + (f c - f (IccBot hab)) * (Ici c).indicator 1 t ≤ f t :=
      fun t => by
        by_cases ht : t ∈ Ici c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, add_zero]; exact hm (IccBot_le hab t)
    have := integral_mono ((integrable_const _).add ((hI _ measurableSet_Ici).const_mul _)) hfi hle
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_const _) ((hI _ measurableSet_Ici).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Ici] at this
    have hca : f (IccBot hab) ≤ f c := hm (IccBot_le hab c)
    change _ ≤ ∫ t, f t ∂ν
    nlinarith
  · have hle : ∀ t, f t ≤ f (IccTop hab) - (f (IccTop hab) - f c) * (Iic c).indicator 1 t :=
      fun t => by
        by_cases ht : t ∈ Iic c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, sub_zero]; exact hm (le_IccTop hab t)
    have := integral_mono hfi ((integrable_const _).sub ((hI _ measurableSet_Iic).const_mul _)) hle
    simp only [Pi.sub_apply] at this
    rw [integral_sub (integrable_const _) ((hI _ measurableSet_Iic).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Iic] at this
    have hcb : f c ≤ f (IccTop hab) := hm (le_IccTop hab c)
    change ∫ t, f t ∂ν ≤ _
    nlinarith

/-- **Theorem 12.12.** On `[a, b]`, a monotone Feller transition function satisfying Assumption
12.1 has a unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hA : Assumption12_1 hab κ c ε N) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  obtain ⟨-, -, ⟨μa, hμa, hca, hia⟩, ⟨μb, hμb, hcb, hib⟩⟩ := ex_12_12 hab κ hM hF
  set lo := IccBot hab
  set hi := IccTop hab
  have hε1 : ε ≤ 1 := by
    have := ex_8_4a κ N
    exact hA.2.2.1.trans measureReal_le_one
  -- the limits along `Tⁿf` at the two ends
  have hT : ∀ (s : Icc a b) (f : Icc a b →ᵇ ℝ) (n : ℕ),
      ∫ t, f t ∂(adjointOp κ)^[n] (Measure.dirac s) = markovOpR (kpow κ n) f s :=
    fun s f n => by rw [iterate_dirac]; rfl
  have heq : μa = μb := by
    refine ex_12_5b μa μb fun f hfm => ?_
    have hfb := bcf_abs_le_norm f
    have hfmeas := f.continuous.measurable
    set d : ℕ → ℝ := fun n => markovOpR (kpow κ n) f hi - markovOpR (kpow κ n) f lo
    have hdlim : Tendsto d atTop (𝓝 (∫ t, f t ∂μb - ∫ t, f t ∂μa)) := by
      have h1 := hcb f; have h2 := hca f
      simp only [hT] at h1 h2
      exact h1.sub h2
    have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.2
      (isMonotoneTF_kpow hM n f hfmeas ⟨_, hfb⟩ hfm (IccBot_le hab hi))
    have hdN : ∀ m, d (N * m) ≤ (1 - ε) ^ m * (f hi - f lo) := fun m => by
      induction m with
      | zero =>
        simp only [d, mul_zero, pow_zero, one_mul, markovOpR_kpow_zero κ hfmeas]; rfl
      | succ m ih =>
        have := ex_8_4a κ (N * m)
        have hg := theorem_8_1_cor (kpow κ (N * m)) hfmeas hfb
        have hgm := isMonotoneTF_kpow hM (N * m) f hfmeas ⟨_, hfb⟩ hfm
        have hsplit : markovOpR (kpow κ (N * (m + 1))) f =
            markovOpR (kpow κ N) (markovOpR (kpow κ (N * m)) f) := by
          rw [show N * (m + 1) = N + N * m by ring, markovOpR_kpow_add κ N (N * m) hfmeas hfb]
        have hup := (lemma_12_11 hM hA hg.1 hg.2 hgm hi).2
        have hlo := (lemma_12_11 hM hA hg.1 hg.2 hgm lo).1
        simp only [d, hsplit]
        have h1ε : 0 ≤ 1 - ε := by linarith
        calc _ ≤ (1 - ε) * d (N * m) := by simp only [d]; linarith
          _ ≤ (1 - ε) * ((1 - ε) ^ m * (f hi - f lo)) := mul_le_mul_of_nonneg_left ih h1ε
          _ = _ := by ring
    have hNm : Tendsto (fun m => N * m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hA.2.1) tendsto_id
    have hup : ∫ t, f t ∂μb - ∫ t, f t ∂μa ≤ 0 := by
      have hbound : Tendsto (fun m : ℕ => (1 - ε) ^ m * (f hi - f lo)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith [hA.1])
          ).mul_const (f hi - f lo)
      exact le_of_tendsto_of_tendsto' (hdlim.comp hNm) hbound hdN
    have hlow : 0 ≤ ∫ t, f t ∂μb - ∫ t, f t ∂μa := ge_of_tendsto' hdlim hd0
    linarith
  subst heq
  have hglob : ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μa := fun lam₀ _ => by
    have : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] n,
        IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun ν _ n => isProbabilityMeasure_iterate ν n
    exact ex_12_10 (fun n => (adjointOp κ)^[n] (Measure.dirac lo))
      (fun n => (adjointOp κ)^[n] (Measure.dirac hi)) (fun n => (adjointOp κ)^[n] lam₀) μa
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).1 n)
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).2 n) hca hcb
  refine ⟨μa, hμa, hia, fun ν _ hν => ?_, hglob⟩
  have hconst : ConvWeak (fun n => (adjointOp κ)^[n] ν) ν := fun f => by
    simp only [Function.iterate_fixed hν]; exact tendsto_const_nhds
  have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun n =>
    isProbabilityMeasure_iterate ν n
  exact convWeak_unique hconst (hglob ν inferInstance)

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 12.13: monotone and Feller are not enough for uniqueness (SLP pp. 380–381)

The book's example is drawn (Figure 12.4): `P(s, ·)` is uniform on a band `[h(s), H(s)]` between
two continuous nondecreasing curves, with two intervals `E₁`, `E₂` mapped into themselves and a
transient interval `F` between them. We realise it explicitly with `E₁ = [0, 1]`, `F = (1, 2)`,
`E₂ = [2, 3]` and, writing `c(x) = max 0 (min x 1)`,

* `h(s) = c(s)/2 + (3/2) c(10(s − 1.9)) + c(s − 2)/2`,
* `H(s) = 1/2 + c(s)/2 + (3/2) c(10(s − 1)) + c(s − 2)/2`,

so that `H − h ≥ 1/2` (the book's denominator `μ([h(s), H(s)])` is positive), `h(s) = s/2`,
`H(s) = (1 + s)/2` on `E₁`, `h(s) = 1 + s/2`, `H(s) = 3/2 + s/2` on `E₂`, and on `F` the band
reaches into `E₁` (when `s ≤ 1.9`, `h(s) = 1/2`) or into `E₂` (when `s ≥ 1.1`, `H(s) = 5/2`). The
state space is `ℝ`; all mass lies in `[0, 3]`.

* (a) `P` is monotone and Feller (`ex_12_13a`);
* (b) `E₁` and `E₂` are disjoint and invariant (`Pⁿ(s, Eᵢ) = 1` for `s ∈ Eᵢ`), and from every
  `s ∈ F` the process enters `E₁ ∪ E₂`, which it never leaves, with positive probability
  (`ex_12_13b`). (For general state spaces SLP never defines a "transient set", see the Chapter 11
  corrections; this is the finite-chain notion of p. 333: a positive probability of leaving and
  never returning.)
* (c) `T*ⁿδ₀` and `T*ⁿδ₃` have no common weak limit (`ex_12_13c`): every weak limit of the first
  is concentrated on `E₁`, of the second on `E₂`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ### The clamp and the band -/

/-- `c(x) = max 0 (min x 1)`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem monotone_clamp01 : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right 1 h)

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem clamp01_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  rw [clamp01, min_eq_left (h.trans zero_le_one), max_eq_left h]

theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  rw [clamp01, min_eq_right h, max_eq_right zero_le_one]

theorem clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  rw [clamp01, min_eq_left h1, max_eq_right h0]

/-- The lower curve `h`. -/
noncomputable def lowEnd (s : ℝ) : ℝ :=
  clamp01 s / 2 + 3 / 2 * clamp01 (10 * (s - 19 / 10)) + clamp01 (s - 2) / 2

/-- The upper curve `H`. -/
noncomputable def highEnd (s : ℝ) : ℝ :=
  1 / 2 + clamp01 s / 2 + 3 / 2 * clamp01 (10 * (s - 1)) + clamp01 (s - 2) / 2

theorem continuous_lowEnd : Continuous lowEnd :=
  ((continuous_clamp01.div_const 2).add ((continuous_clamp01.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).const_mul _)).add
    ((continuous_clamp01.comp (continuous_id.sub continuous_const)).div_const 2)

theorem continuous_highEnd : Continuous highEnd :=
  ((continuous_const.add (continuous_clamp01.div_const 2)).add ((continuous_clamp01.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).const_mul _)).add
    ((continuous_clamp01.comp (continuous_id.sub continuous_const)).div_const 2)

theorem monotone_lowEnd : Monotone lowEnd := fun s t h => by
  have h1 := monotone_clamp01 h
  have h2 := monotone_clamp01 (show 10 * (s - 19 / 10) ≤ 10 * (t - 19 / 10) by linarith)
  have h3 := monotone_clamp01 (show s - 2 ≤ t - 2 by linarith)
  simp only [lowEnd]; linarith

theorem monotone_highEnd : Monotone highEnd := fun s t h => by
  have h1 := monotone_clamp01 h
  have h2 := monotone_clamp01 (show 10 * (s - 1) ≤ 10 * (t - 1) by linarith)
  have h3 := monotone_clamp01 (show s - 2 ≤ t - 2 by linarith)
  simp only [highEnd]; linarith

theorem lowEnd_nonneg (s : ℝ) : 0 ≤ lowEnd s := by
  have := clamp01_nonneg s; have := clamp01_nonneg (10 * (s - 19 / 10))
  have := clamp01_nonneg (s - 2)
  simp only [lowEnd]; linarith

theorem highEnd_le (s : ℝ) : highEnd s ≤ 3 := by
  have := clamp01_le_one s; have := clamp01_le_one (10 * (s - 1))
  have := clamp01_le_one (s - 2)
  simp only [highEnd]; linarith

/-- The band has width at least `1/2`. -/
theorem gap_le (s : ℝ) : 1 / 2 ≤ highEnd s - lowEnd s := by
  have := monotone_clamp01 (show 10 * (s - 19 / 10) ≤ 10 * (s - 1) by linarith)
  simp only [highEnd, lowEnd]; linarith

/-- The point at fraction `u` of the band. -/
noncomputable def bandPt (s u : ℝ) : ℝ := lowEnd s + u * (highEnd s - lowEnd s)

theorem continuous_bandPt : Continuous fun p : ℝ × ℝ => bandPt p.1 p.2 :=
  (continuous_lowEnd.comp continuous_fst).add (continuous_snd.mul
    ((continuous_highEnd.comp continuous_fst).sub (continuous_lowEnd.comp continuous_fst)))

theorem continuous_bandPt_left (u : ℝ) : Continuous fun s => bandPt s u :=
  continuous_bandPt.comp (continuous_id.prodMk continuous_const)

theorem continuous_bandPt_right (s : ℝ) : Continuous (bandPt s) :=
  continuous_bandPt.comp (continuous_const.prodMk continuous_id)

theorem bandPt_mono {s t u : ℝ} (hst : s ≤ t) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ≤ bandPt t u := by
  have h1 := monotone_lowEnd hst
  have h2 := monotone_highEnd hst
  simp only [bandPt]
  nlinarith [hu.1, hu.2]

/-! ### The transition function -/

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Icc 0 1)

theorem isProbabilityMeasure_unif : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Icc]⟩

theorem unif_Icc {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1) : unif (Icc a b) = ENNReal.ofReal (b - a) := by
  rw [unif, Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_eq_left h0,
    min_eq_left h1, Real.volume_Icc]

/-- `P(s, ·)`: the uniform distribution on `[h(s), H(s)]`, as the image of `unif` under
`u ↦ h(s) + u (H(s) − h(s))`. -/
noncomputable def bandKernel : Kernel ℝ ℝ :=
  haveI := isProbabilityMeasure_unif
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const ℝ unif)
    fun p => bandPt p.1 p.2

theorem bandKernel_apply (s : ℝ) : bandKernel s = unif.map (bandPt s) := by
  have := isProbabilityMeasure_unif
  rw [bandKernel, Kernel.map_apply _ continuous_bandPt.measurable, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map continuous_bandPt.measurable measurable_prodMk_left]
  rfl

theorem isMarkovKernel_bandKernel : IsMarkovKernel bandKernel := by
  have := isProbabilityMeasure_unif
  exact Kernel.IsMarkovKernel.map _ continuous_bandPt.measurable

theorem bandKernel_apply_set (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    bandKernel s A = unif (bandPt s ⁻¹' A) := by
  rw [bandKernel_apply, Measure.map_apply (continuous_bandPt_right s).measurable hA]

theorem integral_bandKernel (s : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂bandKernel s = ∫ u, f (bandPt s u) ∂unif := by
  rw [bandKernel_apply, integral_map (continuous_bandPt_right s).measurable.aemeasurable
    hf.aestronglyMeasurable]

/-- **Exercise 12.13a.** `P` is monotone and has the Feller property. -/
theorem ex_12_13a : IsMonotoneTF bandKernel ∧ IsFeller bandKernel := by
  have := isProbabilityMeasure_unif
  have hint : ∀ {f : ℝ → ℝ}, Measurable f → ∀ {M : ℝ}, (∀ x, |f x| ≤ M) → ∀ s,
      Integrable (fun u => f (bandPt s u)) unif := fun hf _ hM s =>
    integrable_of_bounded (hf.comp (continuous_bandPt_right s).measurable) fun u => hM _
  refine ⟨fun f hf ⟨M, hM⟩ hm s t hst => ?_, fun f hf ⟨M, hM⟩ => ?_⟩
  · change ∫ x, f x ∂bandKernel s ≤ ∫ x, f x ∂bandKernel t
    rw [integral_bandKernel s hf, integral_bandKernel t hf]
    exact integral_mono_ae (hint hf hM s) (hint hf hM t)
      (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => hm (bandPt_mono hst hu))
  · have : markovOpR bandKernel f = fun s => ∫ u, f (bandPt s u) ∂unif :=
      funext fun s => integral_bandKernel s hf.measurable
    rw [this]
    exact continuous_of_dominated (bound := fun _ => M)
      (fun s => (hf.comp (continuous_bandPt_right s)).aestronglyMeasurable)
      (fun s => Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hM _)
      (integrable_const M) (Eventually.of_forall fun u => hf.comp (continuous_bandPt_left u))

/-! ### Invariant sets -/

/-- If `P(s, E) = 1` for every `s ∈ E`, then `Pⁿ(s, E) = 1` for every `s ∈ E` and `n`. -/
theorem kpow_eq_one_of_invariant {S : Type*} [MeasurableSpace S] (κ : Kernel S S)
    [IsMarkovKernel κ] {E : Set S} (hE : MeasurableSet E) (h : ∀ s ∈ E, κ s E = 1) :
    ∀ n, ∀ s ∈ E, kpow κ n s E = 1 := by
  intro n
  induction n with
  | zero => intro s hs; simp [kpow, Kernel.id_apply, Measure.dirac_apply_of_mem hs]
  | succ n ih =>
    intro s hs
    have := ex_8_4a κ n
    change (kpow κ n ∘ₖ κ) s E = 1
    rw [Kernel.comp_apply' _ _ _ hE]
    refine le_antisymm ?_ ?_
    · calc ∫⁻ b, kpow κ n b E ∂κ s ≤ ∫⁻ _, 1 ∂κ s := lintegral_mono fun b => prob_le_one
        _ = 1 := by simp
    · calc (1 : ℝ≥0∞) = κ s E := (h s hs).symm
        _ = ∫⁻ b, E.indicator 1 b ∂κ s := (lintegral_indicator_one hE).symm
        _ ≤ ∫⁻ b, kpow κ n b E ∂κ s := lintegral_mono fun b => by
            by_cases hb : b ∈ E
            · rw [indicator_of_mem hb, Pi.one_apply, ih b hb]
            · rw [indicator_of_notMem hb]; exact zero_le

theorem bandKernel_eq_one {s : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (h : ∀ u ∈ Icc (0 : ℝ) 1, bandPt s u ∈ E) : bandKernel s E = 1 := by
  rw [bandKernel_apply_set s hE, unif, Measure.restrict_apply (hE.preimage
    (continuous_bandPt_right s).measurable), inter_eq_right.2
      (show Icc (0 : ℝ) 1 ⊆ bandPt s ⁻¹' E from h), Real.volume_Icc]
  norm_num

theorem bandPt_E₁ {s u : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ∈ Icc (0 : ℝ) 1 := by
  have e1 := clamp01_of_mem hs.1 hs.2
  have e2 := clamp01_of_nonpos (show 10 * (s - 19 / 10) ≤ 0 by linarith [hs.2])
  have e3 := clamp01_of_nonpos (show s - 2 ≤ 0 by linarith [hs.2])
  have e4 := clamp01_of_nonpos (show 10 * (s - 1) ≤ 0 by linarith [hs.2])
  simp only [bandPt, lowEnd, highEnd, e1, e2, e3, e4, mem_Icc]
  constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]

theorem bandPt_E₂ {s u : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    bandPt s u ∈ Icc (2 : ℝ) 3 := by
  have e1 := clamp01_of_one_le (show 1 ≤ s by linarith [hs.1])
  have e2 := clamp01_of_one_le (show 1 ≤ 10 * (s - 19 / 10) by linarith [hs.1])
  have e3 := clamp01_of_mem (show 0 ≤ s - 2 by linarith [hs.1]) (show s - 2 ≤ 1 by
    linarith [hs.2])
  have e4 := clamp01_of_one_le (show 1 ≤ 10 * (s - 1) by linarith [hs.1])
  simp only [bandPt, lowEnd, highEnd, e1, e2, e3, e4, mem_Icc]
  constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2]

/-- From `s ∈ (1, 2)` the band reaches `E₁ ∪ E₂` with probability at least `1/5`. -/
theorem bandKernel_leave {s : ℝ} (hs : s ∈ Ioo (1 : ℝ) 2) :
    0 < bandKernel s (Icc 0 1 ∪ Icc 2 3) := by
  have hm : MeasurableSet (Icc (0 : ℝ) 1 ∪ Icc 2 3) := measurableSet_Icc.union measurableSet_Icc
  rw [bandKernel_apply_set s hm]
  have hc1 := clamp01_of_one_le (show 1 ≤ s by linarith [hs.1])
  have hc3 := clamp01_of_nonpos (show s - 2 ≤ 0 by linarith [hs.2])
  have hH := highEnd_le s
  have hh := lowEnd_nonneg s
  have hgap := gap_le s
  by_cases h19 : s ≤ 19 / 10
  · -- `h(s) = 1/2`: the bottom fifth of the band lies in `E₁`
    have hc2 := clamp01_of_nonpos (show 10 * (s - 19 / 10) ≤ 0 by linarith)
    have hlow : lowEnd s = 1 / 2 := by simp only [lowEnd, hc1, hc2, hc3]; norm_num
    have hsub : Icc (0 : ℝ) (1 / 5) ⊆ bandPt s ⁻¹' (Icc 0 1 ∪ Icc 2 3) := fun u hu => by
      left
      simp only [bandPt, hlow, mem_Icc] at hu ⊢
      rw [hlow] at hgap
      constructor <;> nlinarith [hu.1, hu.2]
    calc (0 : ℝ≥0∞) < unif (Icc 0 (1 / 5)) := by
          rw [unif_Icc le_rfl (by norm_num)]; norm_num
      _ ≤ _ := measure_mono hsub
  · -- `H(s) = 5/2`: the top fifth of the band lies in `E₂`
    have hc4 := clamp01_of_one_le (show 1 ≤ 10 * (s - 1) by linarith)
    have hhigh : highEnd s = 5 / 2 := by simp only [highEnd, hc1, hc4, hc3]; norm_num
    have hlow2 : lowEnd s ≤ 2 := by
      have := clamp01_le_one (10 * (s - 19 / 10))
      simp only [lowEnd, hc1, hc3]; linarith
    have hsub : Icc (4 / 5 : ℝ) 1 ⊆ bandPt s ⁻¹' (Icc 0 1 ∪ Icc 2 3) := fun u hu => by
      right
      simp only [bandPt, hhigh, mem_Icc] at hu ⊢
      constructor <;> nlinarith [hu.1, hu.2]
    calc (0 : ℝ≥0∞) < unif (Icc (4 / 5) 1) := by
          rw [unif_Icc (by norm_num) le_rfl]; norm_num
      _ ≤ _ := measure_mono hsub

/-- **Exercise 12.13b.** `E₁ = [0, 1]` and `E₂ = [2, 3]` are disjoint and invariant, and from every
point of `F = (1, 2)` the process enters `E₁ ∪ E₂` with positive probability. -/
theorem ex_12_13b :
    Disjoint (Icc (0 : ℝ) 1) (Icc 2 3) ∧
      (∀ n, ∀ s ∈ Icc (0 : ℝ) 1, kpow bandKernel n s (Icc 0 1) = 1) ∧
      (∀ n, ∀ s ∈ Icc (2 : ℝ) 3, kpow bandKernel n s (Icc 2 3) = 1) ∧
      ∀ s ∈ Ioo (1 : ℝ) 2, 0 < bandKernel s (Icc 0 1 ∪ Icc 2 3) := by
  have := isMarkovKernel_bandKernel
  refine ⟨?_, kpow_eq_one_of_invariant _ measurableSet_Icc fun s hs =>
      bandKernel_eq_one measurableSet_Icc fun u hu => bandPt_E₁ hs hu,
    kpow_eq_one_of_invariant _ measurableSet_Icc fun s hs =>
      bandKernel_eq_one measurableSet_Icc fun u hu => bandPt_E₂ hs hu,
    fun s hs => bandKernel_leave hs⟩
  rw [Set.disjoint_iff]
  intro x ⟨h1, h2⟩
  linarith [h1.2, h2.1]

/-- **Exercise 12.13c.** `T*ⁿδ₀` and `T*ⁿδ₃` have no common weak limit. -/
theorem ex_12_13c :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp bandKernel)^[n] (Measure.dirac 0)) μ ∧
      ConvWeak (fun n => (adjointOp bandKernel)^[n] (Measure.dirac 3)) μ := by
  rintro ⟨μ, hμ, h0, h3⟩
  have := isMarkovKernel_bandKernel
  obtain ⟨hdis, hE₁, hE₂, -⟩ := ex_12_13b
  have : ∀ (s : ℝ) n, IsProbabilityMeasure ((adjointOp bandKernel)^[n] (Measure.dirac s)) :=
    fun s n => isProbabilityMeasure_iterate _ n
  have m1 := measure_eq_one_of_convWeak h0 isClosed_Icc fun n => by
    rw [iterate_dirac]; exact hE₁ n 0 ⟨le_rfl, zero_le_one⟩
  have m2 := measure_eq_one_of_convWeak h3 isClosed_Icc fun n => by
    rw [iterate_dirac]; exact hE₂ n 3 ⟨by norm_num, le_rfl⟩
  have := measure_union hdis measurableSet_Icc (μ := μ)
  rw [m1, m2] at this
  have h2 : μ (Icc 0 1 ∪ Icc 2 3) ≤ 1 := prob_le_one
  rw [this] at h2
  norm_num at h2

end StokeyLucasPrescott.WeakConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dependence on a parameter, and a loose end (SLP §§12.5–12.6, pp. 383–388)

* **Theorem 12.13**: on a compact metric state space, if `(s, θ) ↦ P_θ(s, ·)` is weakly continuous
  and each `T_θ*` has a unique fixed point `μ_θ`, then `θ ↦ μ_θ` is weakly continuous. The book's
  "uniformly continuous on `S × Θ̂`" step becomes the sequential lemma `tendsto_uniform_markovOp`
  (`T_{θₙ}f → T_{θ₀}f` uniformly), proved by compactness of `S`; `Θ` may be any metric space;
* **Lemma 12.14**: for Feller `Q` and bounded continuous `f` on `X × Z`,
  `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous (`lemma_12_14_cont`), for any
  metric spaces `X`, `Z`; and `T` preserves monotonicity, strict monotonicity, concavity and strict
  concavity in `y` (`lemma_12_14_mono`, `_strictMono`, `_concave`, `_strictConcave`). The key limit
  (1) is proved with the continuous majorants `gₖ(z′) = sup_{n ≥ k} |f(yₙ, z′) - f(y, z′)|`
  (maxima of a jointly continuous function over the compact sets `{y} ∪ {yₙ : n ≥ k}`) in place of
  the book's boundary-counting argument; this avoids the book's inexact description of
  `∂E_k(ε)`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Theorem 12.13 -/

variable {S Θ : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MetricSpace Θ]

omit [BorelSpace S] in
/-- Under the joint weak continuity of Theorem 12.13(b) on compact `S`, `T_{θₙ}f → T_{θ₀}f`
uniformly whenever `θₙ → θ₀`. -/
theorem tendsto_uniform_markovOp [CompactSpace S] (P : Θ → Kernel S S)
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) (f : S →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s, |markovOpR (P (θ n)) f s - markovOpR (P θ₀) f s| < ε := by
  intro ε hε
  by_contra hne
  rw [not_eventually, frequently_atTop] at hne
  choose nk hnk hbad using hne
  have hbad' : ∀ k, ∃ s, ε ≤ |markovOpR (P (θ (nk k))) f s - markovOpR (P θ₀) f s| := fun k => by
    have := hbad k; push Not at this; exact this
  choose sk hsk using hbad'
  obtain ⟨s₀, -, ψ, hψ, hsψ⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (sk k))
  have hn : Tendsto (fun j => nk (ψ j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (hψ.id_le j).trans (hnk (ψ j))) tendsto_id
  have hA := hcont (sk ∘ ψ) (fun j => θ (nk (ψ j))) s₀ θ₀ hsψ (hθ.comp hn) f
  have hB := hcont (sk ∘ ψ) (fun _ => θ₀) s₀ θ₀ hsψ tendsto_const_nhds f
  have hdiff := (hA.sub hB).abs
  rw [sub_self, abs_zero] at hdiff
  obtain ⟨j, hj⟩ := (hdiff.eventually (gt_mem_nhds hε)).exists
  exact absurd (hsk (ψ j)) (not_le.2 hj)

/-- **Theorem 12.13.** Let `S` be a compact metric space and `Θ` a metric space. If
(b) `(sₙ, θₙ) → (s₀, θ₀)` implies `P_{θₙ}(sₙ, ·) ⇒ P_{θ₀}(s₀, ·)`, and (c) each `T_θ*` has a
unique fixed point `μ_θ`, then `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. -/
theorem theorem_12_13 [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) := by
  have hF0 : IsFeller (P θ₀) :=
    (ex_12_7 (P θ₀)).1.2 fun s s₀ hs => hcont s (fun _ => θ₀) s₀ θ₀ hs tendsto_const_nhds
  have hT : ∀ (κ : Kernel S S) [IsMarkovKernel κ] (g : S →ᵇ ℝ),
      Measurable (markovOpR κ g) ∧ ∀ s, |markovOpR κ g s| ≤ ‖g‖ := fun κ _ g =>
    theorem_8_1_cor κ g.continuous.measurable (bcf_abs_le_norm g)
  intro f
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨μh, hμh, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight (fun k => μ (θ (ns k)))
    fun ε hε => ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  set m : ℕ → ℕ := fun j => ns (φ j)
  have hm : Tendsto m atTop atTop := hns.comp hφ.tendsto_atTop
  have : ∀ j, IsProbabilityMeasure (((fun k => μ (θ (ns k))) ∘ φ) j) := fun j =>
    inferInstanceAs (IsProbabilityMeasure (μ (θ (ns (φ j)))))
  -- the subsequential limit is a fixed point of `T₀*`
  have hinv : adjointOp (P θ₀) μh = μh := by
    have : IsProbabilityMeasure (adjointOp (P θ₀) μh) := (theorem_8_2 (P θ₀) μh).1
    refine theorem_12_6_cor2 fun g => ?_
    rw [← integral_markovOpR (P θ₀) μh g]
    have h1 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j))) atTop
        (𝓝 (∫ s, markovOpR (P θ₀) g s ∂μh)) := hconv (fellerBCF hF0 g)
    have h2 : Tendsto (fun j => ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 (∫ s, g s ∂μh)) := hconv g
    have h3 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j)) -
        ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hm.eventually (tendsto_uniform_markovOp P hcont hθ g (ε / 2)
        (half_pos hε))] with j hj
      have hgj : ∫ s, g s ∂μ (θ (m j)) = ∫ s, markovOpR (P (θ (m j))) g s ∂μ (θ (m j)) := by
        rw [integral_markovOpR, hfix]
      rw [hgj, Real.dist_eq, sub_zero, ← integral_sub
        (integrable_of_bounded (hT _ g).1 (hT _ g).2)
        (integrable_of_bounded (hT _ g).1 (hT _ g).2)]
      have := norm_integral_le_of_norm_le_const (μ := μ (θ (m j))) (C := ε / 2)
        (f := fun s => markovOpR (P θ₀) g s - markovOpR (P (θ (m j))) g s)
        (Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_sub_comm]; exact (hj s).le)
      rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
      linarith
    have h4 := h3.add h2
    simp only [sub_add_cancel, zero_add] at h4
    exact (tendsto_nhds_unique h4 h1).symm
  have := huniq θ₀ μh hμh hinv
  subst this
  exact ⟨φ, hconv f⟩

/-! ### Lemma 12.14 -/

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The key limit (1) in the proof of Lemma 12.14: if `yₙ → y` and `Q(zₙ, ·) ⇒ Q(z, ·)`, then
`∫ |f(yₙ, z′) - f(y, z′)| Q(zₙ, dz′) → 0`. -/
theorem tendsto_integral_abs_sub (f : X × Z →ᵇ ℝ) {y : ℕ → X} {y₀ : X}
    (hy : Tendsto y atTop (𝓝 y₀)) {ν : ℕ → Measure Z} {ν₀ : Measure Z}
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀] (hν : ConvWeak ν ν₀) :
    Tendsto (fun n => ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n) atTop (𝓝 0) := by
  set h : Z → X → ℝ := fun z' w => |f (w, z') - f (y₀, z')|
  have hh : Continuous (Function.uncurry h) := by
    have : Function.uncurry h = fun p : Z × X => |f (p.2, p.1) - f (y₀, p.1)| := rfl
    rw [this]
    exact ((f.continuous.comp (continuous_snd.prodMk continuous_fst)).sub
      (f.continuous.comp (continuous_const.prodMk continuous_fst))).abs
  have hbd : ∀ z' w, h z' w ≤ 2 * ‖f‖ := fun z' w => by
    have h1 := bcf_abs_le_norm f (w, z'); have h2 := bcf_abs_le_norm f (y₀, z')
    linarith [abs_sub (f (w, z')) (f (y₀, z'))]
  set W : ℕ → Set X := fun k => insert y₀ (range fun n => y (n + k))
  have hW : ∀ k, IsCompact (W k) := fun k =>
    (hy.comp (tendsto_add_atTop_nat k)).isCompact_insert_range
  set g : ℕ → Z → ℝ := fun k z' => sSup (h z' '' W k)
  have hne : ∀ k z', (h z' '' W k).Nonempty := fun k z' => (insert_nonempty _ _).image _
  have hbdd : ∀ k z', BddAbove (h z' '' W k) := fun k z' =>
    ⟨2 * ‖f‖, by rintro _ ⟨w, -, rfl⟩; exact hbd z' w⟩
  have hg0 : ∀ k z', 0 ≤ g k z' := fun k z' =>
    (abs_nonneg _).trans (le_csSup (hbdd k z') ⟨y₀, mem_insert _ _, rfl⟩)
  have hg2 : ∀ k z', g k z' ≤ 2 * ‖f‖ := fun k z' =>
    csSup_le (hne k z') (by rintro _ ⟨w, -, rfl⟩; exact hbd z' w)
  have hgle : ∀ k n z', k ≤ n → |f (y n, z') - f (y₀, z')| ≤ g k z' := fun k n z' hkn =>
    le_csSup (hbdd k z') ⟨y n, mem_insert_of_mem _ ⟨n - k, by
      simp only; rw [Nat.sub_add_cancel hkn]⟩, rfl⟩
  have hgc : ∀ k, Continuous (g k) := fun k => (hW k).continuous_sSup hh
  set G : ℕ → Z →ᵇ ℝ := fun k => BoundedContinuousFunction.mkOfBound ⟨g k, hgc k⟩ (2 * ‖f‖)
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [hg0 k a, hg0 k b, hg2 k a, hg2 k b]
  -- `gₖ ↓ 0` pointwise
  have hgk : ∀ z', Tendsto (fun k => g k z') atTop (𝓝 0) := fun z' => by
    have hc : Tendsto (fun n => f (y n, z')) atTop (𝓝 (f (y₀, z'))) :=
      (f.continuous.tendsto _).comp (hy.prodMk_nhds tendsto_const_nhds)
    rw [Metric.tendsto_nhds] at hc ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hc (ε / 2) (half_pos hε))
    refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg0 k z')]
    refine lt_of_le_of_lt (csSup_le (hne k z') ?_) (half_lt_self hε)
    rintro _ ⟨w, hw, rfl⟩
    rcases hw with rfl | ⟨n, rfl⟩
    · simp only [h, sub_self, abs_zero]; positivity
    · have := hK (n + k) (by omega)
      rw [Real.dist_eq] at this; exact this.le
  -- `∫ gₖ dν₀ → 0` by dominated convergence
  have hGk : Tendsto (fun k => ∫ z', g k z' ∂ν₀) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν₀) (fun _ => 2 * ‖f‖)
      (fun k => (hgc k).aestronglyMeasurable) (integrable_const _)
      (fun k => Eventually.of_forall fun z' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k z')]; exact hg2 k z')
      (Eventually.of_forall hgk)
    simpa using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := (hGk.eventually (gt_mem_nhds (half_pos hε))).exists
  have hconvk : Tendsto (fun n => ∫ z', g k z' ∂ν n) atTop (𝓝 (∫ z', g k z' ∂ν₀)) := hν (G k)
  filter_upwards [hconvk.eventually (gt_mem_nhds (show ∫ z', g k z' ∂ν₀ < ε by linarith)),
    eventually_ge_atTop k] with n hn hkn
  have hint : Integrable (fun z' => |f (y n, z') - f (y₀, z')|) (ν n) :=
    integrable_of_bounded ((hh.comp (continuous_id.prodMk continuous_const)).measurable)
      (M := 2 * ‖f‖) fun z' => by
        rw [abs_abs]; exact hbd z' (y n)
  have h1 : ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n ≤ ∫ z', g k z' ∂ν n :=
    integral_mono hint ((G k).integrable _) fun z' => hgle k n z' hkn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  linarith

/-- **Lemma 12.14** (continuity). For a Feller transition function `Q` on `Z` and bounded continuous
`f` on `X × Z`, `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous. (The book takes
`X ⊆ ℝˡ`, `Z ⊆ ℝᵏ` convex; continuity holds for any metric spaces.) -/
theorem lemma_12_14_cont (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (f : X × Z →ᵇ ℝ) :
    Continuous (fun p : X × Z => ∫ z', f (p.1, z') ∂Q p.2) ∧
      ∀ p : X × Z, |∫ z', f (p.1, z') ∂Q p.2| ≤ ‖f‖ := by
  refine ⟨?_, fun p => ?_⟩
  · rw [continuous_iff_seqContinuous]
    intro p p₀ hp
    have hy : Tendsto (fun n => (p n).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
    have hz : Tendsto (fun n => (p n).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
    have hQz := (ex_12_7 Q).1.1 hQ _ _ hz
    set F₀ : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => (p₀.1, z'), by fun_prop⟩
    have hv : Tendsto (fun n => ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop
        (𝓝 (∫ z', f (p₀.1, z') ∂Q p₀.2)) := hQz F₀
    have hd := tendsto_integral_abs_sub f hy hQz
    have hu : Tendsto (fun n => ∫ z', f ((p n).1, z') ∂Q (p n).2 -
        ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) hd
      set Fn : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => ((p n).1, z'), by fun_prop⟩
      rw [← integral_sub (f := fun z' => f ((p n).1, z')) (g := fun z' => f (p₀.1, z'))
        (Fn.integrable _) (F₀.integrable _)]
      exact norm_integral_le_integral_norm _
    have := hu.add hv
    simp only [sub_add_cancel, zero_add] at this
    exact this
  · have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := ‖f‖)
      (f := fun z' => f (p.1, z')) (Eventually.of_forall fun z' => f.norm_coe_le_norm _)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

variable {l : ℕ} {E : Set (Fin l → ℝ)}

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (monotonicity). If `f(·, z′)` is nondecreasing on `X` for every `z′`, so is
`Tf(·, z)`. -/
theorem lemma_12_14_mono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', MonotoneOn (fun y => f y z') E)
    (z : Z) : MonotoneOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  integral_mono (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- A strict pointwise inequality between integrable functions integrates to a strict inequality
under a probability measure. -/
theorem integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {u v : Z → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ) (h : ∀ z, u z < v z) :
    ∫ z, u z ∂μ < ∫ z, v z ∂μ := by
  have hpos : 0 < ∫ z, (v z - u z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (h z)).le) (hv.sub hu)]
    have : Function.support (fun z => v z - u z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (h z)).ne'
    rw [this, measure_univ]; exact zero_lt_one
  rw [integral_sub hv hu] at hpos
  linarith

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict monotonicity). -/
theorem lemma_12_14_strictMono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', StrictMonoOn (fun y => f y z') E)
    (z : Z) : StrictMonoOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  integral_lt_integral_of_lt (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (concavity). If `f(·, z′)` is concave on the convex set `X` for every `z′`,
so is `Tf(·, z)`. -/
theorem lemma_12_14_concave (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', ConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    ConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine integral_mono (((hint y hy z).const_mul α).add ((hint y' hy' z).const_mul β))
    (hint _ (hE hy hy' hα hβ hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hα hβ hαβ
  simpa only [smul_eq_mul] using this

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict concavity). -/
theorem lemma_12_14_strictConcave (Q : Kernel Z Z) [IsMarkovKernel Q]
    {f : (Fin l → ℝ) → Z → ℝ} (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', StrictConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    StrictConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' hne α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine integral_lt_integral_of_lt (((hint y hy z).const_mul α).add
    ((hint y' hy' z).const_mul β)) (hint _ (hE hy hy' hα.le hβ.le hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hne hα hβ hαβ
  simpa only [smul_eq_mul] using this

end StokeyLucasPrescott.WeakConvergence

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.WeakConvergence.IsTransitionFunction
#print axioms StokeyLucasPrescott.WeakConvergence.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.WeakConvergence.markovOp
#print axioms StokeyLucasPrescott.WeakConvergence.markovOpR
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp
#print axioms StokeyLucasPrescott.WeakConvergence.markovOp_indicator
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_8_1
#print axioms StokeyLucasPrescott.WeakConvergence.integrable_of_bounded
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_8_1_cor
#print axioms StokeyLucasPrescott.WeakConvergence.ex_8_1
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_apply
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_8_2
#print axioms StokeyLucasPrescott.WeakConvergence.ex_8_2
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_8_3
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_8_3_cor
#print axioms StokeyLucasPrescott.WeakConvergence.pairing
#print axioms StokeyLucasPrescott.WeakConvergence.ex_8_3
#print axioms StokeyLucasPrescott.WeakConvergence.kpow
#print axioms StokeyLucasPrescott.WeakConvergence.kpow_one
#print axioms StokeyLucasPrescott.WeakConvergence.ex_8_4a
#print axioms StokeyLucasPrescott.WeakConvergence.kpow_add
#print axioms StokeyLucasPrescott.WeakConvergence.markovOp_comp
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_comp
#print axioms StokeyLucasPrescott.WeakConvergence.ex_8_4b
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_iterate
#print axioms StokeyLucasPrescott.WeakConvergence.IsFeller
#print axioms StokeyLucasPrescott.WeakConvergence.IsMonotoneTF
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_1
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_2
#print axioms StokeyLucasPrescott.WeakConvergence.bump
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_bump
#print axioms StokeyLucasPrescott.WeakConvergence.bump_mem
#print axioms StokeyLucasPrescott.WeakConvergence.bump_eq_one
#print axioms StokeyLucasPrescott.WeakConvergence.bump_antitone
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_bump
#print axioms StokeyLucasPrescott.WeakConvergence.ConvWeak
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_1
#print axioms StokeyLucasPrescott.WeakConvergence.count_bounds
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_2
#print axioms StokeyLucasPrescott.WeakConvergence.LimsupLe
#print axioms StokeyLucasPrescott.WeakConvergence.LiminfGe
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_of_limsup_liminf
#print axioms StokeyLucasPrescott.WeakConvergence.toBCF
#print axioms StokeyLucasPrescott.WeakConvergence.limsup_closed_of_weak
#print axioms StokeyLucasPrescott.WeakConvergence.limsup_integral_of_closed
#print axioms StokeyLucasPrescott.WeakConvergence.weak_of_limsup_closed
#print axioms StokeyLucasPrescott.WeakConvergence.liminf_open_of_limsup_closed
#print axioms StokeyLucasPrescott.WeakConvergence.limsup_closed_of_liminf_open
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_of_null_frontier
#print axioms StokeyLucasPrescott.WeakConvergence.limsup_closed_of_null_frontier
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_3
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_finite_union
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_4
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_5
#print axioms StokeyLucasPrescott.WeakConvergence.IsConvDetermining
#print axioms StokeyLucasPrescott.WeakConvergence.frontier_iInter_fin_subset
#print axioms StokeyLucasPrescott.WeakConvergence.ballInters
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_5_cor
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_6
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_6_cor1
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_6_cor2
#print axioms StokeyLucasPrescott.WeakConvergence.convWeak_unique
#print axioms StokeyLucasPrescott.WeakConvergence.IsConvDetermining.eq
#print axioms StokeyLucasPrescott.WeakConvergence.distFun
#print axioms StokeyLucasPrescott.WeakConvergence.box
#print axioms StokeyLucasPrescott.WeakConvergence.vertex
#print axioms StokeyLucasPrescott.WeakConvergence.vertexSum
#print axioms StokeyLucasPrescott.WeakConvergence.diag
#print axioms StokeyLucasPrescott.WeakConvergence.ContFromAbove
#print axioms StokeyLucasPrescott.WeakConvergence.ContFromBelow
#print axioms StokeyLucasPrescott.WeakConvergence.Iic_eq_pi
#print axioms StokeyLucasPrescott.WeakConvergence.box_indicator_eq
#print axioms StokeyLucasPrescott.WeakConvergence.measurableSet_box
#print axioms StokeyLucasPrescott.WeakConvergence.vertexSum_eq
#print axioms StokeyLucasPrescott.WeakConvergence.distFun_mono
#print axioms StokeyLucasPrescott.WeakConvergence.contFromAbove_distFun
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_7a
#print axioms StokeyLucasPrescott.WeakConvergence.generateFrom_Iic_pi
#print axioms StokeyLucasPrescott.WeakConvergence.distFun_injective
#print axioms StokeyLucasPrescott.WeakConvergence.lowerOpen
#print axioms StokeyLucasPrescott.WeakConvergence.frontier_Iic_eq
#print axioms StokeyLucasPrescott.WeakConvergence.lowerOpen_subset
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_distFun_below
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_7c
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_3
#print axioms StokeyLucasPrescott.WeakConvergence.nullCoord
#print axioms StokeyLucasPrescott.WeakConvergence.countable_nullCoord_compl
#print axioms StokeyLucasPrescott.WeakConvergence.dense_nullCoord
#print axioms StokeyLucasPrescott.WeakConvergence.continuousAt_distFun
#print axioms StokeyLucasPrescott.WeakConvergence.frontier_null_of_continuousAt
#print axioms StokeyLucasPrescott.WeakConvergence.box_inter
#print axioms StokeyLucasPrescott.WeakConvergence.box_eq_empty
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_8
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_4
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_5a
#print axioms StokeyLucasPrescott.WeakConvergence.ramp
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_ramp
#print axioms StokeyLucasPrescott.WeakConvergence.ramp_mem
#print axioms StokeyLucasPrescott.WeakConvergence.monotone_ramp
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_ramp
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_5b
#print axioms StokeyLucasPrescott.WeakConvergence.vertexSum_eq_erase
#print axioms StokeyLucasPrescott.WeakConvergence.vertexSum_split
#print axioms StokeyLucasPrescott.WeakConvergence.boxContent
#print axioms StokeyLucasPrescott.WeakConvergence.boxContent_apply
#print axioms StokeyLucasPrescott.WeakConvergence.boxes
#print axioms StokeyLucasPrescott.WeakConvergence.box_mem_boxes
#print axioms StokeyLucasPrescott.WeakConvergence.coe_box_eq
#print axioms StokeyLucasPrescott.WeakConvergence.eq_empty_or_coe
#print axioms StokeyLucasPrescott.WeakConvergence.coe_mem_boxes
#print axioms StokeyLucasPrescott.WeakConvergence.isSetSemiring_boxes
#print axioms StokeyLucasPrescott.WeakConvergence.boxSet
#print axioms StokeyLucasPrescott.WeakConvergence.boxFun
#print axioms StokeyLucasPrescott.WeakConvergence.boxFun_coe
#print axioms StokeyLucasPrescott.WeakConvergence.boxFun_of_notMem
#print axioms StokeyLucasPrescott.WeakConvergence.stieltjesContent
#print axioms StokeyLucasPrescott.WeakConvergence.stieltjesContent_box
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_shift
#print axioms StokeyLucasPrescott.WeakConvergence.indVec
#print axioms StokeyLucasPrescott.WeakConvergence.indVec_nonneg
#print axioms StokeyLucasPrescott.WeakConvergence.indVec_le_one
#print axioms StokeyLucasPrescott.WeakConvergence.vertex_add_upper
#print axioms StokeyLucasPrescott.WeakConvergence.vertex_add_lower
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_vertexSum_upper
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_vertexSum_lower
#print axioms StokeyLucasPrescott.WeakConvergence.ofReal_le_ofReal_add
#print axioms StokeyLucasPrescott.WeakConvergence.exists_open_cover
#print axioms StokeyLucasPrescott.WeakConvergence.exists_compact_inner
#print axioms StokeyLucasPrescott.WeakConvergence.isSigmaSubadditive
#print axioms StokeyLucasPrescott.WeakConvergence.Iic_eq_iUnion_box
#print axioms StokeyLucasPrescott.WeakConvergence.borel_eq_generateFrom_boxes
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_vertexSum_Iic
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_7b
#print axioms StokeyLucasPrescott.WeakConvergence.IsSupport
#print axioms StokeyLucasPrescott.WeakConvergence.support_inter
#print axioms StokeyLucasPrescott.WeakConvergence.exists_support
#print axioms StokeyLucasPrescott.WeakConvergence.exists_convWeak_subseq_of_tight
#print axioms StokeyLucasPrescott.WeakConvergence.measure_eq_one_of_convWeak
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_9_cor1
#print axioms StokeyLucasPrescott.WeakConvergence.concentrated_iff
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_9
#print axioms StokeyLucasPrescott.WeakConvergence.distFun_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.not_convWeak_escape
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_9_false_hyp
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_9_false_concl
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_6a
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_6a_false
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_6b
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_6c
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_9_cor2
#print axioms StokeyLucasPrescott.WeakConvergence.bcf_abs_le_norm
#print axioms StokeyLucasPrescott.WeakConvergence.convWeak_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.integral_markovOpR
#print axioms StokeyLucasPrescott.WeakConvergence.fellerBCF
#print axioms StokeyLucasPrescott.WeakConvergence.fellerBCF_apply
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_7
#print axioms StokeyLucasPrescott.WeakConvergence.flipKernel
#print axioms StokeyLucasPrescott.WeakConvergence.isMarkovKernel_flipKernel
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_flip
#print axioms StokeyLucasPrescott.WeakConvergence.adjointOp_flip_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_8a
#print axioms StokeyLucasPrescott.WeakConvergence.iterate_flip_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.symm_ne_self
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_8b
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_8c
#print axioms StokeyLucasPrescott.WeakConvergence.isProbabilityMeasure_iterate
#print axioms StokeyLucasPrescott.WeakConvergence.invariant_of_convWeak
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_10
#print axioms StokeyLucasPrescott.WeakConvergence.Dominates
#print axioms StokeyLucasPrescott.WeakConvergence.Dominates.trans
#print axioms StokeyLucasPrescott.WeakConvergence.Dominates.real_le
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_9a
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_9a_subtype
#print axioms StokeyLucasPrescott.WeakConvergence.measure_lower_le
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_9b
#print axioms StokeyLucasPrescott.WeakConvergence.real_half_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_9c
#print axioms StokeyLucasPrescott.WeakConvergence.distFun_map_val
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_10
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_11
#print axioms StokeyLucasPrescott.WeakConvergence.markovOpR_kpow_zero
#print axioms StokeyLucasPrescott.WeakConvergence.markovOpR_kpow_add
#print axioms StokeyLucasPrescott.WeakConvergence.isMonotoneTF_kpow
#print axioms StokeyLucasPrescott.WeakConvergence.iterate_dirac
#print axioms StokeyLucasPrescott.WeakConvergence.dominates_iterate
#print axioms StokeyLucasPrescott.WeakConvergence.IccBot
#print axioms StokeyLucasPrescott.WeakConvergence.IccTop
#print axioms StokeyLucasPrescott.WeakConvergence.IccBot_le
#print axioms StokeyLucasPrescott.WeakConvergence.le_IccTop
#print axioms StokeyLucasPrescott.WeakConvergence.dominates_dirac_bot_top
#print axioms StokeyLucasPrescott.WeakConvergence.exists_subtype_measure
#print axioms StokeyLucasPrescott.WeakConvergence.map_val_Icc
#print axioms StokeyLucasPrescott.WeakConvergence.convWeak_of_dominance_mono
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_12
#print axioms StokeyLucasPrescott.WeakConvergence.Assumption12_1
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_14
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_11
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_12
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_clamp01
#print axioms StokeyLucasPrescott.WeakConvergence.monotone_clamp01
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01_nonneg
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01_le_one
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01_of_nonpos
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01_of_one_le
#print axioms StokeyLucasPrescott.WeakConvergence.clamp01_of_mem
#print axioms StokeyLucasPrescott.WeakConvergence.lowEnd
#print axioms StokeyLucasPrescott.WeakConvergence.highEnd
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_lowEnd
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_highEnd
#print axioms StokeyLucasPrescott.WeakConvergence.monotone_lowEnd
#print axioms StokeyLucasPrescott.WeakConvergence.monotone_highEnd
#print axioms StokeyLucasPrescott.WeakConvergence.lowEnd_nonneg
#print axioms StokeyLucasPrescott.WeakConvergence.highEnd_le
#print axioms StokeyLucasPrescott.WeakConvergence.gap_le
#print axioms StokeyLucasPrescott.WeakConvergence.bandPt
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_bandPt
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_bandPt_left
#print axioms StokeyLucasPrescott.WeakConvergence.continuous_bandPt_right
#print axioms StokeyLucasPrescott.WeakConvergence.bandPt_mono
#print axioms StokeyLucasPrescott.WeakConvergence.unif
#print axioms StokeyLucasPrescott.WeakConvergence.isProbabilityMeasure_unif
#print axioms StokeyLucasPrescott.WeakConvergence.unif_Icc
#print axioms StokeyLucasPrescott.WeakConvergence.bandKernel
#print axioms StokeyLucasPrescott.WeakConvergence.bandKernel_apply
#print axioms StokeyLucasPrescott.WeakConvergence.isMarkovKernel_bandKernel
#print axioms StokeyLucasPrescott.WeakConvergence.bandKernel_apply_set
#print axioms StokeyLucasPrescott.WeakConvergence.integral_bandKernel
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_13a
#print axioms StokeyLucasPrescott.WeakConvergence.kpow_eq_one_of_invariant
#print axioms StokeyLucasPrescott.WeakConvergence.bandKernel_eq_one
#print axioms StokeyLucasPrescott.WeakConvergence.bandPt_E₁
#print axioms StokeyLucasPrescott.WeakConvergence.bandPt_E₂
#print axioms StokeyLucasPrescott.WeakConvergence.bandKernel_leave
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_13b
#print axioms StokeyLucasPrescott.WeakConvergence.ex_12_13c
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_uniform_markovOp
#print axioms StokeyLucasPrescott.WeakConvergence.theorem_12_13
#print axioms StokeyLucasPrescott.WeakConvergence.tendsto_integral_abs_sub
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_14_cont
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_14_mono
#print axioms StokeyLucasPrescott.WeakConvergence.integral_lt_integral_of_lt
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_14_strictMono
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_14_concave
#print axioms StokeyLucasPrescott.WeakConvergence.lemma_12_14_strictConcave
