/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ErgodicTheory.InvariantEvents
import ErgodicTheory.StationaryErgodicity
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Stationary Markov processes (Miao §4.3)

Miao, §4.3, pp. 125–129, and Exercises 3, 5 and 6. A transition function is a Markov kernel
`P : Kernel X X` on an arbitrary measurable space; `invariantDistributions P = M` is the set of
invariant distributions. `pathMeasure P μ` is the law of the chain with initial law `μ` on
`X^ℕ` (Ionescu-Tulcea, copied in `ErgodicTheory.PathSpace`), and `pathKernel P x = P_x`.

* `convex_invariantDistributions`: `M` is convex; `pathMeasure_add_smul`:
  `P_{απ₁ + βπ₂} = αP_{π₁} + βP_{π₂}` (p. 127).
* **Exercise 3** (`ex_4_3`): started at `π ∈ M` the coordinate process is stationary, Markov with
  transition function `P`, and every `Xₙ` has law `π`; `eq_4_4`: its finite-dimensional
  distributions are (4.4).
* **Definition 3.3.5** (recalled on p. 128): `IsPInvariantSet`, `IsErgodicMeasure`.
* **Lemma 4.3.1** (`lemma_4_3_1`): every shift-invariant event `A` is, up to a `P_π`-null set, of
  the form `{x₀ ∈ A₁}` (and `{xₙ ∈ A₁}` for every `n`), with `A₁` a `P`-invariant set.
* `isInvariant_restrict`, `isInvariant_restrict_compl` (p. 128): for an (a.e.) `P`-invariant
  set `A₁`, `π(A₁ ∩ ·)` and `π(A₁ᶜ ∩ ·)` are invariant.
* **Theorem 4.3.1** (`theorem_4_3_1`): `(X^ℕ, P_π, θ)` is ergodic iff `π` is an extreme point of
  `M`; `theorem_4_3_1_iff_isErgodicMeasure`: iff `π` is ergodic in the sense of
  Definition 3.3.5 (p. 128).
* **Corollary 4.3.1** (`corollary_4_3_1`): a unique invariant distribution is ergodic.
* **Theorem 4.3.2** (`theorem_4_3_2`): for an extremal `π` and bounded measurable `f`, for
  `π`-a.e. `x₀`, `(1/N) Σ_{k=1}^N f(x_k) → ∫ f dπ`, `P_{x₀}`-a.s.; `ex_4_5_b` is Exercise 5.
* **Exercise 6** (`ex_4_6`): two distinct ergodic invariant probabilities of a measurable map
  are mutually singular; `ex_4_6_markov`: two distinct ergodic invariant distributions of `P`
  (Definition 3.3.5) are mutually singular, and so are their path measures.

**Departures.** The book builds the stationary chain on the two-sided space `X^ℤ` by the
Kolmogorov extension theorem (4.4). Here the chain is the one-sided chain on `X^ℕ` with
`X₀ ∼ π` (the first construction mentioned on p. 125), and `θ` is the one-sided shift. Exercise 3,
Lemma 4.3.1 and Theorem 4.3.1 are proved for this chain. Lemma 4.3.1 then says `I ⊆ σ(x₀)` up to
null sets; the book's proof (via the remote past and future and Exercise 4) is replaced by
Lévy's upward theorem and stationarity (copied `mt_lemma_17_1_1`). The book's footnote 2 uses
"`P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁`" while Definition 3.3.5 requires every `x ∈ A₁`;
Lemma 4.3.1 produces a set with the stronger property, so both readings give the same notion of
ergodic `π` (`theorem_4_3_1_iff_isErgodicMeasure`). In the proof of Theorem 4.3.1 the book picks
an `f` with `∫ f dP_{π₁} ≠ ∫ f dP_{π₂}` and derives `E₁ ∩ E₂ = ∅`; here the same ergodic theorem
shows `π₁ = π` directly (`eq_of_ergodic_of_absolutelyContinuous`).
-/

namespace Miao.ErgodicTheory

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The set `M` of invariant distributions -/

/-- `M`, the set of invariant distributions of the transition function `P` (Miao, p. 126). -/
def invariantDistributions (P : Kernel X X) : Set (Measure X) :=
  {π | IsProbabilityMeasure π ∧ IsInvariant P π}

/-- Miao, Theorem 4.3.1, p. 126: `M` is a convex set. -/
theorem convex_invariantDistributions (P : Kernel X X) :
    Convex ℝ≥0∞ (invariantDistributions P) := by
  intro π₁ h₁ π₂ h₂ a b _ _ hab
  refine ⟨⟨?_⟩, (h₁.2.smul a).add (h₂.2.smul b)⟩
  have := h₁.1
  have := h₂.1
  simp [Measure.add_apply, Measure.smul_apply, hab]

/-- Miao, p. 127: `P_{απ₁ + βπ₂} = αP_{π₁} + βP_{π₂}`. -/
theorem pathMeasure_add_smul (P : Kernel X X) [IsMarkovKernel P] (π₁ π₂ : Measure X)
    (a b : ℝ≥0∞) :
    pathMeasure P (a • π₁ + b • π₂) = a • pathMeasure P π₁ + b • pathMeasure P π₂ := by
  rw [pathMeasure_eq_comp, pathMeasure_eq_comp, pathMeasure_eq_comp, Measure.comp_add,
    Measure.comp_smul, Measure.comp_smul]

/-! ### Exercise 3: the stationary chain -/

/-- The law of the coordinate process on path space is the measure itself. -/
theorem pathLaw_coord (μ : Measure (ℕ → X)) : pathLaw μ (fun n ω => ω n) = μ :=
  Measure.map_id'

/-- **Exercise 3** (Miao, p. 129), on `X^ℕ`: if `π` is invariant, the coordinate process under
`P_π` is stationary, every `Xₙ` has distribution `π`, and it is Markov with transition function
`P`: `E[1_A(X_{n+1}) | X₀, …, Xₙ] = P(Xₙ, A)`. -/
theorem ex_4_3 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) :
    IsStationary (pathMeasure P π) (fun n ω => ω n) ∧
      (∀ n, (pathMeasure P π).map (fun ω => ω n) = π) ∧
      ∀ n {A : Set X}, MeasurableSet A →
        (pathMeasure P π)[fun ω => A.indicator (1 : X → ℝ) (ω (n + 1)) | natFilt n]
          =ᵐ[pathMeasure P π] fun ω => (P (ω n)).real A := by
  have := isProbabilityMeasure_pathMeasure P π
  refine ⟨(isStationary_iff_map_shift (fun n => measurable_pi_apply n)).2 fun t => ?_,
    fun n => hπ.map_coord n, fun n A hA => ?_⟩
  · rw [pathLaw_coord]
    exact hπ.map_shift t
  · have hH : Measurable fun ω : ℕ → X => A.indicator (1 : X → ℝ) (ω 1) :=
      (measurable_one.indicator hA).comp (measurable_pi_apply 1)
    have h := markov_property_bdd P π n hH (B := 1) fun ω => by
      by_cases h : ω 1 ∈ A <;> simp [h]
    refine h.trans (Eventually.of_forall fun ω => ?_)
    have hm : Measurable fun ω' : ℕ → X => ω' 1 := measurable_pi_apply 1
    simp only
    rw [← integral_map hm.aemeasurable (measurable_one.indicator hA).aestronglyMeasurable,
      pathKernel_map_coord, pow_one, integral_indicator_one hA]

/-- Miao, (4.4), p. 126, for the one-sided chain: `P_π(x₀ ∈ A₀, …, xₙ ∈ Aₙ) =
∫_{A₀} ⋯ ∫_{Aₙ} P(x_{n−1}, dxₙ) ⋯ P(x₀, dx₁) π(dx₀)` (`cylFn` is the nested integral). -/
theorem eq_4_4 (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) :
    pathMeasure P π {ω | ∀ i ≤ n, ω i ∈ A i} = ∫⁻ x, cylFn P n A x ∂π :=
  pathMeasure_boxSet P π n hA

/-! ### Definition 3.3.5 -/

/-- Definition 3.3.5 (Miao, p. 111, recalled on p. 128): `A` is a `P`-invariant set if
`P(x, A) = 1` for every `x ∈ A`. -/
def IsPInvariantSet (P : Kernel X X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ x ∈ A, P x A = 1

/-- Definition 3.3.5 (Miao, p. 111): an invariant distribution `π` is ergodic if `π(A) ∈ {0, 1}`
for every `P`-invariant set `A`. -/
def IsErgodicMeasure (P : Kernel X X) (π : Measure X) : Prop :=
  ∀ A : Set X, IsPInvariantSet P A → π A = 0 ∨ π A = 1

/-! ### Lemma 4.3.1 -/

/-- Miao, proof of Lemma 4.3.1: for a strictly shift-invariant event `A`, `h(x) = P_x(A)` is
harmonic, `∫ h(y) P(x, dy) = h(x)`. -/
theorem expectFn_harmonic_of_invariant (P : Kernel X X) [IsMarkovKernel P]
    {A : Set (ℕ → X)} (hA : MeasurableSet A) (hθA : shift 1 ⁻¹' A = A) (x : X) :
    ∫ y, expectFn P (A.indicator 1) y ∂P x = expectFn P (A.indicator 1) x := by
  have := isMarkovKernel_pathKernel P
  set Y : (ℕ → X) → ℝ := A.indicator 1 with hY
  have hYm : Measurable Y := measurable_one.indicator hA
  have hYb : ∀ ω, |Y ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hY, h]
  have hhm : Measurable (expectFn P Y) := measurable_expectFn P hYm
  have h1 : ∫ y, expectFn P Y y ∂P x = ∫ ω, expectFn P Y (ω 1) ∂pathKernel P x := by
    rw [← integral_map (measurable_pi_apply 1).aemeasurable hhm.aestronglyMeasurable,
      pathKernel_map_coord, pow_one]
  have h2 := markov_setIntegral P (Measure.dirac x) (n := 1) MeasurableSet.univ hYm
    (integrable_shift_of_bdd P (Measure.dirac x) 1 hYm hYb).integrableOn
  simp only [pathMeasure_dirac, Measure.restrict_univ] at h2
  have h3 : (fun ω => Y (shift 1 ω)) = Y := by
    ext ω
    exact indicator_shift_of_invariant hθA 1 ω
  rw [h3] at h2
  rw [h1]
  exact h2.symm

/-- **Lemma 4.3.1** (Miao, p. 127), one-sided form: if `π` is invariant and `A` is a
shift-invariant event (`θ⁻¹A = A`), there is a `P`-invariant set `A₁` (Definition 3.3.5) with
`A = {x₀ ∈ A₁}` and indeed `A = {xₙ ∈ A₁}` for every `n`, up to `P_π`-null sets. So
`I ⊆ F₀⁰` (and `I ⊆ Fₙⁿ`) up to null sets. -/
theorem lemma_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {A : Set (ℕ → X)} (hA : MeasurableSet A) (hθA : shift 1 ⁻¹' A = A) :
    ∃ A₁ : Set X, IsPInvariantSet P A₁ ∧ A =ᵐ[pathMeasure P π] {ω | ω 0 ∈ A₁} ∧
      ∀ n, A =ᵐ[pathMeasure P π] {ω | ω n ∈ A₁} := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  set Y : (ℕ → X) → ℝ := A.indicator 1 with hY
  have hYm : Measurable Y := measurable_one.indicator hA
  have hYb : ∀ ω, |Y ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hY, h]
  set h := expectFn P Y with hh
  have hhm : Measurable h := measurable_expectFn P hYm
  have hh1 : ∀ x, h x ≤ 1 := fun x => (abs_le.1 (abs_expectFn_le P hYb x)).2
  have hh0 : ∀ x, 0 ≤ h x := fun x => integral_nonneg fun ω => by
    by_cases hω : ω ∈ A <;> simp [hY, hω]
  have hinvY : IsPathInvariant P π Y := fun k => Eventually.of_forall fun ω =>
    indicator_shift_of_invariant hθA k ω
  have hlem := mt_lemma_17_1_1 P hπ hYm (integrable_of_bdd P π hYm hYb) hinvY
  set A₁ : Set X := {x | h x = 1} with hA₁
  have hA₁m : MeasurableSet A₁ := measurableSet_eq_fun hhm measurable_const
  have h0 : A =ᵐ[pathMeasure P π] {ω | ω 0 ∈ A₁} := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hlem] with ω hω
    change Y ω = h (ω 0) at hω
    by_cases hωA : ω ∈ A
    · have h1 : Y ω = 1 := by rw [hY, Set.indicator_of_mem hωA]; rfl
      have : ω 0 ∈ A₁ := by
        change h (ω 0) = 1
        rw [← hω, h1]
      exact iff_of_true hωA this
    · have h1 : Y ω = 0 := by rw [hY, Set.indicator_of_notMem hωA]
      have : ω 0 ∉ A₁ := by
        intro hc
        change h (ω 0) = 1 at hc
        rw [← hω, h1] at hc
        norm_num at hc
      exact iff_of_false hωA this
  refine ⟨A₁, ⟨hA₁m, fun x hx => ?_⟩, h0, fun n => ?_⟩
  · -- `h(x) = 1 = ∫ h dP(x)` and `h ≤ 1` force `h = 1`, `P(x, ·)`-a.s.
    have hharm := expectFn_harmonic_of_invariant P hA hθA x
    rw [← hh, hx] at hharm
    have hint : Integrable h (P x) := Integrable.of_bound hhm.aestronglyMeasurable 1
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hh0 y)]; exact hh1 y)
    have hii : Integrable (fun y => 1 - h y) (P x) := (integrable_const 1).sub hint
    have hnn : 0 ≤ fun y => 1 - h y := fun y => by
      simp only [Pi.zero_apply]
      linarith [hh1 y]
    have hz : ∫ y, (1 - h y) ∂P x = 0 := by
      rw [integral_sub (integrable_const 1) hint, hharm]
      simp
    rw [integral_eq_zero_iff_of_nonneg hnn hii] at hz
    have hnull : P x A₁ᶜ = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hz
      refine le_antisymm (le_of_eq_of_le ?_ (le_of_eq hz)) zero_le
      congr 1
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hA₁, Pi.zero_apply]
      constructor
      · intro hy h'
        exact hy (by linarith)
      · intro hy h'
        exact hy (by rw [h']; ring)
    exact (prob_compl_eq_zero_iff hA₁m).1 hnull
  · have hmp : MeasurePreserving (shift (X := X) n) (pathMeasure P π) (pathMeasure P π) :=
      ⟨measurable_shift n, hπ.map_shift n⟩
    have hpre := hmp.quasiMeasurePreserving.preimage_ae_eq h0
    have hAn : shift n ⁻¹' A = A := by
      ext ω
      rw [Set.mem_preimage, ← iterate_shift_one, iterate_mem_iff hθA]
    rw [hAn] at hpre
    refine hpre.trans ?_
    have : shift n ⁻¹' {ω : ℕ → X | ω 0 ∈ A₁} = {ω | ω n ∈ A₁} := by
      ext ω
      simp [shift]
    rw [this]

/-! ### Invariant restrictions -/

/-- For an invariant `π` and a set `A₁` with `P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁` (Miao,
footnote 2, p. 128), `P(x, A₁) = 0` for `π`-a.e. `x ∉ A₁`. -/
theorem setLIntegral_compl_eq_zero (P : Kernel X X) {π : Measure X} [IsFiniteMeasure π]
    (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : ∫⁻ x in A₁ᶜ, P x A₁ ∂π = 0 := by
  have h1 : ∫⁻ x in A₁, P x A₁ ∂π = π A₁ := by
    rw [setLIntegral_congr_fun_ae hA (hinv.mono fun x hx hxA => hx hxA), setLIntegral_const,
      one_mul]
  have h2 := lintegral_add_compl (μ := π) (fun x => P x A₁) hA
  rw [h1, (isInvariant_iff P π).1 hπ A₁ hA] at h2
  exact (ENNReal.add_right_inj (measure_ne_top π A₁)).1 (h2.trans (add_zero _).symm)

/-- Miao, p. 128: if `P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁`, then `B ↦ π(A₁ ∩ B)` is invariant. -/
theorem isInvariant_restrict (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : IsInvariant P (π.restrict A₁) := by
  rw [isInvariant_iff]
  intro B hB
  have hπB := (isInvariant_iff P π).1 hπ
  have hout := setLIntegral_compl_eq_zero P hπ hA hinv
  have hin : ∫⁻ x in A₁, P x A₁ᶜ ∂π = 0 := by
    rw [setLIntegral_congr_fun_ae (g := fun _ => 0) hA (hinv.mono fun x hx hxA =>
      (prob_compl_eq_zero_iff hA).2 (hx hxA)), lintegral_zero]
  have hmeas : ∀ S : Set X, MeasurableSet S → Measurable fun x => P x S :=
    fun S hS => Kernel.measurable_coe P hS
  rw [Measure.restrict_apply hB]
  apply le_antisymm
  · calc ∫⁻ x in A₁, P x B ∂π ≤ ∫⁻ x in A₁, (P x (B ∩ A₁) + P x A₁ᶜ) ∂π := by
          refine lintegral_mono fun x => ?_
          calc P x B ≤ P x (B ∩ A₁) + P x (B \ A₁) := measure_le_inter_add_sdiff _ _ _
            _ ≤ P x (B ∩ A₁) + P x A₁ᶜ := by
              gcongr
              exact fun y hy => hy.2
      _ = ∫⁻ x in A₁, P x (B ∩ A₁) ∂π := by
          rw [lintegral_add_right _ (hmeas _ hA.compl), hin, add_zero]
      _ ≤ ∫⁻ x, P x (B ∩ A₁) ∂π := setLIntegral_le_lintegral _ _
      _ = π (B ∩ A₁) := hπB _ (hB.inter hA)
  · calc π (B ∩ A₁) = ∫⁻ x, P x (B ∩ A₁) ∂π := (hπB _ (hB.inter hA)).symm
      _ = ∫⁻ x in A₁, P x (B ∩ A₁) ∂π + ∫⁻ x in A₁ᶜ, P x (B ∩ A₁) ∂π :=
          (lintegral_add_compl _ hA).symm
      _ ≤ ∫⁻ x in A₁, P x B ∂π + ∫⁻ x in A₁ᶜ, P x A₁ ∂π := by
          gcongr with x x
          · exact Set.inter_subset_left
          · exact Set.inter_subset_right
      _ = ∫⁻ x in A₁, P x B ∂π := by rw [hout, add_zero]

/-- Miao, p. 128: under the same hypothesis, `B ↦ π(A₁ᶜ ∩ B)` is invariant. -/
theorem isInvariant_restrict_compl (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : IsInvariant P (π.restrict A₁ᶜ) := by
  refine isInvariant_restrict P hπ hA.compl ?_
  have hout := setLIntegral_compl_eq_zero P hπ hA hinv
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe P hA), Filter.EventuallyEq,
    ae_restrict_iff' hA.compl] at hout
  filter_upwards [hout] with x hx hxA
  exact (prob_compl_eq_one_iff hA).2 (hx hxA)

/-- Miao, proof of Theorem 4.3.1 (converse), p. 128: if `A₁` is (a.e.) `P`-invariant with
`0 < π(A₁) < 1`, then `π = απ₁ + (1 − α)π₂` with `π₁ = π(A₁ ∩ ·)/α`,
`π₂ = π(A₁ᶜ ∩ ·)/(1 − α)` distinct invariant distributions, so `π` is not extremal. -/
theorem not_mem_extremePoints_of_invariantSet (P : Kernel X X) [IsMarkovKernel P]
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {A₁ : Set X}
    (hA : MeasurableSet A₁) (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) (h0 : π A₁ ≠ 0)
    (h1 : π A₁ ≠ 1) : π ∉ Set.extremePoints ℝ≥0∞ (invariantDistributions P) := by
  intro hext
  set α := π A₁ with hα
  have hαtop : α ≠ ⊤ := measure_ne_top π A₁
  have hαle : α ≤ 1 := prob_le_one
  have hα1 : 1 - α ≠ 0 := by
    intro h
    exact h1 (le_antisymm hαle (tsub_eq_zero_iff_le.1 h))
  have hα1top : 1 - α ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hc : π A₁ᶜ = 1 - α := prob_compl_eq_one_sub hA
  set π₁ := α⁻¹ • π.restrict A₁ with hπ₁
  set π₂ := (1 - α)⁻¹ • π.restrict A₁ᶜ with hπ₂
  have hm₁ : π₁ ∈ invariantDistributions P := by
    refine ⟨⟨?_⟩, (isInvariant_restrict P hπ hA hinv).smul _⟩
    rw [hπ₁, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 hαtop]
  have hm₂ : π₂ ∈ invariantDistributions P := by
    refine ⟨⟨?_⟩, (isInvariant_restrict_compl P hπ hA hinv).smul _⟩
    rw [hπ₂, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hc,
      ENNReal.inv_mul_cancel hα1 hα1top]
  have hseg : π ∈ openSegment ℝ≥0∞ π₁ π₂ := by
    refine ⟨α, 1 - α, pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 hα1,
      add_tsub_cancel_of_le hαle, ?_⟩
    rw [hπ₁, hπ₂, smul_smul, smul_smul, ENNReal.mul_inv_cancel h0 hαtop,
      ENNReal.mul_inv_cancel hα1 hα1top, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hA]
  have heq := ((mem_extremePoints.1 hext).2 π₁ hm₁ π₂ hm₂ hseg).1
  have : π₁ A₁ = 1 := by
    rw [hπ₁, Measure.smul_apply, Measure.restrict_apply hA, Set.inter_self, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 hαtop]
  rw [heq] at this
  exact h1 this

/-! ### Theorem 4.3.1 -/

/-- `E_{P_ν}[1_C(x₀)] = ν(C)`. -/
theorem integral_indicator_coord_zero (P : Kernel X X) [IsMarkovKernel P] (ν : Measure X)
    {C : Set X} (hC : MeasurableSet C) :
    ∫ ω, C.indicator (1 : X → ℝ) (ω 0) ∂pathMeasure P ν = ν.real C := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_one.indicator hC).aestronglyMeasurable, pathMeasure_map_zero,
    integral_indicator_one hC]

/-- Miao, proof of Theorem 4.3.1, p. 127: if `(X^ℕ, P_π, θ)` is ergodic and `P_ν ≪ P_π` for an
invariant `ν`, then `ν = π` (the time averages of `1_C(x_k)` converge to `π(C)` `P_π`-a.s., hence
`P_ν`-a.s., while their `P_ν`-expectation is `ν(C)`). -/
theorem eq_of_ergodic_of_absolutelyContinuous (P : Kernel X X) [IsMarkovKernel P]
    {π ν : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure ν] (hπ : IsInvariant P π)
    (hν : IsInvariant P ν) (herg : IsErgodic (pathMeasure P π) (shift 1))
    (hac : pathMeasure P ν ≪ pathMeasure P π) : ν = π := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isProbabilityMeasure_pathMeasure P ν
  have hmpπ : MeasurePreserving (shift (X := X) 1) (pathMeasure P π) (pathMeasure P π) :=
    ⟨measurable_shift 1, hπ.map_shift 1⟩
  have hmpν : MeasurePreserving (shift (X := X) 1) (pathMeasure P ν) (pathMeasure P ν) :=
    ⟨measurable_shift 1, hν.map_shift 1⟩
  ext C hC
  set f : (ℕ → X) → ℝ := fun ω => C.indicator 1 (ω 0) with hf
  have hfm : Measurable f := (measurable_one.indicator hC).comp (measurable_pi_apply 0)
  have hfb : ∀ ω, |f ω| ≤ 1 := fun ω => by by_cases h : ω 0 ∈ C <;> simp [hf, h]
  have hint : ∀ ρ : Measure (ℕ → X), IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfb ω)
  have h1 := theorem_4_1_1_ergodic hmpπ herg hfm (hint _ inferInstance)
  have h1' := hac.ae_le h1
  have h2 := ae_tendsto_birkhoffLimit hmpν hfm (hint _ inferInstance)
  have hL : birkhoffLimit (shift 1) f =ᵐ[pathMeasure P ν]
      fun _ => ∫ ω, f ω ∂pathMeasure P π := by
    filter_upwards [h1', h2] with ω hω1 hω2
    refine tendsto_nhds_unique hω2 ?_
    simpa only [birkhoffAverage_eq_sum] using hω1
  have h3 := setIntegral_birkhoffLimit hmpν hfm (hint _ inferInstance) MeasurableSet.univ
    Set.preimage_univ
  simp only [Measure.restrict_univ] at h3
  rw [integral_congr_ae hL, integral_const, probReal_univ, one_smul,
    integral_indicator_coord_zero P π hC, integral_indicator_coord_zero P ν hC] at h3
  rw [measureReal_def, measureReal_def] at h3
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3).symm

/-- **Theorem 4.3.1** (Miao, p. 126), on the one-sided path space: for `π ∈ M`, the dynamical
system `(X^ℕ, X^ℕ, P_π, θ)` is ergodic iff `π` is an extreme point of the convex set `M`. -/
theorem theorem_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    IsErgodic (pathMeasure P π) (shift 1) ↔
      π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) := by
  have := isProbabilityMeasure_pathMeasure P π
  constructor
  · intro herg
    refine mem_extremePoints.2 ⟨⟨inferInstance, hπ⟩, fun π₁ h₁ π₂ h₂ hseg => ?_⟩
    obtain ⟨a, b, ha, hb, -, hπeq⟩ := hseg
    have := h₁.1
    have := h₂.1
    have hP : pathMeasure P π = a • pathMeasure P π₁ + b • pathMeasure P π₂ := by
      rw [← hπeq, pathMeasure_add_smul]
    have hac₁ : pathMeasure P π₁ ≪ pathMeasure P π := by
      intro S hS
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul] at hS
      exact (mul_eq_zero.1 (add_eq_zero.1 hS).1).resolve_left ha.ne'
    have hac₂ : pathMeasure P π₂ ≪ pathMeasure P π := by
      intro S hS
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul] at hS
      exact (mul_eq_zero.1 (add_eq_zero.1 hS).2).resolve_left hb.ne'
    exact ⟨eq_of_ergodic_of_absolutelyContinuous P hπ h₁.2 herg hac₁,
      eq_of_ergodic_of_absolutelyContinuous P hπ h₂.2 herg hac₂⟩
  · intro hext A ⟨hAm, hθA⟩
    obtain ⟨A₁, ⟨hA₁m, hA₁⟩, hAe, -⟩ := lemma_4_3_1 P hπ hAm hθA
    have hPA : pathMeasure P π A = π A₁ := by
      rw [measure_congr hAe]
      change pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = _
      rw [← Measure.map_apply (measurable_pi_apply 0) hA₁m, pathMeasure_map_zero]
    rw [hPA]
    by_contra hcon
    push Not at hcon
    exact not_mem_extremePoints_of_invariantSet P hπ hA₁m
      (Eventually.of_forall fun x hx => hA₁ x hx) hcon.1 hcon.2 hext

/-- Miao, p. 128: `(X^ℕ, P_π, θ)` is ergodic iff the invariant distribution `π` is ergodic in
the sense of Definition 3.3.5. -/
theorem theorem_4_3_1_iff_isErgodicMeasure (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    IsErgodic (pathMeasure P π) (shift 1) ↔ IsErgodicMeasure P π := by
  have := isProbabilityMeasure_pathMeasure P π
  constructor
  · intro herg A ⟨hAm, hA⟩
    by_contra hcon
    push Not at hcon
    exact not_mem_extremePoints_of_invariantSet P hπ hAm
      (Eventually.of_forall fun x hx => hA x hx) hcon.1 hcon.2 ((theorem_4_3_1 P hπ).1 herg)
  · intro herg A ⟨hAm, hθA⟩
    obtain ⟨A₁, hA₁, hAe, -⟩ := lemma_4_3_1 P hπ hAm hθA
    rw [measure_congr hAe]
    change pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = 0 ∨
      pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = 1
    rw [← Measure.map_apply (measurable_pi_apply 0) hA₁.1, pathMeasure_map_zero]
    exact herg A₁ hA₁

/-- **Corollary 4.3.1** (Miao, p. 128): if `P` has a unique invariant distribution `π`, then `π`
is ergodic (Definition 3.3.5), `π` is extremal in `M`, and `(X^ℕ, P_π, θ)` is ergodic. -/
theorem corollary_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (huniq : ∀ ν : Measure X, IsProbabilityMeasure ν → IsInvariant P ν → ν = π) :
    IsErgodicMeasure P π ∧ π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) ∧
      IsErgodic (pathMeasure P π) (shift 1) := by
  have hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) :=
    mem_extremePoints.2 ⟨⟨inferInstance, hπ⟩, fun π₁ h₁ π₂ h₂ _ =>
      ⟨huniq π₁ h₁.1 h₁.2, huniq π₂ h₂.1 h₂.2⟩⟩
  have herg := (theorem_4_3_1 P hπ).2 hext
  exact ⟨(theorem_4_3_1_iff_isErgodicMeasure P hπ).1 herg, hext, herg⟩

/-! ### Theorem 4.3.2 -/

/-- **Theorem 4.3.2** (strong law for Markov processes, Miao, p. 128). If `π` is an extremal
invariant distribution and `f` is bounded measurable, then for `π`-almost every `x₀`,
`(1/N) Σ_{k=1}^N f(x_k) → ∫ f dπ` for `P_{x₀}`-almost every path `(x₀, x₁, x₂, …)`. -/
theorem theorem_4_3_2 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P)) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ x₀ ∂π, ∀ᵐ ω ∂pathKernel P x₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, f (ω (k + 1))) atTop (𝓝 (∫ y, f y ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have herg := (theorem_4_3_1 P hπ).2 hext
  have hmp : MeasurePreserving (shift (X := X) 1) (pathMeasure P π) (pathMeasure P π) :=
    ⟨measurable_shift 1, hπ.map_shift 1⟩
  set F : (ℕ → X) → ℝ := fun ω => f (ω 0) with hF
  have hFm : Measurable F := hf.comp (measurable_pi_apply 0)
  have hFi : Integrable F (pathMeasure P π) := Integrable.of_bound hFm.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  have hE : ∫ ω, F ω ∂pathMeasure P π = ∫ y, f y ∂π := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
      pathMeasure_map_zero]
  have h1 := theorem_4_1_1_ergodic hmp herg hFm hFi
  rw [hE] at h1
  set S : Set (ℕ → X) := {ω | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, f (ω (k + 1))) atTop (𝓝 (∫ y, f y ∂π))} with hS
  have hSm : MeasurableSet S := measurableSet_tendsto _ fun N =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply _))
  have hSae : ∀ᵐ ω ∂pathMeasure P π, ω ∈ S := by
    filter_upwards [h1] with ω hω
    have := tendsto_avg_succ hω
    refine this.congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, iterate_shift_one, shift_apply, add_zero]
  have hnull : pathMeasure P π Sᶜ = 0 := by
    rw [ae_iff] at hSae
    exact hSae
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm.compl (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm.compl)] at hnull
  filter_upwards [hnull] with x hx
  rw [ae_iff]
  exact hx

/-- **Exercise 5** (Miao, p. 129), second part: the proof of Theorem 4.3.2 (`theorem_4_3_2`),
here stated for `f = 1_B` of a measurable set. -/
theorem ex_4_5_b (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P)) {B : Set X}
    (hB : MeasurableSet B) :
    ∀ᵐ x₀ ∂π, ∀ᵐ ω ∂pathKernel P x₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, B.indicator (1 : X → ℝ) (ω (k + 1))) atTop (𝓝 (π.real B)) := by
  have h := theorem_4_3_2 P hπ hext (measurable_one.indicator hB) (C := 1) fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  rwa [integral_indicator_one hB] at h

/-! ### Exercise 6 -/

/-- **Exercise 6** (Miao, p. 129). Two distinct ergodic invariant probability measures of a
measurable map `θ` are mutually singular. -/
theorem ex_4_6 {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {θ : Ω → Ω} (hμ : MeasurePreserving θ μ μ)
    (hν : MeasurePreserving θ ν ν) (hμe : IsErgodic μ θ) (hνe : IsErgodic ν θ) (hne : μ ≠ ν) :
    μ ⟂ₘ ν := by
  obtain ⟨C, hC, hCne⟩ : ∃ C, MeasurableSet C ∧ μ C ≠ ν C := by
    by_contra h
    push Not at h
    exact hne (Measure.ext fun C hC => h C hC)
  have hCne' : μ.real C ≠ ν.real C := by
    rw [measureReal_def, measureReal_def]
    exact fun h => hCne ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)).1 h)
  set f : Ω → ℝ := C.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hC
  have hint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; by_cases h : ω ∈ C <;> simp [hf, h])
  have hEρ : ∀ ρ : Measure Ω, ∫ ω, f ω ∂ρ = ρ.real C := fun ρ => integral_indicator_one hC
  set S : ℝ → Set Ω := fun c => {ω | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ n ∈ Finset.range N, f (θ^[n] ω)) atTop (𝓝 c)} with hS
  have hSm : ∀ c, MeasurableSet (S c) := fun c => measurableSet_tendsto _ fun N =>
    measurable_const.mul (Finset.measurable_sum _ fun n _ =>
      hfm.comp (hμ.measurable.iterate n))
  have hμS : μ (S (μ.real C))ᶜ = 0 := by
    have h := theorem_4_1_1_ergodic hμ hμe hfm (hint μ inferInstance)
    rw [hEρ] at h
    rw [ae_iff] at h
    exact h
  have hνS : ν (S (ν.real C))ᶜ = 0 := by
    have h := theorem_4_1_1_ergodic hν hνe hfm (hint ν inferInstance)
    rw [hEρ] at h
    rw [ae_iff] at h
    exact h
  have hdisj : S (ν.real C) ⊆ (S (μ.real C))ᶜ := fun ω h1 h2 =>
    hCne' (tendsto_nhds_unique h2 h1)
  exact ⟨S (ν.real C), hSm _, measure_mono_null hdisj hμS, hνS⟩

/-- **Exercise 6** (Miao, p. 129) for Markov processes: two distinct invariant distributions of
`P` that are ergodic (Definition 3.3.5) are mutually singular, and so are their path
measures. -/
theorem ex_4_6_markov (P : Kernel X X) [IsMarkovKernel P] {π₁ π₂ : Measure X}
    [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂] (h₁ : IsInvariant P π₁)
    (h₂ : IsInvariant P π₂) (he₁ : IsErgodicMeasure P π₁) (he₂ : IsErgodicMeasure P π₂)
    (hne : π₁ ≠ π₂) : pathMeasure P π₁ ⟂ₘ pathMeasure P π₂ ∧ π₁ ⟂ₘ π₂ := by
  have := isProbabilityMeasure_pathMeasure P π₁
  have := isProbabilityMeasure_pathMeasure P π₂
  have := isMarkovKernel_pathKernel P
  have hpne : pathMeasure P π₁ ≠ pathMeasure P π₂ := by
    intro h
    apply hne
    rw [← pathMeasure_map_zero P π₁, ← pathMeasure_map_zero P π₂, h]
  have hpath := ex_4_6 ⟨measurable_shift 1, h₁.map_shift 1⟩ ⟨measurable_shift 1, h₂.map_shift 1⟩
    ((theorem_4_3_1_iff_isErgodicMeasure P h₁).2 he₁)
    ((theorem_4_3_1_iff_isErgodicMeasure P h₂).2 he₂) hpne
  refine ⟨hpath, ?_⟩
  obtain ⟨S, hSm, hS1, hS2⟩ := hpath
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm)] at hS1
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm.compl (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm.compl)] at hS2
  set T : Set X := {x | pathKernel P x S = 0} with hT
  have hTm : MeasurableSet T := measurableSet_eq_fun (Kernel.measurable_coe _ hSm)
    measurable_const
  refine ⟨Tᶜ, hTm.compl, ?_, ?_⟩
  · have : ∀ᵐ x ∂π₁, x ∈ T := hS1
    rw [ae_iff] at this
    exact this
  · rw [compl_compl]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hS2)
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    have hx' : pathKernel P x S = 0 := hx
    rw [prob_compl_eq_zero_iff hSm, hx']
    exact zero_ne_one

end Miao.ErgodicTheory
