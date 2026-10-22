/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.PathSpace
import Ergodicity.Kernels
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The Markov property (MT §3.4.2)

Meyn and Tweedie, §3.4.2, pp. 61–63. `shift n` is the shift `θⁿ` on paths,
`(θⁿω)ᵢ = ω_{n+i}` (p. 63), so `H ∘ θⁿ = θⁿH`.

* `pathMeasure_map_coord`, `pathKernel_map_coord` (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`,
  and `P_x(Φₙ ∈ A) = Pⁿ(x, A)`; `pathKernel_coord_chapmanKolmogorov` is (3.24).
* `markov_measure`: for `G ∈ 𝓕ₙ^Φ`, the law of `θⁿΦ` on `G` is `∫_G P_{Φₙ}(·) dP_μ`. This is the
  Markov property in its strongest form, as an identity of measures on path space.
* `markov_lintegral_mul`: `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]` for `𝓕ₙ^Φ`-measurable `F ≥ 0`.
* `markov_lintegral`, `markov_setIntegral`: `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ` for
  nonnegative and for integrable `H`.
* `markov_property` (3.28), p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for every
  measurable `H` with `θⁿH` integrable; `markov_property_bdd` for bounded `H`.
* **Proposition 3.4.3** (`proposition_3_4_3`, p. 63), (3.27):
  `E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]` for bounded measurable `h`.
* `isMarkovChain_of_step`: a process adapted to a filtration whose one-step conditional laws are
  given by `Q` is a Markov chain with kernel `Q`. Hence `skeleton_isMarkovChain` (3.25),
  p. 61: the `m`-skeleton `(Φ_{mn})ₙ` is a Markov chain with transition kernel `Pᵐ`.

**Corrections.** None. The book states (3.27) and (3.28) for bounded `h`; they hold for every
`h` with `θⁿH` integrable (`markov_property`).
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The shift -/

/-- The shift `θⁿ` on paths: `(θⁿω)ᵢ = ω_{n+i}` (MT p. 63). -/
def shift (n : ℕ) (ω : ℕ → X) : ℕ → X := fun i => ω (n + i)

/-- The shift is measurable. -/
theorem measurable_shift (n : ℕ) : Measurable (shift (X := X) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (n + i)

omit [MeasurableSpace X] in
/-- `θ⁰ = id`. -/
@[simp] theorem shift_zero (ω : ℕ → X) : shift 0 ω = ω := by
  ext i; simp [shift]

omit [MeasurableSpace X] in
/-- `θᵐ ∘ θⁿ = θⁿ⁺ᵐ`. -/
theorem shift_shift (m n : ℕ) (ω : ℕ → X) : shift m (shift n ω) = shift (n + m) ω := by
  ext i; simp [shift, add_assoc]

omit [MeasurableSpace X] in
/-- `Φᵢ ∘ θⁿ = Φₙ₊ᵢ` (MT p. 63). -/
@[simp] theorem shift_apply (n i : ℕ) (ω : ℕ → X) : shift n ω i = ω (n + i) := rfl

/-! ### Integrals against `κ ∘ₘ ν` -/

/-- `∫ f d(κ ∘ₘ ν) = ∫ ∫ f dκ(x) ν(dx)` for integrable `f`. -/
theorem integral_measure_comp {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℝ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-! ### The law of `Φₙ` -/

/-- (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`. -/
theorem pathMeasure_map_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (pathMeasure P μ).map (fun ω => ω n) = (P ^ n) ∘ₘ μ := by
  induction n with
  | zero => rw [pathMeasure_map_zero, pow_zero]; exact Measure.id_comp.symm
  | succ n ih =>
    ext A hA
    have hmA : Measurable (fun y => P y A) := Kernel.measurable_coe _ hA
    rw [Measure.map_apply (measurable_pi_apply (n + 1) : Measurable fun ω : ℕ → X => ω (n + 1))
      hA, ← lintegral_indicator_one (measurable_pi_apply (n + 1) hA)]
    have h1 := setLIntegral_succ P μ (n := n) MeasurableSet.univ
      (measurable_one.indicator hA : Measurable (A.indicator (1 : X → ℝ≥0∞)))
    simp only [Measure.restrict_univ, lintegral_indicator_one hA] at h1
    have h2 : ((fun ω : ℕ → X => ω (n + 1)) ⁻¹' A).indicator (1 : (ℕ → X) → ℝ≥0∞) =
        fun ω => A.indicator 1 (ω (n + 1)) := by
      ext ω; by_cases h : ω (n + 1) ∈ A <;> simp [h]
    rw [h2, h1, ← lintegral_map hmA (measurable_pi_apply n), ih, pow_succ',
      ← measure_kernel_apply _ _ hA, measure_kernel_assoc]
    rfl

/-- (3.8): `P_x(Φₙ ∈ ·) = Pⁿ(x, ·)`. -/
theorem pathKernel_map_coord (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    (pathKernel P x).map (fun ω => ω n) = (P ^ n) x := by
  rw [← pathMeasure_dirac, pathMeasure_map_coord, dirac_kernel]

/-- `P_x(Φₙ ∈ A) = Pⁿ(x, A)`. -/
theorem pathKernel_coord_mem (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) {A : Set X}
    (hA : MeasurableSet A) : pathKernel P x {ω | ω n ∈ A} = (P ^ n) x A := by
  rw [← pathKernel_map_coord P x n,
    Measure.map_apply (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n) hA]
  rfl

/-- (3.24), MT p. 61: `P_x(Φₙ ∈ A) = ∫ P_x(Φₘ ∈ dy) P_y(Φₙ₋ₘ ∈ A)` for `m ≤ n`. -/
theorem pathKernel_coord_chapmanKolmogorov (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {m n : ℕ} (hmn : m ≤ n) {A : Set X} (hA : MeasurableSet A) :
    pathKernel P x {ω | ω n ∈ A} =
      ∫⁻ y, pathKernel P y {ω | ω (n - m) ∈ A} ∂(pathKernel P x).map (fun ω => ω m) := by
  simp_rw [pathKernel_coord_mem P _ _ hA, pathKernel_map_coord]
  exact theorem_3_4_2 P hmn x hA

/-! ### The Markov property -/

/-- **The Markov property as an identity of measures.** For `G ∈ 𝓕ₙ^Φ`, the law of the shifted
path `θⁿΦ` restricted to `G` is the mixture of the `P_y` over the law of `Φₙ` restricted to
`G`. -/
theorem markov_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) :
    ((pathMeasure P μ).restrict G).map (shift n) =
      pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isMarkovKernel_pathKernel P
  have hGm : MeasurableSet G := (natFilt (X := X)).le n _ hG
  have hn : Measurable fun ω : ℕ → X => ω n := measurable_pi_apply n
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨m, A, hA, rfl⟩
    have hB := measurableSet_boxSet m hA
    rw [Measure.map_apply (measurable_shift n) hB, Measure.restrict_apply
      (measurable_shift n hB), Measure.bind_apply hB (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hB) hn, inter_comm]
    simp_rw [pathKernel_boxSet P _ m hA]
    exact measure_inter_shift_box P μ m hA hG
  · rw [Measure.map_apply (measurable_shift n) MeasurableSet.univ,
      Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp [Measure.map_apply hn MeasurableSet.univ]

/-- **The Markov property** for nonnegative functionals: for `G ∈ 𝓕ₙ^Φ` and measurable
`H ≥ 0`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_lintegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  rw [← lintegral_map hH (measurable_shift n), markov_measure P μ hG,
    Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable,
    lintegral_map hH.lintegral_kernel (measurable_pi_apply n)]

/-- **The Markov property** with an `𝓕ₙ^Φ`-measurable weight: for `F ≥ 0` measurable for
`𝓕ₙ^Φ` and measurable `H ≥ 0`, `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]`. -/
theorem markov_lintegral_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {F : (ℕ → X) → ℝ≥0∞} (hF : Measurable[natFilt n] F)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, F ω * H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hle := (natFilt (X := X)).le n
  have hG : Measurable fun ω => H (shift n ω) := hH.comp (measurable_shift n)
  have hK : Measurable fun ω : ℕ → X => ∫⁻ ω', H ω' ∂pathKernel P (ω n) :=
    hH.lintegral_kernel.comp (measurable_pi_apply n)
  refine Measurable.ennreal_induction (motive := fun F => ∫⁻ ω, F ω * H (shift n ω)
      ∂pathMeasure P μ = ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ)
    ?_ ?_ ?_ hF
  · intro c s hs
    have hs' : MeasurableSet s := hle _ hs
    have e1 : ∀ ω, s.indicator (fun _ => c) ω * H (shift n ω) =
        s.indicator (fun ω => c * H (shift n ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∀ ω, s.indicator (fun _ => c) ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) =
        s.indicator (fun ω => c * ∫⁻ ω', H ω' ∂pathKernel P (ω n)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    simp_rw [e1, e2, lintegral_indicator hs', lintegral_const_mul _ hG,
      lintegral_const_mul _ hK, markov_lintegral P μ hs hH]
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * H (shift n ω)) ((hf.mono hle le_rfl).mul hG),
      lintegral_add_left (f := fun ω => f ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        ((hf.mono hle le_rfl).mul hK), ihf, ihg]
  · intro f hf hmono ih
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun k ω => f k ω * H (shift n ω))
        (fun k => ((hf k).mono hle le_rfl).mul hG)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _),
      lintegral_iSup (f := fun k ω => f k ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        (fun k => ((hf k).mono hle le_rfl).mul hK)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _)]
    simp_rw [ih]

/-- The unconditional form: `E_μ[H ∘ θⁿ] = E_μ[E_{Φₙ}[H]]`. -/
theorem markov_lintegral_univ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  simpa using markov_lintegral P μ (n := n) MeasurableSet.univ hH

/-- **The Markov property** for integrable functionals: for `G ∈ 𝓕ₙ^Φ` and measurable `H` with
`H ∘ θⁿ` integrable on `G`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_setIntegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : IntegrableOn (fun ω => H (shift n ω)) G (pathMeasure P μ)) :
    ∫ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hmeas := markov_measure P μ hG
  have hi : Integrable H (((pathMeasure P μ).restrict G).map (shift n)) :=
    (integrable_map_measure hH.aestronglyMeasurable (measurable_shift n).aemeasurable).2 hint
  rw [hmeas] at hi
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  calc ∫ ω in G, H (shift n ω) ∂pathMeasure P μ
      = ∫ ω', H ω' ∂(((pathMeasure P μ).restrict G).map (shift n)) :=
        (integral_map (measurable_shift n).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ ω', H ω' ∂(pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n)) := by
        rw [hmeas]
    _ = ∫ y, ∫ ω', H ω' ∂pathKernel P y ∂(((pathMeasure P μ).restrict G).map fun ω => ω n) :=
        integral_measure_comp _ _ hi
    _ = ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        integral_map (measurable_pi_apply n).aemeasurable hk.aestronglyMeasurable

/-- `ω ↦ E_{Φₙ(ω)}[H]` is `𝓕ₙ^Φ`-strongly measurable. -/
theorem stronglyMeasurable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (n : ℕ)
    {H : (ℕ → X) → ℝ} (hH : Measurable H) :
    StronglyMeasurable[natFilt n] fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isMarkovKernel_pathKernel P
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  exact hk.comp_measurable (measurable_coord_natFilt n)

/-- `ω ↦ E_{Φₙ(ω)}[H]` is integrable when `H ∘ θⁿ` is. -/
theorem integrable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    Integrable (fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n)) (pathMeasure P μ) := by
  refine ⟨((stronglyMeasurable_expect_coord P n hH).mono
    ((natFilt (X := X)).le n)).aestronglyMeasurable, ?_⟩
  have hlin := markov_lintegral_univ P μ n (H := fun ω => ‖H ω‖ₑ) hH.enorm
  calc ∫⁻ ω, ‖∫ ω', H ω' ∂pathKernel P (ω n)‖ₑ ∂pathMeasure P μ
      ≤ ∫⁻ ω, ∫⁻ ω', ‖H ω'‖ₑ ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖H (shift n ω)‖ₑ ∂pathMeasure P μ := hlin.symm
    _ < ∞ := hint.2

/-- **The Markov property** (3.28), MT p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for
measurable `H` with `θⁿH` integrable. -/
theorem markov_property (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hg := integrable_expect_coord P μ n hH hint
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((natFilt (X := X)).le n) hint
    (fun s _ _ => hg.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_expect_coord P n hH).aestronglyMeasurable).symm
  exact (markov_setIntegral P μ hs hH hint.integrableOn).symm

/-- `H ∘ θⁿ` is integrable for bounded measurable `H`. -/
theorem integrable_shift_of_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  exact Integrable.of_bound (hH.comp (measurable_shift n)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)

/-- (3.28) for bounded measurable `H`, as stated in MT p. 63. -/
theorem markov_property_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) :=
  markov_property P μ n hH (integrable_shift_of_bdd P μ n hH hB)

/-- **Proposition 3.4.3** (MT p. 63), (3.27): for bounded measurable `h` on path space,
`E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]`, `P_μ`-a.s. -/
theorem proposition_3_4_3 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {h : (ℕ → X) → ℝ} (hh : Measurable h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    (pathMeasure P μ)[fun ω => h (shift (n + 1) ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', h (shift 1 ω') ∂pathKernel P (ω n) := by
  have := markov_property_bdd P μ n (hh.comp (measurable_shift 1)) (fun ω => hB (shift 1 ω))
  simp only [Function.comp_apply, shift_shift] at this
  exact this

/-! ### Markov chains from the one-step property; skeletons -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] in
/-- A process `Ψ` adapted to a filtration `𝓖`, with `Ψ₀ ∼ μ` and one-step conditional laws given
by `Q` (`∫_G f(Ψₙ₊₁) = ∫_G Qf(Ψₙ)` for `G ∈ 𝓖ₙ`), is a Markov chain with kernel `Q` and initial
distribution `μ`. -/
theorem isMarkovChain_of_step (Q : Kernel X X) (μ : Measure X) {pr : Measure Ω}
    {Ψ : ℕ → Ω → X} {𝓖 : Filtration ℕ mΩ} (hΨ : ∀ n, Measurable[𝓖 n] (Ψ n))
    (h0 : pr.map (Ψ 0) = μ)
    (hstep : ∀ n G, MeasurableSet[𝓖 n] G → ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ ω in G, f (Ψ (n + 1) ω) ∂pr = ∫⁻ ω in G, ∫⁻ y, f y ∂Q (Ψ n ω) ∂pr) :
    IsMarkovChain Q μ pr Ψ := by
  have hΨm : ∀ n, Measurable (Ψ n) := fun n => (hΨ n).mono (𝓖.le n) le_rfl
  have key : ∀ m (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) → ∀ n G, MeasurableSet[𝓖 n] G →
      pr (G ∩ {ω | ∀ i ≤ m, Ψ (n + i) ω ∈ A i}) = ∫⁻ ω in G, cylFn Q m A (Ψ n ω) ∂pr := by
    intro m
    induction m with
    | zero =>
      intro A hA n G hG
      have hset : {ω | ∀ i ≤ 0, Ψ (n + i) ω ∈ A i} = Ψ n ⁻¹' A 0 := by ext ω; simp
      have hm : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q 0 A (Ψ n ω)) = (Ψ n ⁻¹' A 0).indicator 1 := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h]
      rw [hset, hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]
    | succ m ih =>
      intro A hA n G hG
      set A' : ℕ → Set X := fun i => A (i + 1)
      have hA' : ∀ i, MeasurableSet (A' i) := fun i => hA (i + 1)
      have hG' : MeasurableSet[𝓖 n] (G ∩ Ψ n ⁻¹' A 0) := hG.inter (hΨ n (hA 0))
      have hset : G ∩ {ω | ∀ i ≤ m + 1, Ψ (n + i) ω ∈ A i} =
          (G ∩ Ψ n ⁻¹' A 0) ∩ {ω | ∀ i ≤ m, Ψ (n + 1 + i) ω ∈ A' i} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, A']
        constructor
        · rintro ⟨hg, h⟩
          refine ⟨⟨hg, by simpa using h 0 (Nat.zero_le _)⟩, fun i hi => ?_⟩
          have := h (i + 1) (by omega)
          rwa [show n + (i + 1) = n + 1 + i by omega] at this
        · rintro ⟨⟨hg, h0⟩, h⟩
          refine ⟨hg, fun i hi => ?_⟩
          rcases i with _ | i
          · simpa using h0
          · have := h i (by omega)
            rwa [show n + 1 + i = n + (i + 1) by omega] at this
      have hmeas := measurable_cylFn Q m hA'
      rw [hset, ih A' hA' (n + 1) _ (𝓖.mono (Nat.le_succ n) _ hG'),
        hstep n _ hG' _ hmeas]
      have hmn : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q (m + 1) A (Ψ n ω)) =
          (Ψ n ⁻¹' A 0).indicator (fun ω => ∫⁻ y, cylFn Q m A' y ∂Q (Ψ n ω)) := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h, A']
      rw [hind, setLIntegral_indicator hmn, inter_comm]
  refine ⟨hΨm, fun n A hA => ?_⟩
  have := key n A hA 0 univ MeasurableSet.univ
  simp only [univ_inter, zero_add, Measure.restrict_univ] at this
  rw [this, ← lintegral_map (measurable_cylFn Q n hA) (hΨm 0), h0]

/-- The filtration `(𝓕_{mn}^Φ)ₙ` along the `m`-skeleton. -/
def skeletonFilt (m : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) where
  seq n := natFilt (X := X) (m * n)
  mono' _ _ hij := (natFilt (X := X)).mono (Nat.mul_le_mul_left m hij)
  le' n := (natFilt (X := X)).le (m * n)

/-- (3.25), MT p. 61: the `m`-skeleton `(Φ_{mn})ₙ` of the chain is a Markov chain with
transition kernel `Pᵐ`, under every `P_μ`. In particular `P_x(Φ_{mn} ∈ A) = Pᵐⁿ(x, A)`
(`pathKernel_coord_mem`). -/
theorem skeleton_isMarkovChain (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) :
    IsMarkovChain (skeleton P m) μ (pathMeasure P μ) (fun n ω => ω (m * n)) := by
  refine isMarkovChain_of_step (𝓖 := skeletonFilt m) _ μ
    (fun n => measurable_coord_natFilt (m * n)) (by simpa using pathMeasure_map_zero P μ)
    fun n G hG f hf => ?_
  have hH : Measurable fun ω : ℕ → X => f (ω m) := hf.comp (measurable_pi_apply m)
  have h := markov_lintegral P μ (n := m * n) hG hH
  simp only [shift_apply] at h
  rw [show m * (n + 1) = m * n + m by ring, h]
  refine setLIntegral_congr_fun ((skeletonFilt m).le n _ hG) fun ω _ => ?_
  rw [← lintegral_map hf (measurable_pi_apply m), pathKernel_map_coord]

end MeynTweedie.Ergodicity
