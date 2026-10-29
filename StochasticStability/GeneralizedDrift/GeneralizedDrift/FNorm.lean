/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.TotalVariation

/-!
# The `f`-norm (MT Chapter 14, p. 336)

Meyn and Tweedie, Chapter 14 introduction, p. 336. For a measurable `f : X → [0, ∞]` and two
measures `μ`, `ν` the `f`-norm of the signed measure `μ − ν` is

  `‖μ − ν‖_f = sup_{|g| ≤ f} |μ(g) − ν(g)|`,

the supremum over measurable `g : X → ℝ` with `|g| ≤ f` that are integrable for both measures.
It is valued in `[0, ∞]` (`fNorm f μ ν`), so that no finiteness of `μ(f)` or `ν(f)` is needed to
state it; it is finite when `μ(f)` and `ν(f)` are (`fNorm_le_add`). The total variation norm of
Chapter 13 is the case `f ≡ 1` (`fNorm_one`).

**Basic properties.**
* `IsFTest f μ ν g`: the admissible test functions; `integrable_of_ofReal_abs_le` (a measurable
  `g` with `|g| ≤ f` is integrable when `μ(f) < ∞`).
* `ofReal_abs_integral_sub_le_fNorm` (the defining bound), `fNorm_le` (a bound on all test
  functions bounds the norm), `fNorm_comm`, `fNorm_self`, `fNorm_mono` (monotone in `f`),
  `fNorm_triangle` (when the middle measure has `ν(f) < ∞`), `fNorm_le_add`
  (`‖μ − ν‖_f ≤ μ(f) + ν(f)`).
* `fNorm_le_of_add_eq`: if `μ + σ₂ = ν + σ₁` then `‖μ − ν‖_f ≤ σ₁(f) + σ₂(f)`; the regenerative
  decompositions are turned into `f`-norm bounds through it.
* `fNorm_one`: `‖μ − ν‖_1 = ‖μ − ν‖` for finite measures, and `ofReal_tvNorm_le_fNorm`: for
  `f ≥ 1` the `f`-norm dominates the total variation norm.

**Transport.**
* `fNorm_map_le`: `‖μg⁻¹ − νg⁻¹‖_f ≤ ‖μ − ν‖_{f ∘ g}` (for the marginal of the split chain).
* `integral_comp_kernel_of_integrable`: `(μQ)(g) = μ(Qg)` for `g` integrable for `μQ`.
* `fNorm_comp_le`: `‖μQ − νQ‖_f ≤ ‖μ − ν‖_{Qf}` for a transition kernel `Q` (used in
  Lemma 14.3.2: `|Pⁱg| ≤ Pⁱf` when `|g| ≤ f`).
* `fNorm_comp_le_lintegral`: `‖λQ − μQ‖_f ≤ ∫ λ(dx) ∫ μ(dy) ‖Q(x, ·) − Q(y, ·)‖_f` for
  probabilities `λ`, `μ` (used in Theorems 14.3.4 and 14.3.5).

**Convergence.** `tendsto_integral_of_tendsto_fNorm` (p. 337): `‖μₙ − ν‖_f → 0` gives
`μₙ(g) → ν(g)` for every measurable `|g| ≤ f`.

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The definition -/

/-- The test functions of the `f`-norm: measurable `g : X → ℝ` with `|g| ≤ f`, integrable for
both `μ` and `ν`. -/
def IsFTest (f : X → ℝ≥0∞) (μ ν : Measure X) (g : X → ℝ) : Prop :=
  Measurable g ∧ (∀ x, ENNReal.ofReal |g x| ≤ f x) ∧ Integrable g μ ∧ Integrable g ν

/-- The **`f`-norm** `‖μ − ν‖_f = sup_{|g| ≤ f} |μ(g) − ν(g)|` (MT p. 336), valued in `[0, ∞]`. -/
noncomputable def fNorm (f : X → ℝ≥0∞) (μ ν : Measure X) : ℝ≥0∞ :=
  ⨆ (g : X → ℝ) (_ : IsFTest f μ ν g), ENNReal.ofReal |∫ x, g x ∂μ - ∫ x, g x ∂ν|

omit [MeasurableSpace X] in
/-- `‖g‖ₑ ≤ f` in the form used by the definition. -/
theorem enorm_le_of_ofReal_abs_le {f : X → ℝ≥0∞} {g : X → ℝ}
    (hg : ∀ x, ENNReal.ofReal |g x| ≤ f x) (x : X) : ‖g x‖ₑ ≤ f x := by
  rw [Real.enorm_eq_ofReal_abs]; exact hg x

/-- A measurable `g` with `|g| ≤ f` is integrable when `μ(f) < ∞`. -/
theorem integrable_of_ofReal_abs_le {μ : Measure X} {f : X → ℝ≥0∞} {g : X → ℝ}
    (hgm : Measurable g) (hg : ∀ x, ENNReal.ofReal |g x| ≤ f x) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    Integrable g μ :=
  ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono (enorm_le_of_ofReal_abs_le hg))
    (lt_top_iff_ne_top.2 hf)⟩

/-- `‖μ(g)‖ₑ ≤ μ(f)` for `|g| ≤ f`. -/
theorem enorm_integral_le_lintegral {μ : Measure X} {f : X → ℝ≥0∞} {g : X → ℝ}
    (hg : ∀ x, ENNReal.ofReal |g x| ≤ f x) : ‖∫ x, g x ∂μ‖ₑ ≤ ∫⁻ x, f x ∂μ :=
  (enorm_integral_le_lintegral_enorm g).trans (lintegral_mono (enorm_le_of_ofReal_abs_le hg))

/-- `|μ(g)| ≤ μ(f)` for `|g| ≤ f`, in `[0, ∞]`. -/
theorem ofReal_abs_integral_le_lintegral {μ : Measure X} {f : X → ℝ≥0∞} {g : X → ℝ}
    (hg : ∀ x, ENNReal.ofReal |g x| ≤ f x) : ENNReal.ofReal |∫ x, g x ∂μ| ≤ ∫⁻ x, f x ∂μ := by
  rw [← Real.enorm_eq_ofReal_abs]; exact enorm_integral_le_lintegral hg

/-- The defining bound: `|μ(g) − ν(g)| ≤ ‖μ − ν‖_f` for every test function `g`. -/
theorem ofReal_abs_integral_sub_le_fNorm {f : X → ℝ≥0∞} {μ ν : Measure X} {g : X → ℝ}
    (hg : IsFTest f μ ν g) :
    ENNReal.ofReal |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ fNorm f μ ν :=
  le_iSup₂ (f := fun g (_ : IsFTest f μ ν g) => ENNReal.ofReal |∫ x, g x ∂μ - ∫ x, g x ∂ν|) g hg

/-- A bound valid for every test function bounds the `f`-norm. -/
theorem fNorm_le {f : X → ℝ≥0∞} {μ ν : Measure X} {c : ℝ≥0∞}
    (h : ∀ g, IsFTest f μ ν g → ENNReal.ofReal |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ c) :
    fNorm f μ ν ≤ c :=
  iSup₂_le h

/-- `‖μ − ν‖_f = ‖ν − μ‖_f`. -/
theorem fNorm_comm (f : X → ℝ≥0∞) (μ ν : Measure X) : fNorm f μ ν = fNorm f ν μ := by
  refine le_antisymm (fNorm_le fun g hg => ?_) (fNorm_le fun g hg => ?_)
  · rw [abs_sub_comm]
    exact ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hg.2.2.2, hg.2.2.1⟩
  · rw [abs_sub_comm]
    exact ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hg.2.2.2, hg.2.2.1⟩

/-- `‖μ − μ‖_f = 0`. -/
theorem fNorm_self (f : X → ℝ≥0∞) (μ : Measure X) : fNorm f μ μ = 0 :=
  le_antisymm (fNorm_le fun g _ => by simp) zero_le

/-- The `f`-norm is monotone in `f`. -/
theorem fNorm_mono {f f' : X → ℝ≥0∞} (hff' : f ≤ f') (μ ν : Measure X) :
    fNorm f μ ν ≤ fNorm f' μ ν :=
  fNorm_le fun _ hg => ofReal_abs_integral_sub_le_fNorm
    ⟨hg.1, fun x => (hg.2.1 x).trans (hff' x), hg.2.2.1, hg.2.2.2⟩

/-- `|a − b| ≤ |a| + |b|` in `[0, ∞]`. -/
theorem ofReal_abs_sub_le (a b : ℝ) :
    ENNReal.ofReal |a - b| ≤ ENNReal.ofReal |a| + ENNReal.ofReal |b| := by
  rw [← ENNReal.ofReal_add (abs_nonneg a) (abs_nonneg b)]
  exact ENNReal.ofReal_le_ofReal (abs_sub a b)

/-- **`f`-norm bounds from decompositions.** If `μ + σ₂ = ν + σ₁` then
`‖μ − ν‖_f ≤ σ₁(f) + σ₂(f)`. -/
theorem fNorm_le_of_add_eq {f : X → ℝ≥0∞} {μ ν σ₁ σ₂ : Measure X} (heq : μ + σ₂ = ν + σ₁) :
    fNorm f μ ν ≤ ∫⁻ x, f x ∂σ₁ + ∫⁻ x, f x ∂σ₂ := by
  refine fNorm_le fun g hg => ?_
  by_cases h1 : ∫⁻ x, f x ∂σ₁ = ∞
  · rw [h1, top_add]; exact le_top
  by_cases h2 : ∫⁻ x, f x ∂σ₂ = ∞
  · rw [h2, add_top]; exact le_top
  have hi1 := integrable_of_ofReal_abs_le hg.1 hg.2.1 h1
  have hi2 := integrable_of_ofReal_abs_le hg.1 hg.2.1 h2
  have hsum : ∫ x, g x ∂μ + ∫ x, g x ∂σ₂ = ∫ x, g x ∂ν + ∫ x, g x ∂σ₁ := by
    rw [← integral_add_measure hg.2.2.1 hi2, ← integral_add_measure hg.2.2.2 hi1, heq]
  have e : ∫ x, g x ∂μ - ∫ x, g x ∂ν = ∫ x, g x ∂σ₁ - ∫ x, g x ∂σ₂ := by linarith
  rw [e]
  exact (ofReal_abs_sub_le _ _).trans (add_le_add (ofReal_abs_integral_le_lintegral hg.2.1)
    (ofReal_abs_integral_le_lintegral hg.2.1))

/-- `‖μ − ν‖_f ≤ μ(f) + ν(f)`. -/
theorem fNorm_le_add (f : X → ℝ≥0∞) (μ ν : Measure X) :
    fNorm f μ ν ≤ ∫⁻ x, f x ∂μ + ∫⁻ x, f x ∂ν :=
  fNorm_le_of_add_eq (σ₁ := μ) (σ₂ := ν) (add_comm μ ν)

/-- The triangle inequality, when the middle measure has `ν(f) < ∞`. -/
theorem fNorm_triangle {f : X → ℝ≥0∞} (μ ν ρ : Measure X) (hν : ∫⁻ x, f x ∂ν ≠ ∞) :
    fNorm f μ ρ ≤ fNorm f μ ν + fNorm f ν ρ := by
  refine fNorm_le fun g hg => ?_
  have hi := integrable_of_ofReal_abs_le hg.1 hg.2.1 hν
  have e : ∫ x, g x ∂μ - ∫ x, g x ∂ρ =
      (∫ x, g x ∂μ - ∫ x, g x ∂ν) + (∫ x, g x ∂ν - ∫ x, g x ∂ρ) := by ring
  rw [e]
  refine (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact add_le_add (ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hg.2.2.1, hi⟩)
    (ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hi, hg.2.2.2⟩)

/-! ### The total variation norm is the `1`-norm -/

/-- **`‖μ − ν‖_1 = ‖μ − ν‖`** (MT p. 336): for finite measures the `f`-norm with `f ≡ 1` is the
total variation norm of Chapter 13. -/
theorem fNorm_one (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fNorm 1 μ ν = ENNReal.ofReal (tvNorm μ ν) := by
  have hfin : ∫⁻ x, (1 : X → ℝ≥0∞) x ∂μ + ∫⁻ x, (1 : X → ℝ≥0∞) x ∂ν ≠ ∞ := by
    simp only [Pi.one_apply, lintegral_one]
    exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  refine le_antisymm (fNorm_le fun g hg => ENNReal.ofReal_le_ofReal ?_) ?_
  · refine abs_integral_sub_le_tvNorm μ ν hg.1 fun x => ?_
    have := hg.2.1 x
    rw [Pi.one_apply, ← ENNReal.ofReal_one] at this
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 this
  · rw [ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hfin (fNorm_le_add 1 μ ν))]
    refine tvNorm_le fun g hg h1 => ?_
    have hle : ∀ x, ENNReal.ofReal |g x| ≤ (1 : X → ℝ≥0∞) x := fun x => by
      rw [Pi.one_apply, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (h1 x)
    have h := ofReal_abs_integral_sub_le_fNorm (f := 1)
      ⟨hg, hle, integrable_of_abs_le_one (μ := μ) hg h1, integrable_of_abs_le_one (μ := ν) hg h1⟩
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin (fNorm_le_add 1 μ ν))] at h
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h

/-- For `f ≥ 1` the `f`-norm dominates the total variation norm. -/
theorem ofReal_tvNorm_le_fNorm {f : X → ℝ≥0∞} (hf : ∀ x, 1 ≤ f x) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ENNReal.ofReal (tvNorm μ ν) ≤ fNorm f μ ν := by
  rw [← fNorm_one]; exact fNorm_mono hf μ ν

/-! ### Transport by maps and kernels -/

/-- `‖μg⁻¹ − νg⁻¹‖_f ≤ ‖μ − ν‖_{f ∘ g}` for a measurable map `g`. -/
theorem fNorm_map_le {Y : Type*} [MeasurableSpace Y] {φ : Y → X} (hφ : Measurable φ)
    (f : X → ℝ≥0∞) (μ ν : Measure Y) :
    fNorm f (μ.map φ) (ν.map φ) ≤ fNorm (f ∘ φ) μ ν := by
  refine fNorm_le fun g hg => ?_
  rw [integral_map hφ.aemeasurable hg.1.aestronglyMeasurable,
    integral_map hφ.aemeasurable hg.1.aestronglyMeasurable]
  exact ofReal_abs_integral_sub_le_fNorm ⟨hg.1.comp hφ, fun y => hg.2.1 (φ y),
    (integrable_map_measure hg.1.aestronglyMeasurable hφ.aemeasurable).1 hg.2.2.1,
    (integrable_map_measure hg.1.aestronglyMeasurable hφ.aemeasurable).1 hg.2.2.2⟩

/-- `(μQ)(g) = μ(Qg)` for a Markov kernel `Q` and `g` integrable for `μQ`. -/
theorem integral_comp_kernel_of_integrable {Y : Type*} [MeasurableSpace Y] (Q : Kernel X Y)
    [IsMarkovKernel Q] (μ : Measure X) [SFinite μ] {g : Y → ℝ} (hg : Measurable g)
    (hi : Integrable g (Q ∘ₘ μ)) :
    ∫ y, g y ∂(Q ∘ₘ μ) = ∫ x, (∫ y, g y ∂Q x) ∂μ := by
  have hi' : Integrable (fun z : X × Y => g z.2) (μ ⊗ₘ Q) := by
    rw [← Measure.snd_compProd μ Q, Measure.snd] at hi
    exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).1 hi
  rw [← Measure.snd_compProd μ Q, Measure.snd,
    integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    Measure.integral_compProd (f := fun z : X × Y => g z.2) hi']

/-- `∫ μ(dx) ∫ Q(x, dy) h(y) = ∫ h d(μQ)` for nonnegative measurable `h`. -/
theorem lintegral_comp_kernel {Y : Type*} [MeasurableSpace Y] (Q : Kernel X Y) (μ : Measure X)
    {h : Y → ℝ≥0∞} (hh : Measurable h) : ∫⁻ x, ∫⁻ y, h y ∂Q x ∂μ = ∫⁻ y, h y ∂(Q ∘ₘ μ) :=
  (Measure.lintegral_bind Q.aemeasurable hh.aemeasurable).symm

/-- `x ↦ Q g(x)` is a test function for `(μ, ν)` with the bound `Qf`, when `g` is a test function
for `(μQ, νQ)`. -/
theorem isFTest_comp {Y : Type*} [MeasurableSpace Y] (Q : Kernel X Y) [IsMarkovKernel Q]
    {f : Y → ℝ≥0∞} {μ ν : Measure X} {g : Y → ℝ} (hg : IsFTest f (Q ∘ₘ μ) (Q ∘ₘ ν) g) :
    IsFTest (fun x => ∫⁻ y, f y ∂Q x) μ ν (fun x => ∫ y, g y ∂Q x) := by
  have hm : Measurable fun x => ∫ y, g y ∂Q x :=
    (StronglyMeasurable.integral_kernel (κ := Q) hg.1.stronglyMeasurable).measurable
  have hle : ∀ x, ‖∫ y, g y ∂Q x‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ ∂Q x := fun x =>
    enorm_integral_le_lintegral_enorm g
  have hgm : Measurable fun y => ‖g y‖ₑ := hg.1.enorm
  refine ⟨hm, fun x => ?_, ⟨hm.aestronglyMeasurable, ?_⟩, ⟨hm.aestronglyMeasurable, ?_⟩⟩
  · rw [← Real.enorm_eq_ofReal_abs]
    exact (hle x).trans (lintegral_mono (enorm_le_of_ofReal_abs_le hg.2.1))
  · calc ∫⁻ x, ‖∫ y, g y ∂Q x‖ₑ ∂μ ≤ ∫⁻ x, ∫⁻ y, ‖g y‖ₑ ∂Q x ∂μ := lintegral_mono hle
      _ = ∫⁻ y, ‖g y‖ₑ ∂(Q ∘ₘ μ) := lintegral_comp_kernel Q μ hgm
      _ < ∞ := hg.2.2.1.2
  · calc ∫⁻ x, ‖∫ y, g y ∂Q x‖ₑ ∂ν ≤ ∫⁻ x, ∫⁻ y, ‖g y‖ₑ ∂Q x ∂ν := lintegral_mono hle
      _ = ∫⁻ y, ‖g y‖ₑ ∂(Q ∘ₘ ν) := lintegral_comp_kernel Q ν hgm
      _ < ∞ := hg.2.2.2.2

/-- **Transport by a kernel**: `‖μQ − νQ‖_f ≤ ‖μ − ν‖_{Qf}` for a Markov kernel `Q`. -/
theorem fNorm_comp_le {Y : Type*} [MeasurableSpace Y] (Q : Kernel X Y) [IsMarkovKernel Q]
    (f : Y → ℝ≥0∞) (μ ν : Measure X) [SFinite μ] [SFinite ν] :
    fNorm f (Q ∘ₘ μ) (Q ∘ₘ ν) ≤ fNorm (fun x => ∫⁻ y, f y ∂Q x) μ ν := by
  refine fNorm_le fun g hg => ?_
  rw [integral_comp_kernel_of_integrable Q μ hg.1 hg.2.2.1,
    integral_comp_kernel_of_integrable Q ν hg.1 hg.2.2.2]
  exact ofReal_abs_integral_sub_le_fNorm (isFTest_comp Q hg)

/-- `∫ λ(dx) ∫ μ(dy) (a(x) − b(y)) = λ(a) − μ(b)` for probabilities `λ`, `μ`. -/
theorem integral_integral_sub {Y : Type*} [MeasurableSpace Y] (l : Measure X) (m : Measure Y)
    [IsProbabilityMeasure l] [IsProbabilityMeasure m] {a : X → ℝ} {b : Y → ℝ}
    (ha : Integrable a l) (hb : Integrable b m) :
    ∫ x, ∫ y, (a x - b y) ∂m ∂l = ∫ x, a x ∂l - ∫ y, b y ∂m := by
  have h1 : ∀ x, ∫ y, (a x - b y) ∂m = a x - ∫ y, b y ∂m := fun x => by
    rw [integral_sub (integrable_const _) hb, integral_const, smul_eq_mul, probReal_univ,
      one_mul]
  simp_rw [h1]
  rw [integral_sub ha (integrable_const _), integral_const, smul_eq_mul, probReal_univ,
    one_mul]

/-- **Convexity of the `f`-norm**: for a Markov kernel `Q` and probabilities `λ`, `μ`,
`‖λQ − μQ‖_f ≤ ∫ λ(dx) ∫ μ(dy) ‖Q(x, ·) − Q(y, ·)‖_f`. -/
theorem fNorm_comp_le_lintegral {Y : Type*} [MeasurableSpace Y] (Q : Kernel X Y)
    [IsMarkovKernel Q] (f : Y → ℝ≥0∞) (l m : Measure X) [IsProbabilityMeasure l]
    [IsProbabilityMeasure m] :
    fNorm f (Q ∘ₘ l) (Q ∘ₘ m) ≤ ∫⁻ x, ∫⁻ y, fNorm f (Q x) (Q y) ∂m ∂l := by
  refine fNorm_le fun g hg => ?_
  have ht := isFTest_comp Q hg
  set h := fun x => ∫ y, g y ∂Q x with hh
  rw [integral_comp_kernel_of_integrable Q l hg.1 hg.2.2.1,
    integral_comp_kernel_of_integrable Q m hg.1 hg.2.2.2,
    ← integral_integral_sub l m ht.2.2.1 ht.2.2.2, ← Real.enorm_eq_ofReal_abs]
  have hgm : Measurable fun y => ‖g y‖ₑ := hg.1.enorm
  -- `g` is integrable for `Q(x, ·)` for almost every `x`
  have hae : ∀ ρ : Measure X, ∫⁻ y, ‖g y‖ₑ ∂(Q ∘ₘ ρ) < ∞ →
      ∀ᵐ x ∂ρ, Integrable g (Q x) := fun ρ hρ => by
    rw [← lintegral_comp_kernel Q ρ hgm] at hρ
    filter_upwards [ae_lt_top (hgm.lintegral_kernel) hρ.ne] with x hx
    exact ⟨hg.1.aestronglyMeasurable, hx⟩
  have hl := hae l hg.2.2.1.2
  have hm := hae m hg.2.2.2.2
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hl] with x hx
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hm] with y hy
  rw [Real.enorm_eq_ofReal_abs]
  exact ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hx, hy⟩

/-! ### Convergence -/

/-- The remark on p. 337: `‖μₙ − ν‖_f → 0` gives `μₙ(g) → ν(g)` for every measurable `g` with
`|g| ≤ f`, when `μₙ(f)` and `ν(f)` are finite. -/
theorem tendsto_integral_of_tendsto_fNorm {f : X → ℝ≥0∞} {μs : ℕ → Measure X} {ν : Measure X}
    (h : Tendsto (fun n => fNorm f (μs n) ν) atTop (𝓝 0))
    (hμ : ∀ n, ∫⁻ x, f x ∂μs n ≠ ∞) (hν : ∫⁻ x, f x ∂ν ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal |g x| ≤ f x) :
    Tendsto (fun n => ∫ x, g x ∂μs n) atTop (𝓝 (∫ x, g x ∂ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ n, ENNReal.ofReal ‖∫ x, g x ∂μs n - ∫ x, g x ∂ν‖ ≤ fNorm f (μs n) ν := fun n =>
    ofReal_abs_integral_sub_le_fNorm ⟨hgm, hg, integrable_of_ofReal_abs_le hgm hg (hμ n),
      integrable_of_ofReal_abs_le hgm hg hν⟩
  have h' : Tendsto (fun n => ENNReal.ofReal ‖∫ x, g x ∂μs n - ∫ x, g x ∂ν‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hle
  have h'' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h'
  simp only [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_zero] at h''
  exact h''

end MeynTweedie.GeneralizedDrift
