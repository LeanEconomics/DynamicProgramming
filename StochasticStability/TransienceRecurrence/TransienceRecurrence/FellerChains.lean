/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransienceRecurrence.PetiteSets
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Support

/-!
# Feller chains (MT §6.1)

Meyn and Tweedie, §6.0–6.1, pp. 123–129. `X` carries a topology and a σ-algebra containing the
open sets (`OpensMeasurableSpace`); each result states the extra topological hypotheses it
uses (first countability, pseudo-metrizability). The book's standing assumption, a locally
compact separable metric space, implies all of them.

**Definitions (p. 124 and p. 125).**
* `IsWeakFeller P`: `P(·, O)` is lower semicontinuous for every open `O` (p. 124, (i)).
* `IsStrongFeller P`: `P` maps bounded measurable functions to continuous functions (p. 125).

**Lower semicontinuity of integrals.**
* `lintegral_ofReal_le_liminf`, `lintegral_le_liminf_of_lsc`: Fatou's lemma for a sequence of
  measures with `μ(G) ≤ liminf μₙ(G)` on open sets and a lower semicontinuous integrand (the
  layer-cake argument of Mathlib's portmanteau theorem, for semicontinuous integrands).
* `IsWeakFeller.lowerSemicontinuous_lintegral`: for a weak Feller chain on a first-countable
  space, `x ↦ ∫ f(y) P(x, dy)` is lower semicontinuous for every lower semicontinuous
  `f ≥ 0`. This is the form of Theorem D.4.1 that the chapter uses.
* `IsWeakFeller.pow`, `IsWeakFeller.lsc_sampledKernel`, `IsWeakFeller.isWeakFeller_sampledKernel`:
  `Pⁿ` and `K_a` are weak Feller; `usc_of_lsc_compl`, `IsWeakFeller.usc_pow_closed`,
  `IsWeakFeller.usc_sampledKernel_closed`: `Pⁿ(·, F)` and `K_a(·, F)` are upper semicontinuous
  for closed `F` (used in Lemma 6.2.7).
* Tools: `lowerSemicontinuous_indicator_of_isOpen`, `lowerSemicontinuous_const_mul`,
  `lowerSemicontinuous_of_seq`, `le_liminf_seq_of_lsc`.

**Proposition 6.1.1** (p. 125).
* (i) `proposition_6_1_1_i_weak`: on a pseudo-metrizable space, `P` is weak Feller iff it maps
  `C(X)` into `C(X)`; `proposition_6_1_1_i_strong`: on a first-countable space, `P` is strong
  Feller iff `P(·, A)` is lower semicontinuous for every measurable `A` (via
  `continuous_apply_of_lsc` and the layer-cake bound `continuous_integral_of_nonneg`);
  `IsStrongFeller.isWeakFeller`: strong Feller chains are weak Feller.
* (ii) For a closed set `C`: `tailProb P C n x = Pₓ(τ_C ≥ n)` (with `tailProb_succ`, the
  recursion `Pₓ(τ_C ≥ k + 1) = (P I_{Cᶜ})ᵏ(x, X)`) is lower semicontinuous
  (`proposition_6_1_1_ii_tail`); for nondecreasing `m`, `Eₓ[m(τ_C)]` is lower semicontinuous
  (`proposition_6_1_1_ii`), via the identity `Eₓ[m(τ_C)] = m(0) + Σᵢ Δm(i + 1) Pₓ(τ_C ≥ i + 1)`
  (`expectReturn_eq_tsum`, from the pointwise `extendSup_eq_tsum`); in particular `Eₓ[τ_C]`
  and `Eₓ[r^{τ_C}]` (`proposition_6_1_1_ii_mean`, `proposition_6_1_1_ii_geom`).
* (iii) For an open set `O`: `Pₓ(τ_O ≤ n)` (`hitWithin`, with the first-step equation
  `hitWithin_succ` and `hitProb_eq_iSup_hitWithin`), `K_a(x, O)` and `L(x, O)` are lower
  semicontinuous (`proposition_6_1_1_iii`).

**Reachability and open set irreducibility** (§6.1.2, pp. 128–129).
* `IsReachable P x`, `IsOpenSetIrreducible P` (p. 128). The book's `Σₙ Pⁿ(y, O) > 0` is read as
  `U(y, O) > 0` (`n ≥ 1`), which is what the proof of Lemma 6.1.4 uses.
* **Lemma 6.1.4** (`lemma_6_1_4`, p. 129): for a maximal irreducibility measure `ψ`, `x` is
  reachable iff `x ∈ supp ψ` (Mathlib's `Measure.support`).
* `isOpenSetIrreducible_iff_irreducible` (p. 129): on a countable space with the discrete
  topology, open set irreducibility is irreducibility (all states communicate); countability is
  not needed.
* **Proposition 6.1.5** (`proposition_6_1_5`, p. 129): a strong Feller chain with a reachable
  point `x*` is `P(x*, ·)`-irreducible.
* **Proposition 6.1.6** (`proposition_6_1_6`, p. 129): an open set irreducible strong Feller
  chain is `ψ`-irreducible.

**Corrections.** Lemma 6.1.4 needs `ψ` maximal (as almost everywhere in the book, `ψ` denotes a
maximal irreducibility measure): the zero measure is an irreducibility measure of every chain,
and `lemma_6_1_4_counterexample` exhibits a reachable point outside `supp 0 = ∅`.

**Hypotheses.** In Proposition 6.1.1 (ii) the book takes `m : ℤ₊ → ℤ₊` but then applies it to
`m(n) = rⁿ`; here `m` is any nondecreasing `ℕ → ℝ≥0`, with `m(∞) = sup m`.
-/

namespace MeynTweedie.TransienceRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

variable [TopologicalSpace X] in
/-- `P` is **(weak) Feller** (MT p. 124): `P(·, O)` is lower semicontinuous for every open
`O`. -/
def IsWeakFeller (P : Kernel X X) : Prop :=
  ∀ O : Set X, IsOpen O → LowerSemicontinuous fun x => P x O

variable [TopologicalSpace X] in
/-- `P` is **strong Feller** (MT p. 125): `Pf` is continuous for every bounded measurable
`f`. -/
def IsStrongFeller (P : Kernel X X) : Prop :=
  ∀ f : X → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → Continuous (kfunR P f)

/-! ### Semicontinuity tools -/

/-- The indicator of an open set times a lower semicontinuous function `g ≥ 0` is lower
semicontinuous. -/
theorem lowerSemicontinuous_indicator_of_isOpen {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    (hU : IsOpen U) {g : Y → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (U.indicator g) := by
  intro x c hc
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx] at hc
    filter_upwards [hg x c hc, hU.mem_nhds hx] with z hz hzU
    rwa [indicator_of_mem hzU]
  · rw [indicator_of_notMem hx] at hc
    exact absurd hc (not_lt.2 zero_le)

/-- A constant multiple `c F` of a lower semicontinuous `F : Y → [0, ∞]` is lower
semicontinuous, also for `c = ∞`. -/
theorem lowerSemicontinuous_const_mul {Y : Type*} [TopologicalSpace Y] {F : Y → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (c : ℝ≥0∞) : LowerSemicontinuous fun x => c * F x := by
  by_cases hc : c = ∞
  · subst hc
    intro x a ha
    have hF0 : F x ≠ 0 := fun h => by simp [h] at ha
    filter_upwards [hF x 0 (pos_iff_ne_zero.2 hF0)] with z hz
    rw [ENNReal.top_mul hz.ne']
    exact lt_of_lt_of_le ha le_top
  · exact (ENNReal.continuous_const_mul hc).comp_lowerSemicontinuous hF
      fun a b hab => mul_le_mul_right hab c

/-- The sequential criterion for lower semicontinuity on a first-countable space. -/
theorem lowerSemicontinuous_of_seq {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    {F : Y → ℝ≥0∞}
    (h : ∀ x (z : ℕ → Y), Tendsto z atTop (𝓝 x) → F x ≤ atTop.liminf fun n => F (z n)) :
    LowerSemicontinuous F := by
  intro x c hc
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨z, hz, hzc⟩ := exists_seq_forall_of_frequently hne
  have h2 : (atTop.liminf fun n => F (z n)) ≤ c :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => not_lt.1 (hzc n))
  exact absurd ((h x z hz).trans h2) (not_le.2 hc)

/-- A lower semicontinuous function along a convergent sequence:
`F(x) ≤ liminf F(zₙ)`. -/
theorem le_liminf_seq_of_lsc {Y : Type*} [TopologicalSpace Y] {F : Y → ℝ≥0∞}
    (hF : LowerSemicontinuous F) {x : Y} {z : ℕ → Y} (hz : Tendsto z atTop (𝓝 x)) :
    F x ≤ atTop.liminf fun n => F (z n) := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  exact le_liminf_of_le (by isBoundedDefault) ((hz.eventually (hF x c hc)).mono fun n hn => hn.le)

/-! ### Fatou's lemma for lower semicontinuous integrands -/

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Fatou's lemma along a sequence of measures with `μ(G) ≤ liminf μₙ(G)` for open `G`, for a
lower semicontinuous real integrand `f ≥ 0` (the layer-cake argument). -/
theorem lintegral_ofReal_le_liminf {μ : Measure X} {μs : ℕ → Measure X}
    (h : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun n => μs n G) {f : X → ℝ}
    (hf : LowerSemicontinuous f) (hf0 : 0 ≤ f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂μs n := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hf0) hf.measurable.aemeasurable]
  calc ∫⁻ t in Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ t in Ioi 0, atTop.liminf fun n => μs n {a | t < f a} :=
        lintegral_mono fun t => h _ (hf.isOpen_preimage t)
    _ ≤ atTop.liminf fun n => ∫⁻ t in Ioi 0, μs n {a | t < f a} :=
        lintegral_liminf_le fun n => Antitone.measurable fun s t hst =>
          measure_mono fun ω hω => lt_of_le_of_lt hst hω

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Fatou's lemma along a sequence of measures with `μ(G) ≤ liminf μₙ(G)` for open `G`, for a
lower semicontinuous integrand `f : X → [0, ∞]`. -/
theorem lintegral_le_liminf_of_lsc {μ : Measure X} {μs : ℕ → Measure X}
    (h : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun n => μs n G) {f : X → ℝ≥0∞}
    (hf : LowerSemicontinuous f) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun n => ∫⁻ x, f x ∂μs n := by
  have hsup : ∀ x, f x = ⨆ N : ℕ, min (f x) N := fun x => by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]; simp
  have hmeas : ∀ N : ℕ, Measurable fun x => min (f x) N := fun N =>
    hf.measurable.min measurable_const
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, ⨆ N : ℕ, min (f x) N ∂μ := by simp_rw [← hsup]
    _ = ⨆ N : ℕ, ∫⁻ x, min (f x) N ∂μ := lintegral_iSup hmeas fun N M hNM x =>
        min_le_min le_rfl (by exact_mod_cast hNM)
    _ ≤ _ := iSup_le fun N => by
        have hN : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
        have hg : LowerSemicontinuous fun x => ENNReal.truncateToReal N (f x) :=
          (ENNReal.continuous_truncateToReal hN).comp_lowerSemicontinuous hf
            (ENNReal.monotone_truncateToReal hN)
        have he : ∀ x, ENNReal.ofReal (ENNReal.truncateToReal N (f x)) = min (f x) N := by
          intro x
          rw [ENNReal.truncateToReal, ENNReal.ofReal_toReal (ne_top_of_le_ne_top hN
            (min_le_left _ _)), min_comm]
        have := lintegral_ofReal_le_liminf h hg fun x => ENNReal.truncateToReal_nonneg
        simp_rw [he] at this
        exact this.trans (liminf_le_liminf (Eventually.of_forall fun n =>
          lintegral_mono fun x => min_le_left _ _))

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **The integral form of the Feller property** (MT Theorem D.4.1 as used on p. 126): for a
weak Feller kernel on a first-countable space and a lower semicontinuous `f ≥ 0`,
`x ↦ ∫ f(y) P(x, dy)` is lower semicontinuous. -/
theorem IsWeakFeller.lowerSemicontinuous_lintegral {P : Kernel X X} (hP : IsWeakFeller P)
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun x => ∫⁻ y, f y ∂P x :=
  lowerSemicontinuous_of_seq fun _ _ hz =>
    lintegral_le_liminf_of_lsc (fun G hG => le_liminf_seq_of_lsc (hP G hG) hz) hf

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- The `n`-step kernel of a weak Feller kernel is weak Feller. -/
theorem IsWeakFeller.pow {P : Kernel X X} (hP : IsWeakFeller P) (n : ℕ) :
    IsWeakFeller (P ^ n) := by
  induction n with
  | zero =>
    intro O hO
    have : (fun x => (P ^ 0) x O) = O.indicator 1 := by
      ext x; rw [pow_zero_apply, Measure.dirac_apply' _ hO.measurableSet]
    rw [this]
    exact hO.lowerSemicontinuous_indicator zero_le
  | succ n ih =>
    intro O hO
    have : (fun x => (P ^ (n + 1)) x O) = fun x => ∫⁻ y, (P ^ n) y O ∂P x := by
      ext x; exact pow_succ_apply P n x hO.measurableSet
    rw [this]
    exact hP.lowerSemicontinuous_lintegral (ih O hO)

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller kernel, `K_a(·, O)` is lower semicontinuous for every open `O`. -/
theorem IsWeakFeller.lsc_sampledKernel {P : Kernel X X} (hP : IsWeakFeller P)
    (a : ℕ → ℝ≥0∞) {O : Set X} (hO : IsOpen O) :
    LowerSemicontinuous fun x => sampledKernel P a x O := by
  have : (fun x => sampledKernel P a x O) = fun x => ∑' n, a n * (P ^ n) x O := by
    ext x; exact sampledKernel_apply P a x hO.measurableSet
  rw [this]
  exact lowerSemicontinuous_tsum fun n => lowerSemicontinuous_const_mul (hP.pow n O hO) _

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller kernel, `K_a` is weak Feller. -/
theorem IsWeakFeller.isWeakFeller_sampledKernel {P : Kernel X X} (hP : IsWeakFeller P)
    (a : ℕ → ℝ≥0∞) :
    IsWeakFeller (sampledKernel P a) := fun _ hO => hP.lsc_sampledKernel a hO

variable [TopologicalSpace X] in
/-- For a Markov kernel whose sets `P(·, Fᶜ)` are lower semicontinuous, `P(·, F)` is upper
semicontinuous. -/
theorem usc_of_lsc_compl {P : Kernel X X} [IsMarkovKernel P] {F : Set X} (hF : MeasurableSet F)
    (h : LowerSemicontinuous fun x => P x Fᶜ) : UpperSemicontinuous fun x => P x F := by
  have h1 : (fun x => P x F) = (fun t => 1 - t) ∘ fun x => P x Fᶜ := by
    ext x
    simp [prob_compl_eq_one_sub hF, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [h1]
  exact (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp_lowerSemicontinuous_antitone
    h fun a b hab => tsub_le_tsub_left hab 1

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller chain and a closed set `F`, `Pⁿ(·, F)` is upper semicontinuous. -/
theorem IsWeakFeller.usc_pow_closed {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (n : ℕ) {F : Set X} (hF : IsClosed F) : UpperSemicontinuous fun x => (P ^ n) x F := by
  have := isMarkovKernel_pow P n
  exact usc_of_lsc_compl hF.measurableSet (hP.pow n _ hF.isOpen_compl)

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller chain, a sampling distribution `a` and a closed set `F`, `K_a(·, F)` is
upper semicontinuous. -/
theorem IsWeakFeller.usc_sampledKernel_closed {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsWeakFeller P) {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) {F : Set X} (hF : IsClosed F) :
    UpperSemicontinuous fun x => sampledKernel P a x F := by
  have := isMarkovKernel_sampledKernel P ha
  exact usc_of_lsc_compl hF.measurableSet (hP.lsc_sampledKernel a hF.isOpen_compl)

/-! ### Proposition 6.1.1 (i) -/

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [OpensMeasurableSpace X] in
/-- **Proposition 6.1.1 (i)**, weak Feller part (MT p. 125). On a pseudo-metrizable space, `P`
is weak Feller iff `Pf` is continuous for every bounded continuous `f`. -/
theorem proposition_6_1_1_i_weak (P : Kernel X X) [IsMarkovKernel P] :
    IsWeakFeller P ↔ ∀ f : X →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂P x := by
  set μ : X → ProbabilityMeasure X := fun x => ⟨P x, inferInstance⟩
  constructor
  · intro h f
    refine continuous_iff_continuousAt.2 fun x => ?_
    have ht : Tendsto μ (𝓝 x) (𝓝 (μ x)) :=
      tendsto_of_forall_isOpen_le_liminf' fun G hG => (h G hG).le_liminf x
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht f
  · intro h O hO
    refine lowerSemicontinuous_iff_le_liminf.2 fun x => ?_
    have ht : Tendsto μ (𝓝 x) (𝓝 (μ x)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => (h f).tendsto x
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hO

variable [TopologicalSpace X] in
/-- If `P(·, A)` is lower semicontinuous for every measurable `A`, then it is continuous (apply
the hypothesis to `Aᶜ`). -/
theorem continuous_apply_of_lsc (P : Kernel X X) [IsMarkovKernel P]
    (h : ∀ A, MeasurableSet A → LowerSemicontinuous fun x => P x A) {A : Set X}
    (hA : MeasurableSet A) : Continuous fun x => P x A := by
  refine continuous_iff_lower_upperSemicontinuous.2 ⟨h A hA, ?_⟩
  have h1 : (fun x => P x A) = (fun t => 1 - t) ∘ fun x => P x Aᶜ := by
    ext x
    simp [prob_compl_eq_one_sub hA, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [h1]
  exact (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp_lowerSemicontinuous_antitone
    (h _ hA.compl) fun a b hab => tsub_le_tsub_left hab 1

variable [TopologicalSpace X] [FirstCountableTopology X] in
/-- If every `P(·, A)` is continuous, then `Pf` is continuous for measurable `0 ≤ f ≤ M`: by the
layer-cake formula `Pf(x) = ∫₀^M P(x, {f > t}) dt` and dominated convergence. -/
theorem continuous_integral_of_nonneg (P : Kernel X X) [IsMarkovKernel P]
    (h : ∀ A, MeasurableSet A → Continuous fun x => P x A) {f : X → ℝ} (hf : Measurable f)
    (hf0 : 0 ≤ f) {M : ℝ} (hM : ∀ x, f x ≤ M) : Continuous fun x => ∫ y, f y ∂P x := by
  have hint : ∀ x, Integrable f (P x) := fun x =>
    Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]; exact hM y)
  have heq : (fun x => ∫ y, f y ∂P x) =
      fun x => ∫ t in Ioi 0, (P x).real {a | t < f a} := by
    ext x; exact (hint x).integral_eq_integral_meas_lt (Eventually.of_forall hf0)
  rw [heq]
  refine continuous_of_dominated (bound := (Iio M).indicator 1) (fun x => ?_) (fun x => ?_)
    ?_ (Eventually.of_forall fun t => ?_)
  · exact (Antitone.measurable (f := fun t : ℝ => (P x).real {a | t < f a}) fun s t hst =>
      measureReal_mono (fun ω (hω : t < f ω) => lt_of_le_of_lt hst hω)
        (measure_ne_top _ _)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    by_cases ht : t < M
    · simp only [indicator_of_mem (show t ∈ Iio M from ht), Pi.one_apply]
      exact measureReal_le_one
    · have : {a | t < f a} = ∅ := eq_empty_of_forall_notMem fun a ha =>
        ht (lt_of_lt_of_le ha (hM a))
      simp only [this, measureReal_empty]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  · refine (integrable_indicator_iff measurableSet_Iio).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iio]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun s hs => ?_) (measure_Ioo_lt_top (a := 0)
      (b := M)))
    exact ⟨hs.2, hs.1⟩
  · exact ENNReal.continuousOn_toReal.comp_continuous (h _ (measurableSet_lt measurable_const hf))
      fun x => measure_ne_top _ _

variable [TopologicalSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (i)**, strong Feller part (MT p. 125). On a first-countable space, `P`
is strong Feller iff `P(·, A)` is lower semicontinuous for every measurable `A`. -/
theorem proposition_6_1_1_i_strong (P : Kernel X X) [IsMarkovKernel P] :
    IsStrongFeller P ↔ ∀ A, MeasurableSet A → LowerSemicontinuous fun x => P x A := by
  constructor
  · intro h A hA
    have hc := h (A.indicator 1) (measurable_one.indicator hA) ⟨1, fun x => by
      by_cases hx : x ∈ A <;> simp [hx]⟩
    have he : (fun x => P x A) = fun x => ENNReal.ofReal (kfunR P (A.indicator 1) x) := by
      ext x
      rw [kfunR, integral_indicator_one hA, measureReal_def, ENNReal.ofReal_toReal
        (measure_ne_top _ _)]
    rw [he]
    exact (ENNReal.continuous_ofReal.comp hc).lowerSemicontinuous
  · intro h f hf ⟨C, hC⟩
    have hg := continuous_integral_of_nonneg P (fun A hA => continuous_apply_of_lsc P h hA)
      (f := fun y => f y + C) (hf.add_const C)
      (fun y => by have := (abs_le.1 (hC y)).1; simp only [Pi.zero_apply]; linarith)
      (M := C + C) (fun y => by have := (abs_le.1 (hC y)).2; linarith)
    have hint : ∀ x, Integrable f (P x) := fun x =>
      Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hC y)
    have he : kfunR P f = fun x => ∫ y, f y + C ∂P x - C := by
      ext x
      rw [kfunR, integral_add (hint x) (integrable_const C), integral_const, probReal_univ,
        one_smul, add_sub_cancel_right]
    rw [he]
    exact hg.sub continuous_const

variable [TopologicalSpace X] [FirstCountableTopology X] in
/-- A strong Feller chain is weak Feller. -/
theorem IsStrongFeller.isWeakFeller {P : Kernel X X} [IsMarkovKernel P] [OpensMeasurableSpace X]
    (h : IsStrongFeller P) : IsWeakFeller P := fun _ hO =>
  (proposition_6_1_1_i_strong P).1 h _ hO.measurableSet

/-! ### Proposition 6.1.1 (ii): tail probabilities of return times to closed sets -/

/-- The tail probability `Pₓ(τ_C ≥ k)`. -/
noncomputable def tailProb (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (k : ℕ) (x : X) :
    ℝ≥0∞ :=
  pathKernel P x {ω | WithTop.some k ≤ firstReturn C ω}

/-- `Pₓ(τ_C ≥ 1) = 1`. -/
theorem tailProb_one (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (x : X) :
    tailProb P C 1 x = 1 := by
  have := isMarkovKernel_pathKernel P
  have : {ω : ℕ → X | WithTop.some 1 ≤ firstReturn C ω} = univ :=
    eq_univ_of_forall fun ω => one_le_firstReturn C ω
  rw [tailProb, this, measure_univ]

/-- `Pₓ(τ_C ≥ 0) = 1`. -/
theorem tailProb_zero (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (x : X) :
    tailProb P C 0 x = 1 := by
  have := isMarkovKernel_pathKernel P
  have : {ω : ℕ → X | WithTop.some 0 ≤ firstReturn C ω} = univ :=
    eq_univ_of_forall fun ω => (WithTop.coe_le_coe.2 zero_le).trans (one_le_firstReturn C ω)
  rw [tailProb, this, measure_univ]

/-- The recursion `Pₓ(τ_C ≥ k + 2) = ∫_{Cᶜ} P(x, dy) P_y(τ_C ≥ k + 1)`, i.e.
`Pₓ(τ_C ≥ k + 1) = (P I_{Cᶜ})ᵏ(x, X)` (MT p. 126). -/
theorem tailProb_succ (P : Kernel X X) [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C)
    (k : ℕ) (x : X) : tailProb P C (k + 2) x = ∫⁻ y in Cᶜ, tailProb P C (k + 1) y ∂P x := by
  have hset : {ω : ℕ → X | WithTop.some (k + 2) ≤ firstReturn C ω} =
      {ω | ω 1 ∈ Cᶜ} ∩ shift 1 ⁻¹' {ω | WithTop.some (k + 1) ≤ firstReturn C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    exact le_firstReturn_succ_iff C ω k
  rw [tailProb, hset, pathKernel_first_step P x hC.compl (measurableSet_le_firstReturn hC _)]
  rfl

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (ii)**, tail form (MT p. 125): for a weak Feller chain on a
first-countable space and a closed set `C`, `x ↦ Pₓ(τ_C ≥ k)` is lower semicontinuous. -/
theorem proposition_6_1_1_ii_tail {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {C : Set X} (hC : IsClosed C) (k : ℕ) : LowerSemicontinuous (tailProb P C k) := by
  have key : ∀ k, LowerSemicontinuous (tailProb P C (k + 1)) := by
    intro k
    induction k with
    | zero =>
      have : tailProb P C 1 = fun _ => 1 := funext (tailProb_one P C)
      rw [zero_add, this]
      exact lowerSemicontinuous_const
    | succ k ih =>
      have : tailProb P C (k + 1 + 1) = fun x => ∫⁻ y, Cᶜ.indicator (tailProb P C (k + 1)) y
          ∂P x := by
        ext x
        rw [tailProb_succ P hC.measurableSet k x, lintegral_indicator hC.measurableSet.compl]
      rw [this]
      exact hP.lowerSemicontinuous_lintegral
        (lowerSemicontinuous_indicator_of_isOpen hC.isOpen_compl ih)
  rcases k with _ | k
  · have : tailProb P C 0 = fun _ => 1 := funext (tailProb_zero P C)
    rw [this]
    exact lowerSemicontinuous_const
  · exact key k

/-- The extension of `m : ℕ → ℝ≥0` to `ℕ ∪ {∞}` by `m(t) = sup_{n ≤ t} m(n)` (for nondecreasing
`m`, `m(∞) = sup m`). -/
noncomputable def extendSup (m : ℕ → ℝ≥0) (t : WithTop ℕ) : ℝ≥0∞ :=
  ⨆ n : ℕ, if WithTop.some n ≤ t then (m n : ℝ≥0∞) else 0

/-- `Eₓ[m(τ_C)]`, with `m(∞) = sup m`. -/
noncomputable def expectReturn (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (m : ℕ → ℝ≥0)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, extendSup m (firstReturn C ω) ∂pathKernel P x

/-- The partial sums of the increments: `Σ_{i < N} Δm(i + 1) 1{i < k} = m(min N k) − m(0)`. -/
theorem sum_increments_eq {m : ℕ → ℝ≥0} (hm : Monotone m) (N k : ℕ) :
    ∑ i ∈ Finset.range N, (m (i + 1) - m i) * (if i < k then 1 else 0) = m (min N k) - m 0 := by
  have h1 : ∑ i ∈ Finset.range N, (m (i + 1) - m i) * (if i < k then 1 else 0) =
      ∑ i ∈ Finset.range (min N k), (m (i + 1) - m i) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (· < k)]
    have h2 : ∑ i ∈ (Finset.range N).filter (fun i => ¬ i < k),
        (m (i + 1) - m i) * (if i < k then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [(Finset.mem_filter.1 hi).2]
    rw [h2, add_zero]
    have h3 : (Finset.range N).filter (· < k) = Finset.range (min N k) := by
      ext i; simp [Finset.mem_filter, Finset.mem_range]
    rw [h3]
    exact Finset.sum_congr rfl fun i hi => by
      simp [show i < k by have := Finset.mem_range.1 hi; omega]
  rw [h1, Finset.sum_range_tsub hm]

/-- The summation-by-parts identity of MT p. 126, pointwise:
`m(t) = m(0) + Σ_{i ≥ 0} Δm(i + 1) 1{t ≥ i + 1}` for nondecreasing `m`. -/
theorem extendSup_eq_tsum {m : ℕ → ℝ≥0} (hm : Monotone m) (t : WithTop ℕ) :
    extendSup m t = m 0 + ∑' i, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) *
      (if WithTop.some (i + 1) ≤ t then 1 else 0) := by
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  induction t using WithTop.recTopCoe with
  | top =>
    have hs : ∀ N, (m 0 : ℝ≥0∞) + ∑ i ∈ Finset.range N, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) *
        (if WithTop.some (i + 1) ≤ ⊤ then 1 else 0) = m N := fun N => by
      have := sum_increments_eq hm N N
      simp only [min_self] at this
      have h' : ∑ i ∈ Finset.range N, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) *
          (if WithTop.some (i + 1) ≤ ⊤ then 1 else 0) =
          ((∑ i ∈ Finset.range N, (m (i + 1) - m i) * (if i < N then 1 else 0) : ℝ≥0) :
            ℝ≥0∞) := by
        rw [ENNReal.ofNNReal_finsetSum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.coe_mul]
        simp [Finset.mem_range.1 hi]
      rw [h', this, ← ENNReal.coe_add, add_tsub_cancel_of_le (hm (Nat.zero_le N))]
    simp_rw [hs]
    simp [extendSup]
  | coe k =>
    have hs : ∀ N, (m 0 : ℝ≥0∞) + ∑ i ∈ Finset.range N, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) *
        (if WithTop.some (i + 1) ≤ WithTop.some k then 1 else 0) = m (min N k) :=
      fun N => by
      have h' : ∑ i ∈ Finset.range N, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) *
          (if WithTop.some (i + 1) ≤ WithTop.some k then 1 else 0) =
          ((∑ i ∈ Finset.range N, (m (i + 1) - m i) * (if i < k then 1 else 0) : ℝ≥0) :
            ℝ≥0∞) := by
        rw [ENNReal.ofNNReal_finsetSum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.coe_mul]
        congr 1
        split_ifs with h1 h2 h2
        · simp
        · exact absurd (by have := WithTop.coe_le_coe.1 h1; omega) h2
        · exact absurd (WithTop.coe_le_coe.2 (by omega)) h1
        · simp
      rw [h', sum_increments_eq hm, ← ENNReal.coe_add,
        add_tsub_cancel_of_le (hm (Nat.zero_le _))]
    simp_rw [hs]
    apply le_antisymm
    · refine iSup_le fun n => ?_
      split_ifs with h
      · exact le_iSup_of_le k (by rw [min_self]; exact_mod_cast hm (WithTop.coe_le_coe.1 h))
      · exact zero_le
    · refine iSup_le fun N => le_iSup_of_le (min N k) ?_
      simp

/-- **The identity of MT p. 126**: `Eₓ[m(τ_C)] = m(0) + Σ_{i ≥ 0} Δm(i + 1) Pₓ(τ_C ≥ i + 1)`. -/
theorem expectReturn_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {m : ℕ → ℝ≥0} (hm : Monotone m) (x : X) :
    expectReturn P C m x = m 0 + ∑' i, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) * tailProb P C (i + 1) x
    := by
  have := isMarkovKernel_pathKernel P
  have hind : ∀ i : ℕ, (fun ω : ℕ → X =>
      if WithTop.some (i + 1) ≤ firstReturn C ω then (1 : ℝ≥0∞) else 0) =
      {ω | WithTop.some (i + 1) ≤ firstReturn C ω}.indicator 1 := fun i => by
    ext ω
    by_cases h : WithTop.some (i + 1) ≤ firstReturn C ω
    · rw [indicator_of_mem (show ω ∈ {ω : ℕ → X | WithTop.some (i + 1) ≤ firstReturn C ω}
        from h)]
      simp only [h, ↓reduceIte, Pi.one_apply]
    · rw [indicator_of_notMem (show ω ∉ {ω : ℕ → X | WithTop.some (i + 1) ≤ firstReturn C ω}
        from h)]
      simp only [h, ↓reduceIte]
  have hmeas : ∀ i : ℕ, Measurable fun ω : ℕ → X =>
      if WithTop.some (i + 1) ≤ firstReturn C ω then (1 : ℝ≥0∞) else 0 := fun i =>
    Measurable.ite (measurableSet_le_firstReturn hC _) measurable_const measurable_const
  rw [expectReturn]
  simp_rw [extendSup_eq_tsum hm]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_tsum fun i => ((hmeas i).const_mul _).aemeasurable]
  congr 1
  refine tsum_congr fun i => ?_
  rw [lintegral_const_mul _ (hmeas i), hind i,
    lintegral_indicator_one (measurableSet_le_firstReturn hC _)]
  rfl

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (ii)** (MT p. 125): for a weak Feller chain on a first-countable space, a
closed set `C` and a nondecreasing `m`, `x ↦ Eₓ[m(τ_C)]` is lower semicontinuous. -/
theorem proposition_6_1_1_ii {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {C : Set X} (hC : IsClosed C) {m : ℕ → ℝ≥0} (hm : Monotone m) :
    LowerSemicontinuous (expectReturn P C m) := by
  have : expectReturn P C m = fun x => (m 0 : ℝ≥0∞) +
      ∑' i, ((m (i + 1) - m i : ℝ≥0) : ℝ≥0∞) * tailProb P C (i + 1) x :=
    funext (expectReturn_eq_tsum P hC.measurableSet hm)
  rw [this]
  exact lowerSemicontinuous_const.add (lowerSemicontinuous_tsum fun i =>
    lowerSemicontinuous_const_mul (proposition_6_1_1_ii_tail hP hC (i + 1)) _)

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (ii)**, the mean return time (MT p. 125): `x ↦ Eₓ[τ_C]` is lower
semicontinuous for closed `C` (`m(n) = n`, `m(∞) = ∞`). -/
theorem proposition_6_1_1_ii_mean {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {C : Set X} (hC : IsClosed C) :
    LowerSemicontinuous (expectReturn P C fun n => (n : ℝ≥0)) :=
  proposition_6_1_1_ii hP hC fun _ _ h => by exact_mod_cast h

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (ii)**, geometric moments (MT p. 125): `x ↦ Eₓ[r^{τ_C}]` is lower
semicontinuous for closed `C` and `r ≥ 1`. -/
theorem proposition_6_1_1_ii_geom {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {C : Set X} (hC : IsClosed C) {r : ℝ≥0} (hr : 1 ≤ r) :
    LowerSemicontinuous (expectReturn P C fun n => r ^ n) :=
  proposition_6_1_1_ii hP hC fun _ _ h => pow_le_pow_right₀ hr h

/-! ### Proposition 6.1.1 (iii): hitting open sets -/

omit [MeasurableSpace X] in
/-- `t ≤ n` iff not `t ≥ n + 1`, in `ℕ ∪ {∞}`. -/
theorem withTop_le_iff_not_succ_le (t : WithTop ℕ) (n : ℕ) :
    t ≤ WithTop.some n ↔ ¬ WithTop.some (n + 1) ≤ t := by
  induction t using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    rw [WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega

/-- The probability `Pₓ(τ_O ≤ n)` of entering `O` by time `n`. -/
noncomputable def hitWithin (P : Kernel X X) [IsMarkovKernel P] (O : Set X) (n : ℕ) (x : X) :
    ℝ≥0∞ :=
  pathKernel P x {ω | firstReturn O ω ≤ WithTop.some n}

/-- `{τ_O ≤ n}` is an event. -/
theorem measurableSet_firstReturn_le {O : Set X} (hO : MeasurableSet O) (n : ℕ) :
    MeasurableSet {ω : ℕ → X | firstReturn O ω ≤ WithTop.some n} := by
  have : {ω : ℕ → X | firstReturn O ω ≤ WithTop.some n} =
      {ω | WithTop.some (n + 1) ≤ firstReturn O ω}ᶜ := by
    ext ω; simp only [mem_ofPred_eq, mem_compl_iff, withTop_le_iff_not_succ_le]
  rw [this]
  exact (measurableSet_le_firstReturn hO _).compl

/-- `Pₓ(τ_O ≤ 0) = 0`. -/
theorem hitWithin_zero (P : Kernel X X) [IsMarkovKernel P] (O : Set X) (x : X) :
    hitWithin P O 0 x = 0 := by
  have : {ω : ℕ → X | firstReturn O ω ≤ WithTop.some 0} = ∅ :=
    eq_empty_of_forall_notMem fun ω h => by
      have := (one_le_firstReturn O ω).trans h
      exact absurd (WithTop.coe_le_coe.1 this) (by omega)
  rw [hitWithin, this, measure_empty]

/-- First-step equation: `Pₓ(τ_O ≤ n + 1) = P(x, O) + ∫_{Oᶜ} P(x, dy) P_y(τ_O ≤ n)`. -/
theorem hitWithin_succ (P : Kernel X X) [IsMarkovKernel P] {O : Set X} (hO : MeasurableSet O)
    (n : ℕ) (x : X) :
    hitWithin P O (n + 1) x = P x O + ∫⁻ y in Oᶜ, hitWithin P O n y ∂P x := by
  have hset : {ω : ℕ → X | firstReturn O ω ≤ WithTop.some (n + 1)} =
      {ω | ω 1 ∈ O} ∪ ({ω | ω 1 ∈ Oᶜ} ∩
        shift 1 ⁻¹' {ω | firstReturn O ω ≤ WithTop.some n}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage,
      withTop_le_iff_not_succ_le, le_firstReturn_succ_iff, mem_compl_iff]
    tauto
  have hdisj : Disjoint {ω : ℕ → X | ω 1 ∈ O}
      ({ω | ω 1 ∈ Oᶜ} ∩ shift 1 ⁻¹' {ω | firstReturn O ω ≤ WithTop.some n}) :=
    Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1
  rw [hitWithin, hset, measure_union hdisj ((measurable_pi_apply 1 hO.compl).inter
      (measurable_shift 1 (measurableSet_firstReturn_le hO n))),
    pathKernel_first_step P x hO.compl (measurableSet_firstReturn_le hO n),
    pathKernel_coord_mem P x 1 hO, pow_one]
  rfl

/-- `Pₓ(τ_O ≤ n) ≤ 1`. -/
theorem hitWithin_le_one (P : Kernel X X) [IsMarkovKernel P] (O : Set X) (n : ℕ) (x : X) :
    hitWithin P O n x ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  exact prob_le_one

/-- `L(x, O) = sup_n Pₓ(τ_O ≤ n)`. -/
theorem hitProb_eq_iSup_hitWithin (P : Kernel X X) [IsMarkovKernel P] (O : Set X) (x : X) :
    hitProb P O x = ⨆ n, hitWithin P O n x := by
  have hset : {ω : ℕ → X | firstReturn O ω ≠ ⊤} =
      ⋃ n : ℕ, {ω | firstReturn O ω ≤ WithTop.some n} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 h
      exact ⟨k, hk.symm.le⟩
    · rintro ⟨n, hn⟩ h
      rw [h] at hn
      exact absurd hn (by simp)
  rw [hitProb, hset, Monotone.measure_iUnion]
  · rfl
  · intro i j hij ω hω
    exact le_trans hω (WithTop.coe_le_coe.2 hij)

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.1 (iii)** (MT p. 125): for a weak Feller chain on a first-countable space
and an open set `O`, the functions `x ↦ Pₓ(τ_O ≤ n)`, `x ↦ K_a(x, O)` and `x ↦ L(x, O)` are
lower semicontinuous. -/
theorem proposition_6_1_1_iii {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {O : Set X} (hO : IsOpen O) :
    (∀ n, LowerSemicontinuous (hitWithin P O n)) ∧
      (∀ a : ℕ → ℝ≥0∞, LowerSemicontinuous fun x => sampledKernel P a x O) ∧
      LowerSemicontinuous (hitProb P O) := by
  have hn : ∀ n, LowerSemicontinuous (hitWithin P O n) := by
    intro n
    induction n with
    | zero =>
      have : hitWithin P O 0 = fun _ => 0 := funext (hitWithin_zero P O)
      rw [this]
      exact lowerSemicontinuous_const
    | succ n ih =>
      have hmax : hitWithin P O (n + 1) = fun x =>
          ∫⁻ y, max (O.indicator 1 y) (hitWithin P O n y) ∂P x := by
        ext x
        have he : (fun y => max (O.indicator 1 y) (hitWithin P O n y)) =
            O.indicator 1 + Oᶜ.indicator (hitWithin P O n) := by
          ext y
          by_cases hy : y ∈ O
          · simp [hy, hitWithin_le_one]
          · simp [hy]
        rw [hitWithin_succ P hO.measurableSet n x, he]
        change _ = ∫⁻ y, (O.indicator 1 y + Oᶜ.indicator (hitWithin P O n) y) ∂P x
        rw [lintegral_add_left
          (measurable_one.indicator hO.measurableSet), lintegral_indicator_one hO.measurableSet,
          lintegral_indicator hO.measurableSet.compl]
      rw [hmax]
      exact hP.lowerSemicontinuous_lintegral
        ((hO.lowerSemicontinuous_indicator zero_le).sup ih)
  refine ⟨hn, fun a => hP.lsc_sampledKernel a hO, ?_⟩
  have : hitProb P O = fun x => ⨆ n, hitWithin P O n x :=
    funext (hitProb_eq_iSup_hitWithin P O)
  rw [this]
  exact lowerSemicontinuous_iSup hn

/-! ### Reachable points and open set irreducibility (§6.1.2) -/

variable [TopologicalSpace X] in
/-- `x` is **reachable** (MT p. 128): every open neighbourhood `O` of `x` has `U(y, O) > 0` for
every `y`. -/
def IsReachable (P : Kernel X X) (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → ∀ y, 0 < potKernel P y O

variable [TopologicalSpace X] in
/-- `P` is **open set irreducible** (MT p. 128): every point is reachable. -/
def IsOpenSetIrreducible (P : Kernel X X) : Prop := ∀ x, IsReachable P x

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Lemma 6.1.4** (MT p. 129): for a maximal irreducibility measure `ψ`, a point is reachable iff
it lies in the support of `ψ`. -/
theorem lemma_6_1_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (x : X) : IsReachable P x ↔ x ∈ ψ.support := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨U, hU, hU0⟩ := (Measure.notMem_support_iff_exists).1 hx
    obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.1 hU
    have hO0 : ψ O = 0 := measure_mono_null hOU hU0
    have hnull := hψ.hitSet_null hO.measurableSet hO0
    obtain ⟨y, hy⟩ : ∃ y, y ∉ {y | 0 < hitProb P O y} := by
      by_contra hc
      push Not at hc
      have : {y | 0 < hitProb P O y} = univ := eq_univ_of_forall hc
      rw [this, Measure.measure_univ_eq_zero] at hnull
      exact hψ.1 hnull
    apply hy
    have := (potKernel_pos_iff P hO.measurableSet y).1 (h O hO hxO y)
    exact (hitProb_pos_iff P hO.measurableSet y).2 this
  · intro hx O hO hxO y
    have hpos : 0 < ψ O := (Measure.mem_support_iff_forall x).1 hx O (hO.mem_nhds hxO)
    have := (hitProb_pos_iff P hO.measurableSet y).1 (hψ.2.1 O hO.measurableSet hpos y)
    exact (potKernel_pos_iff P hO.measurableSet y).2 this

/-- **Correction to Lemma 6.1.4** (MT p. 129): for an irreducibility measure that is not maximal
the lemma fails. On the one-point space with the identity kernel, the zero measure is an
irreducibility measure and the point is reachable, but `supp 0 = ∅`. -/
theorem lemma_6_1_4_counterexample :
    IsPhiIrreducible (Kernel.id : Kernel Unit Unit) 0 ∧
      IsReachable (Kernel.id : Kernel Unit Unit) () ∧ () ∉ (0 : Measure Unit).support := by
  refine ⟨isPhiIrreducible_zero _, fun O _ hO y => ?_, by simp [Measure.support_zero]⟩
  have hOu : O = univ := eq_univ_of_forall fun z => by cases z; exact hO
  rw [potKernel_pos_iff _ (by rw [hOu]; exact MeasurableSet.univ)]
  refine ⟨0, ?_⟩
  rw [hOu]
  have : IsMarkovKernel (Kernel.id ^ (0 + 1) : Kernel Unit Unit) :=
    isMarkovKernel_pow _ _
  simp

variable [TopologicalSpace X] [DiscreteTopology X] [MeasurableSingletonClass X] [Nonempty X] in
/-- MT p. 129: on a countable space with the discrete topology, open set irreducibility is
irreducibility in the sense of §4.1 (all states communicate). -/
theorem isOpenSetIrreducible_iff_irreducible (P : Kernel X X) [IsMarkovKernel P] :
    IsOpenSetIrreducible P ↔ IsIrreducibleChain P := by
  rw [isIrreducibleChain_iff]
  have hlead : ∀ x y, 0 < potKernel P x {y} → Leads P x y := fun x y h =>
    Or.inr ((hitProb_pos_iff P (measurableSet_singleton y) x).2
      ((potKernel_pos_iff P (measurableSet_singleton y) x).1 h))
  constructor
  · intro h x y
    exact ⟨hlead x y (h y {y} (isOpen_discrete _) rfl x),
      hlead y x (h x {x} (isOpen_discrete _) rfl y)⟩
  · intro h x O _ hxO y
    have hsub : potKernel P y {x} ≤ potKernel P y O := measure_mono (singleton_subset_iff.2 hxO)
    refine lt_of_lt_of_le ?_ hsub
    rw [potKernel_pos_iff P (measurableSet_singleton x)]
    have hhit : ∀ z, z ≠ x → ∃ n, 0 < (P ^ (n + 1)) z {x} := fun z hz => by
      rcases (h z x).1 with h1 | h1
      · exact absurd h1 hz
      · exact (hitProb_pos_iff P (measurableSet_singleton x) z).1 h1
    by_cases hyx : y = x
    · subst hyx
      by_cases hz : ∃ z, z ≠ y
      · obtain ⟨z, hz⟩ := hz
        obtain ⟨m, hm⟩ := hhit z hz
        have hyz : ∃ n, 0 < (P ^ (n + 1)) y {z} := by
          rcases (h y z).1 with h1 | h1
          · exact absurd h1.symm hz
          · exact (hitProb_pos_iff P (measurableSet_singleton z) y).1 h1
        obtain ⟨n, hn⟩ := hyz
        refine ⟨n + 1 + m, ?_⟩
        rw [show n + 1 + m + 1 = (n + 1) + (m + 1) by omega,
          pow_add_pos_iff P (n + 1) (m + 1) y (measurableSet_singleton y)]
        exact lt_of_lt_of_le hn (measure_mono (singleton_subset_iff.2 hm))
      · push Not at hz
        refine ⟨0, ?_⟩
        have hu : ({y} : Set X) = univ := eq_univ_of_forall fun z => hz z
        have := isMarkovKernel_pow P (0 + 1)
        rw [hu, measure_univ]
        exact one_pos
    · exact hhit y hyx

variable [TopologicalSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.5** (MT p. 129): if a strong Feller chain has a reachable point `x*`, it is
`P(x*, ·)`-irreducible. -/
theorem proposition_6_1_5 {P : Kernel X X} [IsMarkovKernel P] (hP : IsStrongFeller P) {x₀ : X}
    (hx : IsReachable P x₀) : IsPhiIrreducible P (P x₀) := by
  intro A hA hpos y
  have hl := (proposition_6_1_1_i_strong P).1 hP A hA
  have hO : IsOpen {z | 0 < P z A} := hl.isOpen_preimage 0
  have hOm : MeasurableSet {z | 0 < P z A} :=
    measurableSet_lt measurable_const (Kernel.measurable_coe P hA)
  obtain ⟨n, hn⟩ := (potKernel_pos_iff P hOm y).1 (hx _ hO hpos y)
  refine (hitProb_pos_iff P hA y).2 ⟨n + 1, ?_⟩
  rw [pow_add_pos_iff P (n + 1) 1 y hA]
  simpa only [pow_one] using hn

variable [TopologicalSpace X] [FirstCountableTopology X] in
/-- **Proposition 6.1.6** (MT p. 129): an open set irreducible strong Feller chain is
`ψ`-irreducible for a nonzero `ψ` (namely `P(x, ·)` for any `x`). -/
theorem proposition_6_1_6 [Nonempty X] {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsStrongFeller P) (hirr : IsOpenSetIrreducible P) :
    ∃ ψ : Measure X, ψ ≠ 0 ∧ IsPhiIrreducible P ψ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨P x, IsProbabilityMeasure.ne_zero _, proposition_6_1_5 hP (hirr x)⟩

end MeynTweedie.TransienceRecurrence
