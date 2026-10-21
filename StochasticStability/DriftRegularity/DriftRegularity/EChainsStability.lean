/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.EChains
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.PartitionOfUnity

/-!
# e-chains and the stability of the dynamical systems (MT §6.4.1–6.4.2)

Meyn and Tweedie, Propositions 6.4.3 and 6.4.5, pp. 141–142.

* `eventually_forall_dist_lt_of_isCompact`: the converse half of Ascoli's theorem, a compact set
  of `C(X, ℝ)` (compact-open topology) is equicontinuous at every point of a locally compact `X`.
* `eventually_dist_lt_of_eChain`, `integral_bump_bounds`, `abs_integral_tail_le`,
  `eventually_dist_lt_of_eChain_bounded`: for an e-chain that is bounded in probability,
  `{Pᵏ f}` is equicontinuous at every point for every *bounded* continuous `f`.
* `orbitCM hP f`: the orbit `k ↦ Pᵏ f` in `C(X, ℝ)`, the dynamical system `(P, C(X), d_c)`.
* **Proposition 6.4.5** (`proposition_6_4_5`, p. 142): for a weak Feller chain bounded in
  probability, the chain is an e-chain iff every orbit `{Pᵏ f}` has compact closure in
  `C(X, ℝ)` (Lagrange stability of `(P, C(X), d_c)`).
* `dmDist fs` (6.16), `term_le_dmDist`, `IsLyapunovStable P fs`: the metric `d_m` built from a
  sequence `fs` of functions with `‖fⱼ‖ ≤ 1`, and stability in the sense of Lyapunov.
* `eventually_forall_abs_integral_sub_lt`: weak convergence `ν → μ` gives `∫ gᵢ dν → ∫ gᵢ dμ`
  uniformly over a bounded family equicontinuous at every point (a partition-of-unity
  argument); `exists_isCompact_measureReal_compl_lt`: a single probability measure is tight;
  `dm_terms_le`: the terms of `d_m` are at most `2 · 2^{−j}`.
* **Proposition 6.4.3** (p. 141; the book omits the proof): `proposition_6_4_3`, on a locally
  compact second-countable Hausdorff space, with `d_m` built from compactly supported `fⱼ`,
  `‖fⱼ‖ ≤ 1`, that approximate every compactly supported `f` with `‖f‖ ≤ 1`, the chain is an
  e-chain iff `(P, M, d_m)` is Lyapunov stable; `proposition_6_4_3_of_lyapunov` is the "if"
  direction, which needs neither local compactness nor compact supports.

**Hypotheses.** The book leaves the functions `fⱼ` of (6.16) unspecified ("an appropriate set");
Proposition 6.4.3 depends on that choice (for `fⱼ = 0` every chain is Lyapunov stable), so the
density hypothesis is made explicit.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The converse half of Ascoli's theorem: on a locally compact space, a compact set of continuous
real functions (compact-open topology) is equicontinuous at every point. -/
theorem eventually_forall_dist_lt_of_isCompact [TopologicalSpace X] [LocallyCompactSpace X]
    {S : Set C(X, ℝ)} (hS : IsCompact S) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ g ∈ S, dist (g x₀) (g x) < ε := by
  refine hS.eventually_forall_of_forall_eventually fun g _ => ?_
  have hc : Continuous fun z : X × C(X, ℝ) => dist (z.2 x₀) (z.2 z.1) :=
    ((continuous_eval_const x₀).comp continuous_snd).dist
      (continuous_eval.comp (continuous_snd.prodMk continuous_fst))
  have := hc.tendsto (x₀, g)
  simp only [dist_self] at this
  exact this.eventually (gt_mem_nhds hε)

variable [TopologicalSpace X] in
/-- An equicontinuous-on-`N` family with `N` a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem eventually_dist_lt_of_eChain {P : Kernel X X} (he : IsEChain P) {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {N : Set X} (hN : IsCompact N) {x₀ : X}
    (hxN : N ∈ 𝓝 x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ k : ℕ, dist (∫ y, f y ∂(P ^ k) x₀) (∫ y, f y ∂(P ^ k) x) < ε := by
  have h := he f hf hfc N hN x₀ (mem_of_mem_nhds hxN) _ (Metric.dist_mem_uniformity hε)
  rwa [nhdsWithin_eq_nhds.2 hxN] at h

/-- Bounds for a function `0 ≤ g ≤ 1` with `g = 1` on `C` and support in `L`:
`μ(C) ≤ ∫ g dμ ≤ μ(L)` for a probability measure `μ`. -/
theorem integral_bump_bounds {μ : Measure X} [IsProbabilityMeasure μ] {g : X → ℝ}
    (hg : Measurable g) (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {C L : Set X} (hC : MeasurableSet C)
    (hL : MeasurableSet L) (hgC : EqOn g 1 C) (hgL : ∀ x, g x ≠ 0 → x ∈ L) :
    μ.real C ≤ ∫ x, g x ∂μ ∧ ∫ x, g x ∂μ ≤ μ.real L := by
  have hint : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
  constructor
  · rw [← integral_indicator_one hC]
    refine integral_mono ((integrable_const 1).indicator hC) hint fun x => ?_
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, hgC hx]
    · rw [indicator_of_notMem hx]; exact (h01 x).1
  · rw [← integral_indicator_one hL]
    refine integral_mono hint ((integrable_const 1).indicator hL) fun x => ?_
    by_cases hx : x ∈ L
    · rw [indicator_of_mem hx]; exact (h01 x).2
    · rw [indicator_of_notMem hx]
      by_contra h
      exact hx (hgL x (ne_of_gt (lt_of_not_ge h)))

/-- The tail estimate: if `0 ≤ g' ≤ 1` with `g' = 1` on `L`, then
`|∫ (f − f g') dμ| ≤ ‖f‖ μ(Lᶜ)`. -/
theorem abs_integral_tail_le {μ : Measure X} [IsProbabilityMeasure μ] [TopologicalSpace X]
    [OpensMeasurableSpace X] (f : X →ᵇ ℝ) {g' : X → ℝ}
    (h01 : ∀ x, g' x ∈ Icc (0 : ℝ) 1) {L : Set X} (hL : MeasurableSet L) (hgL : EqOn g' 1 L) :
    |∫ y, (f y - f y * g' y) ∂μ| ≤ ‖f‖ * μ.real Lᶜ := by
  have hb : ∀ y, |f y - f y * g' y| ≤ ‖f‖ * Lᶜ.indicator 1 y := fun y => by
    by_cases hy : y ∈ L
    · simp only [hgL hy, Pi.one_apply, mul_one, sub_self, abs_zero]
      exact mul_nonneg (norm_nonneg _) (indicator_nonneg (fun _ _ => zero_le_one) y)
    · rw [indicator_of_mem (show y ∈ Lᶜ from hy), Pi.one_apply, mul_one,
        show f y - f y * g' y = f y * (1 - g' y) by ring, abs_mul]
      have h1 : |1 - g' y| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(h01 y).1, (h01 y).2]
      calc |f y| * |1 - g' y| ≤ |f y| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ ‖f‖ := by rw [mul_one, ← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
  have hint : Integrable (fun y => ‖f‖ * Lᶜ.indicator (1 : X → ℝ) y) μ :=
    ((integrable_const 1).indicator hL.compl).const_mul _
  calc |∫ y, (f y - f y * g' y) ∂μ| ≤ ∫ y, |f y - f y * g' y| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, ‖f‖ * Lᶜ.indicator 1 y ∂μ := integral_mono_of_nonneg
        (Eventually.of_forall fun y => abs_nonneg _) hint (Eventually.of_forall hb)
    _ = ‖f‖ * μ.real Lᶜ := by
        rw [integral_const_mul, integral_indicator_one hL.compl]

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [LocallyCompactSpace X]
  [BorelSpace X] in
/-- For a weak Feller e-chain that is bounded in probability, `{Pᵏ f}` is equicontinuous at every
point for every bounded continuous `f` (not only for `f` with compact support): the mass of
`Pᵏ(x, ·)` outside a compact set is uniformly small for `x` near `x₀` and large `k`, by
equicontinuity applied to a bump function. -/
theorem eventually_dist_lt_of_eChain_bounded {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsWeakFeller P) (he : IsEChain P) (hb : IsBoundedInProbability P) (f : X →ᵇ ℝ)
    (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ k : ℕ, dist (∫ y, f y ∂(P ^ k) x₀) (∫ y, f y ∂(P ^ k) x) < ε := by
  have hB : 0 < ‖f‖ + 1 := by positivity
  set η : ℝ := min (1 / 8) (ε / (16 * (‖f‖ + 1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hfη : ‖f‖ * η ≤ ε / 16 := by
    calc ‖f‖ * η ≤ ‖f‖ * (ε / (16 * (‖f‖ + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _)
          (norm_nonneg _)
      _ ≤ (‖f‖ + 1) * (ε / (16 * (‖f‖ + 1))) := mul_le_mul_of_nonneg_right (by linarith)
          (by positivity)
      _ = ε / 16 := by field_simp
  obtain ⟨C, hCc, hlim⟩ := hb x₀ (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  obtain ⟨g, hg1, -, hgc, hg01⟩ := exists_continuous_one_zero_of_isCompact hCc isClosed_empty
    (disjoint_empty _)
  set L := tsupport g
  have hLc : IsCompact L := hgc
  obtain ⟨g', hg'1, -, hg'c, hg'01⟩ := exists_continuous_one_zero_of_isCompact hLc
    isClosed_empty (disjoint_empty _)
  obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds x₀
  have hgev := eventually_dist_lt_of_eChain he g.continuous hgc hNc hNx hη
  have hhc : Continuous fun y => f y * g' y := f.continuous.mul g'.continuous
  have hhcs : HasCompactSupport fun y => f y * g' y := hg'c.mul_left
  have hhev := eventually_dist_lt_of_eChain he hhc hhcs hNc hNx (half_pos hε)
  -- large `k`: `Pᵏ(x₀, C) > 1 − 2η`
  have h2 : ENNReal.ofReal (1 - 2 * η) < atTop.liminf fun k : ℕ => (P ^ k) x₀ C := by
    refine lt_of_lt_of_le ?_ hlim
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hη.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf h2)
  -- small `k`: continuity of each `Pᵏ f`
  have hfin : ∀ᶠ x in 𝓝 x₀, ∀ k ∈ Finset.range N₀,
      dist (∫ y, f y ∂(P ^ k) x₀) (∫ y, f y ∂(P ^ k) x) < ε :=
    (Finset.eventually_all _).2 fun k _ => by
      have := isMarkovKernel_pow P k
      have hc := ((proposition_6_1_1_i_weak (P ^ k)).1 (hP.pow k) f).tendsto x₀
      filter_upwards [hc (Metric.ball_mem_nhds _ hε)] with x hx
      rw [dist_comm]; exact hx
  filter_upwards [hgev, hhev, hfin] with x hgx hhx hfx k
  by_cases hk : k < N₀
  · exact hfx k (Finset.mem_range.2 hk)
  have hpk := isMarkovKernel_pow P k
  have hgm : Measurable fun y => g y := g.continuous.measurable
  have hgL : ∀ y, g y ≠ 0 → y ∈ L := fun y hy => subset_tsupport _ hy
  have hLm : MeasurableSet L := hLc.isClosed.measurableSet
  -- the mass outside `L`
  have hC0 : 1 - 2 * η < ((P ^ k) x₀).real C := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)).1
      (hN₀ k (not_lt.1 hk))
  obtain ⟨b0, b0'⟩ := integral_bump_bounds (μ := (P ^ k) x₀) hgm hg01 hCc.measurableSet hLm hg1
    hgL
  obtain ⟨-, bx'⟩ := integral_bump_bounds (μ := (P ^ k) x) hgm hg01 hCc.measurableSet hLm hg1
    hgL
  have hL0 : ((P ^ k) x₀).real Lᶜ ≤ 3 * η := by
    rw [probReal_compl_eq_one_sub hLm]; linarith
  have hLx : ((P ^ k) x).real Lᶜ ≤ 3 * η := by
    rw [probReal_compl_eq_one_sub hLm]
    have := hgx k
    rw [Real.dist_eq, abs_lt] at this
    linarith
  -- split `f = f g' + f(1 − g')`
  have hsplit : ∀ z : X, ∫ y, f y ∂(P ^ k) z =
      ∫ y, f y * g' y ∂(P ^ k) z + ∫ y, (f y - f y * g' y) ∂(P ^ k) z := fun z => by
    have hi1 : Integrable (fun y => f y * g' y) ((P ^ k) z) :=
      Integrable.of_bound hhc.aestronglyMeasurable ‖f‖ (Eventually.of_forall fun y => by
        rw [norm_mul]
        calc ‖f y‖ * ‖g' y‖ ≤ ‖f‖ * 1 := mul_le_mul (f.norm_coe_le_norm y)
              (by rw [Real.norm_eq_abs, abs_of_nonneg (hg'01 y).1]; exact (hg'01 y).2)
              (norm_nonneg _) (norm_nonneg _)
          _ = ‖f‖ := mul_one _)
    rw [integral_sub (f.integrable _) hi1]
    ring
  have ht0 := abs_integral_tail_le (μ := (P ^ k) x₀) f hg'01 hLm hg'1
  have htx := abs_integral_tail_le (μ := (P ^ k) x) f hg'01 hLm hg'1
  rw [hsplit x₀, hsplit x, Real.dist_eq]
  have hh := hhx k
  rw [Real.dist_eq] at hh
  calc |∫ y, f y * g' y ∂(P ^ k) x₀ + ∫ y, (f y - f y * g' y) ∂(P ^ k) x₀ -
        (∫ y, f y * g' y ∂(P ^ k) x + ∫ y, (f y - f y * g' y) ∂(P ^ k) x)|
      ≤ |∫ y, f y * g' y ∂(P ^ k) x₀ - ∫ y, f y * g' y ∂(P ^ k) x| +
        |∫ y, (f y - f y * g' y) ∂(P ^ k) x₀| + |∫ y, (f y - f y * g' y) ∂(P ^ k) x| := by
        have := abs_sub_le (∫ y, f y * g' y ∂(P ^ k) x₀ - ∫ y, f y * g' y ∂(P ^ k) x) 0
          (∫ y, (f y - f y * g' y) ∂(P ^ k) x - ∫ y, (f y - f y * g' y) ∂(P ^ k) x₀)
        have h3 := abs_sub (∫ y, (f y - f y * g' y) ∂(P ^ k) x)
          (∫ y, (f y - f y * g' y) ∂(P ^ k) x₀)
        calc _ = |(∫ y, f y * g' y ∂(P ^ k) x₀ - ∫ y, f y * g' y ∂(P ^ k) x) -
              (∫ y, (f y - f y * g' y) ∂(P ^ k) x - ∫ y, (f y - f y * g' y) ∂(P ^ k) x₀)| := by
              congr 1; ring
          _ ≤ _ := abs_sub _ _
          _ ≤ _ := by linarith
    _ < ε / 2 + ‖f‖ * (3 * η) + ‖f‖ * (3 * η) := by
        have h4 : ‖f‖ * ((P ^ k) x₀).real Lᶜ ≤ ‖f‖ * (3 * η) :=
          mul_le_mul_of_nonneg_left hL0 (norm_nonneg _)
        have h5 : ‖f‖ * ((P ^ k) x).real Lᶜ ≤ ‖f‖ * (3 * η) :=
          mul_le_mul_of_nonneg_left hLx (norm_nonneg _)
        linarith
    _ ≤ ε := by nlinarith

/-! ### Proposition 6.4.5 -/

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [OpensMeasurableSpace X]
  in
/-- The orbit `k ↦ Pᵏ f` of a bounded continuous `f` under a weak Feller kernel, in `C(X, ℝ)`
(the dynamical system `(P, C(X), d_c)` of MT p. 142). -/
noncomputable def orbitCM {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (f : X →ᵇ ℝ) (k : ℕ) : C(X, ℝ) :=
  ⟨fun x => ∫ y, f y ∂(P ^ k) x, by
    have := isMarkovKernel_pow P k
    exact (proposition_6_1_1_i_weak (P ^ k)).1 (hP.pow k) f⟩

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [LocallyCompactSpace X]
  [BorelSpace X] in
/-- **Proposition 6.4.5** (MT p. 142): for a weak Feller chain that is bounded in probability, the
chain is an e-chain iff `(P, C(X), d_c)` is Lagrange stable, i.e. every orbit `{Pᵏ f}`,
`f ∈ C(X)`, has compact closure in the topology of uniform convergence on compact sets. The
forward direction uses `eventually_dist_lt_of_eChain_bounded` and the Arzelà–Ascoli theorem; the
converse (which needs neither boundedness in probability nor more than local compactness) is the
converse half of Ascoli's theorem (`eventually_forall_dist_lt_of_isCompact`). -/
theorem proposition_6_4_5 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hb : IsBoundedInProbability P) :
    IsEChain P ↔ ∀ f : X →ᵇ ℝ, IsCompact (closure (range (orbitCM hP f))) := by
  constructor
  · intro he f
    have hemb : IsClosedEmbedding (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
        ((⇑) : C(X, ℝ) → X → ℝ)) := by
      change IsClosedEmbedding ContinuousMap.toUniformOnFunIsCompact
      refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hemb
      (fun K _ x₀ _ U hU => ?_) (fun K _ x _ => ⟨Icc (-‖f‖) ‖f‖, isCompact_Icc, ?_⟩)
    · obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
      filter_upwards [nhdsWithin_le_nhds
        (eventually_dist_lt_of_eChain_bounded hP he hb f x₀ hε)] with x hx i
      obtain ⟨k, hk⟩ := i.2
      refine hεU ?_
      simp only [Function.comp_apply, ← hk]
      exact hx k
    · rintro _ ⟨k, rfl⟩
      have hpk := isMarkovKernel_pow P k
      have h1 := abs_kfunR_le (P ^ k) (f := f) (B := ‖f‖) (fun y => by
        rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y) x
      exact abs_le.1 h1
  · intro h f hf hfc K _ x₀ _ U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
    set F : X →ᵇ ℝ := _root_.ofCompactSupport f hf hfc
    filter_upwards [nhdsWithin_le_nhds (eventually_forall_dist_lt_of_isCompact (h F) x₀ hε)]
      with x hx k
    exact hεU (hx (orbitCM hP F k) (subset_closure ⟨k, rfl⟩))

/-! ### Proposition 6.4.3 -/

/-- The metric `d_m` of (6.16) (MT p. 140), built from a sequence `fs` of bounded continuous
functions: `d_m(μ, ν) = Σⱼ 2^{−j} |∫ fⱼ dμ − ∫ fⱼ dν|`. -/
noncomputable def dmDist [TopologicalSpace X] (fs : ℕ → X →ᵇ ℝ) (μ ν : ProbabilityMeasure X) :
    ℝ :=
  ∑' j, (1 / 2 : ℝ) ^ j * |∫ x, fs j x ∂(μ : Measure X) - ∫ x, fs j x ∂(ν : Measure X)|

/-- For `‖fⱼ‖ ≤ 1` the series defining `d_m` converges, and each term is at most `d_m`. -/
theorem term_le_dmDist [TopologicalSpace X] [OpensMeasurableSpace X] {fs : ℕ → X →ᵇ ℝ}
    (hfs : ∀ j, ‖fs j‖ ≤ 1) (μ ν : ProbabilityMeasure X) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * |∫ x, fs j x ∂(μ : Measure X) - ∫ x, fs j x ∂(ν : Measure X)| ≤
      dmDist fs μ ν := by
  have hbound : ∀ i, (1 / 2 : ℝ) ^ i *
      |∫ x, fs i x ∂(μ : Measure X) - ∫ x, fs i x ∂(ν : Measure X)| ≤ 2 * (1 / 2 : ℝ) ^ i :=
    fun i => by
      have h1 := (fs i).norm_integral_le_norm (μ := (μ : Measure X))
      have h2 := (fs i).norm_integral_le_norm (μ := (ν : Measure X))
      rw [Real.norm_eq_abs] at h1 h2
      have : |∫ x, fs i x ∂(μ : Measure X) - ∫ x, fs i x ∂(ν : Measure X)| ≤ 2 := by
        have := abs_sub (∫ x, fs i x ∂(μ : Measure X)) (∫ x, fs i x ∂(ν : Measure X))
        linarith [hfs i]
      nlinarith [show (0 : ℝ) ≤ (1 / 2) ^ i by positivity]
  have hsum : Summable fun i => (1 / 2 : ℝ) ^ i *
      |∫ x, fs i x ∂(μ : Measure X) - ∫ x, fs i x ∂(ν : Measure X)| :=
    Summable.of_nonneg_of_le (fun i => by positivity) hbound
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)
  exact hsum.le_tsum j fun i _ => by positivity

/-- `(P, M, d_m)` is **stable in the sense of Lyapunov** (MT p. 141): for every `μ`,
`sup_k d_m(νPᵏ, μPᵏ) → 0` as `ν → μ`. -/
def IsLyapunovStable [TopologicalSpace X] [OpensMeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] (fs : ℕ → X →ᵇ ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure X, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ ν in 𝓝 μ, ∀ k : ℕ, dmDist fs (orbitPM P μ k) (orbitPM P ν k) < ε

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Proposition 6.4.3**, "if" direction (MT p. 141): if `(P, M, d_m)` is Lyapunov stable, where
`d_m` is built from functions `fⱼ`, `‖fⱼ‖ ≤ 1`, that approximate every compactly supported `f`
with `‖f‖ ≤ 1` in the sup norm, then the chain is an e-chain (in fact `{Pᵏ f}` is equicontinuous
at every point). -/
theorem proposition_6_4_3_of_lyapunov {P : Kernel X X} [IsMarkovKernel P]
    {fs : ℕ → X →ᵇ ℝ} (hfs : ∀ j, ‖fs j‖ ≤ 1)
    (hdense : ∀ f : X →ᵇ ℝ, HasCompactSupport f → ‖f‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ j, ‖f - fs j‖ < ε)
    (hL : IsLyapunovStable P fs) : IsEChain P := by
  intro f hf hfc K _ x₀ _ U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  set F : X →ᵇ ℝ := _root_.ofCompactSupport f hf hfc
  set c : ℝ := ‖F‖ + 1
  have hc : 0 < c := by positivity
  set F' : X →ᵇ ℝ := c⁻¹ • F
  have hF' : ‖F'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc]
    linarith
  have hF'c : HasCompactSupport F' := hfc.smul_left (f := fun _ => c⁻¹)
  obtain ⟨j, hj⟩ := hdense F' hF'c hF' (ε / (3 * c)) (by positivity)
  have hδ : 0 < (1 / 2 : ℝ) ^ j * (ε / (3 * c)) := by positivity
  have hev := (continuous_diracProba (X := X)).tendsto x₀ |>.eventually
    (hL (diracProba x₀) _ hδ)
  refine nhdsWithin_le_nhds (hev.mono fun x hx k => hεU ?_)
  have hpk := isMarkovKernel_pow P k
  have horb : ∀ z, ((orbitPM P (diracProba z) k : ProbabilityMeasure X) : Measure X) =
      (P ^ k) z := fun z => dirac_kernel (P ^ k) z
  have h1 := (term_le_dmDist hfs _ _ j).trans_lt (hx k)
  rw [horb, horb] at h1
  have h2 : |∫ y, fs j y ∂(P ^ k) x₀ - ∫ y, fs j y ∂(P ^ k) x| < ε / (3 * c) :=
    lt_of_mul_lt_mul_left h1 (by positivity)
  have happ : ∀ z, |∫ y, F' y ∂(P ^ k) z - ∫ y, fs j y ∂(P ^ k) z| ≤ ‖F' - fs j‖ := fun z => by
    rw [← integral_sub (F'.integrable _) ((fs j).integrable _), ← Real.norm_eq_abs]
    exact (F' - fs j).norm_integral_le_norm (μ := (P ^ k) z)
  have hscale : ∀ z, ∫ y, f y ∂(P ^ k) z = c * ∫ y, F' y ∂(P ^ k) z := fun z => by
    simp only [F', BoundedContinuousFunction.coe_smul, smul_eq_mul,
      integral_const_mul, F]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rfl
  change |∫ y, f y ∂(P ^ k) x₀ - ∫ y, f y ∂(P ^ k) x| < ε
  rw [hscale, hscale, ← mul_sub, abs_mul, abs_of_pos hc]
  have h3 : |∫ y, F' y ∂(P ^ k) x₀ - ∫ y, F' y ∂(P ^ k) x| < ε / c := by
    have ha := happ x₀
    have hb := happ x
    have := abs_sub_le (∫ y, F' y ∂(P ^ k) x₀) (∫ y, fs j y ∂(P ^ k) x₀) (∫ y, F' y ∂(P ^ k) x)
    have := abs_sub_le (∫ y, fs j y ∂(P ^ k) x₀) (∫ y, fs j y ∂(P ^ k) x) (∫ y, F' y ∂(P ^ k) x)
    rw [abs_sub_comm (∫ y, fs j y ∂(P ^ k) x)] at this
    have : ε / (3 * c) * 3 = ε / c := by field_simp
    linarith
  calc c * |∫ y, F' y ∂(P ^ k) x₀ - ∫ y, F' y ∂(P ^ k) x| < c * (ε / c) :=
        mul_lt_mul_of_pos_left h3 hc
    _ = ε := by field_simp

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [OpensMeasurableSpace X] in
/-- **Uniform weak convergence over an equicontinuous family** (the step "the proof is routine"
of MT Proposition 6.4.3): if the functions `G i` are bounded by `B` and equicontinuous at every
point, and `μ(Kᶜ) < δ` is attainable for compact `K`, then `∫ G i dν → ∫ G i dμ` uniformly in
`i` as `ν → μ` weakly. The proof approximates every `G i` on a compact set by `Σⱼ G i(xⱼ) φⱼ`
for one partition of unity `(φⱼ)`. -/
theorem eventually_forall_abs_integral_sub_lt {ι : Type*} (G : ι → X →ᵇ ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i x, |G i x| ≤ B)
    (heq : ∀ x, EquicontinuousAt (fun i => ⇑(G i)) x) (μ : ProbabilityMeasure X)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧ (μ : Measure X).real Kᶜ < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν : ProbabilityMeasure X in 𝓝 μ, ∀ i,
      |∫ x, G i x ∂(ν : Measure X) - ∫ x, G i x ∂(μ : Measure X)| < ε := by
  set δ : ℝ := ε / (4 * B + 3)
  have hδ : 0 < δ := by positivity
  obtain ⟨K, hK, hKδ⟩ := htight δ hδ
  set W : X → Set X := fun x => {y | ∀ i, dist (G i x) (G i y) < δ}
  have hW : ∀ x, W x ∈ 𝓝 x := fun x => (Metric.equicontinuousAt_iff_right.1 (heq x)) δ hδ
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x => interior (W x))
    fun x _ => interior_mem_nhds.2 (hW x)
  have hcov : K ⊆ ⋃ i : t, interior (W i) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (htK hy)
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hyx⟩
  obtain ⟨φ, hsub, hcs⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space hK
    (fun i : t => interior (W i)) (fun _ => isOpen_interior) (locallyFinite_of_finite _) hcov
  set Φ : t → X →ᵇ ℝ := fun j => _root_.ofCompactSupport (φ j) (φ j).continuous (hcs j)
  have hΦ : ∀ j y, Φ j y = φ j y := fun _ _ => rfl
  have hsum1 : ∀ y ∈ K, ∑ j : t, Φ j y = 1 := fun y hy => by
    simp only [hΦ]; rw [← finsum_eq_sum_of_fintype]; exact φ.sum_eq_one hy
  have hsumle : ∀ y, ∑ j : t, Φ j y ≤ 1 := fun y => by
    simp only [hΦ]; rw [← finsum_eq_sum_of_fintype]; exact φ.sum_le_one y
  have hnn : ∀ j y, 0 ≤ Φ j y := fun j y => φ.nonneg j y
  -- the pointwise approximation
  have happrox : ∀ i y, |G i y - ∑ j : t, G i (j : X) * Φ j y| ≤ δ + B * (1 - ∑ j : t, Φ j y) := by
    intro i y
    have hsplit : G i y - ∑ j : t, G i (j : X) * Φ j y =
        G i y * (1 - ∑ j : t, Φ j y) + ∑ j : t, Φ j y * (G i y - G i (j : X)) := by
      rw [mul_sub, mul_one, Finset.mul_sum]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [mul_comm]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) |>.trans_eq (add_comm _ _)
    · have h1 : 0 ≤ 1 - ∑ j : t, Φ j y := by linarith [hsumle y]
      rw [abs_mul, abs_of_nonneg h1]
      exact mul_le_mul_of_nonneg_right (hB i y) h1
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j : t, |Φ j y * (G i y - G i (j : X))| ≤ ∑ j : t, Φ j y * δ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (hnn j y)]
            by_cases h0 : Φ j y = 0
            · rw [h0, zero_mul, zero_mul]
            · refine mul_le_mul_of_nonneg_left ?_ (hnn j y)
              have hy : y ∈ W j := interior_subset (hsub j (subset_tsupport _ h0))
              rw [← Real.dist_eq, dist_comm]
              exact (hy i).le
        _ = (∑ j : t, Φ j y) * δ := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * δ := mul_le_mul_of_nonneg_right (hsumle y) hδ.le
        _ = δ := one_mul δ
  -- integrals
  set n : ℕ := Fintype.card t
  set δ' : ℝ := δ / (n + 1)
  have hδ' : 0 < δ' := by positivity
  have hnδ : (n : ℝ) * δ' ≤ δ := by
    simp only [δ']
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hconv : ∀ᶠ ν : ProbabilityMeasure X in 𝓝 μ, ∀ j ∈ (Finset.univ : Finset t),
      |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)| < δ' :=
    (Finset.eventually_all _).2 fun j _ => by
      have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := id) (μ := μ)
        (F := 𝓝 μ)).1 tendsto_id (Φ j)
      filter_upwards [h (Metric.ball_mem_nhds _ hδ')] with ν hν
      rw [← Real.dist_eq]; exact hν
  filter_upwards [hconv] with ν hν i
  have hdecomp : ∀ ρ : ProbabilityMeasure X, ∫ x, G i x ∂(ρ : Measure X) =
      ∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ρ : Measure X) +
        ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ρ : Measure X) := fun ρ => by
    have hint : Integrable (fun x => ∑ j : t, G i (j : X) * Φ j x) (ρ : Measure X) :=
      integrable_finsetSum _ fun j _ => ((Φ j).integrable _).const_mul _
    rw [integral_sub ((G i).integrable _) hint, integral_finsetSum _ fun j _ =>
      ((Φ j).integrable _).const_mul _]
    simp_rw [integral_const_mul]
    ring
  have hA : ∀ ρ : ProbabilityMeasure X,
      |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ρ : Measure X)| ≤
        δ + B * (1 - ∑ j : t, ∫ x, Φ j x ∂(ρ : Measure X)) := fun ρ => by
    have hsumint : Integrable (fun x => ∑ j : t, Φ j x) (ρ : Measure X) :=
      integrable_finsetSum _ fun j _ => (Φ j).integrable _
    have hbint : Integrable (fun x => δ + B * (1 - ∑ j : t, Φ j x)) (ρ : Measure X) :=
      (integrable_const δ).add (((integrable_const 1).sub hsumint).const_mul B)
    calc |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ρ : Measure X)|
        ≤ ∫ x, |G i x - ∑ j : t, G i (j : X) * Φ j x| ∂(ρ : Measure X) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, (δ + B * (1 - ∑ j : t, Φ j x)) ∂(ρ : Measure X) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hbint
            (Eventually.of_forall fun y => happrox i y)
      _ = δ + B * (1 - ∑ j : t, ∫ x, Φ j x ∂(ρ : Measure X)) := by
          rw [integral_add (f := fun _ => δ) (g := fun x => B * (1 - ∑ j : t, Φ j x))
              (integrable_const δ) (((integrable_const 1).sub hsumint).const_mul B),
            integral_const, integral_const_mul, integral_sub (integrable_const 1) hsumint,
            integral_const, integral_finsetSum _ fun j _ => (Φ j).integrable _]
          simp
  -- the mass off `K`
  have hμK : 1 - ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X) < δ := by
    have hsumint : Integrable (fun x => ∑ j : t, Φ j x) (μ : Measure X) :=
      integrable_finsetSum _ fun j _ => (Φ j).integrable _
    have h1 : 1 - ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X) =
        ∫ x, (1 - ∑ j : t, Φ j x) ∂(μ : Measure X) := by
      rw [integral_sub (integrable_const 1) hsumint, integral_const,
        integral_finsetSum _ fun j _ => (Φ j).integrable _]
      simp
    rw [h1]
    refine lt_of_le_of_lt ?_ hKδ
    rw [← integral_indicator_one hK.isClosed.measurableSet.compl]
    refine integral_mono ((integrable_const 1).sub hsumint)
      ((integrable_const 1).indicator hK.isClosed.measurableSet.compl) fun y => ?_
    by_cases hy : y ∈ K
    · rw [hsum1 y hy, indicator_of_notMem (show y ∉ Kᶜ from not_not.2 hy)]; simp
    · rw [indicator_of_mem (show y ∈ Kᶜ from hy), Pi.one_apply]
      linarith [Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset t)) => hnn j y]
  have hdiff : ∑ j : t, |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)| ≤ δ := by
    calc ∑ j : t, |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)|
        ≤ ∑ _j : t, δ' := Finset.sum_le_sum fun j hj => (hν j hj).le
      _ = n * δ' := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ δ := hnδ
  have hνK : 1 - ∑ j : t, ∫ x, Φ j x ∂(ν : Measure X) ≤
      (1 - ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X)) + δ := by
    have : ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X) - ∑ j : t, ∫ x, Φ j x ∂(ν : Measure X) ≤ δ := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.sum_le_sum fun j _ => ?_).trans hdiff
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hmid : |∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
      ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X)| ≤ B * δ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : t, |G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
          G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X)|
        = ∑ j : t, |G i (j : X)| *
          |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)| := by
          simp_rw [← mul_sub, abs_mul]
      _ ≤ ∑ j : t, B * |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB i j) (abs_nonneg _)
      _ = B * ∑ j : t, |∫ x, Φ j x ∂(ν : Measure X) - ∫ x, Φ j x ∂(μ : Measure X)| :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ B * δ := mul_le_mul_of_nonneg_left hdiff hB0
  rw [hdecomp ν, hdecomp μ]
  have hAν := hA ν
  have hAμ := hA μ
  have h4 : |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ν : Measure X) +
      ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
      (∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(μ : Measure X) +
      ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X))| ≤
      |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ν : Measure X)| +
      |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(μ : Measure X)| +
      |∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
        ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X)| := by
    have := abs_add_three (∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ν : Measure X))
      (-∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(μ : Measure X))
      (∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
        ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X))
    rw [abs_neg] at this
    calc _ = |∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(ν : Measure X) +
          -∫ x, (G i x - ∑ j : t, G i (j : X) * Φ j x) ∂(μ : Measure X) +
          (∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(ν : Measure X) -
            ∑ j : t, G i (j : X) * ∫ x, Φ j x ∂(μ : Measure X))| := by congr 1; ring
      _ ≤ _ := this
  have hεδ : 2 * δ + 4 * B * δ < ε := by
    have : δ * (4 * B + 3) = ε := by simp only [δ]; field_simp
    nlinarith
  calc _ ≤ _ := h4
    _ ≤ (δ + B * (1 - ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X) + δ)) +
        (δ + B * (1 - ∑ j : t, ∫ x, Φ j x ∂(μ : Measure X))) + B * δ := by
        gcongr
        · exact hAν.trans (by gcongr)
    _ ≤ (δ + B * (δ + δ)) + (δ + B * δ) + B * δ := by
        gcongr
    _ = 2 * δ + 4 * B * δ := by ring
    _ < ε := hεδ

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
/-- On a locally compact second-countable Hausdorff space, a probability measure gives mass
less than `δ` to the complement of some compact set (along a compact exhaustion). -/
theorem exists_isCompact_measureReal_compl_lt (μ : ProbabilityMeasure X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set X, IsCompact K ∧ (μ : Measure X).real Kᶜ < δ := by
  let Kx : CompactExhaustion X := CompactExhaustion.choice X
  have ht := tendsto_measure_iInter_atTop (μ := (μ : Measure X)) (s := fun m => (Kx m)ᶜ)
    (fun m => (Kx.isCompact m).measurableSet.compl.nullMeasurableSet)
    (fun a b hab => compl_subset_compl.2 (Kx.subset hab)) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ m, (Kx m)ᶜ) = ∅ := by rw [← compl_iUnion, Kx.iUnion_eq, compl_univ]
  rw [hempty, measure_empty] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))).exists
  refine ⟨Kx m, Kx.isCompact m, ?_⟩
  rw [measureReal_def]
  exact (ENNReal.toReal_lt_of_lt_ofReal hm)

/-- The terms of `d_m` are summable when `‖fⱼ‖ ≤ 1`, with the tail beyond `J` at most
`4 · 2^{−J}`. -/
theorem dm_terms_le [TopologicalSpace X] [OpensMeasurableSpace X] {fs : ℕ → X →ᵇ ℝ}
    (hfs : ∀ j, ‖fs j‖ ≤ 1) (μ ν : ProbabilityMeasure X) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * |∫ x, fs j x ∂(μ : Measure X) - ∫ x, fs j x ∂(ν : Measure X)| ≤
      2 * (1 / 2 : ℝ) ^ j := by
  have h1 := (fs j).norm_integral_le_norm (μ := (μ : Measure X))
  have h2 := (fs j).norm_integral_le_norm (μ := (ν : Measure X))
  rw [Real.norm_eq_abs] at h1 h2
  have : |∫ x, fs j x ∂(μ : Measure X) - ∫ x, fs j x ∂(ν : Measure X)| ≤ 2 := by
    have := abs_sub (∫ x, fs j x ∂(μ : Measure X)) (∫ x, fs j x ∂(ν : Measure X))
    linarith [hfs j]
  nlinarith [show (0 : ℝ) ≤ (1 / 2) ^ j by positivity]

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
/-- **Proposition 6.4.3** (MT p. 141; the book omits the proof): with `d_m` built from compactly
supported `fⱼ`, `‖fⱼ‖ ≤ 1`, approximating every compactly supported `f` with `‖f‖ ≤ 1`, the chain
is an e-chain iff `(P, M, d_m)` is stable in the sense of Lyapunov. -/
theorem proposition_6_4_3 {P : Kernel X X} [IsMarkovKernel P] {fs : ℕ → X →ᵇ ℝ}
    (hfs : ∀ j, ‖fs j‖ ≤ 1) (hcs : ∀ j, HasCompactSupport (fs j))
    (hdense : ∀ f : X →ᵇ ℝ, HasCompactSupport f → ‖f‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ j, ‖f - fs j‖ < ε) :
    IsEChain P ↔ IsLyapunovStable P fs := by
  refine ⟨fun he μ ε hε => ?_, proposition_6_4_3_of_lyapunov hfs hdense⟩
  have hpk : ∀ k, IsMarkovKernel (P ^ k) := isMarkovKernel_pow P
  -- equicontinuity at every point of `{Pᵏ fⱼ}`
  have heqat : ∀ j x₀, EquicontinuousAt (fun k : ℕ => fun x => ∫ y, fs j y ∂(P ^ k) x) x₀ :=
    fun j x₀ => by
      obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds x₀
      exact Metric.equicontinuousAt_iff_right.2 fun δ hδ =>
        eventually_dist_lt_of_eChain he (fs j).continuous (hcs j) hNc hNx hδ
  have hbd : ∀ j k x, |∫ y, fs j y ∂(P ^ k) x| ≤ 1 := fun j k x => by
    have := (fs j).norm_integral_le_norm (μ := (P ^ k) x)
    rw [Real.norm_eq_abs] at this; exact this.trans (hfs j)
  set G : ℕ → ℕ → X →ᵇ ℝ := fun j k => BoundedContinuousFunction.mkOfBound
    ⟨fun x => ∫ y, fs j y ∂(P ^ k) x, continuous_iff_continuousAt.2 fun x =>
      (heqat j x).continuousAt k⟩ 2 fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have := abs_sub (∫ z, fs j z ∂(P ^ k) x) (∫ z, fs j z ∂(P ^ k) y)
        linarith [hbd j k x, hbd j k y]
  have hGapp : ∀ j k x, G j k x = ∫ y, fs j y ∂(P ^ k) x := fun _ _ _ => rfl
  -- the tail
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 4 * (1 / 2 : ℝ) ^ J < ε / 2 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 4
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (half_pos hε))).exists
  have hev : ∀ᶠ ν : ProbabilityMeasure X in 𝓝 μ, ∀ j ∈ Finset.range J, ∀ k,
      |∫ x, G j k x ∂(ν : Measure X) - ∫ x, G j k x ∂(μ : Measure X)| < ε / 4 :=
    (Finset.eventually_all _).2 fun j _ =>
      eventually_forall_abs_integral_sub_lt (G j) zero_le_one (fun k x => hbd j k x)
        (fun x => heqat j x) μ (fun δ hδ => exists_isCompact_measureReal_compl_lt μ hδ)
        (by positivity)
  filter_upwards [hev] with ν hν k
  have hcomp : ∀ (ρ : ProbabilityMeasure X) j, ∫ x, fs j x ∂(orbitPM P ρ k : Measure X) =
      ∫ x, G j k x ∂(ρ : Measure X) := fun ρ j => by
    change ∫ x, fs j x ∂((P ^ k : Kernel X X) ∘ₘ (ρ : Measure X)) = _
    rw [integral_comp_measure (P ^ k) _ ((fs j).integrable _)]
    rfl
  set a : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j *
    |∫ x, fs j x ∂(orbitPM P μ k : Measure X) - ∫ x, fs j x ∂(orbitPM P ν k : Measure X)|
  have ha : ∀ j, a j ≤ 2 * (1 / 2 : ℝ) ^ j := fun j => dm_terms_le hfs _ _ j
  have ha0 : ∀ j, 0 ≤ a j := fun j => by positivity
  have hsum : Summable a := Summable.of_nonneg_of_le ha0 ha
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)
  change ∑' j, a j < ε
  rw [← hsum.sum_add_tsum_nat_add J]
  have hhead : ∑ j ∈ Finset.range J, a j ≤ ε / 2 := by
    calc ∑ j ∈ Finset.range J, a j ≤ ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * (ε / 4) :=
          Finset.sum_le_sum fun j hj => by
            simp only [a, hcomp]
            rw [abs_sub_comm]
            exact mul_le_mul_of_nonneg_left (hν j hj k).le (by positivity)
      _ = (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j) * (ε / 4) := (Finset.sum_mul _ _ _).symm
      _ ≤ 2 * (ε / 4) := by
          gcongr
          calc ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j ≤ ∑' j, (1 / 2 : ℝ) ^ j :=
                (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
                  fun _ _ => by positivity
            _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ = ε / 2 := by ring
  have htail : ∑' j, a (j + J) ≤ 4 * (1 / 2 : ℝ) ^ J := by
    calc ∑' j, a (j + J) ≤ ∑' j, 2 * (1 / 2 : ℝ) ^ (j + J) :=
          Summable.tsum_le_tsum (fun j => ha (j + J)) ((summable_nat_add_iff J).2 hsum)
            ((summable_nat_add_iff J).2
              ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2))
      _ = 4 * (1 / 2 : ℝ) ^ J := by
          simp_rw [pow_add]
          rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num)
            (by norm_num)]
          ring
  linarith

end MeynTweedie.DriftRegularity
