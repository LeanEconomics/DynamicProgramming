/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FellerChains

/-!
# T-chains (MT §6.2.1–6.2.2)

Meyn and Tweedie, §6.2.1–6.2.2, pp. 130–132.

* `IsContinuousComponent P a T` (p. 124, (ii)): `T` is substochastic, `T ≤ K_a`, and `T(·, A)` is
  lower semicontinuous for every measurable `A`. `IsTChain P` (p. 124, (iii)): some `K_a` has a
  continuous component with `T(x, X) > 0` everywhere.
* `lsc_lintegral_of_lsc_sets`: such a `T` integrates every measurable `f ≥ 0` to a lower
  semicontinuous `T(·, f)` (used for `T K_{a_ε}(·, A)` and `T(·, s)` in the book).
* `hitProb_pos_of_pow_sampled`: `Pⁿ⁺¹(y, {K_a(·, A) > 0}) > 0` implies `L(y, A) > 0`.
* **Proposition 6.2.1** (`proposition_6_2_1`, p. 130): a T-chain with a reachable point `x*` is
  `T(x*, ·)`-irreducible. The statement only needs `T ≤ K_a` with `T(·, A)` lower
  semicontinuous.
* **Proposition 6.2.2** (`proposition_6_2_2`, p. 130): an open set irreducible T-chain is
  `ψ`-irreducible.
* **Proposition 6.2.3** (`proposition_6_2_3`, p. 131): an open `ν_a`-petite set `A` gives the
  continuous component `T(x, B) = 1_A(x) ν(B)` of `K_a`, non-trivial on `A`.
* `mixKernel`, `mixSampling`, `sampledKernel_mixSampling`: the mixtures `Σ 2^{-k} T_k` and
  `Σ 2^{-k} a_k` of the proof of Proposition 6.2.4 (here with weights `2^{-(k+1)}`).
* **Proposition 6.2.4** (`proposition_6_2_4`, p. 131): continuous components non-trivial at each
  point combine into a T-chain (Lindelöf's theorem, via second countability).
* **Theorem 6.2.5** (p. 131): (i) `theorem_6_2_5_i`, on a locally compact second-countable space,
  if every compact set is petite then `P` is a T-chain; (ii) `theorem_6_2_5_ii`, every compact set
  is petite for a `ψ`-irreducible T-chain, and `theorem_6_2_5_ii_openSet` for an open set
  irreducible T-chain.
* `exists_continuous_pos_le_of_lsc`: on a pseudo-metrizable space an everywhere positive lower
  semicontinuous function dominates an everywhere positive continuous function (the step "it
  dominates an everywhere positive continuous function" of the proof of Proposition 6.2.6).
* **Proposition 6.2.6** (`proposition_6_2_6`, p. 132): for a `ψ`-irreducible T-chain,
  `K_b(x, B) ≥ s(x) ψ_b(B)` with `s` continuous and positive and `ψ_b` maximal.

**Hypotheses.** Theorem 6.2.5 (ii) and Proposition 6.2.6 use Theorem 5.2.2 and Proposition
5.5.5, hence a countably generated σ-algebra (true for the Borel σ-algebra of a second-countable
space); Theorem 6.2.5 (ii) also uses that compact sets are measurable (Hausdorff space).
Theorem 6.2.5 (i) uses local compactness where the book says "since X is σ-compact".

**Corrections.** None.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Continuous components and T-chains -/

variable [TopologicalSpace X] in
/-- `T` is a **continuous component** of `K_a` (MT p. 124, (ii)): a substochastic kernel with
`T ≤ K_a` such that `T(·, A)` is lower semicontinuous for every measurable `A`. -/
def IsContinuousComponent (P : Kernel X X) (a : ℕ → ℝ≥0∞) (T : Kernel X X) : Prop :=
  IsSubstochasticKernel T ∧ (∀ x, T x ≤ sampledKernel P a x) ∧
    ∀ A, MeasurableSet A → LowerSemicontinuous fun x => T x A

variable [TopologicalSpace X] in
/-- `P` is a **T-chain** (MT p. 124, (iii)): for some sampling distribution `a`, `K_a` has a
continuous component `T` with `T(x, X) > 0` for every `x`. -/
def IsTChain (P : Kernel X X) : Prop :=
  ∃ a T, IsSamplingDist a ∧ IsContinuousComponent P a T ∧ ∀ x, 0 < T x univ

variable [TopologicalSpace X] in
/-- A kernel whose sets `T(·, A)` are all lower semicontinuous integrates every measurable
`f ≥ 0` to a lower semicontinuous function (approximate `f` by simple functions). -/
theorem lsc_lintegral_of_lsc_sets {T : Kernel X X}
    (hT : ∀ A, MeasurableSet A → LowerSemicontinuous fun x => T x A) {f : X → ℝ≥0∞}
    (hf : Measurable f) : LowerSemicontinuous fun x => ∫⁻ y, f y ∂T x := by
  have : (fun x => ∫⁻ y, f y ∂T x) = fun x => ⨆ n, (SimpleFunc.eapprox f n).lintegral (T x) := by
    ext x; exact lintegral_eq_iSup_eapprox_lintegral hf
  rw [this]
  refine lowerSemicontinuous_iSup fun n => ?_
  simp only [SimpleFunc.lintegral]
  exact lowerSemicontinuous_sum fun c _ =>
    lowerSemicontinuous_const_mul (hT _ (SimpleFunc.measurableSet_fiber _ c)) c

/-- If `Pⁿ⁺¹(y, ·)` charges the set where `K_a(·, A) > 0`, then `L(y, A) > 0`. -/
theorem hitProb_pos_of_pow_sampled (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    {A : Set X} (hA : MeasurableSet A) {y : X} {n : ℕ}
    (h : 0 < (P ^ (n + 1)) y {w | 0 < sampledKernel P a w A}) : 0 < hitProb P A y := by
  have h1 : 0 < ∫⁻ w, sampledKernel P a w A ∂(P ^ (n + 1)) y := by
    rw [lintegral_pos_iff_support (Kernel.measurable_coe _ hA)]
    refine lt_of_lt_of_le h (measure_mono fun w hw => ?_)
    exact (pos_iff_ne_zero.1 hw)
  simp_rw [sampledKernel_apply P a _ hA] at h1
  rw [lintegral_tsum fun k => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable] at h1
  obtain ⟨k, hk⟩ : ∃ k, 0 < ∫⁻ w, a k * (P ^ k) w A ∂(P ^ (n + 1)) y := by
    by_contra hc
    push Not at hc
    exact h1.ne' (ENNReal.tsum_eq_zero.2 fun k => nonpos_iff_eq_zero.1 (hc k))
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA),
    ← Kernel.pow_add_apply_eq_lintegral P (n + 1) k y hA] at hk
  refine (hitProb_pos_iff P hA y).2 ⟨n + k, ?_⟩
  rw [show n + k + 1 = n + 1 + k by omega]
  exact pos_of_mul_pos_right hk zero_le

/-! ### Proposition 6.2.1 and 6.2.2 -/

variable [TopologicalSpace X] in
/-- **Proposition 6.2.1** (MT p. 130): if `T` is an everywhere non-trivial continuous component of
`K_a` and `x*` is reachable, the chain is `T(x*, ·)`-irreducible. -/
theorem proposition_6_2_1 {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} {T : Kernel X X}
    (hT : IsContinuousComponent P a T) {x₀ : X} (hx : IsReachable P x₀) :
    IsPhiIrreducible P (T x₀) := by
  intro A hA hpos y
  have hO : IsOpen {w | 0 < T w A} := (hT.2.2 A hA).isOpen_preimage 0
  have hOm : MeasurableSet {w | 0 < T w A} :=
    measurableSet_lt measurable_const (Kernel.measurable_coe T hA)
  obtain ⟨n, hn⟩ := (potKernel_pos_iff P hOm y).1 (hx _ hO hpos y)
  refine hitProb_pos_of_pow_sampled P hA (a := a) (n := n) (lt_of_lt_of_le hn
    (measure_mono fun w hw => ?_))
  exact lt_of_lt_of_le hw (hT.2.1 w A)

variable [TopologicalSpace X] in
/-- **Proposition 6.2.2** (MT p. 130): an open set irreducible T-chain is `ψ`-irreducible for a
nonzero `ψ`. -/
theorem proposition_6_2_2 [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hP : IsTChain P)
    (hirr : IsOpenSetIrreducible P) : ∃ ψ : Measure X, ψ ≠ 0 ∧ IsPhiIrreducible P ψ := by
  obtain ⟨a, T, -, hT, hpos⟩ := hP
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨T x, fun h => ?_, proposition_6_2_1 hT (hirr x)⟩
  have := hpos x
  rw [h] at this
  simp at this

/-! ### Petite sets and continuous components -/

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Proposition 6.2.3** (MT p. 131): if an open set `A` is `ν_a`-petite, then
`T(x, B) = 1_A(x) ν(B)` is a continuous component of `K_a`, non-trivial on `A`. -/
theorem proposition_6_2_3 {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} {ν : Measure X}
    {A : Set X} (hA : IsOpen A) (hpet : IsPetiteSet P a ν A) :
    ∃ T : Kernel X X, IsContinuousComponent P a T ∧ ∀ x ∈ A, 0 < T x univ := by
  classical
  have hK := isMarkovKernel_sampledKernel P hpet.2.1
  let T : Kernel X X := Kernel.piecewise hA.measurableSet (Kernel.const X ν) 0
  have hTx : ∀ x, T x = if x ∈ A then ν else 0 := fun x => by
    simp [T, Kernel.piecewise_apply]
  refine ⟨T, ⟨fun x => ?_, fun x => ?_, fun B hB => ?_⟩, fun x hx => ?_⟩
  · rw [hTx]
    split_ifs with hx
    · exact (hpet.2.2.2 x hx univ).trans prob_le_one
    · simp
  · rw [hTx]
    split_ifs with hx
    · exact hpet.2.2.2 x hx
    · exact Measure.zero_le _
  · have : (fun x => T x B) = A.indicator fun _ => ν B := by
      ext x; rw [hTx]; by_cases hx : x ∈ A <;> simp [hx]
    rw [this]
    exact hA.lowerSemicontinuous_indicator zero_le
  · rw [hTx]
    simp only [hx, ↓reduceIte]
    exact pos_iff_ne_zero.2 fun h => hpet.2.2.1 (Measure.measure_univ_eq_zero.1 h)

/-- The mixture `Σₖ cₖ Tₖ` of a sequence of kernels. -/
noncomputable def mixKernel (c : ℕ → ℝ≥0∞) (T : ℕ → Kernel X X) : Kernel X X where
  toFun x := Measure.sum fun k => c k • T k x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum fun k => (Kernel.measurable_coe _ hs).const_mul _

/-- `(Σₖ cₖ Tₖ)(x, A) = Σₖ cₖ Tₖ(x, A)`. -/
theorem mixKernel_apply (c : ℕ → ℝ≥0∞) (T : ℕ → Kernel X X) (x : X) {A : Set X}
    (hA : MeasurableSet A) : mixKernel c T x A = ∑' k, c k * T k x A := by
  change (Measure.sum fun k => c k • T k x) A = _
  rw [Measure.sum_apply _ hA]
  rfl

/-- The mixture `Σₖ cₖ aₖ` of sampling distributions. -/
noncomputable def mixSampling (c : ℕ → ℝ≥0∞) (a : ℕ → ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' k, c k * a k n

/-- `K_{Σ cₖ aₖ} = Σₖ cₖ K_{aₖ}`. -/
theorem sampledKernel_mixSampling (P : Kernel X X) (c : ℕ → ℝ≥0∞) (a : ℕ → ℕ → ℝ≥0∞) (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    sampledKernel P (mixSampling c a) x A = ∑' k, c k * sampledKernel P (a k) x A := by
  simp_rw [sampledKernel_apply P _ x hA, mixSampling, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

/-- A mixture of sampling distributions with weights summing to one is a sampling
distribution. -/
theorem isSamplingDist_mixSampling {c : ℕ → ℝ≥0∞} (hc : IsSamplingDist c)
    {a : ℕ → ℕ → ℝ≥0∞} (ha : ∀ k, IsSamplingDist (a k)) : IsSamplingDist (mixSampling c a) := by
  unfold IsSamplingDist mixSampling at *
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, ha, mul_one, hc]

variable [TopologicalSpace X] [SecondCountableTopology X] in
/-- **Proposition 6.2.4** (MT p. 131): if every `x` has a sampling distribution `aₓ` and a
continuous component `Tₓ` of `K_{aₓ}` with `Tₓ(x, X) > 0`, then `P` is a T-chain. The proof uses
Lindelöf's theorem, here through second countability. -/
theorem proposition_6_2_4 {P : Kernel X X}
    (h : ∀ x, ∃ a T, IsSamplingDist a ∧ IsContinuousComponent P a T ∧ 0 < T x univ) :
    IsTChain P := by
  choose a T ha hT hpos using h
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨diracDist 0, 0, isSamplingDist_diracDist 0, ⟨fun x => isEmptyElim x,
      fun x => isEmptyElim x, fun A _ => fun x => isEmptyElim x⟩, fun x => isEmptyElim x⟩
  set O : X → Set X := fun x => {y | 0 < T x y univ}
  have hO : ∀ x, IsOpen (O x) := fun x => ((hT x).2.2 univ MeasurableSet.univ).isOpen_preimage 0
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcover : ⋃ x ∈ S, O x = univ :=
    hSU.trans (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hpos x⟩)
  have hSne : S.Nonempty := by
    obtain ⟨x⟩ := hX
    have : x ∈ ⋃ x ∈ S, O x := hcover ▸ mem_univ x
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 this
    exact ⟨y, hy⟩
  obtain ⟨e, he⟩ := hS.exists_eq_range hSne
  set c : ℕ → ℝ≥0∞ := geomDist 2⁻¹
  have hc : IsSamplingDist c := isSamplingDist_geomDist_half
  have hcpos : ∀ k, 0 < c k := fun k => ENNReal.mul_pos (by simp) (by simp)
  have hc1 : ∀ k, c k ≤ 1 := fun k => hc ▸ ENNReal.le_tsum k
  refine ⟨mixSampling c fun k => a (e k), mixKernel c fun k => T (e k),
    isSamplingDist_mixSampling hc fun k => ha (e k), ⟨fun x => ?_, fun x => ?_, fun A hA => ?_⟩,
    fun x => ?_⟩
  · rw [mixKernel_apply c _ x MeasurableSet.univ]
    calc ∑' k, c k * T (e k) x univ ≤ ∑' k, c k * 1 :=
          ENNReal.tsum_le_tsum fun k => mul_le_mul_right ((hT (e k)).1 x) _
      _ = 1 := by simp_rw [mul_one]; exact hc
  · refine Measure.le_intro fun B hB _ => ?_
    rw [mixKernel_apply c _ x hB, sampledKernel_mixSampling P c _ x hB]
    exact ENNReal.tsum_le_tsum fun k => mul_le_mul_right ((hT (e k)).2.1 x B) _
  · have : (fun x => mixKernel c (fun k => T (e k)) x A) =
        fun x => ∑' k, c k * T (e k) x A := by
      ext x; exact mixKernel_apply c _ x hA
    rw [this]
    exact lowerSemicontinuous_tsum fun k => lowerSemicontinuous_const_mul ((hT (e k)).2.2 A hA) _
  · have : x ∈ ⋃ x ∈ S, O x := hcover ▸ mem_univ x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 this
    rw [he] at hy
    obtain ⟨k, rfl⟩ := hy
    rw [mixKernel_apply c _ x MeasurableSet.univ]
    exact lt_of_lt_of_le (ENNReal.mul_pos (hcpos k).ne' (ne_of_gt hxy))
      (ENNReal.le_tsum (f := fun k => c k * T (e k) x univ) k)

/-! ### Theorem 6.2.5 -/

variable [TopologicalSpace X] [OpensMeasurableSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 6.2.5 (i)** (MT p. 131): on a locally compact second-countable space, if every
compact set is petite then `P` is a T-chain. -/
theorem theorem_6_2_5_i {P : Kernel X X} [IsMarkovKernel P]
    (h : ∀ K : Set X, IsCompact K → IsPetite P K) : IsTChain P := by
  refine proposition_6_2_4 fun x => ?_
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨a, ν, hpet⟩ := h K hKc
  have hint : IsPetiteSet P a ν (interior K) := ⟨isOpen_interior.measurableSet, hpet.2.1,
    hpet.2.2.1, fun y hy => hpet.2.2.2 y (interior_subset hy)⟩
  obtain ⟨T, hT, hTpos⟩ := proposition_6_2_3 isOpen_interior hint
  exact ⟨a, T, hpet.2.1, hT, hTpos x (mem_interior_iff_mem_nhds.2 hKx)⟩

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 6.2.5 (ii)** (MT p. 131): if a T-chain is `ψ`-irreducible for a nonzero `ψ` (on a
countably generated Hausdorff space), every compact set is petite. -/
theorem theorem_6_2_5_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) (hψ0 : ψ ≠ 0) (hP : IsTChain P) {K : Set X} (hK : IsCompact K) :
    IsPetite P K := by
  obtain ⟨a, T, ha, hT, hTpos⟩ := hP
  have hmax := isMaximalIrreducibility_maxIrrMeasure P hψ hψ0
  have hψu : 0 < maxIrrMeasure P ψ univ :=
    pos_iff_ne_zero.2 fun h => hmax.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hmax MeasurableSet.univ hψu
  have hKpos : ∀ y, 0 < resolventHalf P y C := fun y =>
    (proposition_4_2_1 P _).2.2.1 hmax.2.1 C hC.1 hψC y
  set g : X → ℝ≥0∞ := fun x => ∫⁻ y, resolventHalf P y C ∂T x
  have hg : LowerSemicontinuous g := lsc_lintegral_of_lsc_sets hT.2.2
    (Kernel.measurable_coe _ hC.1)
  have hgpos : ∀ x, 0 < g x := fun x => lintegral_pos_of_pos
    (fun h0 => by have := hTpos x; rw [h0] at this; simp at this)
    (Kernel.measurable_coe _ hC.1) hKpos
  have hge : ∀ x, g x ≤ sampledKernel P (sampleConv a (geomDist 2⁻¹)) x C := fun x => by
    rw [lemma_5_5_2_i P _ _ x hC.1, sampledKernel_geomDist_half]
    exact lintegral_mono' (hT.2.1 x) le_rfl
  have hacc : SampledAccessible P (sampleConv a (geomDist 2⁻¹)) K C := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun x hx => by rw [hKe] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, -, hmin⟩ :=
        LowerSemicontinuousOn.exists_isMinOn hKne hK (hg.lowerSemicontinuousOn K)
      exact ⟨g x₀, hgpos x₀, fun x hx => (isMinOn_iff.1 hmin x hx).trans (hge x)⟩
  obtain ⟨δ, -, hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC) hK.measurableSet
    (isSamplingDist_sampleConv ha isSamplingDist_geomDist_half) hacc
  exact ⟨_, _, hpet⟩

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 6.2.5 (ii)**, second part (MT p. 131): for an open set irreducible T-chain every
compact set is petite. -/
theorem theorem_6_2_5_ii_openSet [Nonempty X] {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsTChain P) (hirr : IsOpenSetIrreducible P) {K : Set X} (hK : IsCompact K) :
    IsPetite P K := by
  obtain ⟨ψ, hψ0, hψ⟩ := proposition_6_2_2 hP hirr
  exact theorem_6_2_5_ii hψ hψ0 hP hK

/-! ### Proposition 6.2.6 -/

omit [MeasurableSpace X] in
variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- On a pseudo-metrizable space, an everywhere positive lower semicontinuous `h : X → [0, ∞]`
dominates an everywhere positive continuous real function, namely
`s(x) = inf_y (min(h(y), 1) + d(x, y))`. -/
theorem exists_continuous_pos_le_of_lsc {h : X → ℝ≥0∞} (hh : LowerSemicontinuous h)
    (hpos : ∀ x, 0 < h x) :
    ∃ s : X → ℝ, Continuous s ∧ (∀ x, 0 < s x) ∧ ∀ x, ENNReal.ofReal (s x) ≤ h x := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  set r : X → ℝ := fun y => ENNReal.truncateToReal 1 (h y)
  have hr0 : ∀ y, 0 ≤ r y := fun y => ENNReal.truncateToReal_nonneg
  have hrpos : ∀ y, 0 < r y := fun y => ENNReal.toReal_pos (ne_of_gt (lt_min one_pos (hpos y)))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  have hrlsc : LowerSemicontinuous r :=
    (ENNReal.continuous_truncateToReal ENNReal.one_ne_top).comp_lowerSemicontinuous hh
      (ENNReal.monotone_truncateToReal ENNReal.one_ne_top)
  have hbdd : ∀ x, BddBelow (range fun y => r y + dist x y) := fun x =>
    ⟨0, by rintro _ ⟨y, rfl⟩; exact add_nonneg (hr0 y) dist_nonneg⟩
  set s : X → ℝ := fun x => ⨅ y, (r y + dist x y)
  have hle : ∀ x, s x ≤ r x := fun x => by
    have := ciInf_le (hbdd x) x
    simpa using this
  refine ⟨s, ?_, fun x => ?_, fun x => ?_⟩
  · refine (LipschitzWith.of_le_add fun x y => ?_).continuous
    have : Nonempty X := ⟨x⟩
    have : ∀ z, s x - dist x y ≤ r z + dist y z := fun z => by
      have h1 := ciInf_le (hbdd x) z
      have h2 := dist_triangle x y z
      simp only [s] at h1 ⊢
      linarith
    have := le_ciInf this
    linarith
  · have : Nonempty X := ⟨x⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hrlsc x (r x / 2)
      (half_lt_self (hrpos x)))
    refine lt_of_lt_of_le (lt_min (half_pos (hrpos x)) hε) (le_ciInf fun y => ?_)
    by_cases hy : dist y x < ε
    · exact (min_le_left _ _).trans ((hball hy).le.trans (le_add_of_nonneg_right dist_nonneg))
    · rw [dist_comm] at hy
      exact (min_le_right _ _).trans ((not_lt.1 hy).trans (le_add_of_nonneg_left (hr0 y)))
  · calc ENNReal.ofReal (s x) ≤ ENNReal.ofReal (r x) := ENNReal.ofReal_le_ofReal (hle x)
      _ = min 1 (h x) := ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
      _ ≤ h x := min_le_right _ _

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 6.2.6** (MT p. 132): for a `ψ`-irreducible T-chain there are a sampling
distribution `b`, an everywhere positive continuous `s` and a maximal irreducibility measure `ψ_b`
with `K_b(x, B) ≥ s(x) ψ_b(B)`. -/
theorem proposition_6_2_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hP : IsTChain P) :
    ∃ (b : ℕ → ℝ≥0∞) (s : X → ℝ) (ψb : Measure X), IsSamplingDist b ∧ Continuous s ∧
      (∀ x, 0 < s x) ∧ IsMaximalIrreducibility P ψb ∧
      ∀ x, ENNReal.ofReal (s x) • ψb ≤ sampledKernel P b x := by
  obtain ⟨a, T, ha, hT, hTpos⟩ := hP
  obtain ⟨c, s₀, ψc, hc, hs₀, hs₀pos, hmax, hle⟩ := proposition_5_5_5_iii P hψ
  set h : X → ℝ≥0∞ := fun x => ∫⁻ y, s₀ y ∂T x
  have hh : LowerSemicontinuous h := lsc_lintegral_of_lsc_sets hT.2.2 hs₀
  have hhpos : ∀ x, 0 < h x := fun x => lintegral_pos_of_pos
    (fun h0 => by have := hTpos x; rw [h0] at this; simp at this) hs₀ hs₀pos
  obtain ⟨s, hsc, hspos, hsle⟩ := exists_continuous_pos_le_of_lsc hh hhpos
  refine ⟨sampleConv a c, s, ψc, isSamplingDist_sampleConv ha hc, hsc, hspos, hmax,
    fun x => Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, lemma_5_5_2_i P a c x hB]
  calc ENNReal.ofReal (s x) * ψc B ≤ h x * ψc B := mul_le_mul_left (hsle x) _
    _ = ∫⁻ y, s₀ y * ψc B ∂T x := (lintegral_mul_const _ hs₀).symm
    _ ≤ ∫⁻ y, sampledKernel P c y B ∂T x := lintegral_mono fun y => by
        have := hle y B
        rwa [Measure.smul_apply, smul_eq_mul] at this
    _ ≤ ∫⁻ y, sampledKernel P c y B ∂sampledKernel P a x := lintegral_mono' (hT.2.1 x) le_rfl

end MeynTweedie.FErgodicity
