/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.CompactPetite
import Epilogue.ModelLinearModels
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# e-chains (MT §6.4)

Meyn and Tweedie, §6.4, pp. 139–144. Probability measures carry Mathlib's topology of weak
convergence (`ProbabilityMeasure X`), which the book metrizes by `d_m` (6.16).

* `pushPM P μ = μP` and `integral_comp_measure`: `∫ f d(μP) = ∫ Pf dμ`.
* **Proposition 6.4.1** (`proposition_6_4_1`, p. 140): `μ ↦ μP` is continuous (so `(P, M, d_m)`
  is a dynamical system) iff `P` is weak Feller.
* `IsEChain P` (p. 140): for every continuous `f` with compact support, `{Pᵏ f}` is
  equicontinuous on every compact set.
* `equicontinuousOn_of_tendstoUniformlyOn`: a sequence of continuous functions converging
  uniformly on `K` to a continuous function is equicontinuous on `K`.
* **Proposition 6.4.2** (p. 141): **false as stated**. `proposition_6_4_2_counterexample`: the
  doubling chain (`jumpKernel 2`: from `x`, jump to `0` with probability `min(|x|, 1)`, else move
  to `2x`) is weak Feller with `Pᵏ(x, ·) → δ₀` weakly for every `x`, but is not an e-chain
  (`jumpKernel_two_pow_zero_eq_one`, `jumpKernel_two_pow_one_ge`, `tentAtOne`).
  `proposition_6_4_2_corrected`: the conclusion holds when `Pᵏ f` converges uniformly on compact
  sets to a continuous limit.
* **Proposition 6.4.6** (`proposition_6_4_6`, p. 143): the simple linear model with `|α| ≤ 1` is
  an e-chain (via (6.19), `controlMap_ar1_sub`); `randomWalk_isEChain`: so is random walk.
* `IsBoundedInProbability P` (p. 142), `orbitPM`, `IsLagrangeStable P` (orbits `{μPᵏ}`
  precompact); `isTight_orbit_of_boundedInProbability`: boundedness in probability makes every
  orbit tight.
* **Proposition 6.4.4** (`proposition_6_4_4`, p. 142): on a locally compact separable complete
  metric space, boundedness in probability is Lagrange stability (Prokhorov's theorem).

**Corrections.**
* Proposition 6.4.2: the book's proof applies Ascoli's theorem to a sequence that converges only
  pointwise; `proposition_6_4_2_counterexample` shows the statement fails, and
  `proposition_6_4_2_corrected` is the statement with uniform convergence on compact sets.
* Proposition 6.4.4: the book's "boundedness in probability is tightness of `{Pᵏ(x, ·)}`" covers
  `μ = δₓ`; for a general initial law the orbit is shown tight by Fatou's lemma along a compact
  exhaustion (`isTight_orbit_of_boundedInProbability`).

**Hypotheses.** Proposition 6.4.4 uses a complete metric (for the converse of Prokhorov's theorem
in Mathlib); a locally compact separable metrizable space admits one.

Propositions 6.4.3 and 6.4.5 are in `EChainsStability`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

/-! ### The dynamical system `(P, M)` (§6.4.1) -/

/-- The map `μ ↦ μP` on probability measures (MT §1.3.2 and p. 139). -/
noncomputable def pushPM (P : Kernel X X) [IsMarkovKernel P] (μ : ProbabilityMeasure X) :
    ProbabilityMeasure X :=
  ⟨P ∘ₘ (μ : Measure X), inferInstance⟩

/-- `∫ f d(μP) = ∫ Pf dμ` for integrable `f`. -/
theorem integral_comp_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f (P ∘ₘ μ)) :
    ∫ y, f y ∂(P ∘ₘ μ) = ∫ x, ∫ y, f y ∂P x ∂μ := by
  have h : P ∘ₘ μ = (P ∘ₖ Kernel.const Unit μ) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  rw [h] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- `δₓP = P(x, ·)` as probability measures. -/
theorem pushPM_dirac (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    ((pushPM P (diracProba x) : ProbabilityMeasure X) : Measure X) = P x := by
  change P ∘ₘ Measure.dirac x = P x
  exact dirac_kernel P x

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [OpensMeasurableSpace X]
  in
/-- **Proposition 6.4.1** (MT p. 140): `μ ↦ μP` is continuous on the probability measures with the
topology of weak convergence (so `(P, M, d_m)` is a dynamical system) iff `P` is weak Feller. -/
theorem proposition_6_4_1 (P : Kernel X X) [IsMarkovKernel P] :
    Continuous (pushPM P) ↔ IsWeakFeller P := by
  rw [proposition_6_1_1_i_weak]
  constructor
  · intro h f
    have hc : Continuous fun x => pushPM P (diracProba x) := h.comp continuous_diracProba
    refine continuous_iff_continuousAt.2 fun x => ?_
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hc.tendsto x) f
    simp only [pushPM_dirac] at ht
    exact ht
  · intro h
    refine continuous_iff_continuousAt.2 fun μ => ?_
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
    set g : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fun x => ∫ y, f y ∂P x, h f⟩
      (2 * ‖f‖) fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have h1 := abs_kfunR_le P (f := f) (B := ‖f‖) (fun y => by
          rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y) x
        have h2 := abs_kfunR_le P (f := f) (B := ‖f‖) (fun y => by
          rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y) y
        simp only [kfunR] at h1 h2
        calc |∫ z, f z ∂P x - ∫ z, f z ∂P y| ≤ |∫ z, f z ∂P x| + |∫ z, f z ∂P y| :=
              abs_sub _ _
          _ ≤ 2 * ‖f‖ := by linarith
    have hint : ∀ ν : ProbabilityMeasure X, ∫ y, f y ∂(pushPM P ν : Measure X) =
        ∫ x, g x ∂(ν : Measure X) := fun ν => by
      change ∫ y, f y ∂(P ∘ₘ (ν : Measure X)) = _
      rw [integral_comp_measure P _ (f.integrable _)]
      rfl
    simp_rw [hint]
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id g

/-! ### e-chains -/

variable [TopologicalSpace X] in
/-- `P` is **equicontinuous**, and the chain an **e-chain** (MT p. 140): for every continuous `f`
with compact support, the functions `Pᵏf`, `k ≥ 0`, are equicontinuous on every compact set. -/
def IsEChain (P : Kernel X X) : Prop :=
  ∀ f : X → ℝ, Continuous f → HasCompactSupport f → ∀ K : Set X, IsCompact K →
    EquicontinuousOn (fun k : ℕ => fun x => ∫ y, f y ∂(P ^ k) x) K

omit [MeasurableSpace X] in
/-- A sequence of functions, each continuous on `K`, converging uniformly on `K` to a function
continuous on `K`, is equicontinuous on `K` (the Ascoli step of MT p. 141, with the uniform
convergence it needs). -/
theorem equicontinuousOn_of_tendstoUniformlyOn [TopologicalSpace X] {F : ℕ → X → ℝ}
    {g : X → ℝ} {K : Set X} (hF : ∀ k, ContinuousOn (F k) K) (hg : ContinuousOn g K)
    (htu : TendstoUniformlyOn F g atTop K) : EquicontinuousOn F K := by
  intro x₀ hx₀ U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 htu (ε / 3)
    (by positivity))
  have hfin : ∀ᶠ x in 𝓝[K] x₀, ∀ k ∈ Finset.range N, dist (F k x₀) (F k x) < ε :=
    (Finset.eventually_all _).2 fun k _ => by
      have := (hF k x₀ hx₀).tendsto
      filter_upwards [this (Metric.ball_mem_nhds (F k x₀) hε)] with x hx
      rw [dist_comm]; exact hx
  have hgc : ∀ᶠ x in 𝓝[K] x₀, dist (g x₀) (g x) < ε / 3 := by
    filter_upwards [(hg x₀ hx₀).tendsto (Metric.ball_mem_nhds (g x₀)
      (show (0 : ℝ) < ε / 3 by positivity))]
      with x hx
    rw [dist_comm]; exact hx
  filter_upwards [hfin, hgc, self_mem_nhdsWithin] with x h1 h2 hxK k
  refine hεU ?_
  by_cases hk : k < N
  · exact h1 k (Finset.mem_range.2 hk)
  · have ha := hN k (not_lt.1 hk) x₀ hx₀
    have hb := hN k (not_lt.1 hk) x hxK
    calc dist (F k x₀) (F k x) ≤ dist (F k x₀) (g x₀) + dist (g x₀) (g x) + dist (g x) (F k x) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [dist_comm (F k x₀)]
          gcongr
      _ = ε := by ring

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [OpensMeasurableSpace X]
  in
/-- **Proposition 6.4.2**, corrected (MT p. 141): a weak Feller chain for which, for every
continuous `f` with compact support, `Pᵏf` converges *uniformly on compact sets* to a continuous
limit (for instance to the constant `π(f)`) is an e-chain. -/
theorem proposition_6_4_2_corrected {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → ∃ g : X → ℝ, Continuous g ∧
      ∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun k : ℕ => fun x => ∫ y, f y ∂(P ^ k) x) g atTop K) :
    IsEChain P := by
  intro f hf hfc K hK
  obtain ⟨g, hg, hu⟩ := h f hf hfc
  refine equicontinuousOn_of_tendstoUniformlyOn (fun k => ?_) hg.continuousOn (hu K hK)
  have := isMarkovKernel_pow P k
  exact ((proposition_6_1_1_i_weak (P ^ k)).1 (hP.pow k)
    (_root_.ofCompactSupport f hf hfc)).continuousOn

/-! ### The counterexample to Proposition 6.4.2: the doubling chain -/

/-- For the doubling chain (`c = 2`), once `2ᵐ |x| ≥ 1` the chain is at `0` from time `m + 1`
on. -/
theorem jumpKernel_two_pow_zero_eq_one (m : ℕ) : ∀ x : ℝ, 1 ≤ 2 ^ m * |x| → ∀ j, m + 1 ≤ j →
    (jumpKernel 2 ^ j) x {0} = 1 := by
  induction m with
  | zero =>
    intro x hx j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [jumpKernel_pow_succ_apply _ j x (measurableSet_singleton 0), jumpKernel_pow_zero_zero]
    have hq : jumpProb x = 1 := min_eq_right (by simpa using hx)
    simp [hq]
  | succ m ih =>
    intro x hx j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [jumpKernel_pow_succ_apply _ j x (measurableSet_singleton 0), jumpKernel_pow_zero_zero,
      ih (2 * x) (by rw [abs_mul, abs_two, pow_succ] at *; linarith) j (by omega), mul_one,
      mul_one, ← ENNReal.ofReal_add (jumpProb_mem x).1 (by linarith [(jumpProb_mem x).2]),
      add_sub_cancel, ENNReal.ofReal_one]

/-- A probability measure on `ℝ` with full mass at `0` is `δ₀`. -/
theorem eq_dirac_of_apply_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : μ {0} = 1) :
    μ = Measure.dirac 0 := by
  ext A hA
  have hc : μ {0}ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton 0), h, tsub_self]
  have hd : μ (A \ {0}) = 0 := measure_mono_null (sdiff_subset_compl A {0}) hc
  rw [Measure.dirac_apply' _ hA, ← measure_inter_add_sdiff A (measurableSet_singleton 0), hd,
    add_zero]
  by_cases h0 : (0 : ℝ) ∈ A
  · rw [inter_eq_right.2 (singleton_subset_iff.2 h0), h, indicator_of_mem h0]; rfl
  · rw [inter_singleton_eq_empty.2 h0, measure_empty, indicator_of_notMem h0]

/-- For the doubling chain, `Pᵏ⁺¹(2^{−(k+1)}, {1}) ≥ 1/4 + 2^{−(k+2)}`: the chain doubles its way
up to `1` with probability `∏ⱼ (1 − 2^{−j})`. -/
theorem jumpKernel_two_pow_one_ge (k : ℕ) :
    ENNReal.ofReal (1 / 4 + (1 / 2) ^ (k + 2)) ≤
      (jumpKernel 2 ^ (k + 1)) ((1 / 2) ^ (k + 1)) {1} := by
  have hone : ∀ j, (jumpKernel 2 ^ j) 0 {1} = 0 := fun j => by
    have := isMarkovKernel_jumpKernel 2
    have := isMarkovKernel_pow (jumpKernel 2) j
    refine measure_mono_null (fun y hy => ?_) (show (jumpKernel 2 ^ j) 0 {0}ᶜ = 0 by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), jumpKernel_pow_zero_zero,
        tsub_self])
    rw [mem_singleton_iff] at hy; rw [hy]; norm_num
  have hq : ∀ i, jumpProb ((1 / 2 : ℝ) ^ (i + 1)) = (1 / 2) ^ (i + 1) := fun i => by
    rw [jumpProb, abs_of_pos (by positivity)]
    exact min_eq_left (pow_le_one₀ (by norm_num) (by norm_num))
  induction k with
  | zero =>
    rw [jumpKernel_pow_succ_apply _ 0 _ (measurableSet_singleton 1), hone, mul_zero, zero_add,
      pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton 1), hq 0]
    norm_num
  | succ k ih =>
    rw [jumpKernel_pow_succ_apply _ (k + 1) _ (measurableSet_singleton 1), hone, mul_zero,
      zero_add, hq (k + 1), show (2 : ℝ) * (1 / 2) ^ (k + 1 + 1) = (1 / 2) ^ (k + 1) by ring]
    set t : ℝ := (1 / 2) ^ (k + 2)
    have ht0 : 0 ≤ t := by positivity
    have ht : t ≤ 1 / 4 := by
      simp only [t, pow_succ]
      have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    calc ENNReal.ofReal (1 / 4 + (1 / 2) ^ (k + 1 + 2))
        ≤ ENNReal.ofReal ((1 - t) * (1 / 4 + t)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : (1 / 2 : ℝ) ^ (k + 1 + 2) = t / 2 := by simp only [t]; ring
          rw [this]; nlinarith
      _ = ENNReal.ofReal (1 - t) * ENNReal.ofReal (1 / 4 + t) :=
          ENNReal.ofReal_mul (by linarith)
      _ ≤ _ := mul_le_mul_right ih _

/-- The test function `f(y) = max(0, 1 − |y − 1|)`, continuous with compact support. -/
noncomputable def tentAtOne (y : ℝ) : ℝ := max 0 (1 - |y - 1|)

/-- `f` is continuous. -/
theorem continuous_tentAtOne : Continuous tentAtOne :=
  continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs)

/-- `f` has compact support. -/
theorem hasCompactSupport_tentAtOne : HasCompactSupport tentAtOne :=
  HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2)) fun y hy => by
    simp only [mem_Icc, not_and_or, not_le] at hy
    simp only [tentAtOne, max_eq_left_iff, sub_nonpos]
    rcases hy with hy | hy
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The `k`-step law `Pᵏ(x, ·)` as a probability measure. -/
noncomputable def powPM (P : Kernel X X) [IsMarkovKernel P] (k : ℕ) (x : X) :
    ProbabilityMeasure X :=
  ⟨(P ^ k) x, by have := isMarkovKernel_pow P k; infer_instance⟩

/-- **Counterexample to Proposition 6.4.2** (MT p. 141). The doubling chain on `ℝ`, which from `x`
jumps to `0` with probability `min(|x|, 1)` and moves to `2x` otherwise, is weak Feller and
`Pᵏ(x, ·) → δ₀` weakly for every `x` (indeed `Pᵏ(x, ·) = δ₀` for large `k`), but it is not an
e-chain: points `2^{−(k+1)}` near `0` reach `1` at time `k + 1` with probability more than `1/4`,
while `0` is absorbing. The book's appeal to Ascoli's theorem needs uniform convergence on compact
sets, which pointwise convergence to a continuous limit does not give
(`proposition_6_4_2_corrected`). -/
theorem proposition_6_4_2_counterexample :
    IsWeakFeller (jumpKernel 2) ∧
      (haveI := isMarkovKernel_jumpKernel 2;
        ∀ x : ℝ, Tendsto (fun k => powPM (jumpKernel 2) k x) atTop (𝓝 (diracProba 0))) ∧
      ¬ IsEChain (jumpKernel 2) := by
  have hM := isMarkovKernel_jumpKernel 2
  set P := jumpKernel 2
  have hdirac : ∀ k x, (P ^ k) x {0} = 1 → powPM P k x = diracProba 0 := fun k x h => by
    have := isMarkovKernel_pow P k
    exact Subtype.ext (eq_dirac_of_apply_zero (μ := (P ^ k) x) h)
  refine ⟨jumpKernel_isWeakFeller 2, fun x => ?_, ?_⟩
  · by_cases hx : x = 0
    · subst hx
      have : (fun k => powPM P k 0) = fun _ => diracProba 0 :=
        funext fun k => hdirac k 0 (jumpKernel_pow_zero_zero 2 k)
      rw [this]
      exact tendsto_const_nhds
    · obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / |x|) (by norm_num : (1 : ℝ) < 2)
      have hm' : 1 ≤ 2 ^ m * |x| := by
        rw [div_lt_iff₀ (abs_pos.2 hx)] at hm; linarith
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m + 1, fun k hk => ?_⟩)
      exact (hdirac k x (jumpKernel_two_pow_zero_eq_one m x hm' k hk)).symm
  · intro h
    have hK : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
    have heq := h tentAtOne continuous_tentAtOne hasCompactSupport_tentAtOne _ hK 0
      (by norm_num) _ (Metric.dist_mem_uniformity (show (0 : ℝ) < 1 / 4 by norm_num))
    set xs : ℕ → ℝ := fun k => (1 / 2) ^ (k + 1)
    have hxs : Tendsto xs atTop (𝓝[Icc (-1) 1] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ⟨?_, ?_⟩⟩
      · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
          (tendsto_add_atTop_nat 1)
      · have : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
        linarith
      · exact pow_le_one₀ (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := (hxs.eventually heq).exists
    have h1 := hk (k + 1)
    simp only [mem_ofPred_eq] at h1
    have h0 : ∫ y, tentAtOne y ∂(P ^ (k + 1)) 0 = 0 := by
      have := isMarkovKernel_pow P (k + 1)
      rw [eq_dirac_of_apply_zero (jumpKernel_pow_zero_zero 2 (k + 1)), integral_dirac]
      simp [tentAtOne]
    have hlow : 1 / 4 + (1 / 2) ^ (k + 2) ≤ ∫ y, tentAtOne y ∂(P ^ (k + 1)) (xs k) := by
      have := isMarkovKernel_pow P (k + 1)
      have hint : Integrable tentAtOne ((P ^ (k + 1)) (xs k)) :=
        (_root_.ofCompactSupport tentAtOne continuous_tentAtOne
          hasCompactSupport_tentAtOne).integrable _
      have hnn : 0 ≤ᵐ[(P ^ (k + 1)) (xs k)] tentAtOne :=
        Eventually.of_forall fun y => le_max_left _ _
      calc 1 / 4 + (1 / 2) ^ (k + 2) ≤ ((P ^ (k + 1)) (xs k)).real {1} := by
            rw [measureReal_def]
            refine (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 ?_
            exact jumpKernel_two_pow_one_ge k
        _ = ∫ y in {1}, tentAtOne y ∂(P ^ (k + 1)) (xs k) := by
            rw [integral_singleton]; simp [tentAtOne]
        _ ≤ _ := setIntegral_le_integral hint hnn
    change dist (∫ y, tentAtOne y ∂(P ^ (k + 1)) 0)
      (∫ y, tentAtOne y ∂(P ^ (k + 1)) (xs k)) < 1 / 4 at h1
    have hpos : (0 : ℝ) < (1 / 2) ^ (k + 2) := by positivity
    rw [h0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by linarith)] at h1
    linarith

/-! ### Proposition 6.4.6: the simple linear model -/

/-- (6.19): driven by the same noise, two AR(1) paths satisfy `Xₖ(x) − Xₖ(y) = αᵏ(x − y)`. -/
theorem controlMap_ar1_sub (α : ℝ) (k : ℕ) (x y : ℝ) (u : Fin k → ℝ) :
    controlMap (fun p : ℝ × ℝ => α * p.1 + p.2) k x u -
      controlMap (fun p : ℝ × ℝ => α * p.1 + p.2) k y u = α ^ k * (x - y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [controlMap_succ, controlMap_succ]
    have := ih (Fin.init u)
    simp only at this ⊢
    rw [pow_succ]
    linear_combination α * this

/-- **Proposition 6.4.6** (MT p. 143): the simple linear model `Xₙ₊₁ = αXₙ + Wₙ₊₁` with
`|α| ≤ 1` is an e-chain; in fact `{Pᵏf}` is equicontinuous on all of `ℝ`. -/
theorem proposition_6_4_6 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| ≤ 1) :
    IsEChain (ar1Kernel Γ α) := by
  intro f hf hfc K _
  refine Equicontinuous.equicontinuousOn (fun x₀ => ?_) K
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨C, hC⟩ := (_root_.ofCompactSupport f hf hfc).isBounded_range.exists_norm_le
  refine ⟨δ, hδ, fun x hx k => ?_⟩
  set F := fun p : ℝ × ℝ => α * p.1 + p.2
  have hF : Measurable F := measurable_ar1Step α
  have hrepr : ∀ z, ∫ y, f y ∂(ar1Kernel Γ α ^ k) z =
      ∫ u, f (controlMap F k z u) ∂(Measure.pi fun _ : Fin k => Γ) := fun z => by
    rw [ar1Kernel, recursionKernel_pow_apply Γ hF k z,
      integral_map (measurable_controlMap_right hF k z).aemeasurable
        hf.aestronglyMeasurable]
  have hint : ∀ z, Integrable (fun u => f (controlMap F k z u))
      (Measure.pi fun _ : Fin k => Γ) := fun z =>
    Integrable.of_bound
      (hf.measurable.comp (measurable_controlMap_right hF k z)).aestronglyMeasurable
      C (Eventually.of_forall fun u => hC _ ⟨_, rfl⟩)
  rw [hrepr, hrepr, Real.dist_eq, ← integral_sub (hint x₀) (hint x)]
  calc |∫ u, f (controlMap F k x₀ u) - f (controlMap F k x u) ∂(Measure.pi fun _ : Fin k => Γ)|
      ≤ ε / 2 * (Measure.pi fun _ : Fin k => Γ).real univ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => ?_)
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        refine (hfδ ?_).le
        rw [Real.dist_eq, controlMap_ar1_sub, abs_mul, abs_pow]
        calc |α| ^ k * |x₀ - x| ≤ 1 * |x₀ - x| :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg α) hα) (abs_nonneg _)
          _ < δ := by rw [one_mul, abs_sub_comm, ← Real.dist_eq]; exact hx
    _ < ε := by rw [probReal_univ, mul_one]; linarith

/-- MT p. 143: the random walk on `ℝ` is an e-chain (the case `α = 1`). -/
theorem randomWalk_isEChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsEChain (randomWalkKernel Γ) := by
  rw [← ar1Kernel_one]
  exact proposition_6_4_6 Γ (by simp)

/-! ### Boundedness in probability and Lagrange stability (§6.4.2) -/

/-- The chain is **bounded in probability** (MT p. 142): for every `x` and `ε > 0` there is a
compact `C` with `liminf_k Pᵏ(x, C) ≥ 1 − ε`. -/
def IsBoundedInProbability [TopologicalSpace X] (P : Kernel X X) : Prop :=
  ∀ x : X, ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set X, IsCompact C ∧
    1 - ε ≤ atTop.liminf fun k : ℕ => (P ^ k) x C

/-- The orbit `μPᵏ` of a probability measure. -/
noncomputable def orbitPM (P : Kernel X X) [IsMarkovKernel P] (μ : ProbabilityMeasure X)
    (k : ℕ) : ProbabilityMeasure X :=
  ⟨(P ^ k : Kernel X X) ∘ₘ (μ : Measure X), by have := isMarkovKernel_pow P k; infer_instance⟩

/-- `(P, M)` is **Lagrange stable** (MT §1.3.2 and p. 141): every orbit `{μPᵏ}` is precompact in
the topology of weak convergence. -/
def IsLagrangeStable [TopologicalSpace X] [OpensMeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] : Prop :=
  ∀ μ : ProbabilityMeasure X, IsCompact (closure (range (orbitPM P μ)))

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
/-- Boundedness in probability makes every orbit `{μPᵏ}` tight: Fatou's lemma along a compact
exhaustion handles large `k`, and each of the finitely many remaining `μPᵏ` is tight. -/
theorem isTight_orbit_of_boundedInProbability {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsBoundedInProbability P) (μ : ProbabilityMeasure X) :
    IsTightMeasureSet {ν : Measure X | ∃ k : ℕ, ν = (P ^ k : Kernel X X) ∘ₘ (μ : Measure X)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hpk : ∀ k, IsMarkovKernel (P ^ k) := isMarkovKernel_pow P
  let Kx : CompactExhaustion X := CompactExhaustion.choice X
  set g : ℕ → X → ℝ≥0∞ := fun n x => atTop.liminf fun k : ℕ => (P ^ k) x (Kx n)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    Measurable.liminf fun k => Kernel.measurable_coe _ (Kx.isCompact n).measurableSet
  have hgmono : Monotone g := fun m n hmn x =>
    liminf_le_liminf (Eventually.of_forall fun k => measure_mono (Kx.subset hmn))
  have hgsup : ∀ x, ⨆ n, g n x = 1 := fun x => by
    refine le_antisymm (iSup_le fun n => ?_) (le_of_forall_pos_le_add fun δ hδ => ?_)
    · exact liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans prob_le_one
    · obtain ⟨C, hC, hlim⟩ := hP x δ hδ
      obtain ⟨n, hn⟩ := Kx.exists_superset_of_isCompact hC
      have h1 : 1 - δ ≤ g n x :=
        hlim.trans (liminf_le_liminf (Eventually.of_forall fun k => measure_mono hn))
      calc (1 : ℝ≥0∞) ≤ 1 - δ + δ := le_tsub_add
        _ ≤ (⨆ n, g n x) + δ := add_le_add_left (h1.trans (le_iSup (fun n => g n x) n)) _
  -- choose `n` with `∫ gₙ dμ > 1 − ε`
  have hint : Tendsto (fun n => ∫⁻ x, g n x ∂(μ : Measure X)) atTop (𝓝 1) := by
    have := lintegral_iSup hgm hgmono (μ := (μ : Measure X))
    simp_rw [hgsup, lintegral_one, measure_univ] at this
    rw [this]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono (hgmono hmn)
  have hε1 : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  obtain ⟨n, hn⟩ := (hint.eventually (lt_mem_nhds hε1)).exists
  -- Fatou
  have hfatou : ∫⁻ x, g n x ∂(μ : Measure X) ≤
      atTop.liminf fun k : ℕ => ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx n) := by
    simp_rw [Measure.bind_apply (Kx.isCompact n).measurableSet (Kernel.aemeasurable _)]
    exact lintegral_liminf_le fun k => Kernel.measurable_coe _ (Kx.isCompact n).measurableSet
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf (hn.trans_le hfatou))
  -- the finitely many `k < N`
  have hsmall : ∀ k : ℕ, ∃ m, ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx m)ᶜ ≤ ε := fun k => by
    have ht := tendsto_measure_iInter_atTop (μ := (P ^ k : Kernel X X) ∘ₘ (μ : Measure X))
      (s := fun m => (Kx m)ᶜ) (fun m => (Kx.isCompact m).measurableSet.compl.nullMeasurableSet)
      (fun a b hab => compl_subset_compl.2 (Kx.subset hab)) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ m, (Kx m)ᶜ) = ∅ := by
      rw [← compl_iUnion, Kx.iUnion_eq, compl_univ]
    rw [hempty, measure_empty] at ht
    obtain ⟨m, hm⟩ := (ht.eventually (Iic_mem_nhds hε)).exists
    exact ⟨m, hm⟩
  choose m hm using hsmall
  set M := max n ((Finset.range N).sup m)
  refine ⟨Kx M, Kx.isCompact M, ?_⟩
  rintro ν ⟨k, rfl⟩
  by_cases hk : N ≤ k
  · have h1 := (hN k hk).le
    calc ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx M)ᶜ
        ≤ ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx n)ᶜ :=
          measure_mono (compl_subset_compl.2 (Kx.subset (le_max_left _ _)))
      _ = 1 - ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx n) :=
          prob_compl_eq_one_sub (Kx.isCompact n).measurableSet
      _ ≤ ε := by
          rw [tsub_le_iff_right]
          calc (1 : ℝ≥0∞) ≤ 1 - ε + ε := le_tsub_add
            _ ≤ _ := by rw [add_comm]; exact add_le_add_right h1 _
  · calc ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx M)ᶜ
        ≤ ((P ^ k : Kernel X X) ∘ₘ (μ : Measure X)) (Kx (m k))ᶜ :=
          measure_mono (compl_subset_compl.2 (Kx.subset ((Finset.le_sup
            (Finset.mem_range.2 (not_le.1 hk))).trans (le_max_right _ _))))
      _ ≤ ε := hm k

omit [MeasurableSpace X] in
/-- **Proposition 6.4.4** (MT p. 142): on a locally compact, separable, complete metric space,
the chain is bounded in probability iff `(P, M)` is Lagrange stable. The proof uses Prokhorov's
result in both directions (Mathlib's `isCompact_closure_of_isTightMeasureSet` and
`isTightMeasureSet_of_isCompact_closure`), with `isTight_orbit_of_boundedInProbability` for the
orbit of a general initial law. -/
theorem proposition_6_4_4 [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (P : Kernel X X)
    [IsMarkovKernel P] : IsBoundedInProbability P ↔ IsLagrangeStable P := by
  constructor
  · intro hP μ
    refine isCompact_closure_of_isTightMeasureSet
      ((isTight_orbit_of_boundedInProbability hP μ).subset ?_)
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
  · intro hL x ε hε
    have ht := isTightMeasureSet_of_isCompact_closure (hL (diracProba x))
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
    obtain ⟨K, hK, hKε⟩ := ht ε hε
    refine ⟨K, hK, le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun k => ?_)⟩
    have := isMarkovKernel_pow P k
    have hk : ((orbitPM P (diracProba x) k : ProbabilityMeasure X) : Measure X) = (P ^ k) x :=
      dirac_kernel (P ^ k) x
    have h1 := hKε _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [hk, prob_compl_eq_one_sub hK.measurableSet] at h1
    rw [tsub_le_iff_right] at h1 ⊢
    rwa [add_comm]

end MeynTweedie.Epilogue
