/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.SigmaFiniteInvariant
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.Dini

/-!
# Invariant measures for e-chains (MT §12.4.1, Theorem 12.0.1 (ii))

Meyn and Tweedie, §12.4.1, pp. 300–301, and Theorem 12.0.1 (ii), p. 289. `X` is a locally compact,
second-countable, metrizable Hausdorff space with its Borel σ-algebra, and `P` is an e-chain
(`IsEChain`, Chapter 6).

**Tools.**
* `cesaroFun P n f x = P̄ⁿ f(x)`; `eventually_abs_cesaroFun_sub_le`: the Cesàro averages of an
  e-chain are equicontinuous.
* `exists_dense_cc`: a countable family in `C_c(X)` that is uniformly dense.
* `exists_subseq_tendsto_cesaroFun`: the diagonal argument of p. 301 (Ascoli): every sequence of
  times has a subsequence along which `P̄ⁿ f(x)` converges for all `f ∈ C_c(X)` and all `x`.
* `ext_of_integral_cc`, `integral_cc_eq_of_nonneg`: finite measures are determined by `C_c(X)`.
* For a convergent subsequence `σ` (`CesaroConverges`): the vague limit `limMeasure P σ x`, the
  kernel `limKernel` (`measurable_limMeasure`), `continuous_integral_limMeasure` (`Πf` is
  continuous), `isInvariant_limMeasure` (`ΠP = Π`), `integral_limMeasure_kernel` (`PΠ = Π`),
  `integral_limMeasure_limMeasure` (`ΠΠ = Π`), and `limMeasure_eq`: all such limits coincide.

**Theorem 12.4.1** (p. 300), for `Π = eChainLimit he`.
* (i) `theorem_12_4_1_i`, (12.23): `P̄ⁿ(x, ·) → Π(x, ·)` vaguely for every `x`, `Π(x, X) ≤ 1`.
* (ii) `theorem_12_4_1_ii`, (12.25): `PʲΠᵏPˡ = Π` for `k ≥ 1`, and every `Π(x, ·)` is invariant;
  `kernel_comp_eChainLimit`, `eChainLimit_comp_kernel`, `eChainLimit_comp_self`.
* (iii) `theorem_12_4_1_iii`: the chain is bounded in probability on average iff `Π(x, X) ≡ 1`.

**Theorem 12.0.1 (ii)** (`theorem_12_0_1_ii`, p. 289): for an e-chain bounded in probability on
average, `Π` is a weak Feller transition kernel (`continuous_integral_eChainLimit`, by Dini's
theorem), each `Π(x, ·)` is invariant, and `P̄ⁿ(x, f) → Π(x, f)` for bounded continuous `f`
(`tendsto_integral_bcf_of_cc`: vague convergence without loss of mass is weak convergence).

The resolvent form (12.24) of Theorem 12.4.1 (i) is in `EChainCriteria`.

**Method.** The book takes vague limit points by sequential compactness of the sub-probabilities
(Proposition D.5.6). Here a vague limit point is the Riesz–Markov–Kakutani measure of an
ultrafilter limit (`vagueLimit`); along a subsequence on which the averages converge for every
`f ∈ C_c(X)` it is independent of the ultrafilter.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

variable {X : Type*} [MeasurableSpace X]

/-- The Cesàro average `P̄ⁿ f(x) = ∫ f dP̄ⁿ(x)` of a real function. -/
noncomputable def cesaroFun (P : Kernel X X) (n : ℕ) (f : X → ℝ) (x : X) : ℝ :=
  ∫ y, f y ∂cesaroKernel P n x

/-- `|P̄ⁿ f| ≤ B` for `|f| ≤ B`. -/
theorem abs_cesaroFun_le (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) {f : X → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) (x : X) : |cesaroFun P n f x| ≤ B :=
  abs_integral_le_of_univ_le (cesaroKernel_univ_le P n x) hB0 hB

/-- `x ↦ P̄ⁿ f(x)` is measurable for bounded measurable `f`. -/
theorem measurable_cesaroFun (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) {f : X → ℝ}
    (hf : Measurable f) : Measurable (cesaroFun P n f) := by
  have := isFiniteKernel_cesaroKernel P n
  exact measurable_kfunR (cesaroKernel P n) hf

variable [TopologicalSpace X]

/-- **Cesàro averages of an e-chain are equicontinuous** (used on p. 301): for `f ∈ C_c(X)` and
`ε > 0`, near every `x₀`, `|P̄ⁿ f(x₀) − P̄ⁿ f(x)| ≤ ε` for all `n`. -/
theorem eventually_abs_cesaroFun_sub_le [LocallyCompactSpace X] [OpensMeasurableSpace X]
    {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (f : C_c(X, ℝ)) (x₀ : X) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ n, |cesaroFun P n f x₀ - cesaroFun P n f x| ≤ ε := by
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  filter_upwards [eventually_dist_lt_of_eChain he (map_continuous f) f.hasCompactSupport hN hNx hε]
    with x hx n
  simp only [cesaroFun]
  rw [integral_cesaroKernel P n x₀ (map_continuous f).measurable hB,
    integral_cesaroKernel P n x (map_continuous f).measurable hB, ← mul_sub,
    ← Finset.sum_sub_distrib,
    abs_mul, abs_inv, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hε.le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.Icc 1 n, (∫ y, f y ∂(P ^ i) x₀ - ∫ y, f y ∂(P ^ i) x)|
      ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 n, |∫ y, f y ∂(P ^ i) x₀ - ∫ y, f y ∂(P ^ i) x| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.Icc 1 n, ε := by
        gcongr with i _
        exact (hx i).le
    _ = ε := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hn'.ne', one_mul]

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]

omit [MeasurableSpace X] in
/-- **A countable uniformly dense family in `C_c(X)`**: there are `Fₖ ∈ C_c(X)` such that every
`f ∈ C_c(X)` is a uniform limit of some of them. (Products of cut-offs `φⱼ` with a dense
sequence of `C(X)` in the compact-open topology.) -/
theorem exists_dense_cc : ∃ F : ℕ → C_c(X, ℝ), ∀ f : C_c(X, ℝ), ∀ ε : ℝ, 0 < ε →
    ∃ k, ∀ x, |f x - F k x| ≤ ε := by
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  let F' : ℕ × ℕ → C_c(X, ℝ) := fun p =>
    ⟨(φ p.1 : C(X, ℝ)) * g p.2, (φ p.1).hasCompactSupport.mul_right⟩
  refine ⟨fun k => F' (Nat.unpair k), fun f ε hε => ?_⟩
  obtain ⟨J, hJ⟩ := hφ1 (tsupport f) f.hasCompactSupport
  set S := tsupport (φ J)
  have hS : IsCompact S := (φ J).hasCompactSupport
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1
    (hg.closure_eq ▸ mem_univ (f : C(X, ℝ)) : (f : C(X, ℝ)) ∈ closure (range g))
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hut) S hS
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif ε hε).exists
  obtain ⟨m, hm⟩ := hu n
  refine ⟨Nat.pair J m, fun x => ?_⟩
  simp only [Nat.unpair_pair, F']
  change |f x - φ J x * g m x| ≤ ε
  have hgx : ∀ x ∈ S, |f x - g m x| < ε := fun x hx => by
    have := hn x hx
    rw [← hm, Real.dist_eq] at this
    exact this
  by_cases hxf : x ∈ tsupport f
  · have h1 : φ J x = 1 := hJ J le_rfl x hxf
    have hxS : x ∈ S := subset_tsupport _ (by rw [Function.mem_support, h1]; exact one_ne_zero)
    rw [h1, one_mul]
    exact (hgx x hxS).le
  · rw [image_eq_zero_of_notMem_tsupport hxf, zero_sub, abs_neg, abs_mul,
      abs_of_nonneg (hφ01 J x).1]
    by_cases hxS : x ∈ S
    · have := hgx x hxS
      rw [image_eq_zero_of_notMem_tsupport hxf, zero_sub, abs_neg] at this
      exact (mul_le_of_le_one_left (abs_nonneg _) (hφ01 J x).2).trans this.le
    · rw [image_eq_zero_of_notMem_tsupport hxS, zero_mul]
      exact hε.le


variable [OpensMeasurableSpace X]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- `P̄ⁿ f − P̄ⁿ g = P̄ⁿ (f − g)` for `f, g ∈ C_c(X)`. -/
theorem cesaroFun_sub (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (f g : C_c(X, ℝ)) (x : X) :
    cesaroFun P n f x - cesaroFun P n g x = cesaroFun P n (fun y => f y - g y) x := by
  have := isFiniteKernel_cesaroKernel P n
  simp only [cesaroFun]
  exact (integral_sub f.integrable g.integrable).symm

/-- **The diagonal subsequence** (Ascoli's theorem and the diagonal argument, MT p. 301): for an
e-chain and any sequence of times `ψ`, there is a subsequence `φ` along which `P̄^{ψ(φ i)} f(x)`
converges for every `f ∈ C_c(X)` and every `x`. Convergence on a countable dense family of `f`
and a countable dense set of `x` comes from the compactness of a countable product of intervals;
equicontinuity and uniform approximation extend it everywhere. -/
theorem exists_subseq_tendsto_cesaroFun {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (ψ : ℕ → ℕ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : C_c(X, ℝ), ∀ x : X, ∃ c : ℝ,
      Tendsto (fun i => cesaroFun P (ψ (φ i)) f x) atTop (𝓝 c) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨id, strictMono_id, fun f x => isEmptyElim x⟩
  obtain ⟨F, hF⟩ := exists_dense_cc (X := X)
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq X
  have hB : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |F k x| ≤ B := fun k => exists_abs_le_cc (F k)
  choose B hB0 hB using hB
  set s : ℕ → (ℕ × ℕ → ℝ) := fun n p => cesaroFun P (ψ n) (F p.1) (D p.2)
  have hK : IsCompact (univ.pi fun p : ℕ × ℕ => Icc (-B p.1) (B p.1)) :=
    isCompact_univ_pi fun p => isCompact_Icc
  have hs : ∀ n, s n ∈ univ.pi fun p : ℕ × ℕ => Icc (-B p.1) (B p.1) := fun n p _ =>
    abs_le.1 (abs_cesaroFun_le P (ψ n) (hB0 p.1) (hB p.1) (D p.2))
  obtain ⟨c, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hs
  have hcoord : ∀ p : ℕ × ℕ, Tendsto (fun i => s (φ i) p) atTop (𝓝 (c p)) := fun p =>
    ((continuous_apply p).tendsto c).comp hlim
  refine ⟨φ, hφ, fun f x => cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 ?_)⟩
  intro ε hε
  obtain ⟨k, hk⟩ := hF f (ε / 4) (by positivity)
  have happ : ∀ n y, |cesaroFun P n f y - cesaroFun P n (F k) y| ≤ ε / 4 := fun n y => by
    rw [cesaroFun_sub]
    exact abs_cesaroFun_le P n (by positivity) hk y
  obtain ⟨d, hd⟩ : ∃ d, ∀ n, |cesaroFun P n (F k) x - cesaroFun P n (F k) (D d)| ≤ ε / 8 := by
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hD.inter_nhds_nonempty
      (eventually_abs_cesaroFun_sub_le he (F k) x (by positivity : (0 : ℝ) < ε / 8))
    exact ⟨d, hd⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcoord (k, d)).cauchySeq (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hN m hm n hn
  simp only [s, Real.dist_eq] at h1
  rw [Real.dist_eq]
  have e1 := happ (ψ (φ m)) x
  have e2 := happ (ψ (φ n)) x
  have e3 := hd (ψ (φ m))
  have e4 := hd (ψ (φ n))
  calc |cesaroFun P (ψ (φ m)) f x - cesaroFun P (ψ (φ n)) f x|
      ≤ |cesaroFun P (ψ (φ m)) f x - cesaroFun P (ψ (φ m)) (F k) x| +
        |cesaroFun P (ψ (φ m)) (F k) x - cesaroFun P (ψ (φ m)) (F k) (D d)| +
        |cesaroFun P (ψ (φ m)) (F k) (D d) - cesaroFun P (ψ (φ n)) (F k) (D d)| +
        |cesaroFun P (ψ (φ n)) (F k) (D d) - cesaroFun P (ψ (φ n)) (F k) x| +
        |cesaroFun P (ψ (φ n)) (F k) x - cesaroFun P (ψ (φ n)) f x| := by
        have := abs_sub_le (cesaroFun P (ψ (φ m)) f x) (cesaroFun P (ψ (φ m)) (F k) x)
          (cesaroFun P (ψ (φ n)) f x)
        have := abs_sub_le (cesaroFun P (ψ (φ m)) (F k) x)
          (cesaroFun P (ψ (φ m)) (F k) (D d)) (cesaroFun P (ψ (φ n)) f x)
        have := abs_sub_le (cesaroFun P (ψ (φ m)) (F k) (D d))
          (cesaroFun P (ψ (φ n)) (F k) (D d)) (cesaroFun P (ψ (φ n)) f x)
        have := abs_sub_le (cesaroFun P (ψ (φ n)) (F k) (D d))
          (cesaroFun P (ψ (φ n)) (F k) x) (cesaroFun P (ψ (φ n)) f x)
        linarith
    _ < ε := by
        rw [abs_sub_comm] at e4
        rw [abs_sub_comm (cesaroFun P (ψ (φ n)) (F k) x)] 
        linarith


/-! ### Finite measures are determined by `C_c(X)` -/

variable [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

omit [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Cut-offs recover integrals of bounded continuous functions: `∫ g φₙ dμ → ∫ g dμ`. -/
theorem integral_cutoff_tendsto {μ : Measure X} [IsFiniteMeasure μ] {φ : ℕ → C_c(X, ℝ)}
    (hφ01 : ∀ n x, φ n x ∈ Icc (0 : ℝ) 1)
    (hφ1 : ∀ K : Set X, IsCompact K → ∃ N, ∀ n, N ≤ n → ∀ x ∈ K, φ n x = 1) (g : X →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g x * φ n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
    (fun n => (g.continuous.mul (φ n).continuous).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · rw [norm_mul, Real.norm_eq_abs (φ n x), abs_of_nonneg (hφ01 n x).1]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hφ01 n x).2).trans (g.norm_coe_le_norm x)
  · refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [cutoff_eventually_eq_one hφ1 x] with n hn
    rw [hn, mul_one]

omit [OpensMeasurableSpace X] in
/-- **Finite measures agreeing on `C_c(X)` are equal** (the uniqueness of vague limits used on
p. 301), on a locally compact, σ-compact, metrizable space. -/
theorem ext_of_integral_cc {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => tendsto_nhds_unique
    (integral_cutoff_tendsto hφ01 hφ1 g) ?_
  have := integral_cutoff_tendsto (μ := ν) hφ01 hφ1 g
  refine this.congr fun n => ?_
  exact (h ⟨⟨fun x => g x * φ n x, g.continuous.mul (φ n).continuous⟩,
    (φ n).hasCompactSupport.mul_left⟩).symm


/-! ### The limit kernel along a convergent subsequence -/

/-- Along the times `σ`, the Cesàro averages `P̄^{σ i} f(x)` converge for every `f ∈ C_c(X)` and
every `x`. -/
def CesaroConverges (P : Kernel X X) (σ : ℕ → ℕ) : Prop :=
  ∀ f : C_c(X, ℝ), ∀ x : X, ∃ c : ℝ, Tendsto (fun i => cesaroFun P (σ i) f x) atTop (𝓝 c)

/-- The vague limit `Π_σ(x, ·)` of `P̄^{σ i}(x, ·)`, taken along a fixed ultrafilter finer than
`atTop`. -/
noncomputable def limMeasure (P : Kernel X X) [IsMarkovKernel P] (σ : ℕ → ℕ) (x : X) :
    Measure X :=
  vagueLimit (fun i => cesaroKernel P (σ i) x) (fun i => cesaroKernel_univ_le P (σ i) x)
    (Ultrafilter.of (atTop : Filter ℕ))

omit [OpensMeasurableSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `Π_σ(x, ·)` is a sub-probability. -/
theorem limMeasure_univ_le (P : Kernel X X) [IsMarkovKernel P] (σ : ℕ → ℕ) (x : X) :
    limMeasure P σ x univ ≤ 1 :=
  vagueLimit_univ_le _ _ _

omit [OpensMeasurableSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `Π_σ(x, ·)` is a finite measure. -/
theorem isFiniteMeasure_limMeasure (P : Kernel X X) [IsMarkovKernel P] (σ : ℕ → ℕ) (x : X) :
    IsFiniteMeasure (limMeasure P σ x) :=
  isFiniteMeasure_vagueLimit _ _ _

omit [SecondCountableTopology X] [OpensMeasurableSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Along a convergent `σ`, `P̄^{σ i} f(x) → ∫ f dΠ_σ(x)` for every `f ∈ C_c(X)`. -/
theorem tendsto_limMeasure {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) (f : C_c(X, ℝ)) (x : X) :
    Tendsto (fun i => cesaroFun P (σ i) f x) atTop (𝓝 (∫ y, f y ∂limMeasure P σ x)) := by
  obtain ⟨c, hc⟩ := hσ f x
  have h1 := tendsto_integral_vagueLimit (fun i => cesaroKernel P (σ i) x)
    (fun i => cesaroKernel_univ_le P (σ i) x) (Ultrafilter.of (atTop : Filter ℕ)) f
  have h2 := hc.mono_left (Ultrafilter.of_le (atTop : Filter ℕ))
  have e : ∫ y, f y ∂limMeasure P σ x = c := tendsto_nhds_unique h1 h2
  rw [e]
  exact hc

omit [SecondCountableTopology X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `x ↦ ∫ f dΠ_σ(x)` is measurable for `f ∈ C_c(X)`. -/
theorem measurable_integral_limMeasure {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) (f : C_c(X, ℝ)) :
    Measurable fun x => ∫ y, f y ∂limMeasure P σ x :=
  measurable_of_tendsto_metrizable
    (fun i => measurable_cesaroFun P (σ i) (map_continuous f).measurable)
    (tendsto_pi_nhds.2 fun x => tendsto_limMeasure hσ f x)

omit [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `x ↦ ∫ g dΠ_σ(x)` is measurable for bounded continuous `g`. -/
theorem measurable_integral_limMeasure_bcf {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) (g : X →ᵇ ℝ) :
    Measurable fun x => ∫ y, g y ∂limMeasure P σ x := by
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  refine measurable_of_tendsto_metrizable (f := fun n x => ∫ y, g y * φ n y ∂limMeasure P σ x)
    (fun n => measurable_integral_limMeasure hσ ⟨⟨fun x => g x * φ n x,
      g.continuous.mul (φ n).continuous⟩, (φ n).hasCompactSupport.mul_left⟩)
    (tendsto_pi_nhds.2 fun x => ?_)
  have := isFiniteMeasure_limMeasure P σ x
  exact integral_cutoff_tendsto hφ01 hφ1 g

/-- `x ↦ Π_σ(x, ·)` is measurable: the measures of closed sets are limits of integrals of bounded
continuous functions (`HasOuterApproxClosed`), and closed sets form a generating π-system. -/
theorem measurable_limMeasure {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) : Measurable (limMeasure P σ) := by
  have := isFiniteMeasure_limMeasure P σ
  have hclosed : ∀ F : Set X, IsClosed F → Measurable fun x => limMeasure P σ x F := by
    intro F hF'
    refine measurable_of_tendsto_metrizable
      (f := fun n x => ∫⁻ y, (hF'.apprSeq n y : ℝ≥0∞) ∂limMeasure P σ x) (fun n => ?_)
      (tendsto_pi_nhds.2 fun x => HasOuterApproxClosed.tendsto_lintegral_apprSeq hF' _)
    set g : X →ᵇ ℝ := ⟨⟨fun x => (hF'.apprSeq n x : ℝ),
      NNReal.continuous_coe.comp (hF'.apprSeq n).continuous⟩, (hF'.apprSeq n).map_bounded'⟩
    have heq : (fun x => ∫⁻ y, (hF'.apprSeq n y : ℝ≥0∞) ∂limMeasure P σ x) =
        fun x => ENNReal.ofReal (∫ y, g y ∂limMeasure P σ x) := by
      ext x
      rw [ofReal_integral_eq_lintegral_ofReal (g.integrable _)
        (Eventually.of_forall fun y => NNReal.coe_nonneg _)]
      exact lintegral_congr fun y => ENNReal.ofReal_coe_nnreal.symm
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (measurable_integral_limMeasure_bcf hσ g)
  exact Measurable.measure_of_isPiSystem (S := {s : Set X | IsClosed s})
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    hclosed (hclosed univ isClosed_univ)


/-- The limit kernel `Π_σ` (MT p. 301). -/
noncomputable def limKernel {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) : Kernel X X :=
  ⟨limMeasure P σ, measurable_limMeasure hσ⟩

/-- `Π_σ(x, ·)` is the vague limit. -/
theorem limKernel_apply {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) (x : X) : limKernel hσ x = limMeasure P σ x := rfl

/-- `Π_σ` is a finite (sub-stochastic) kernel. -/
theorem isFiniteKernel_limKernel {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) : IsFiniteKernel (limKernel hσ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x => limMeasure_univ_le P σ x⟩⟩

omit [T2Space X] [SecondCountableTopology X] [OpensMeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- For an e-chain, `Pf` is continuous for `f ∈ C_c(X)` (the member `k = 1` of the equicontinuous
family `{Pᵏ f}`). -/
theorem continuous_kfunR_of_eChain {P : Kernel X X} (he : IsEChain P) (f : C_c(X, ℝ)) :
    Continuous (kfunR P f) := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  filter_upwards [eventually_dist_lt_of_eChain he (map_continuous f) f.hasCompactSupport hN hNx hε]
    with x hx
  have := hx 1
  rw [pow_one, dist_comm] at this
  exact this

omit [SecondCountableTopology X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Continuity of `Π_σ f`** (MT p. 301, "by equicontinuity"): for an e-chain, `x ↦ ∫ f dΠ_σ(x)`
is continuous for every `f ∈ C_c(X)`, as the pointwise limit of an equicontinuous family. -/
theorem continuous_integral_limMeasure {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {σ : ℕ → ℕ} (hσ : CesaroConverges P σ) (f : C_c(X, ℝ)) :
    Continuous fun x => ∫ y, f y ∂limMeasure P σ x := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eventually_abs_cesaroFun_sub_le he f x₀ (half_pos hε)] with x hx
  rw [Real.dist_eq, abs_sub_comm]
  have ht := ((tendsto_limMeasure hσ f x₀).sub (tendsto_limMeasure hσ f x)).abs
  exact lt_of_le_of_lt (le_of_tendsto' ht fun i => hx (σ i)) (half_lt_self hε)

/-- **`Π_σ(x, ·)` is invariant** (MT p. 301, `ΠP = Π`): for `g ∈ C_c(X)`, `g ≥ 0`, `Pg` is
continuous, so (D.6) and the Cesàro telescoping bound give `∫ Pg dΠ_σ(x) ≤ ∫ g dΠ_σ(x)`. -/
theorem isInvariant_limMeasure {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {σ : ℕ → ℕ} (hσ' : Tendsto σ atTop atTop) (x : X) :
    IsInvariant P (limMeasure P σ x) := by
  have := isFiniteMeasure_limMeasure P σ x
  set μs : ℕ → Measure X := fun i => cesaroKernel P (σ i) x
  have hμ : ∀ i, μs i univ ≤ 1 := fun i => cesaroKernel_univ_le P (σ i) x
  set U := Ultrafilter.of (atTop : Filter ℕ)
  refine isInvariant_of_integral_le fun g hg0 => ?_
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc g
  have hPB : ∀ y, |kfunR P g y| ≤ B := abs_kfunR_le P hB
  obtain ⟨c, hc⟩ := exists_tendsto_integral μs hμ U hB0 hPB
  have hdiff : Tendsto (fun i => ∫ y, kfunR P g y ∂μs i - ∫ y, g y ∂μs i) (U : Filter ℕ) (𝓝 0) :=
    (squeeze_zero_norm (fun i => by
      rw [Real.norm_eq_abs]
      exact abs_integral_kfunR_cesaro_sub_le P (σ i) x (map_continuous g).measurable hB)
      ((tendsto_const_div_atTop_nhds_zero_nat (2 * B)).comp hσ')).mono_left
      (Ultrafilter.of_le _)
  have hgc : Tendsto (fun i => ∫ y, g y ∂μs i) (U : Filter ℕ) (𝓝 c) := by
    have := hc.sub hdiff
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  have e : ∫ y, g y ∂limMeasure P σ x = c :=
    tendsto_nhds_unique (tendsto_integral_vagueLimit μs hμ U g) hgc
  rw [e]
  exact integral_vagueLimit_le μs hμ U (continuous_kfunR_of_eChain he g)
    (fun y => integral_nonneg fun z => hg0 z) (fun y => (le_abs_self _).trans (hPB y)) hc


omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `∫ P̄ⁿ f dP(x) = ∫ Pf dP̄ⁿ(x)` for bounded measurable `f`. -/
theorem integral_cesaroFun_kernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) {f : X → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : X) :
    ∫ y, cesaroFun P n f y ∂P x = ∫ y, kfunR P f y ∂cesaroKernel P n x := by
  have hPB : ∀ y, |kfunR P f y| ≤ B := abs_kfunR_le P hB
  rw [integral_cesaroKernel P n x (measurable_kfunR P hf) hPB]
  simp only [cesaroFun]
  simp_rw [integral_cesaroKernel P n _ hf hB]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_kfunR_pow P i x hf hB]
    have := isMarkovKernel_pow P i
    have hint : Integrable f ((P ^ (i + 1)) x) := by
      have := isMarkovKernel_pow P (i + 1)
      exact Integrable.of_bound hf.aestronglyMeasurable B
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
    rw [pow_succ] at hint ⊢
    exact (Kernel.integral_comp hint).symm
  · intro i _
    have := isMarkovKernel_pow P i
    exact Integrable.of_bound (measurable_kfunR (P ^ i) hf).aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_kfunR_le _ hB y)

omit [SecondCountableTopology X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **`PΠ_σ = Π_σ`** (MT p. 301, `PʲΠ = Π`), in integral form: for `f ∈ C_c(X)`,
`∫ Π_σ f dP(x) = Π_σ f(x)`, by dominated convergence along `σ` and the telescoping bound. -/
theorem integral_limMeasure_kernel {P : Kernel X X} [IsMarkovKernel P] {σ : ℕ → ℕ}
    (hσ : CesaroConverges P σ) (hσ' : Tendsto σ atTop atTop) (f : C_c(X, ℝ)) (x : X) :
    ∫ y, (∫ z, f z ∂limMeasure P σ y) ∂P x = ∫ z, f z ∂limMeasure P σ x := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  have hlim : Tendsto (fun i => ∫ y, cesaroFun P (σ i) f y ∂P x) atTop
      (𝓝 (∫ y, (∫ z, f z ∂limMeasure P σ y) ∂P x)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun i => (measurable_cesaroFun P (σ i) (map_continuous f).measurable).aestronglyMeasurable)
      (integrable_const B)
      (fun i => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_cesaroFun_le P (σ i) hB0 hB y)
      (Eventually.of_forall fun y => tendsto_limMeasure hσ f y)
  have hdiff : Tendsto (fun i => ∫ y, cesaroFun P (σ i) f y ∂P x - cesaroFun P (σ i) f x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_)
      ((tendsto_const_div_atTop_nhds_zero_nat (2 * B)).comp hσ')
    rw [Real.norm_eq_abs, integral_cesaroFun_kernel P (σ i) (map_continuous f).measurable hB x]
    exact abs_integral_kfunR_cesaro_sub_le P (σ i) x (map_continuous f).measurable hB
  have := hlim.sub hdiff
  simp only [sub_sub_cancel, sub_zero] at this
  exact tendsto_nhds_unique this (tendsto_limMeasure hσ f x)

/-- **`ΠΠ = Π`** (MT p. 301), in integral form: `∫ Π_σ f dΠ_σ(x) = Π_σ f(x)`, since `Π_σ(x, ·)` is
invariant for every `P̄ⁿ`. -/
theorem integral_limMeasure_limMeasure {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {σ : ℕ → ℕ} (hσ : CesaroConverges P σ) (hσ' : Tendsto σ atTop atTop) (f : C_c(X, ℝ))
    (x : X) :
    ∫ y, (∫ z, f z ∂limMeasure P σ y) ∂limMeasure P σ x = ∫ z, f z ∂limMeasure P σ x := by
  have := isFiniteMeasure_limMeasure P σ x
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  have hinv := isInvariant_limMeasure he hσ' x
  have hlim : Tendsto (fun i => ∫ y, cesaroFun P (σ i) f y ∂limMeasure P σ x) atTop
      (𝓝 (∫ y, (∫ z, f z ∂limMeasure P σ y) ∂limMeasure P σ x)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun i => (measurable_cesaroFun P (σ i) (map_continuous f).measurable).aestronglyMeasurable)
      (integrable_const B)
      (fun i => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_cesaroFun_le P (σ i) hB0 hB y)
      (Eventually.of_forall fun y => tendsto_limMeasure hσ f y)
  refine tendsto_nhds_unique hlim (tendsto_nhds_of_eventually_eq ?_)
  filter_upwards [hσ'.eventually_ge_atTop 1] with i hi
  have hM := isMarkovKernel_cesaroKernel P hi
  have hK := hinv.sampledKernel (isSamplingDist_uniformDist hi)
  unfold IsInvariant at hK
  simp only [cesaroFun]
  rw [← integral_comp_measure _ _ (f.integrable)]
  exact congrArg (fun m : Measure X => ∫ z, f z ∂m) hK


omit [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [T2Space X] [LocallyCompactSpace X] in
/-- Integrals against finite measures that agree on nonnegative `f ∈ C_c(X)` agree on `C_c(X)`. -/
theorem integral_cc_eq_of_nonneg {μ ν : Measure X} [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂μ = ∫ x, f x ∂ν) (f : C_c(X, ℝ)) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  set fp : C_c(X, ℝ) := ⟨⟨fun x => max (f x) 0, (map_continuous f).max continuous_const⟩,
    f.hasCompactSupport.comp_left (g := fun t : ℝ => max t 0) (by simp)⟩
  set fn : C_c(X, ℝ) := ⟨⟨fun x => max (-f x) 0, (map_continuous f).neg.max continuous_const⟩,
    f.hasCompactSupport.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)⟩
  have hf : ∀ x, f x = fp x - fn x := fun x => by
    change f x = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  have e : ∀ m : Measure X, IsFiniteMeasureOnCompacts m →
      ∫ x, f x ∂m = ∫ x, fp x ∂m - ∫ x, fn x ∂m := fun m _ => by
    rw [← integral_sub fp.integrable fn.integrable]
    exact integral_congr_ae (Eventually.of_forall hf)
  rw [e μ inferInstance, e ν inferInstance, h fp fun x => le_max_right _ _,
    h fn fun x => le_max_right _ _]

/-- **Uniqueness of the limit kernel** (MT p. 301, "by symmetry, `Π' = Π`"): for an e-chain, any
two convergent subsequences give the same limit `Π_σ(x, ·)`. For `f ≥ 0` in `C_c(X)`,
`Π_σ f(x) = ∫ Π_{σ'} f dΠ_σ(x) ≤ lim ∫ Π_{σ'} f dP̄^{σ i}(x) = Π_{σ'} f(x)`, by the invariance of
`Π_σ(x, ·)`, the continuity of `Π_{σ'} f` and (D.6), and `PΠ_{σ'} = Π_{σ'}`. -/
theorem limMeasure_eq {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {σ₁ σ₂ : ℕ → ℕ}
    (h₁ : CesaroConverges P σ₁) (h₁' : Tendsto σ₁ atTop atTop) (h₂ : CesaroConverges P σ₂)
    (h₂' : Tendsto σ₂ atTop atTop) (x : X) : limMeasure P σ₁ x = limMeasure P σ₂ x := by
  have hle : ∀ σ σ' : ℕ → ℕ, CesaroConverges P σ → Tendsto σ atTop atTop →
      CesaroConverges P σ' → Tendsto σ' atTop atTop → ∀ f : C_c(X, ℝ), (∀ y, 0 ≤ f y) →
      ∫ y, f y ∂limMeasure P σ x ≤ ∫ y, f y ∂limMeasure P σ' x := by
    intro σ σ' h h' k k' f hf0
    have := isFiniteMeasure_limMeasure P σ x
    obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
    set g : X → ℝ := fun y => ∫ z, f z ∂limMeasure P σ' y
    have hgm : Measurable g := measurable_integral_limMeasure k f
    have hgB : ∀ y, |g y| ≤ B := fun y =>
      abs_integral_le_of_univ_le (limMeasure_univ_le P σ' y) hB0 hB
    -- (a) `Π_σ f(x) = ∫ Π_{σ'} f dΠ_σ(x)`
    have ha : ∫ y, f y ∂limMeasure P σ x = ∫ y, g y ∂limMeasure P σ x := by
      have hinv := isInvariant_limMeasure he h' x
      have hlim : Tendsto (fun j => ∫ y, cesaroFun P (σ' j) f y ∂limMeasure P σ x) atTop
          (𝓝 (∫ y, g y ∂limMeasure P σ x)) :=
        tendsto_integral_of_dominated_convergence (fun _ => B)
          (fun j => (measurable_cesaroFun P (σ' j)
            (map_continuous f).measurable).aestronglyMeasurable)
          (integrable_const B)
          (fun j => Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]; exact abs_cesaroFun_le P (σ' j) hB0 hB y)
          (Eventually.of_forall fun y => tendsto_limMeasure k f y)
      refine tendsto_nhds_unique (tendsto_nhds_of_eventually_eq ?_) hlim
      filter_upwards [k'.eventually_ge_atTop 1] with j hj
      have hM := isMarkovKernel_cesaroKernel P hj
      have hK := hinv.sampledKernel (isSamplingDist_uniformDist hj)
      unfold IsInvariant at hK
      simp only [cesaroFun]
      rw [← integral_comp_measure _ _ (f.integrable)]
      exact congrArg (fun m : Measure X => ∫ z, f z ∂m) hK
    -- `∫ Π_{σ'} f dPⁱ(x) = Π_{σ'} f(x)`
    have hpow : ∀ i y, ∫ z, g z ∂(P ^ i) y = g y := by
      intro i
      induction i with
      | zero => intro y; rw [pow_zero_apply, integral_dirac' _ _ hgm.stronglyMeasurable]
      | succ i ih =>
        intro y
        have := isMarkovKernel_pow P i
        have hint : Integrable g (((P ^ i) ∘ₖ P) y) := Integrable.of_bound
          hgm.aestronglyMeasurable B (Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs]; exact hgB z)
        rw [pow_succ]
        change ∫ z, g z ∂((P ^ i) ∘ₖ P) y = g y
        rw [Kernel.integral_comp hint]
        simp_rw [ih]
        exact integral_limMeasure_kernel k k' f y
    have hces : ∀ n, 1 ≤ n → ∫ z, g z ∂cesaroKernel P n x = g x := fun n hn => by
      rw [integral_cesaroKernel P n x hgm hgB]
      simp_rw [hpow]
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]
    -- (b) `∫ Π_{σ'} f dΠ_σ(x) ≤ Π_{σ'} f(x)`
    have hb : ∫ y, g y ∂limMeasure P σ x ≤ g x := by
      refine integral_vagueLimit_le (fun i => cesaroKernel P (σ i) x)
        (fun i => cesaroKernel_univ_le P (σ i) x) (Ultrafilter.of (atTop : Filter ℕ))
        (continuous_integral_limMeasure he k f) (fun y => integral_nonneg fun z => hf0 z)
        (fun y => (le_abs_self _).trans (hgB y)) ?_
      refine (tendsto_nhds_of_eventually_eq ?_).mono_left (Ultrafilter.of_le _)
      filter_upwards [h'.eventually_ge_atTop 1] with i hi
      exact hces (σ i) hi
    rw [ha]
    exact hb
  have := isFiniteMeasure_limMeasure P σ₁ x
  have := isFiniteMeasure_limMeasure P σ₂ x
  refine ext_of_integral_cc ?_
  exact integral_cc_eq_of_nonneg fun f hf =>
    le_antisymm (hle σ₁ σ₂ h₁ h₁' h₂ h₂' f hf) (hle σ₂ σ₁ h₂ h₂' h₁ h₁' f hf)


/-! ### Theorem 12.4.1 -/

/-- The subsequence chosen by `exists_subseq_tendsto_cesaroFun` for `ψ = id`. -/
noncomputable def eChainSubseq {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    ℕ → ℕ :=
  Classical.choose (exists_subseq_tendsto_cesaroFun he id)

omit [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `eChainSubseq` is a convergent subsequence. -/
theorem cesaroConverges_eChainSubseq {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    CesaroConverges P (eChainSubseq he) :=
  (Classical.choose_spec (exists_subseq_tendsto_cesaroFun he id)).2

omit [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `eChainSubseq` tends to infinity. -/
theorem tendsto_eChainSubseq {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    Tendsto (eChainSubseq he) atTop atTop :=
  (Classical.choose_spec (exists_subseq_tendsto_cesaroFun he id)).1.tendsto_atTop

/-- **The limit kernel `Π` of an e-chain** (Theorem 12.4.1, MT p. 300). -/
noncomputable def eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    Kernel X X :=
  limKernel (cesaroConverges_eChainSubseq he)

/-- `Π` is a finite kernel. -/
theorem isFiniteKernel_eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    IsFiniteKernel (eChainLimit he) :=
  isFiniteKernel_limKernel _

/-- **Theorem 12.4.1 (i)**, (12.23) (MT p. 300): for an e-chain, `P̄ⁿ(x, ·) → Π(x, ·)` vaguely
for every `x`: `P̄ⁿ f(x) → ∫ f dΠ(x)` for every `f ∈ C_c(X)`; and `Π(x, X) ≤ 1`. Every
subsequence of times has a further subsequence along which the averages converge, and all the
limits coincide (`limMeasure_eq`). -/
theorem theorem_12_4_1_i {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    (∀ x, eChainLimit he x univ ≤ 1) ∧ ∀ f : C_c(X, ℝ), ∀ x,
      Tendsto (fun n => cesaroFun P n f x) atTop (𝓝 (∫ y, f y ∂eChainLimit he x)) := by
  refine ⟨fun x => limMeasure_univ_le P _ x, fun f x => tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto_cesaroFun he ns
  refine ⟨φ, ?_⟩
  have h := tendsto_limMeasure hconv f x
  rw [limMeasure_eq he hconv (hns.comp hφ.tendsto_atTop) (cesaroConverges_eChainSubseq he)
    (tendsto_eChainSubseq he) x] at h
  exact h

/-- `ΠP = Π`: each `Π(x, ·)` is invariant (Theorem 12.4.1 (ii)). -/
theorem isInvariant_eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    IsInvariant P (eChainLimit he x) :=
  isInvariant_limMeasure he (tendsto_eChainSubseq he) x

/-- `PΠ = Π` as kernels. -/
theorem eChainLimit_comp_kernel {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    eChainLimit he ∘ₖ P = eChainLimit he := by
  have := isFiniteKernel_eChainLimit he
  ext1 x
  have : IsFiniteMeasure ((eChainLimit he ∘ₖ P) x) := inferInstance
  have := isFiniteMeasure_limMeasure P (eChainSubseq he) x
  refine ext_of_integral_cc fun f => ?_
  rw [Kernel.integral_comp (f.integrable)]
  exact integral_limMeasure_kernel (cesaroConverges_eChainSubseq he) (tendsto_eChainSubseq he)
    f x

/-- `ΠP = Π` as kernels. -/
theorem kernel_comp_eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    P ∘ₖ eChainLimit he = eChainLimit he := by
  ext1 x
  rw [Kernel.comp_apply]
  exact isInvariant_eChainLimit he x

/-- `ΠΠ = Π` as kernels. -/
theorem eChainLimit_comp_self {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    eChainLimit he ∘ₖ eChainLimit he = eChainLimit he := by
  have := isFiniteKernel_eChainLimit he
  ext1 x
  have : IsFiniteMeasure ((eChainLimit he ∘ₖ eChainLimit he) x) := inferInstance
  have := isFiniteMeasure_limMeasure P (eChainSubseq he) x
  refine ext_of_integral_cc fun f => ?_
  rw [Kernel.integral_comp (f.integrable)]
  exact integral_limMeasure_limMeasure he (cesaroConverges_eChainSubseq he)
    (tendsto_eChainSubseq he) f x

/-- **Theorem 12.4.1 (ii)**, (12.25) (MT p. 300): `Pʲ Πᵏ Pˡ = Π` for all `j, ℓ` and `k ≥ 1`
(in Mathlib's order of composition, `Pˡ * Πᵏ * Pʲ = Π`), and every `Π(x, ·)` is invariant with
`Π(x, X) ≤ 1`. -/
theorem theorem_12_4_1_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    (∀ j k l : ℕ, 1 ≤ k → P ^ l * eChainLimit he ^ k * P ^ j = eChainLimit he) ∧
      ∀ x, IsInvariant P (eChainLimit he x) ∧ eChainLimit he x univ ≤ 1 := by
  set Pi := eChainLimit he
  have hPPi : P * Pi = Pi := kernel_comp_eChainLimit he
  have hPiP : Pi * P = Pi := eChainLimit_comp_kernel he
  have hPiPi : Pi * Pi = Pi := eChainLimit_comp_self he
  have hl : ∀ l : ℕ, P ^ l * Pi = Pi := fun l => by
    induction l with
    | zero => rw [pow_zero, one_mul]
    | succ l ih => rw [pow_succ, mul_assoc, hPPi, ih]
  have hj : ∀ j : ℕ, Pi * P ^ j = Pi := fun j => by
    induction j with
    | zero => rw [pow_zero, mul_one]
    | succ j ih => rw [pow_succ', ← mul_assoc, hPiP, ih]
  have hk : ∀ k : ℕ, Pi ^ (k + 1) = Pi := fun k => by
    induction k with
    | zero => rw [zero_add, pow_one]
    | succ k ih => rw [pow_succ, ih, hPiPi]
  refine ⟨fun j k l hk1 => ?_, fun x => ⟨isInvariant_eChainLimit he x,
    limMeasure_univ_le P _ x⟩⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [hk k', hl l, hj j]


omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `∫ f dμ ≤ μ(X)` for `0 ≤ f ≤ 1` and a finite measure `μ` (in `[0, ∞]`). -/
theorem ofReal_integral_le_univ {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ univ := by
  rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2))
    (Eventually.of_forall fun x => (h01 x).1)]
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun x => ENNReal.ofReal_le_one.2 (h01 x).2
    _ = μ univ := lintegral_one

/-- **Theorem 12.4.1 (iii)** (MT p. 300): an e-chain is bounded in probability on average iff
`Π(x, X) = 1` for every `x` (Proposition D.5.6: no mass escapes in the vague limit). -/
theorem theorem_12_4_1_iii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    IsBoundedInProbabilityOnAverage P ↔ ∀ x, eChainLimit he x univ = 1 := by
  have hfin := isFiniteKernel_eChainLimit he
  have hlim := (theorem_12_4_1_i he).2
  constructor
  · intro hb x
    refine le_antisymm ((theorem_12_4_1_i he).1 x) ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨C, hC, hliminf⟩ := hb x ε (by exact_mod_cast hε)
    obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
    rw [← tsub_le_iff_right]
    refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
    have hev := eventually_lt_of_lt_liminf (ha.trans_le hliminf)
    have hat : a ≠ ∞ := ne_top_of_lt ha
    have hle : a.toReal ≤ ∫ y, f y ∂eChainLimit he x := by
      refine ge_of_tendsto (hlim f x) ?_
      filter_upwards [hev] with n hn
      have := isFiniteKernel_cesaroKernel P n
      calc a.toReal ≤ (cesaroKernel P n x).real C :=
            ENNReal.toReal_mono (measure_ne_top _ _) hn.le
        _ ≤ cesaroFun P n f x :=
            measureReal_le_integral_of_indicator_le hC.measurableSet f.integrable hfC
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
      _ ≤ ENNReal.ofReal (∫ y, f y ∂eChainLimit he x) := ENNReal.ofReal_le_ofReal hle
      _ ≤ eChainLimit he x univ := ofReal_integral_le_univ (map_continuous f).measurable hf01
  · intro h1 x ε hε
    rcases le_or_gt 1 ε with hε1 | hε1
    · exact ⟨∅, isCompact_empty, by rw [tsub_eq_zero_of_le hε1]; exact zero_le⟩
    obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
    have hcut : Tendsto (fun n => ∫ y, φ n y ∂eChainLimit he x) atTop (𝓝 1) := by
      have := integral_cutoff_tendsto (μ := eChainLimit he x) hφ01 hφ1
        (BoundedContinuousFunction.const X 1)
      simp only [BoundedContinuousFunction.const_apply', one_mul, integral_const, smul_eq_mul,
        mul_one] at this
      rwa [measureReal_def, h1 x, ENNReal.toReal_one] at this
    set e := ε.toReal
    have he0 : 0 < e := ENNReal.toReal_pos hε.ne' (ne_top_of_lt hε1)
    obtain ⟨n, hn⟩ := (hcut.eventually (lt_mem_nhds (show 1 - e / 2 < 1 by linarith))).exists
    set C := tsupport (φ n)
    have hC : IsCompact C := (φ n).hasCompactSupport
    refine ⟨C, hC, le_liminf_of_le (by isBoundedDefault) ?_⟩
    filter_upwards [(hlim (φ n) x).eventually
      (lt_mem_nhds (show 1 - e < ∫ y, φ n y ∂eChainLimit he x by linarith))] with k hk
    have := isFiniteKernel_cesaroKernel P k
    have hle : cesaroFun P k (φ n) x ≤ (cesaroKernel P k x).real C := by
      rw [← integral_indicator_one (isClosed_tsupport _).measurableSet]
      refine integral_mono (φ n).integrable ((integrable_const 1).indicator
        (isClosed_tsupport _).measurableSet) fun y => ?_
      by_cases hy : y ∈ C
      · rw [indicator_of_mem hy, Pi.one_apply]; exact (hφ01 n y).2
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy]
    calc 1 - ε = ENNReal.ofReal (1 - e) := by
          rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
            ENNReal.ofReal_toReal (ne_top_of_lt hε1)]
      _ ≤ ENNReal.ofReal ((cesaroKernel P k x).real C) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = cesaroKernel P k x C := ENNReal.ofReal_toReal (measure_ne_top _ _)


/-! ### Theorem 12.0.1 (ii) -/

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `|∫ g dμ − ∫ g φ dμ| ≤ ‖g‖ (1 − ∫ φ dμ)` for a probability `μ` and `0 ≤ φ ≤ 1`. -/
theorem abs_integral_sub_mul_le {μ : Measure X} [IsProbabilityMeasure μ] (g : X →ᵇ ℝ)
    {φ : X → ℝ} (hφ : Continuous φ) (hφ01 : ∀ x, φ x ∈ Icc (0 : ℝ) 1) :
    |∫ x, g x ∂μ - ∫ x, g x * φ x ∂μ| ≤ ‖g‖ * (1 - ∫ x, φ x ∂μ) := by
  have hφi : Integrable φ μ := Integrable.of_bound hφ.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 x).1]; exact (hφ01 x).2)
  have hgφi : Integrable (fun x => g x * φ x) μ := Integrable.of_bound
    (g.continuous.mul hφ).aestronglyMeasurable ‖g‖ (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs (φ x), abs_of_nonneg (hφ01 x).1]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hφ01 x).2).trans (g.norm_coe_le_norm x))
  rw [← integral_sub (g.integrable μ) hgφi]
  calc |∫ x, (g x - g x * φ x) ∂μ| ≤ ∫ x, |g x - g x * φ x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖g‖ * (1 - φ x) ∂μ := by
        have hint : Integrable (fun x => ‖g‖ * (1 - φ x)) μ :=
          ((integrable_const (1 : ℝ)).sub hφi).const_mul ‖g‖
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hint
          (Eventually.of_forall fun x => ?_)
        change |g x - g x * φ x| ≤ ‖g‖ * (1 - φ x)
        rw [show g x - g x * φ x = g x * (1 - φ x) by ring, abs_mul,
          abs_of_nonneg (by linarith [(hφ01 x).2] : (0 : ℝ) ≤ 1 - φ x)]
        exact mul_le_mul_of_nonneg_right ((le_of_eq (Real.norm_eq_abs _).symm).trans
          (g.norm_coe_le_norm x)) (by linarith [(hφ01 x).2])
    _ = ‖g‖ * (1 - ∫ x, φ x ∂μ) := by
        rw [integral_const_mul, integral_sub (integrable_const 1) hφi]; simp


omit [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Vague convergence without loss of mass is weak convergence** (MT Section D.5): if
probabilities `μₙ → μ` vaguely and `μ` is a probability, then `∫ g dμₙ → ∫ g dμ` for every
bounded continuous `g`. -/
theorem tendsto_integral_bcf_of_cc {μs : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μs n)]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ)))
    (g : X →ᵇ ℝ) : Tendsto (fun n => ∫ x, g x ∂μs n) atTop (𝓝 (∫ x, g x ∂μ)) := by
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B := ‖g‖
  set η := ε / (4 * (B + 1))
  have hB : 0 ≤ B := norm_nonneg _
  have hη : 0 < η := div_pos hε (by positivity)
  have hcut : Tendsto (fun m => ∫ x, φ m x ∂μ) atTop (𝓝 1) := by
    have := integral_cutoff_tendsto (μ := μ) hφ01 hφ1 (BoundedContinuousFunction.const X 1)
    simpa using this
  obtain ⟨m, hm⟩ := (hcut.eventually (lt_mem_nhds (show 1 - η < 1 by linarith))).exists
  set gφ : C_c(X, ℝ) := ⟨⟨fun x => g x * φ m x, g.continuous.mul (φ m).continuous⟩,
    (φ m).hasCompactSupport.mul_left⟩
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (h gφ) (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (h (φ m)) η hη
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  rw [Real.dist_eq] at h1 h2 ⊢
  have e1 : |∫ x, g x ∂μs n - ∫ x, g x * φ m x ∂μs n| ≤ B * (1 - ∫ x, φ m x ∂μs n) :=
    abs_integral_sub_mul_le (μ := μs n) g (φ m).continuous (hφ01 m)
  have e2 : |∫ x, g x ∂μ - ∫ x, g x * φ m x ∂μ| ≤ B * (1 - ∫ x, φ m x ∂μ) :=
    abs_integral_sub_mul_le (μ := μ) g (φ m).continuous (hφ01 m)
  change |∫ x, g x * φ m x ∂μs n - ∫ x, g x * φ m x ∂μ| < ε / 4 at h1
  have h2' : 1 - ∫ x, φ m x ∂μs n < 2 * η := by
    have := (abs_lt.1 h2).1; linarith
  have hBη : B * (2 * η) + B * η ≤ 3 * ε / 4 := by
    have : B * η ≤ ε / 4 := by
      rw [show η = ε / (4 * (B + 1)) from rfl, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have t1 := abs_sub_le (∫ x, g x ∂μs n) (∫ x, g x * φ m x ∂μs n) (∫ x, g x ∂μ)
  have t2 := abs_sub_le (∫ x, g x * φ m x ∂μs n) (∫ x, g x * φ m x ∂μ) (∫ x, g x ∂μ)
  rw [abs_sub_comm (∫ x, g x * φ m x ∂μ)] at t2
  have b1 : B * (1 - ∫ x, φ m x ∂μs n) ≤ B * (2 * η) := mul_le_mul_of_nonneg_left h2'.le hB
  have b2 : B * (1 - ∫ x, φ m x ∂μ) ≤ B * η :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  linarith


/-- **`Π` is weak Feller when it is Markov** (MT p. 289, Theorem 12.0.1 (ii)): for bounded
continuous `g`, `Πg` is continuous. The functions `Π φₘ` are continuous (equicontinuity),
increase to `Π(·, X) = 1`, hence converge locally uniformly (Dini's theorem), and
`|Πg − Π(g φₘ)| ≤ ‖g‖ (1 − Π φₘ)`. -/
theorem continuous_integral_eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (h1 : ∀ x, eChainLimit he x univ = 1) (g : X →ᵇ ℝ) :
    Continuous fun x => ∫ y, g y ∂eChainLimit he x := by
  have hprob : ∀ x, IsProbabilityMeasure (eChainLimit he x) := fun x => ⟨h1 x⟩
  obtain ⟨φ, hφm, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  set σ := eChainSubseq he
  have hσ := cesaroConverges_eChainSubseq he
  set F : ℕ → X → ℝ := fun m x => ∫ y, φ m y ∂eChainLimit he x
  have hFc : ∀ m, Continuous (F m) := fun m => continuous_integral_limMeasure he hσ (φ m)
  have hFm : Monotone F := fun a b hab x => integral_mono (φ a).integrable (φ b).integrable
    fun y => hφm hab y
  have hF1 : ∀ x, Tendsto (fun m => F m x) atTop (𝓝 1) := fun x => by
    have := integral_cutoff_tendsto (μ := eChainLimit he x) hφ01 hφ1
      (BoundedContinuousFunction.const X 1)
    simpa using this
  have hloc : TendstoLocallyUniformly F (fun _ => 1) atTop :=
    Monotone.tendstoLocallyUniformly_of_forall_tendsto hFc hFm continuous_const hF1
  set G : ℕ → X → ℝ := fun m x => ∫ y, g y * φ m y ∂eChainLimit he x
  have hGc : ∀ m, Continuous (G m) := fun m => continuous_integral_limMeasure he hσ
    ⟨⟨fun x => g x * φ m x, g.continuous.mul (φ m).continuous⟩, (φ m).hasCompactSupport.mul_left⟩
  refine TendstoLocallyUniformly.continuous (F := G) (p := atTop) ?_ (Frequently.of_forall hGc)
  rw [Metric.tendstoLocallyUniformly_iff] at hloc ⊢
  intro ε hε x
  obtain ⟨t, ht, hev⟩ := hloc (ε / (‖g‖ + 1)) (by positivity) x
  refine ⟨t, ht, hev.mono fun m hm y hy => ?_⟩
  have h1y := hm y hy
  rw [Real.dist_eq] at h1y ⊢
  have e := abs_integral_sub_mul_le (μ := eChainLimit he y) g (φ m).continuous (hφ01 m)
  have hFle : F m y ≤ 1 := by
    calc F m y ≤ ∫ _, (1 : ℝ) ∂eChainLimit he y :=
          integral_mono (φ m).integrable (integrable_const 1) fun z => (hφ01 m z).2
      _ = 1 := by simp
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - F m y)] at h1y
  calc |∫ z, g z ∂eChainLimit he y - G m y| ≤ ‖g‖ * (1 - F m y) := e
    _ ≤ ‖g‖ * (ε / (‖g‖ + 1)) := mul_le_mul_of_nonneg_left h1y.le (norm_nonneg _)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg g]

/-- **Theorem 12.0.1 (ii)** (MT p. 289): for an e-chain bounded in probability on average, `Π`
is a weak Feller transition kernel, each `Π(x, ·)` is invariant, and `P̄ⁿ(x, f) → Π(x, f)` for
every bounded continuous `f` and every `x`. -/
theorem theorem_12_0_1_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) :
    IsMarkovKernel (eChainLimit he) ∧ IsWeakFeller (eChainLimit he) ∧
      (∀ x, IsInvariant P (eChainLimit he x)) ∧
      ∀ f : X →ᵇ ℝ, ∀ x, Tendsto (fun n => ∫ y, f y ∂cesaroKernel P (n + 1) x) atTop
        (𝓝 (∫ y, f y ∂eChainLimit he x)) := by
  have h1 := (theorem_12_4_1_iii he).1 hb
  have hM : IsMarkovKernel (eChainLimit he) := ⟨fun x => ⟨h1 x⟩⟩
  refine ⟨hM, (proposition_6_1_1_i_weak _).2 (continuous_integral_eChainLimit he h1),
    isInvariant_eChainLimit he, fun f x => ?_⟩
  have := fun n => isMarkovKernel_cesaroKernel P (n := n + 1) (by omega)
  exact tendsto_integral_bcf_of_cc (μs := fun n => cesaroKernel P (n + 1) x)
    (fun g => ((theorem_12_4_1_i he).2 g x).comp (tendsto_add_atTop_nat 1)) f

end MeynTweedie.Positivity
