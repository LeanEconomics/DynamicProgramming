/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ConvergenceSLPFellerInvariant
import MarkovProcesses.GeneralKernels
import MarkovProcesses.ConvergenceStrong

/-!
# Weak convergence: tightness, Prohorov, the Feller property and Krylov–Bogolubov

Miao, §3.3.2, pp. 108–111. `X` is a metric space with its Borel σ-algebra.

* **Definition 3.3.2**: `λₙ ⇒ λ` is SLP's `ConvWeak` (`definition_3_3_2`). Strong convergence
  implies weak convergence (p. 104, `eq_p104_strong_imp_weak`), and `δ_{1/(n+1)} ⇒ δ₀` weakly but
  not strongly (p. 108, `eq_p108_dirac`).
* **Definition 3.3.3**: tight families (`IsTightFamily`).
* **Theorem 3.3.2** (Prohorov). As printed ("there exist `μ` and a subsequence `μₙₖ ⇒ μ` iff
  `{μₙ}` is tight") the "only if" is false: on `ℝ`, `μₙ = δ₀` for even `n` and `μₙ = δₙ` for odd
  `n` has the convergent subsequence `(δ₀)` but is not tight (`theorem_3_3_2_counterexample`).
  Proved: on a complete separable metric space `{μₙ}` is tight iff every subsequence has a
  weakly convergent further subsequence (`theorem_3_3_2`). Tight ⇒ convergent subsequence is
  Mathlib's Prokhorov theorem (via SLP's `gp_exists_convWeak_subseq_of_tight`), and it needs no
  completeness. The converse follows Mathlib's `isTightMeasureSet_of_isCompact_closure`, with
  its compactness hypothesis replaced by the sequential one and the portmanteau theorem
  (SLP Theorem 12.3).
* **Definition 3.3.4**: the Feller property is SLP's `IsFeller` (`definition_3_3_4`).
* **Theorem 3.3.3** (Krylov–Bogolubov, `theorem_3_3_3`): the book's proof with the Cesàro
  averages `(1/n) Σ_{k ≤ n} Pᵏ(x, ·)`. Completeness of `X` is not needed.
* **Corollary 3.3.1** (`corollary_3_3_1`), SLP Theorem 12.10. Departure: `X` must be nonempty.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **Definition 3.3.3** (Miao, p. 109): a family `M` of probability measures is **tight** if for
every `ε > 0` there is a compact `K` with `λ(K) ≥ 1 − ε` for all `λ ∈ M`. -/
def IsTightFamily [TopologicalSpace X] (M : Set (Measure X)) : Prop :=
  ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ lam ∈ M, 1 - ε ≤ lam.real K

/-- **Definition 3.3.2** (Miao, p. 109): `λₙ ⇒ λ` iff `∫ f dλₙ → ∫ f dλ` for every bounded
continuous `f`. -/
theorem definition_3_3_2 [MetricSpace X] (ls : ℕ → Measure X) (l : Measure X) :
    ConvWeak ls l ↔ ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂ls n) atTop (𝓝 (∫ x, f x ∂l)) :=
  Iff.rfl

/-- **Definition 3.3.4** (Miao, p. 110): `P` has the **Feller property** iff `T` maps the bounded
continuous functions into themselves. -/
theorem definition_3_3_4 [MetricSpace X] [BorelSpace X] (κ : Kernel X X) [IsMarkovKernel κ] :
    IsFeller κ ↔ ∀ f : X →ᵇ ℝ, ∃ g : X →ᵇ ℝ, ⇑g = markovOpR κ f := by
  constructor
  · intro hF f
    exact ⟨gp_fellerBCF hF f, rfl⟩
  · rintro h f hf ⟨M, hM⟩
    have hb : ∀ x y, dist (f x) (f y) ≤ 2 * M := fun x y => by
      rw [Real.dist_eq]; linarith [abs_sub (f x) (f y), hM x, hM y]
    obtain ⟨g, hg⟩ := h (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) hb)
    have : markovOpR κ f = g := hg.symm
    rw [this]
    exact g.continuous

/-- Tight sequences have weakly convergent subsequences (Prokhorov). -/
theorem gp_exists_convWeak_subseq [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (h : IsTightFamily (Set.range μ)) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (μ ∘ φ) ν :=
  gp_exists_convWeak_subseq_of_tight μ fun ε hε => by
    obtain ⟨K, hK, hKμ⟩ := h (ε / 2) (by positivity)
    exact ⟨K, hK, fun n => by linarith [hKμ (μ n) ⟨n, rfl⟩]⟩

/-- **Theorem 3.3.2** (Prohorov, Miao, p. 109), corrected. On a complete separable metric space
a sequence of probability measures is tight iff every subsequence (indeed every sequence
`μ ∘ ψ`) has a weakly convergent subsequence. -/
theorem theorem_3_3_2 [MetricSpace X] [TopologicalSpace.SeparableSpace X] [CompleteSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)] :
    IsTightFamily (Set.range μ) ↔ ∀ ψ : ℕ → ℕ, ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (fun k => μ (ψ (φ k))) ν := by
  constructor
  · intro h ψ
    have : ∀ n, IsProbabilityMeasure ((μ ∘ ψ) n) := fun n => inferInstanceAs
      (IsProbabilityMeasure (μ (ψ n)))
    obtain ⟨ν, hν, φ, hφ, hc⟩ := gp_exists_convWeak_subseq (μ ∘ ψ) fun ε hε => by
      obtain ⟨K, hK, hKμ⟩ := h ε hε
      exact ⟨K, hK, fun lam ⟨n, hn⟩ => hKμ lam ⟨ψ n, hn⟩⟩
    exact ⟨ν, hν, φ, hφ, hc⟩
  · intro H ε hε
    have : Nonempty X := nonempty_of_isProbabilityMeasure (μ 0)
    obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq X
    set u : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hu : ∀ m, 0 < u m := fun m => by positivity
    set G : ℕ → ℕ → Set X := fun m k => ⋃ i ∈ Finset.range (k + 1), Metric.ball (D i) (u m)
    have hGo : ∀ m k, IsOpen (G m k) := fun m k => isOpen_biUnion fun i _ => Metric.isOpen_ball
    have hGmono : ∀ m, Monotone (G m) := fun m k k' hkk' =>
      Set.biUnion_subset_biUnion_left fun i hi => by
        simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢; omega
    have hGU : ∀ m, ⋃ k, G m k = Set.univ := fun m => by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := hD.exists_dist_lt x (hu m)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self i))
        (by rw [Metric.mem_ball]; exact hi)⟩
    have claim : ∀ m (δ : ℝ), 0 < δ → ∃ k, ∀ n, 1 - δ < (μ n).real (G m k) := by
      intro m δ hδ
      by_contra hcon
      push Not at hcon
      choose ψ hψ using hcon
      obtain ⟨ν, hν, φ, hφ, hconv⟩ := H ψ
      have hlim := (slp_theorem_12_3 _ ν).2.1.1 hconv
      have hbound : ∀ j, ν.real (G m j) ≤ 1 - δ / 2 := by
        intro j
        have ev := hlim (G m j) (hGo m j) (δ / 2) (half_pos hδ)
        obtain ⟨k, hk1, hk2⟩ := (ev.and (eventually_ge_atTop j)).exists
        have : (μ (ψ (φ k))).real (G m j) ≤ (μ (ψ (φ k))).real (G m (φ k)) :=
          measureReal_mono (hGmono m (hk2.trans (hφ.id_le k))) (measure_ne_top _ _)
        linarith [hψ (φ k)]
      have htend : Tendsto (fun j => ν.real (G m j)) atTop (𝓝 (ν.real Set.univ)) := by
        have := tendsto_measure_iUnion_atTop (μ := ν) (hGmono m)
        rw [hGU m] at this
        exact (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp this
      rw [probReal_univ] at htend
      have := le_of_tendsto' htend hbound
      linarith
    set δ : ℕ → ℝ := fun m => ε / 2 / 2 ^ m
    have hδ : ∀ m, 0 < δ m := fun m => by positivity
    choose k hk using fun m => claim m (δ m) (hδ m)
    set C : ℕ → Set X := fun m => ⋃ i ∈ Finset.range (k m + 1), Metric.closedBall (D i) (u m)
    have hGC : ∀ m, G m (k m) ⊆ C m := fun m =>
      Set.biUnion_mono subset_rfl fun i _ => Metric.ball_subset_closedBall
    have hCc : ∀ m, IsClosed (C m) := fun m =>
      isClosed_biUnion_finset fun i _ => Metric.isClosed_closedBall
    set K := ⋂ m, C m
    have hKc : IsClosed K := isClosed_iInter hCc
    have hKt : TotallyBounded K := by
      refine Metric.totallyBounded_iff.2 fun r hr => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
      refine ⟨D '' (Finset.range (k m + 1) : Set ℕ), (Finset.finite_toSet _).image _, ?_⟩
      intro x hx
      have hxC := Set.mem_iInter.1 hx m
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hxC
      refine Set.mem_iUnion₂.2 ⟨D i, ⟨i, hi, rfl⟩, ?_⟩
      exact Metric.closedBall_subset_ball hm hxi
    refine ⟨K, hKt.isCompact_of_isClosed hKc, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hCn : ∀ m, μ n (C m)ᶜ ≤ ENNReal.ofReal (δ m) := fun m => by
      rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [probReal_compl_eq_one_sub (hCc m).measurableSet]
      linarith [hk m n, measureReal_mono (μ := μ n) (hGC m) (measure_ne_top _ _)]
    have hKn : μ n Kᶜ ≤ ENNReal.ofReal ε := by
      calc μ n Kᶜ = μ n (⋃ m, (C m)ᶜ) := by rw [Set.compl_iInter]
        _ ≤ ∑' m, μ n (C m)ᶜ := measure_iUnion_le _
        _ ≤ ∑' m, ENNReal.ofReal (δ m) := ENNReal.tsum_le_tsum hCn
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => (hδ m).le) (summable_geometric_two' ε),
            tsum_geometric_two']
    have hKr : (μ n).real Kᶜ ≤ ε := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hKn
    rw [probReal_compl_eq_one_sub hKc.measurableSet] at hKr
    linarith

/-- **Theorem 3.3.2** as printed is false (Miao, p. 109): on `ℝ` the sequence `δ₀, δ₁, δ₀, δ₃, …`
(`μₙ = δ₀` for even `n`, `δₙ` for odd `n`) has a weakly convergent subsequence but is not
tight. -/
theorem theorem_3_3_2_counterexample :
    let μ : ℕ → Measure ℝ := fun n => if Even n then Measure.dirac 0 else Measure.dirac (n : ℝ)
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (μ ∘ φ) ν) ∧
      ¬ IsTightFamily (Set.range μ) := by
  intro μ
  refine ⟨⟨Measure.dirac 0, inferInstance, fun k => 2 * k, fun a b hab => by
    change 2 * a < 2 * b; omega,
    fun f => ?_⟩, fun h => ?_⟩
  · have : (fun n => ∫ x, f x ∂(μ ∘ fun k => 2 * k) n) = fun _ => ∫ x, f x ∂Measure.dirac 0 :=
      funext fun n => by simp [μ]
    rw [this]
    exact tendsto_const_nhds
  · obtain ⟨K, hK, hKμ⟩ := h (1 / 2) (by norm_num)
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
    set n := 2 * ⌈R⌉₊ + 1
    have hodd : ¬ Even n := by simp [n]
    have hnR : R < (n : ℝ) := by
      have := Nat.le_ceil R
      simp only [n]
      push_cast
      linarith [show (0 : ℝ) ≤ ⌈R⌉₊ from Nat.cast_nonneg _]
    have hnK : (n : ℝ) ∉ K := fun hn => by
      have := hR hn
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] at this
      linarith
    have := hKμ (μ n) ⟨n, rfl⟩
    simp only [μ, hodd, ↓reduceIte] at this
    rw [measureReal_def, Measure.dirac_apply' _ hK.measurableSet,
      Set.indicator_of_notMem hnK] at this
    norm_num at this

/-- Miao, p. 104: strong convergence implies weak convergence. -/
theorem eq_p104_strong_imp_weak [MetricSpace X] [BorelSpace X] (ls : ℕ → Measure X)
    (l : Measure X) [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (h : ConvStrongly ls l) : ConvWeak ls l := by
  intro f
  set C := ‖f‖ + 1
  have hC : 0 < C := by positivity
  have hg : ∀ x, |f x / C| ≤ 1 := fun x => by
    rw [abs_div, abs_of_pos hC, div_le_one hC]
    exact (gp_bcf_abs_le_norm f x).trans (by linarith)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    ((h.const_mul (2 * C)).trans_eq (by rw [mul_zero]) :
      Tendsto (fun n => 2 * C * dTV (ls n) l) atTop (𝓝 0))
  have := gp_abs_integral_sub_le_tvDist (ls n) l (f.continuous.measurable.div_const C) hg
  rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hC, div_le_iff₀ hC,
    gp_tvDist_eq_two_mul_dTV] at this
  rw [Real.norm_eq_abs]
  linarith

/-- Miao, p. 108: `δ_{1/(n+1)} ⇒ δ₀` weakly, but `dTV(δ_{1/(n+1)}, δ₀) = 1` for all `n`, so the
convergence is not strong. -/
theorem eq_p108_dirac :
    ConvWeak (fun n : ℕ => Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac 0) ∧
      ∀ n : ℕ, dTV (Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac (0 : ℝ)) = 1 := by
  refine ⟨gp_convWeak_dirac tendsto_one_div_add_atTop_nhds_zero_nat, fun n => ?_⟩
  refine le_antisymm (gp_dTV_le_one _ _) ?_
  have h := gp_abs_le_dTV (Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac (0 : ℝ))
    (MeasurableSet.singleton 0)
  have hne : (1 / ((n : ℝ) + 1)) ∉ ({0} : Set ℝ) := by
    rw [Set.mem_singleton_iff]; positivity
  have e1 : (Measure.dirac (1 / ((n : ℝ) + 1))).real {0} = 0 := by
    rw [measureReal_def, Measure.dirac_apply' _ (MeasurableSet.singleton 0),
      Set.indicator_of_notMem hne, ENNReal.toReal_zero]
  have e2 : (Measure.dirac (0 : ℝ)).real {0} = 1 := by simp
  rw [e1, e2, zero_sub, abs_neg, abs_one] at h
  exact h

/-- **Theorem 3.3.3** (Krylov–Bogolubov, Miao, p. 110). If `P` is Feller on a separable metric
space and `{Pⁿ(x, ·)}_{n ≥ 1}` is tight for some `x`, then `P` has an invariant probability
measure. The proof is the book's: a weak limit of the Cesàro averages of `Pⁿ(x, ·)`. -/
theorem theorem_3_3_3 [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]
    {κ : Kernel X X} [IsMarkovKernel κ] (hF : IsFeller κ) {x : X}
    (htight : IsTightFamily {lam | ∃ n, 1 ≤ n ∧ lam = kpow κ n x}) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  set lam₀ := κ x
  set L : ℕ → Measure X := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => gp_isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  have hLk : ∀ n, L n = kpow κ (n + 1) x := fun n => by
    simp only [L, lam₀]
    rw [← gp_adjointOp_dirac κ x, ← Function.iterate_succ_apply, gp_adjointOp_iterate,
      gp_adjointOp_dirac]
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  have hc1 : ∀ N, c N * ((N : ℝ≥0∞) + 1) = 1 := fun N =>
    ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)
  set avg : ℕ → Measure X := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact hc1 N⟩
  have hint : ∀ N (g : X →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : X →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← gp_integral_markovOpR κ (avg N) g]
    change ∫ s, gp_fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← gp_integral_markovOpR κ (L n) g]
    rfl
  -- the Cesàro averages are tight
  have htavg : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ N, 1 - ε < (avg N).real K := by
    intro ε hε
    obtain ⟨K, hK, hKL⟩ := htight (ε / 2) (by positivity)
    refine ⟨K, hK, fun N => ?_⟩
    have hLK : ∀ n, ENNReal.ofReal (1 - ε / 2) ≤ L n K := fun n => by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hKL _ ⟨n + 1, by omega, hLk n⟩)
    have hle : ENNReal.ofReal (1 - ε / 2) ≤ avg N K := by
      calc ENNReal.ofReal (1 - ε / 2)
          = c N * (((N : ℝ≥0∞) + 1) * ENNReal.ofReal (1 - ε / 2)) := by
            rw [← mul_assoc, hc1, one_mul]
        _ ≤ c N * ∑ n ∈ Finset.range (N + 1), L n K := by
            gcongr
            calc ((N : ℝ≥0∞) + 1) * ENNReal.ofReal (1 - ε / 2)
                = ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (1 - ε / 2) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
              _ ≤ ∑ n ∈ Finset.range (N + 1), L n K := Finset.sum_le_sum fun n _ => hLK n
        _ = avg N K := by
            simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
              smul_eq_mul]
    have := ENNReal.toReal_mono (measure_ne_top _ K) hle
    rw [ENNReal.toReal_ofReal'] at this
    rw [measureReal_def]
    linarith [le_max_left (1 - ε / 2) 0]
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := gp_exists_convWeak_subseq_of_tight avg htavg
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, gp_invariant_of_convWeak hF hconv fun f => ?_⟩
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

/-- **Corollary 3.3.1** (Miao, p. 111; SLP Theorem 12.10). On a nonempty compact metric space
every Feller transition function has an invariant distribution. -/
theorem corollary_3_3_1 [MetricSpace X] [CompactSpace X] [Nonempty X] [BorelSpace X]
    {κ : Kernel X X} [IsMarkovKernel κ] (hF : IsFeller κ) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ :=
  slp_theorem_12_10 hF

end Miao.MarkovProcesses
