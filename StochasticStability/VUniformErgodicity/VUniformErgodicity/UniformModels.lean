/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.UniformErgodic
import VUniformErgodicity.CountableChains
import Mathlib.Analysis.PSeries

/-!
# Uniformly ergodic models (MT §16.2.2–16.2.3)

Meyn and Tweedie, §16.2.2–16.2.3, pp. 403–407.

**Geometric convergence of moments** (§16.2.2, pp. 403–406). Uniform ergodicity need not give
geometric convergence of unbounded functionals. The book's ladder chain is replaced here by a
simpler chain with the same property (`resetKernel`): from `k` the chain jumps to `0` or to
`k + 1` with probability `½` each, `π(k) = 2^{−(k+1)}` (`resetPi`).
* `isInvariant_resetPi`, `resetKernel_isSmallSet`: `π` is invariant and the whole space is
  `½δ₀`-small, so (Theorem 16.2.4) `‖Pⁿ(x, ·) − π‖ ≤ 2 · 2⁻ⁿ` (`reset_uniformlyErgodic`).
* `resetF k = 2ᵏ/(k + 1)²` has `π(f) < ∞` (`lintegral_resetF_ne_top`), but
  `‖Pⁿ(x, ·) − π‖_f ≥ 1/(2(x + n + 1)²)` (`fNorm_reset_ge`, from `Pⁿ(x, {x + n}) ≥ 2⁻ⁿ`), so
  `Σ rⁿ ‖Pⁿ(x, ·) − π‖_f = ∞` for every `r > 1` and every `x` (`reset_not_fGeometric`):
  `Ex[f(Φₙ)] → π(f)` at no geometric rate.

**T-chains on compact sets** (§16.2.3, pp. 406–407).
* `isSmall_of_isCompact_tChain`: for a `ψ`-irreducible aperiodic T-chain compact sets are small
  (Theorems 6.2.5 (ii) and 5.5.7); this is the step of Lemma 16.2.6.
* `theorem_16_2_7_restrict`: the core of Lemma 16.2.6 and Theorem 16.2.7: for such a chain and a
  compact absorbing set `C`, the chain restricted to `C` has an invariant probability `π` and is
  uniformly ergodic, `‖P_Cⁿ(x, ·) − π‖ ≤ 2ρ^{⌊n/m⌋}`, so `E_y[f(Φₖ)] → ∫ f dπ` geometrically
  for bounded `f` and `y ∈ C`.

**Not formalised as stated.** In Lemma 16.2.6 and Theorem 16.2.7 the NSS(F) model enters through
Theorem 7.3.5 (a `ψ`-irreducible aperiodic T-chain) and through the sets `A₊(x)` of the control
model (compact by Lagrange stability, closed and absorbing); these are hypotheses of
`theorem_16_2_7_restrict` (a T-chain, a compact absorbing set). They are derived from the
NSS(F) and CM(F) hypotheses in `NSSUniformErgodic` (`lemma_16_2_6`, `theorem_16_2_7`).
The book's ladder example (16.24) is replaced by `resetKernel`, which proves the
same claim (a uniformly ergodic chain with `π(f) < ∞` and no geometric rate in `‖·‖_f`).
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-! ### T-chains on compact sets -/

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Compact sets are small** for a `ψ`-irreducible aperiodic T-chain (the step of Lemma 16.2.6,
MT p. 407: petite by Theorem 6.2.5 (ii), small by Theorem 5.5.7). -/
theorem isSmall_of_isCompact_tChain {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hT : IsTChain P) {K : Set X}
    (hK : IsCompact K) : IsSmall P K :=
  theorem_5_5_7 P hψ hap (theorem_6_2_5_ii hψ.2.1 hψ.1 hT hK)

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Lemma 16.2.6 and Theorem 16.2.7, for a T-chain** (MT pp. 406–407): let `P` be a
`ψ`-irreducible aperiodic T-chain and `C` a non-empty compact absorbing set (the book's `A₊(x)`
for a Lagrange stable model). Then the chain restricted to `C` has an invariant probability
`π`, the whole of `C` is `νₘ`-small, and `‖P_Cⁿ(x, ·) − π‖ ≤ 2ρ^{⌊n/m⌋}` with
`ρ = 1 − νₘ(C) < 1`: the restricted chain is uniformly ergodic, and for bounded measurable `f`,
`|E_y[f(Φₙ)] − ∫ f dπ| ≤ 2 sup|f| ρ^{⌊n/m⌋}` for every `y ∈ C`. -/
theorem theorem_16_2_7_restrict {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hT : IsTChain P) {C : Set X}
    (hCc : IsCompact C) (hCm : MeasurableSet C) (hAbs : IsAbsorbing P C) (hne : C.Nonempty) :
    haveI := isMarkovKernel_restrictKernel P hCm hAbs
    ∃ μ : Measure C, IsProbabilityMeasure μ ∧ IsUniformlyErgodic (restrictKernel P hCm) μ ∧
      ∃ m : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
        (∀ x n, tvNorm ((restrictKernel P hCm ^ n) x) μ ≤ 2 * ρ ^ (n / m)) ∧
        ∀ f : C → ℝ, Measurable f → ∀ M : ℝ, 0 < M → (∀ y, |f y| ≤ M) → ∀ y n,
          |∫ z, f z ∂(restrictKernel P hCm ^ n) y - ∫ z, f z ∂μ| ≤ M * (2 * ρ ^ (n / m)) := by
  have hM := isMarkovKernel_restrictKernel P hCm hAbs
  set Q := restrictKernel P hCm with hQ
  obtain ⟨m, ν, hsm⟩ := isSmall_of_isCompact_tChain hψ hap hT hCc
  obtain ⟨x₀, hx₀⟩ := hne
  have hemb := MeasurableEmbedding.subtype_coe hCm
  -- `ν` lives on `C`
  have hνC : ν Cᶜ = 0 :=
    le_antisymm ((hsm.2.2.2 x₀ hx₀ Cᶜ).trans (hAbs.pow_compl hCm m hx₀).le) zero_le
  set ν' : Measure C := ν.comap Subtype.val with hν'
  have hν'apply : ∀ B : Set C, ν' B = ν (Subtype.val '' B) := fun B =>
    hemb.comap_apply ν B
  have hν'univ : ν' univ = ν univ := by
    rw [hν'apply, image_univ, Subtype.range_coe, ← measure_add_measure_compl hCm, hνC,
      add_zero]
  have hν0 : ν univ ≠ 0 := fun h => hsm.2.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hνt : ν univ ≠ ∞ := by
    have := isMarkovKernel_pow P m
    exact ne_top_of_le_ne_top (measure_ne_top ((P ^ m) x₀) univ) (hsm.2.2.2 x₀ hx₀ univ)
  have hfin : IsFiniteMeasure ν' := ⟨by rw [hν'univ]; exact lt_top_iff_ne_top.2 hνt⟩
  -- the whole of `C` is `ν'`-small for the restricted chain
  have hsmQ : IsSmallSet Q m ν' univ := by
    refine ⟨MeasurableSet.univ, hsm.2.1, fun h => hν0 (by
      rw [← hν'univ, h, Measure.coe_zero, Pi.zero_apply]), fun y _ => Measure.le_intro
        fun B hB _ => ?_⟩
    rw [hν'apply, hQ, restrictKernel_pow_apply P hCm hAbs m y hB]
    exact hsm.2.2.2 y y.2 _
  -- irreducibility of the restricted chain
  have hφ : IsPhiIrreducible Q ν' := by
    intro B hB hpos y
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hsm.2.1
    refine (hitProb_pos_iff Q hB y).2 ⟨k, ?_⟩
    have := hsmQ.2.2.2 y (mem_univ y) B
    rw [hk, zero_add] at this
    exact hpos.trans_le this
  have hν'0 : ν' ≠ 0 := hsmQ.2.2.1
  have hψQ := isMaximalIrreducibility_maxIrrMeasure Q hφ hν'0
  have key := theorem_16_0_2 hψQ
  have k51 := key.out 5 1
  obtain ⟨μ, hμp, hUE⟩ := k51.1 ⟨m, ν', hsmQ⟩
  have hρ1 : ν'.real univ ≤ 1 := by
    rw [measureReal_def, hν'univ]
    have := isMarkovKernel_pow P m
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using (hsm.2.2.2 x₀ hx₀ univ).trans prob_le_one)
  have hρ0 : 0 < ν'.real univ := by
    rw [measureReal_def, hν'univ]; exact ENNReal.toReal_pos hν0 hνt
  have hrate := fun x n => theorem_16_2_4 hsmQ hUE.1 x n
  refine ⟨μ, hμp, hUE, m, 1 - ν'.real univ, by linarith, by linarith, hrate,
    fun f hf M hM hfM y n => ?_⟩
  have := isMarkovKernel_pow Q n
  calc |∫ z, f z ∂(Q ^ n) y - ∫ z, f z ∂μ| ≤ M * tvNorm ((Q ^ n) y) μ :=
        abs_integral_sub_le_mul_tvNorm _ _ hf hM hfM
    _ ≤ M * (2 * (1 - ν'.real univ) ^ (n / m)) := mul_le_mul_of_nonneg_left (hrate y n) hM.le

/-! ### Geometric convergence of moments (§16.2.2) -/

/-- The transition matrix of `resetKernel`: from `k` the chain jumps to `0` or to `k + 1`, with
probability `½` each. -/
noncomputable def resetMatrix (k j : ℕ) : ℝ≥0∞ :=
  2⁻¹ * (if j = 0 then 1 else 0) + 2⁻¹ * (if j = k + 1 then 1 else 0)

/-- The reset chain on `ℕ`. -/
noncomputable def resetKernel : Kernel ℕ ℕ := matKernel resetMatrix

/-- The rows of `resetMatrix` sum to one. -/
theorem isTransitionMatrix_resetMatrix : IsTransitionMatrix resetMatrix := fun k => by
  unfold resetMatrix
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, tsum_ite_eq, tsum_ite_eq,
    mul_one, ENNReal.inv_two_add_inv_two]

/-- The reset chain is a Markov kernel. -/
theorem isMarkovKernel_resetKernel : IsMarkovKernel resetKernel :=
  isMarkovKernel_matKernel isTransitionMatrix_resetMatrix

/-- The invariant law `π(k) = 2^{−(k+1)}` of the reset chain. -/
noncomputable def resetPi : Measure ℕ :=
  Measure.sum fun k => ((2 : ℝ≥0∞)⁻¹ ^ (k + 1)) • Measure.dirac k

/-- `π{j} = 2^{−(j+1)}`. -/
theorem resetPi_singleton (j : ℕ) : resetPi {j} = (2 : ℝ≥0∞)⁻¹ ^ (j + 1) :=
  Measure.sum_smul_dirac_singleton

/-- `Σₖ 2^{−(k+1)} = 1`. -/
theorem resetPi_tsum : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- `π` is a probability. -/
theorem isProbabilityMeasure_resetPi : IsProbabilityMeasure resetPi := by
  refine ⟨?_⟩
  rw [resetPi, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact resetPi_tsum

/-- **`π` is invariant** for the reset chain. -/
theorem isInvariant_resetPi : IsInvariant resetKernel resetPi := by
  have := isMarkovKernel_resetKernel
  unfold IsInvariant
  refine Measure.ext_iff_singleton.2 fun j => ?_
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _), lintegral_countable',
    resetPi_singleton]
  simp_rw [resetKernel, matKernel_singleton, resetPi_singleton]
  rcases j with _ | i
  · have e : ∀ k : ℕ, resetMatrix k 0 * (2 : ℝ≥0∞)⁻¹ ^ (k + 1) =
        2⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := fun k => by
      simp [resetMatrix]
    simp_rw [e]
    rw [ENNReal.tsum_mul_left, resetPi_tsum, mul_one, zero_add, pow_one]
  · rw [tsum_eq_single i fun k hk => by
      simp [resetMatrix, Ne.symm hk]]
    simp [resetMatrix, pow_succ]
    ring

/-- **The whole space is `½δ₀`-small** for the reset chain (with `m = 1`). -/
theorem resetKernel_isSmallSet :
    IsSmallSet resetKernel 1 ((2 : ℝ≥0∞)⁻¹ • Measure.dirac 0) univ := by
  refine ⟨MeasurableSet.univ, one_pos, by simp, fun x _ => Measure.le_intro fun B hB _ => ?_⟩
  rw [pow_one, Measure.smul_apply, smul_eq_mul, resetKernel, matKernel_apply,
    Measure.dirac_apply' _ hB]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  by_cases h0 : (0 : ℕ) ∈ B
  · rw [indicator_of_mem h0, indicator_of_mem h0, Pi.one_apply, mul_one]
    simp [resetMatrix]
  · rw [indicator_of_notMem h0, mul_zero]; exact zero_le

/-- **The reset chain is uniformly ergodic** (Theorem 16.2.4): `‖Pⁿ(x, ·) − π‖ ≤ 2 · 2⁻ⁿ`. -/
theorem reset_uniformlyErgodic (x n : ℕ) :
    haveI := isMarkovKernel_resetKernel
    haveI := isProbabilityMeasure_resetPi
    tvNorm ((resetKernel ^ n) x) resetPi ≤ 2 * (1 / 2) ^ n := by
  have := isMarkovKernel_resetKernel
  have := isProbabilityMeasure_resetPi
  have : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (0 : ℕ)) := ⟨by simp⟩
  have h := theorem_16_2_4 resetKernel_isSmallSet isInvariant_resetPi x n
  have hr : (1 : ℝ) - ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (0 : ℕ)).real univ = 1 / 2 := by
    simp [Measure.real]
    norm_num
  rwa [hr, Nat.div_one] at h

/-- The test function `f(k) = 2ᵏ/(k + 1)²` of the example. -/
noncomputable def resetF (k : ℕ) : ℝ≥0∞ := 2 ^ k / ((k : ℝ≥0∞) + 1) ^ 2

/-- `f(k) = 2ᵏ/(k + 1)²` as a real number. -/
theorem resetF_eq_ofReal (k : ℕ) : resetF k = ENNReal.ofReal (2 ^ k / ((k : ℝ) + 1) ^ 2) := by
  rw [resetF, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
  simp

/-- **`π(f) < ∞`**: `Σₖ 2^{−(k+1)} 2ᵏ/(k + 1)² = Σₖ 1/(2(k + 1)²)`. -/
theorem lintegral_resetF_ne_top : ∫⁻ k, resetF k ∂resetPi ≠ ∞ := by
  rw [lintegral_countable']
  simp_rw [resetPi_singleton, resetF_eq_ofReal]
  have e : ∀ k : ℕ, ENNReal.ofReal (2 ^ k / ((k : ℝ) + 1) ^ 2) * (2 : ℝ≥0∞)⁻¹ ^ (k + 1) =
      ENNReal.ofReal (1 / 2 * (1 / ((k : ℝ) + 1) ^ 2)) := fun k => by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_succ, inv_pow]
    field_simp
    ring
  simp_rw [e]
  have hs : Summable fun k : ℕ => 1 / 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  exact ENNReal.ofReal_ne_top

/-- `Pⁿ(x, {x + n}) ≥ 2⁻ⁿ`: the path that climbs at every step. -/
theorem resetKernel_pow_ge (n x : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n ≤ (resetKernel ^ n) x {x + n} := by
  induction n generalizing x with
  | zero =>
    rw [Nat.add_zero, pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton x), pow_zero]
  | succ n ih =>
    rw [pow_succ_apply _ n x (measurableSet_singleton _), resetKernel, lintegral_matKernel]
    refine le_trans ?_ (ENNReal.le_tsum (x + 1))
    have hp : resetMatrix x (x + 1) = 2⁻¹ := by simp [resetMatrix]
    rw [hp, pow_succ, mul_comm]
    have := ih (x + 1)
    rw [show x + 1 + n = x + (n + 1) by ring] at this
    exact mul_le_mul' le_rfl this

/-- **The `f`-norm stays large**: `‖Pⁿ(x, ·) − π‖_f ≥ 1/(2(x + n + 1)²)`. -/
theorem fNorm_reset_ge (x n : ℕ) :
    haveI := isMarkovKernel_resetKernel
    ENNReal.ofReal (1 / (2 * (((x + n : ℕ) : ℝ) + 1) ^ 2)) ≤
      fNorm resetF ((resetKernel ^ n) x) resetPi := by
  have := isMarkovKernel_resetKernel
  have := isProbabilityMeasure_resetPi
  have := isMarkovKernel_pow resetKernel n
  set j := x + n with hj
  set F : ℝ := 2 ^ j / ((j : ℝ) + 1) ^ 2 with hF
  have hF0 : 0 ≤ F := by positivity
  set g : ℕ → ℝ := ({j} : Set ℕ).indicator fun _ => F with hg
  have htest : IsFTest resetF ((resetKernel ^ n) x) resetPi g := by
    have hgm : Measurable g := measurable_of_countable _
    have hb : ∀ y, ‖g y‖ ≤ F := fun y => by
      by_cases hy : y = j
      · simp [hg, hy, abs_of_nonneg hF0]
      · rw [hg, Set.indicator_of_notMem (show y ∉ ({j} : Set ℕ) from hy), norm_zero]
        exact hF0
    refine ⟨hgm, fun y => ?_, Integrable.of_bound hgm.aestronglyMeasurable F
      (Eventually.of_forall hb), Integrable.of_bound hgm.aestronglyMeasurable F
        (Eventually.of_forall hb)⟩
    by_cases hy : y = j
    · subst hy
      simp only [hg, Set.indicator_of_mem (mem_singleton _), abs_of_nonneg hF0]
      rw [resetF_eq_ofReal]
    · simp [hg, hy]
  have hkey := ofReal_abs_integral_sub_le_fNorm htest
  rw [hg, integral_indicator_const _ (measurableSet_singleton j),
    integral_indicator_const _ (measurableSet_singleton j), smul_eq_mul, smul_eq_mul] at hkey
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hkey
  -- the real estimate
  have h1 : (1 / 2 : ℝ) ^ n ≤ ((resetKernel ^ n) x).real {j} := by
    have h := resetKernel_pow_ge n x
    rw [measureReal_def]
    have : ((2 : ℝ≥0∞)⁻¹ ^ n).toReal = (1 / 2) ^ n := by simp
    rw [← this]
    exact ENNReal.toReal_mono (measure_ne_top _ _) h
  have h2 : resetPi.real {j} = (1 / 2) ^ (j + 1) := by
    rw [measureReal_def, resetPi_singleton]; simp
  have h3 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h4 : (2 : ℝ) ^ n ≤ 2 ^ j := pow_le_pow_right₀ one_le_two (by omega)
  rw [h2]
  have hdiff : (1 / 2 : ℝ) ^ (n + 1) ≤ ((resetKernel ^ n) x).real {j} - (1 / 2) ^ (j + 1) := by
    have h5 : (1 / 2 : ℝ) ^ n = 2 * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring
    linarith
  have hpos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
  have h6 : (2 : ℝ) ^ n * (1 / 2) ^ (n + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  calc 1 / (2 * ((j : ℝ) + 1) ^ 2) = 2 ^ n * (1 / 2) ^ (n + 1) / ((j : ℝ) + 1) ^ 2 := by
        rw [h6]; field_simp
    _ ≤ F * ((1 / 2) ^ (n + 1)) := by
        rw [hF, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (by positivity))
          hpos.le
    _ ≤ F * (((resetKernel ^ n) x).real {j} - (1 / 2) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left hdiff hF0
    _ ≤ |((resetKernel ^ n) x).real {j} * F - (1 / 2) ^ (j + 1) * F| := by
        rw [← sub_mul, mul_comm]; exact le_abs_self _

/-- **No geometric rate in the `f`-norm** (MT pp. 404–405): although the reset chain is uniformly
ergodic and `π(f) < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f = ∞` for every `r > 1` and every `x`. -/
theorem reset_not_fGeometric (x : ℕ) {r : ℝ≥0∞} (hr : 1 < r) :
    haveI := isMarkovKernel_resetKernel
    ∑' n, r ^ n * fNorm resetF ((resetKernel ^ n) x) resetPi = ∞ := by
  have := isMarkovKernel_resetKernel
  by_contra hfin
  have hlim := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin
  -- the terms are eventually at least `1`
  have hev : ∀ᶠ n in atTop, 1 ≤ r ^ n * fNorm resetF ((resetKernel ^ n) x) resetPi := by
    rcases eq_or_ne r ∞ with rfl | hrt
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hpos : 0 < fNorm resetF ((resetKernel ^ n) x) resetPi :=
        lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) (fNorm_reset_ge x n)
      rw [ENNReal.top_pow (by omega), ENNReal.top_mul hpos.ne']
      exact le_top
    · set s := r.toReal with hs
      have hs1 : 1 < s := by
        rw [hs, ← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono hrt hr
      have hrs : r = ENNReal.ofReal s := (ENNReal.ofReal_toReal hrt).symm
      have hlim2 := tendsto_pow_const_div_const_pow_of_one_lt 2 hs1
      filter_upwards [hlim2.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)),
        eventually_ge_atTop (x + 1)] with n h8 hn
      have hsn : 0 < s ^ n := pow_pos (by linarith) n
      have h8' : (n : ℝ) ^ 2 ≤ s ^ n / 8 := by
        have := (div_le_iff₀ hsn).1 h8
        linarith
      have hcn : ((x + n : ℕ) : ℝ) + 1 ≤ 2 * n := by
        have : ((x + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        push_cast at this ⊢; linarith
      have hc0 : (0 : ℝ) ≤ ((x + n : ℕ) : ℝ) + 1 := by positivity
      have hreal : 1 ≤ s ^ n * (1 / (2 * (((x + n : ℕ) : ℝ) + 1) ^ 2)) := by
        have hsq : (((x + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
        have hpos : (0 : ℝ) < 2 * (((x + n : ℕ) : ℝ) + 1) ^ 2 := by positivity
        rw [mul_one_div, le_div_iff₀ hpos, one_mul]
        linarith
      calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (s ^ n * (1 / (2 * (((x + n : ℕ) : ℝ) + 1) ^ 2))) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hreal
        _ = r ^ n * ENNReal.ofReal (1 / (2 * (((x + n : ℕ) : ℝ) + 1) ^ 2)) := by
            rw [hrs, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ r ^ n * fNorm resetF ((resetKernel ^ n) x) resetPi :=
            mul_le_mul' le_rfl (fNorm_reset_ge x n)
  have h2 := hlim.eventually (gt_mem_nhds (zero_lt_one))
  obtain ⟨n, hn1, hn2⟩ := (hev.and h2).exists
  exact absurd (hn1.trans_lt hn2) (lt_irrefl _)

end MeynTweedie.VUniformErgodicity
