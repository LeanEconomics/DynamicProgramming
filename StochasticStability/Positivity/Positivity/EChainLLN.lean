/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.EChainAperiodic

/-!
# The law of large numbers for e-chains (MT §18.5; Theorems 18.5.1 and 18.0.2 (ii))

Meyn and Tweedie, pp. 463–464 and 477–480. `X` is a locally compact, second-countable,
metrizable Hausdorff space with its Borel σ-algebra, `Π = eChainLimit he`, and the chain started
at `x` lives on `pathMeasure P (Measure.dirac x)`.

**Martingale differences.** `mdTerm P h j` is `Dⱼ₊₁ = h(Φⱼ₊₁) − Ph(Φⱼ)` and `mdSum P h m` is
`Mₘ = Σ_{j<m} Dⱼ₊₁`. For bounded measurable `h`: `integral_mul_mdTerm` (orthogonality, from the
Markov property), `integral_mdSum_sq_le` (`E[Mₘ²] ≤ 4B²m`), `measure_abs_mdSum_ge_le`
(Chebyshev), `tendsto_measure_abs_mdSum_div` (weak law) and `ae_tendsto_mdSum_div`, the strong
law `Mₘ/m → 0` a.s. that the book takes from Doob (Theorem 5.2 of Chapter 4 of [99]); it is
proved by Chebyshev's bound along the squares, Borel–Cantelli and the bounded increments.

**The decomposition (18.33)–(18.34).** `iterFun P f i = Pⁱf`, `cesaroIter P f M = P̄ᴹf`
(`cesaroIter_eq_cesaroFun`); `sum_sub_sum_kfunR_eq`, `sum_sub_sum_iterFun_eq`,
`abs_sum_sub_sum_cesaroIter_le` ((18.34)), `abs_occAvg_sub_le`, `tendsto_mdRemainder`;
`integral_occAvg`: `E_x[(1/N) Σ_{k=1}^N g(Φₖ)] = P̄ᴺ(x, g)`; `occMeasure` is `μ̃_N` of (18.30).

**Results.**
* **Theorem 18.5.1 (i)** (`theorem_18_5_1_i`, p. 478): for an e-chain bounded in probability on
  average with a reachable state there is a unique invariant probability `π`, and
  `(1/N) Σ_{k=1}^N f(Φₖ) → π(f)` in `P_x`-probability for bounded continuous `f` and every `x`
  (core: `tendsto_occAvg_inProb`).
* **Theorem 18.5.1 (ii)** (`theorem_18_5_1_ii`, p. 478): if the occupation probabilities are
  a.s. tight, `μ̃_N → π` weakly a.s. (18.31). Tools: `eventually_forall_abs_cesaroIter_sub_le`
  (`P̄ᴹf → π(f)` uniformly on compacts for `f ∈ C_c(X)`), `tendsto_occAvg_of_tight` (the strong
  law along one tight path), `tendsto_occAvg_cc_of_dense` (from a dense sequence in `C_c(X)` to
  all of it) and `tendsto_occAvg_bcf_of_cc` (vague to weak, `π` being a probability).
* **Theorem 18.0.2 (ii)** (`theorem_18_0_2_ii`, p. 463): for an e-chain with a reachable state,
  (a) unique invariant probability with Cesàro convergence and the weak law, (b) bounded in
  probability on average, (c) non-evanescent with `x*` positive, are equivalent; with an
  aperiodic reachable state, `Pᵏ(x, ·) → π` weakly (18.5).

Theorem 18.5.2 is in `EChainDriftLLN`.

**Method.** In (i) the book bounds `(1/N) Σₖ |P̄ᴹf(Φₖ) − π(f)|` through (18.32), uniform
convergence on a compact set plus the time spent outside it. Here its `P_x`-mean is used instead:
it is `P̄ᴺ(x, |P̄ᴹf − π(f)|)`, which tends to `π(|P̄ᴹf − π(f)|)` as `N → ∞` because `P̄ᴹf` is
continuous (the chain is weak Feller) and `P̄ᴺ(x, ·) → π` weakly, and this tends to `0` as
`M → ∞` by dominated convergence. Markov's inequality then gives (i). For (ii) the book's route
through (18.32) is followed.

**Hypotheses.**
* Theorem 18.5.1 (ii): a.s. tightness is assumed in the eventual form "for every `δ > 0` there is
  a compact `K` with `μ̃_N(Kᶜ) ≤ δ` for all large `N`", which tightness of `{μ̃_N}` implies.
* Theorem 18.0.2 (ii) (c): positivity of `x*` is the Cesàro form `IsCesaroPositive`, as in
  Proposition 18.4.2 (see `EChainPositivity`).

**Correction.** None.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction CompactlySupported

variable {X : Type*} [MeasurableSpace X]

/-! ### Martingale differences on the path space -/

/-- The martingale difference `Dⱼ₊₁ = h(Φⱼ₊₁) − Ph(Φⱼ)`. -/
noncomputable def mdTerm (P : Kernel X X) (h : X → ℝ) (j : ℕ) (ω : ℕ → X) : ℝ :=
  h (ω (j + 1)) - kfunR P h (ω j)

/-- The martingale `Mₘ = Σ_{j < m} Dⱼ₊₁`. -/
noncomputable def mdSum (P : Kernel X X) (h : X → ℝ) (m : ℕ) (ω : ℕ → X) : ℝ :=
  ∑ j ∈ Finset.range m, mdTerm P h j ω

/-- `Dⱼ₊₁` is `𝓕ₙ`-measurable for `j + 1 ≤ n`. -/
theorem measurable_mdTerm (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ} (hh : Measurable h)
    {j n : ℕ} (hjn : j + 1 ≤ n) : Measurable[natFilt n] (mdTerm P h j) := by
  have h1 : Measurable[natFilt n] fun ω : ℕ → X => ω (j + 1) :=
    (measurable_coord_natFilt (j + 1)).mono ((natFilt (X := X)).mono hjn) le_rfl
  have h2 : Measurable[natFilt n] fun ω : ℕ → X => ω j :=
    (measurable_coord_natFilt j).mono ((natFilt (X := X)).mono (by omega)) le_rfl
  exact (hh.comp h1).sub ((measurable_kfunR P hh).comp h2)

/-- `Mₘ` is `𝓕ₘ`-measurable. -/
theorem measurable_mdSum (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ} (hh : Measurable h)
    (m : ℕ) : Measurable[natFilt m] (mdSum P h m) := by
  unfold mdSum
  exact Finset.measurable_sum _ fun j hj =>
    measurable_mdTerm P hh (Nat.succ_le_of_lt (Finset.mem_range.1 hj))

/-- `|Dⱼ₊₁| ≤ 2B`. -/
theorem abs_mdTerm_le (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ} {B : ℝ}
    (hB : ∀ y, |h y| ≤ B) (j : ℕ) (ω : ℕ → X) : |mdTerm P h j ω| ≤ 2 * B := by
  have := abs_kfunR_le P hB (ω j)
  calc |mdTerm P h j ω| ≤ |h (ω (j + 1))| + |kfunR P h (ω j)| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hB (ω (j + 1))]

/-- `|Mₘ| ≤ 2Bm`. -/
theorem abs_mdSum_le (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ} {B : ℝ}
    (hB : ∀ y, |h y| ≤ B) (m : ℕ) (ω : ℕ → X) : |mdSum P h m ω| ≤ 2 * B * m := by
  unfold mdSum
  calc |∑ j ∈ Finset.range m, mdTerm P h j ω| ≤ ∑ j ∈ Finset.range m, |mdTerm P h j ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, 2 * B := Finset.sum_le_sum fun j _ => abs_mdTerm_le P hB j ω
    _ = 2 * B * m := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- **Orthogonality of martingale differences**: `E_μ[φ Dₙ₊₁] = 0` for bounded `𝓕ₙ`-measurable
`φ`, by the Markov property (3.28). -/
theorem integral_mul_mdTerm (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    (n : ℕ) {φ : (ℕ → X) → ℝ} (hφ : Measurable[natFilt n] φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) :
    ∫ ω, φ ω * mdTerm P h n ω ∂pathMeasure P μ = 0 := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hle := (natFilt (X := X)).le n
  have hφm : Measurable φ := hφ.mono hle le_rfl
  have hH : Measurable fun ω' : ℕ → X => h (ω' 1) := hh.comp (measurable_pi_apply 1)
  have hcond := markov_property_bdd P μ n hH (fun ω => hB _)
  have hkf : ∀ z, ∫ ω', h (ω' 1) ∂pathKernel P z = kfunR P h z := fun z => by
    have := isMarkovKernel_pathKernel P
    rw [kfunR, show P z = (P ^ 1 : Kernel X X) z by rw [pow_one], ← pathKernel_map_coord P z 1,
      integral_map (measurable_pi_apply 1).aemeasurable hh.aestronglyMeasurable]
  have hshift : ∀ ω : ℕ → X, h (shift n ω 1) = h (ω (n + 1)) := fun ω => rfl
  have hint : ∀ {g : (ℕ → X) → ℝ}, Measurable g → ∀ D : ℝ, (∀ ω, |g ω| ≤ D) →
      Integrable g Q := fun hg D hD =>
    Integrable.of_bound hg.aestronglyMeasurable D
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hD ω)
  have hhn : Measurable fun ω : ℕ → X => h (ω (n + 1)) := hh.comp (measurable_pi_apply _)
  have hkn : Measurable fun ω : ℕ → X => kfunR P h (ω n) :=
    (measurable_kfunR P hh).comp (measurable_pi_apply _)
  have hprod1 : Integrable (fun ω => φ ω * h (ω (n + 1))) Q :=
    hint (hφm.mul hhn) (C * B) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hC ω) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have e1 : ∫ ω, φ ω * h (ω (n + 1)) ∂Q = ∫ ω, φ ω * kfunR P h (ω n) ∂Q := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := Q) (m := natFilt n)
      (f := φ) (g := fun ω => h (shift n ω 1)) hφ.stronglyMeasurable hprod1
      (hint hhn B fun ω => hB _)
    rw [← integral_condExp hle (f := fun ω => φ ω * h (ω (n + 1)))]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hcond] with ω h1 h2
    change Q[φ * fun ω => h (shift n ω 1)|natFilt n] ω = _
    rw [h1, Pi.mul_apply, h2, hkf]
  rw [show (fun ω => φ ω * mdTerm P h n ω) =
      fun ω => φ ω * h (ω (n + 1)) - φ ω * kfunR P h (ω n) from
      funext fun ω => by simp only [mdTerm]; ring,
    integral_sub (f := fun ω => φ ω * h (ω (n + 1))) (g := fun ω => φ ω * kfunR P h (ω n))
      hprod1 (hint (hφm.mul hkn) (C * B) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hC ω) (abs_kfunR_le P hB _) (abs_nonneg _)
        ((abs_nonneg _).trans (hC ω))), e1, sub_self]

/-- **The `L²` bound** `E_μ[Mₘ²] ≤ 4B²m` (orthogonal increments). -/
theorem integral_mdSum_sq_le (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    (m : ℕ) : ∫ ω, mdSum P h m ω ^ 2 ∂pathMeasure P μ ≤ 4 * B ^ 2 * m := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hle : ∀ n, natFilt (X := X) n ≤ MeasurableSpace.pi := fun n => (natFilt (X := X)).le n
  have hSm : ∀ m, Measurable (mdSum P h m) := fun m => (measurable_mdSum P hh m).mono (hle m) le_rfl
  have hTm : ∀ j, Measurable (mdTerm P h j) := fun j =>
    (measurable_mdTerm P hh (le_refl (j + 1))).mono (hle _) le_rfl
  have hint : ∀ {g : (ℕ → X) → ℝ}, Measurable g → ∀ D : ℝ, (∀ ω, |g ω| ≤ D) →
      Integrable g Q := fun hg D hD =>
    Integrable.of_bound hg.aestronglyMeasurable D
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hD ω)
  induction m with
  | zero =>
    rw [show (fun ω => mdSum P h 0 ω ^ 2) = fun _ => (0 : ℝ) from funext fun ω => by
      rw [mdSum, Finset.range_zero, Finset.sum_empty]; ring, integral_zero, Nat.cast_zero,
      mul_zero]
  | succ m ih =>
    have hsplit : ∀ ω, mdSum P h (m + 1) ω ^ 2 = mdSum P h m ω ^ 2 +
        2 * (mdSum P h m ω * mdTerm P h m ω) + mdTerm P h m ω ^ 2 := fun ω => by
      simp only [mdSum, Finset.sum_range_succ]; ring
    simp_rw [hsplit]
    have i1 : Integrable (fun ω => mdSum P h m ω ^ 2) Q :=
      hint ((hSm m).pow_const 2) ((2 * B * m) ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_mdSum_le P hB m ω) 2
    have i2 : Integrable (fun ω => 2 * (mdSum P h m ω * mdTerm P h m ω)) Q :=
      hint (((hSm m).mul (hTm m)).const_mul 2) (2 * ((2 * B * m) * (2 * B))) fun ω => by
        rw [abs_mul, abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (abs_mdSum_le P hB m ω)
          (abs_mdTerm_le P hB m ω) (abs_nonneg _)
          ((abs_nonneg _).trans (abs_mdSum_le P hB m ω))) zero_le_two
    have i3 : Integrable (fun ω => mdTerm P h m ω ^ 2) Q :=
      hint ((hTm m).pow_const 2) ((2 * B) ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_mdTerm_le P hB m ω) 2
    have i12 : Integrable (fun ω => mdSum P h m ω ^ 2 +
        2 * (mdSum P h m ω * mdTerm P h m ω)) Q := i1.add i2
    have e1 := integral_add i12 i3
    have e2 := integral_add i1 i2
    have e3 : ∫ ω, 2 * (mdSum P h m ω * mdTerm P h m ω) ∂Q = 0 := by
      rw [integral_const_mul,
        integral_mul_mdTerm P μ hh hB m (measurable_mdSum P hh m) (abs_mdSum_le P hB m), mul_zero]
    rw [e1, e2, e3, add_zero]
    have h3 : ∫ ω, mdTerm P h m ω ^ 2 ∂Q ≤ (2 * B) ^ 2 := by
      calc ∫ ω, mdTerm P h m ω ^ 2 ∂Q ≤ ∫ _, (2 * B) ^ 2 ∂Q :=
            integral_mono i3 (integrable_const _) fun ω => by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_mdTerm_le P hB m ω) 2
        _ = (2 * B) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
    push_cast
    nlinarith

/-- **Chebyshev's bound** for the martingale: `P_μ(|Mₘ| ≥ εm) ≤ 4B²/(ε²m)`. -/
theorem measure_abs_mdSum_ge_le (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 0 < m) :
    (pathMeasure P μ).real {ω | ε * m ≤ |mdSum P h m ω|} ≤ 4 * B ^ 2 / (ε ^ 2 * m) := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hSm : Measurable (mdSum P h m) :=
    (measurable_mdSum P hh m).mono ((natFilt (X := X)).le m) le_rfl
  have hint : Integrable (fun ω => mdSum P h m ω ^ 2) Q :=
    Integrable.of_bound (hSm.pow_const 2).aestronglyMeasurable ((2 * B * m) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_mdSum_le P hB m ω) 2)
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    hint ((ε * m) ^ 2)
  have hsub : {ω | ε * m ≤ |mdSum P h m ω|} ⊆ {ω | (ε * m) ^ 2 ≤ mdSum P h m ω ^ 2} :=
    fun ω hω => by
      simp only [mem_ofPred_eq] at hω ⊢
      rw [← sq_abs (mdSum P h m ω)]
      exact pow_le_pow_left₀ (by positivity) hω 2
  have hpos : 0 < (ε * m) ^ 2 := by positivity
  have h1 := measureReal_mono hsub (μ := Q)
  have h2 := (integral_mdSum_sq_le P μ hh hB m)
  rw [le_div_iff₀ (by positivity)]
  have : (ε * m) ^ 2 * Q.real {ω | ε * m ≤ |mdSum P h m ω|} ≤ 4 * B ^ 2 * m :=
    (mul_le_mul_of_nonneg_left h1 hpos.le).trans (hmk.trans h2)
  nlinarith [show (0 : ℝ) < m by exact_mod_cast hm]

/-- **The weak law for martingale differences**: `Mₘ/m → 0` in probability. -/
theorem tendsto_measure_abs_mdSum_div (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => (pathMeasure P μ).real {ω | ε * m ≤ |mdSum P h m ω|}) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hlim : Tendsto (fun m : ℕ => 4 * B ^ 2 / (ε ^ 2 * m)) atTop (𝓝 0) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (show 0 < ε ^ 2 by positivity)
    exact tendsto_const_nhds.div_atTop this
  refine squeeze_zero' (Eventually.of_forall fun m => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact measure_abs_mdSum_ge_le P μ hh hB hε hm

/-- **The strong law for bounded martingale differences**: `Mₘ/m → 0` almost surely (Chebyshev's
bound along the squares, Borel–Cantelli, and the bounded increments in between). The book cites
Theorem 5.2 of Chapter 4 of Doob for this. -/
theorem ae_tendsto_mdSum_div (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun m : ℕ => mdSum P h m ω / m) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hB0 : 0 ≤ 2 * B := (abs_nonneg _).trans (abs_mdTerm_le P hB 0 (fun _ => Classical.choice
    (show Nonempty X from by
      by_contra hX
      rw [not_nonempty_iff] at hX
      have : (μ : Measure X) = 0 := Measure.eq_zero_of_isEmpty μ
      exact IsProbabilityMeasure.ne_zero μ this)))
  -- along the squares
  have hsq : ∀ r : ℕ, ∀ᵐ ω ∂Q, ∀ᶠ k in atTop,
      ω ∉ {ω | (1 / (r + 1 : ℝ)) * ((k + 1) ^ 2 : ℕ) ≤ |mdSum P h ((k + 1) ^ 2) ω|} := fun r => by
    refine ae_eventually_notMem ?_
    have hε : (0 : ℝ) < 1 / (r + 1) := by positivity
    have hb : ∀ k : ℕ, Q {ω | (1 / (r + 1 : ℝ)) * ((k + 1) ^ 2 : ℕ) ≤
        |mdSum P h ((k + 1) ^ 2) ω|} ≤
          ENNReal.ofReal (4 * B ^ 2 / ((1 / (r + 1 : ℝ)) ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) :=
      fun k => by
        rw [← ENNReal.ofReal_toReal (measure_ne_top Q _), ← measureReal_def]
        refine ENNReal.ofReal_le_ofReal ((measure_abs_mdSum_ge_le P μ hh hB hε
          (by positivity)).trans (le_of_eq ?_))
        push_cast
        field_simp
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
    · exact ENNReal.ofReal_ne_top
    · refine Summable.mul_left _ ?_
      have := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
      exact (summable_nat_add_iff 1).2 this
  filter_upwards [ae_all_iff.2 hsq] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hω r)
  obtain ⟨J, hJ⟩ := exists_nat_gt (16 * B / ε)
  refine ⟨(max K J + 1) ^ 2, fun m hm => ?_⟩
  have hn2 : Nat.sqrt m ^ 2 ≤ m := Nat.sqrt_le' m
  have hm2 : m < (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
  have hnK : max K J + 1 ≤ Nat.sqrt m := Nat.le_sqrt'.2 hm
  obtain ⟨k, hk'⟩ : ∃ k, Nat.sqrt m = k + 1 := ⟨Nat.sqrt m - 1, by omega⟩
  rw [hk'] at hn2 hm2 hnK
  have hk := hK k (by omega)
  simp only [not_le] at hk
  -- the increments between `(k+1)²` and `m`
  have hdiff : |mdSum P h m ω - mdSum P h ((k + 1) ^ 2) ω| ≤ 2 * B * (m - (k + 1) ^ 2 : ℕ) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn2
    rw [hd, mdSum, mdSum, Finset.sum_range_add, add_sub_cancel_left, Nat.add_sub_cancel_left]
    calc |∑ j ∈ Finset.range d, mdTerm P h ((k + 1) ^ 2 + j) ω|
        ≤ ∑ j ∈ Finset.range d, |mdTerm P h ((k + 1) ^ 2 + j) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range d, 2 * B :=
          Finset.sum_le_sum fun j _ => abs_mdTerm_le P hB _ ω
      _ = 2 * B * d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := lt_of_lt_of_le (by positivity) hn2
    exact_mod_cast this
  have hdm : ((m - (k + 1) ^ 2 : ℕ) : ℝ) ≤ 2 * (k + 1) + 1 := by
    have : m - (k + 1) ^ 2 ≤ 2 * (k + 1) := by
      rw [show (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 2 * (k + 1) + 1 by ring] at hm2
      generalize (k + 1) ^ 2 = s at hm2 ⊢
      omega
    exact_mod_cast this.trans (Nat.le_succ _)
  have hk1 : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ m := by exact_mod_cast hn2
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hmpos, div_lt_iff₀ hmpos]
  have hJk : (J : ℝ) < k + 1 := by exact_mod_cast (show J < k + 1 by omega)
  have hJ' : 16 * B ≤ ε * (k + 1) := by
    rw [div_lt_iff₀ hε] at hJ
    nlinarith
  calc |mdSum P h m ω| ≤ |mdSum P h ((k + 1) ^ 2) ω| +
        |mdSum P h m ω - mdSum P h ((k + 1) ^ 2) ω| := by
        have := abs_sub_abs_le_abs_sub (mdSum P h m ω) (mdSum P h ((k + 1) ^ 2) ω)
        linarith
    _ < 1 / (r + 1) * ((k + 1) ^ 2 : ℕ) + 2 * B * (2 * (k + 1) + 1) := by
        refine add_lt_add_of_lt_of_le hk (hdiff.trans ?_)
        exact mul_le_mul_of_nonneg_left hdm hB0
    _ ≤ ε * m := by
        push_cast at hk1 ⊢
        have h1 : 1 / (r + 1 : ℝ) * (k + 1) ^ 2 ≤ ε / 2 * m :=
          mul_le_mul hr.le hk1 (by positivity) (by positivity)
        have h2 : 2 * B * (2 * (k + 1) + 1) ≤ ε / 2 * m := by
          have h3 : 2 * B * (2 * ((k : ℝ) + 1) + 1) ≤ 2 * B * (4 * (k + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hB0; linarith
          have hk0 : (0 : ℝ) ≤ k + 1 := by positivity
          have h4 : 2 * B * (4 * ((k : ℝ) + 1)) ≤ ε / 2 * (k + 1) ^ 2 := by
            have := mul_le_mul_of_nonneg_right hJ' hk0
            nlinarith
          have h5 := mul_le_mul_of_nonneg_left hk1 (show (0 : ℝ) ≤ ε / 2 by positivity)
          linarith
        linarith

/-! ### The telescoping decomposition (18.34) -/

/-- The iterates `hᵢ = Pⁱ f`, defined recursively by `h₀ = f` and `hᵢ₊₁ = P hᵢ`. -/
noncomputable def iterFun (P : Kernel X X) (f : X → ℝ) (i : ℕ) : X → ℝ := (kfunR P)^[i] f

/-- `hᵢ₊₁ = P hᵢ`. -/
theorem iterFun_succ (P : Kernel X X) (f : X → ℝ) (i : ℕ) :
    iterFun P f (i + 1) = kfunR P (iterFun P f i) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterates of a measurable function are measurable. -/
theorem measurable_iterFun (P : Kernel X X) [IsSFiniteKernel P] {f : X → ℝ} (hf : Measurable f)
    (i : ℕ) : Measurable (iterFun P f i) := by
  induction i with
  | zero => exact hf
  | succ i ih => rw [iterFun_succ]; exact measurable_kfunR P ih

/-- `|hᵢ| ≤ B` for `|f| ≤ B`. -/
theorem abs_iterFun_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (i : ℕ) (y : X) : |iterFun P f i y| ≤ B := by
  induction i generalizing y with
  | zero => exact hB y
  | succ i ih => rw [iterFun_succ]; exact abs_kfunR_le P ih y

/-- `hᵢ(y) = ∫ f dPⁱ(y)` for bounded measurable `f`. -/
theorem iterFun_eq_integral (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (i : ℕ) (y : X) :
    iterFun P f i y = ∫ z, f z ∂(P ^ i) y := by
  induction i generalizing y with
  | zero =>
    rw [pow_zero_apply, integral_dirac' f y hf.stronglyMeasurable]
    rfl
  | succ i ih =>
    have := isMarkovKernel_pow P i
    have hint : Integrable f (((P ^ i) ∘ₖ P) y) := by
      have := isMarkovKernel_pow P (i + 1)
      rw [pow_succ] at this
      exact Integrable.of_bound hf.aestronglyMeasurable B
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
    rw [iterFun_succ, kfunR, pow_succ]
    change ∫ z, iterFun P f i z ∂P y = ∫ z, f z ∂((P ^ i) ∘ₖ P) y
    rw [Kernel.integral_comp hint]
    exact integral_congr_ae (Eventually.of_forall fun z => ih z)

/-- **One telescoping step**: `Σ_{k=1}^N h(Φₖ) − Σ_{k=1}^N Ph(Φₖ) = M_N + Ph(Φ₀) − Ph(Φ_N)`. -/
theorem sum_sub_sum_kfunR_eq (P : Kernel X X) (h : X → ℝ) (N : ℕ) (ω : ℕ → X) :
    ∑ k ∈ Finset.Icc 1 N, h (ω k) - ∑ k ∈ Finset.Icc 1 N, kfunR P h (ω k) =
      mdSum P h N ω + kfunR P h (ω 0) - kfunR P h (ω N) := by
  induction N with
  | zero =>
    rw [mdSum, Finset.range_zero, Finset.sum_empty, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, Finset.sum_empty]
    ring
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), mdSum,
      Finset.sum_range_succ, ← mdSum, mdTerm]
    linarith

/-- **The iterated telescoping identity**: `Σₖ f(Φₖ) − Σₖ Pʲf(Φₖ)` is the sum over `i < j` of the
martingales `M_N^{(i)}` of `hᵢ = Pⁱf` and of boundary terms. -/
theorem sum_sub_sum_iterFun_eq (P : Kernel X X) (f : X → ℝ) (N j : ℕ) (ω : ℕ → X) :
    ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, iterFun P f j (ω k) =
      ∑ i ∈ Finset.range j, (mdSum P (iterFun P f i) N ω + iterFun P f (i + 1) (ω 0) -
        iterFun P f (i + 1) (ω N)) := by
  induction j with
  | zero =>
    rw [Finset.sum_range_zero]
    change ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, f (ω k) = 0
    exact sub_self _
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih, iterFun_succ, ← sum_sub_sum_kfunR_eq]
    ring

/-- The bound `|Σₖ f(Φₖ) − Σₖ Pʲf(Φₖ)| ≤ Σ_{i<j} |M_N^{(i)}| + 2Bj`. -/
theorem abs_sum_sub_sum_iterFun_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (N j : ℕ) (ω : ℕ → X) :
    |∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, iterFun P f j (ω k)| ≤
      ∑ i ∈ Finset.range j, |mdSum P (iterFun P f i) N ω| + 2 * B * j := by
  rw [sum_sub_sum_iterFun_eq]
  calc |∑ i ∈ Finset.range j, (mdSum P (iterFun P f i) N ω + iterFun P f (i + 1) (ω 0) -
        iterFun P f (i + 1) (ω N))|
      ≤ ∑ i ∈ Finset.range j, |mdSum P (iterFun P f i) N ω + iterFun P f (i + 1) (ω 0) -
        iterFun P f (i + 1) (ω N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j, (|mdSum P (iterFun P f i) N ω| + 2 * B) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := abs_iterFun_le P hB (i + 1) (ω 0)
        have h2 := abs_iterFun_le P hB (i + 1) (ω N)
        have h3 := abs_add_le (mdSum P (iterFun P f i) N ω + iterFun P f (i + 1) (ω 0))
          (-iterFun P f (i + 1) (ω N))
        have h4 := abs_add_le (mdSum P (iterFun P f i) N ω) (iterFun P f (i + 1) (ω 0))
        rw [abs_neg, ← sub_eq_add_neg] at h3
        linarith
    _ = ∑ i ∈ Finset.range j, |mdSum P (iterFun P f i) N ω| + 2 * B * j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- The averaged iterates `(1/M) Σ_{j=1}^M Pʲf`, which equal `P̄ᴹ f`
(`cesaroIter_eq_cesaroFun`). -/
noncomputable def cesaroIter (P : Kernel X X) (f : X → ℝ) (M : ℕ) (y : X) : ℝ :=
  (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 M, iterFun P f j y

/-- **(18.34)**: for `M ≥ 1`, `|Σₖ f(Φₖ) − Σₖ P̄ᴹf(Φₖ)| ≤ Σ_{i<M} |M_N^{(i)}| + 2BM`. -/
theorem abs_sum_sub_sum_cesaroIter_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (N : ℕ) {M : ℕ} (hM : 1 ≤ M) (ω : ℕ → X) :
    |∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, cesaroIter P f M (ω k)| ≤
      ∑ i ∈ Finset.range M, |mdSum P (iterFun P f i) N ω| + 2 * B * M := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (ω 0))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set T := ∑ i ∈ Finset.range M, |mdSum P (iterFun P f i) N ω| + 2 * B * M
  have heq : ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, cesaroIter P f M (ω k) =
      (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 M, (∑ k ∈ Finset.Icc 1 N, f (ω k) -
        ∑ k ∈ Finset.Icc 1 N, iterFun P f j (ω k)) := by
    simp only [cesaroIter]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hMpos.ne', one_mul, ← Finset.mul_sum,
      Finset.sum_comm]
  rw [heq, abs_mul, abs_inv, Nat.abs_cast]
  have hle : ∀ j ∈ Finset.Icc 1 M, |∑ k ∈ Finset.Icc 1 N, f (ω k) -
      ∑ k ∈ Finset.Icc 1 N, iterFun P f j (ω k)| ≤ T := fun j hj => by
    have hjM : j ≤ M := (Finset.mem_Icc.1 hj).2
    refine (abs_sum_sub_sum_iterFun_le P hB N j ω).trans (add_le_add ?_ ?_)
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hjM)
        fun i _ _ => abs_nonneg _
    · have : (j : ℝ) ≤ M := by exact_mod_cast hjM
      exact mul_le_mul_of_nonneg_left this (by positivity)
  calc (M : ℝ)⁻¹ * |∑ j ∈ Finset.Icc 1 M, (∑ k ∈ Finset.Icc 1 N, f (ω k) -
        ∑ k ∈ Finset.Icc 1 N, iterFun P f j (ω k))|
      ≤ (M : ℝ)⁻¹ * ∑ _j ∈ Finset.Icc 1 M, T := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hle)
    _ = T := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hMpos.ne', one_mul]

/-- `(1/M) Σ_{j=1}^M Pʲf = P̄ᴹ f` for bounded measurable `f`. -/
theorem cesaroIter_eq_cesaroFun (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (M : ℕ) (y : X) :
    cesaroIter P f M y = cesaroFun P M f y := by
  rw [cesaroIter, cesaroFun, integral_cesaroKernel P M y hf hB]
  congr 1
  exact Finset.sum_congr rfl fun j _ => iterFun_eq_integral P hf hB j y

/-- `|P̄ᴹ f| ≤ B` for `|f| ≤ B`. -/
theorem abs_cesaroIter_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (M : ℕ) (y : X) : |cesaroIter P f M y| ≤ B := by
  rw [cesaroIter_eq_cesaroFun P hf hB]
  exact abs_cesaroFun_le P M ((abs_nonneg _).trans (hB y)) hB y

/-- **The mean of the occupation averages** (18.30): `E_x[(1/N) Σ_{k=1}^N g(Φₖ)] = P̄ᴺ g(x)`. -/
theorem integral_occAvg (P : Kernel X X) [IsMarkovKernel P] (x : X) {g : X → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) (N : ℕ) :
    ∫ ω, (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, g (ω k) ∂pathMeasure P (Measure.dirac x) =
      ∫ y, g y ∂cesaroKernel P N x := by
  have := isProbabilityMeasure_pathMeasure P (Measure.dirac x)
  rw [integral_const_mul, integral_finsetSum, integral_cesaroKernel P N x hg hB]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable,
      pathMeasure_map_coord, Measure.dirac_bind (Kernel.measurable _)]
  · intro k _
    exact Integrable.of_bound (hg.comp (measurable_pi_apply k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)

/-- **The pointwise form of (18.33)**: for `N, M ≥ 1`,
`|(1/N) Σₖ f(Φₖ) − c| ≤ (1/N)(Σ_{i<M} |M_N^{(i)}| + 2BM) + (1/N) Σₖ |P̄ᴹf(Φₖ) − c|`. -/
theorem abs_occAvg_sub_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (c : ℝ) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (ω : ℕ → X) :
    |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) - c| ≤
      (N : ℝ)⁻¹ * (∑ i ∈ Finset.range M, |mdSum P (iterFun P f i) N ω| + 2 * B * M) +
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, |cesaroIter P f M (ω k) - c| := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) - c =
      (N : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 N, f (ω k) - ∑ k ∈ Finset.Icc 1 N, cesaroIter P f M (ω k)) +
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, (cesaroIter P f M (ω k) - c) := by
    rw [Finset.sum_sub_distrib (s := Finset.Icc 1 N), Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    field_simp
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_inv, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (abs_sum_sub_sum_cesaroIter_le P hB N hM ω) (by positivity)
  · rw [abs_mul, abs_inv, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- **The remainder of (18.34) vanishes**: along a path on which every `M_N^{(i)}/N → 0`,
`(1/N)(Σ_{i<M} |M_N^{(i)}| + 2BM) → 0`. -/
theorem tendsto_mdRemainder (P : Kernel X X) (f : X → ℝ) (B : ℝ) (M : ℕ) {ω : ℕ → X}
    (hω : ∀ i, Tendsto (fun N : ℕ => mdSum P (iterFun P f i) N ω / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      (∑ i ∈ Finset.range M, |mdSum P (iterFun P f i) N ω| + 2 * B * M)) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum (Finset.range M) fun i _ => (hω i).abs
  have hinv : Tendsto (fun N : ℕ => 2 * B * M * (N : ℝ)⁻¹) atTop (𝓝 (2 * B * M * 0)) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _
  have h0 : ∑ i ∈ Finset.range M, |(0 : ℝ)| + 2 * B * M * 0 = 0 := by
    rw [abs_zero, Finset.sum_const_zero, mul_zero, add_zero]
  rw [← h0]
  refine (hs.add hinv).congr fun N => ?_
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_div, Nat.abs_cast, div_eq_inv_mul]
  · ring

omit [MeasurableSpace X] in
/-- Almost sure convergence implies convergence in probability, in the real form used here. -/
theorem tendsto_measureReal_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {R : ℕ → Ω → ℝ} (hR : ∀ n, Measurable (R n))
    (h : ∀ᵐ ω ∂Q, Tendsto (fun n => R n ω) atTop (𝓝 0)) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n => Q.real {ω | γ ≤ |R n ω|}) atTop (𝓝 0) := by
  have hm := tendstoInMeasure_of_tendsto_ae (g := fun _ => (0 : ℝ))
    (fun n => (hR n).aestronglyMeasurable) h
  have h1 := hm (ENNReal.ofReal γ) (ENNReal.ofReal_pos.2 hγ)
  have heq : ∀ n, {ω | ENNReal.ofReal γ ≤ edist (R n ω) 0} = {ω | γ ≤ |R n ω|} := fun n => by
    ext ω
    rw [mem_ofPred_eq, mem_ofPred_eq, edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simp_rw [heq] at h1
  change Tendsto (fun n => (Q {ω | γ ≤ |R n ω|}).toReal) atTop (𝓝 0)
  rw [← ENNReal.toReal_zero]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1

/-! ### The weak law, Theorem 18.5.1 (i) -/

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- For a weak Feller chain and bounded continuous `f`, every `Pʲf` is continuous
(Proposition 6.1.1). -/
theorem continuous_iterFun {P : Kernel X X} [IsMarkovKernel P] (hF : IsWeakFeller P)
    (f : X →ᵇ ℝ) (j : ℕ) : Continuous (iterFun P f j) := by
  have := isMarkovKernel_pow P j
  have hB : ∀ y, |f y| ≤ ‖f‖ := fun y => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
  have heq : iterFun P f j = fun y => ∫ z, f z ∂(P ^ j) y :=
    funext (iterFun_eq_integral P f.continuous.measurable hB j)
  rw [heq]
  exact (proposition_6_1_1_i_weak (P ^ j)).1 (hF.pow j) f

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- `P̄ᴹ f` is continuous for a weak Feller chain and bounded continuous `f`. -/
theorem continuous_cesaroIter {P : Kernel X X} [IsMarkovKernel P] (hF : IsWeakFeller P)
    (f : X →ᵇ ℝ) (M : ℕ) : Continuous (cesaroIter P f M) :=
  continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_iterFun hF f j)

/-- **The weak law of large numbers for e-chains** (the core of Theorem 18.5.1 (i), MT p. 478):
for an e-chain bounded in probability on average with a reachable state `x*`, `π = Π(x*, ·)`, a
bounded continuous `f` and every initial state `x`,
`(1/N) Σ_{k=1}^N f(Φₖ) → π(f)` in `P_x`-probability. The decomposition (18.34) splits off the
martingales `M^{(i)}`, which vanish almost surely after division by `N`; the rest is bounded in
mean by `P̄ᴺ(x, |P̄ᴹf − π(f)|) → π(|P̄ᴹf − π(f)|)`, which is small for large `M`. -/
theorem tendsto_occAvg_inProb {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀) (f : X →ᵇ ℝ)
    (x : X) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun N : ℕ => (pathMeasure P (Measure.dirac x)).real
      {ω | γ ≤ |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∫ y, f y ∂eChainLimit he x₀|})
      atTop (𝓝 0) := by
  set ν := eChainLimit he x₀ with hνdef
  have hνp : IsProbabilityMeasure ν := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  have hNE := proposition_12_1_1 hb
  have hconst := eChainLimit_eq_of_isReachable he hNE hx
  obtain ⟨-, -, -, hconv0⟩ := theorem_12_0_1_ii he hb
  have hconv : ∀ (g : X →ᵇ ℝ) y, Tendsto (fun n => ∫ z, g z ∂cesaroKernel P (n + 1) y) atTop
      (𝓝 (∫ z, g z ∂ν)) := fun g y => by
    have := hconv0 g y
    rwa [hconst y] at this
  have hF := he.isWeakFeller
  set c := ∫ y, f y ∂ν with hcdef
  set B := ‖f‖ with hBdef
  have hB : ∀ y, |f y| ≤ B := fun y => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
  have hB0 : 0 ≤ B := norm_nonneg _
  have hfm : Measurable f := f.continuous.measurable
  have hc : |c| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := B)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  set Q := pathMeasure P (Measure.dirac x) with hQdef
  have hQ := isProbabilityMeasure_pathMeasure P (Measure.dirac x)
  -- the functions `|P̄ᴹ f − π(f)|`
  have hgB : ∀ M y, ‖|cesaroIter P f M y - c|‖ ≤ 2 * B := fun M y => by
    rw [Real.norm_eq_abs, abs_abs]
    have := abs_cesaroIter_le P hfm hB M y
    have := abs_sub (cesaroIter P f M y) c
    linarith
  let g : ℕ → X →ᵇ ℝ := fun M => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => |cesaroIter P f M y - c|) ((continuous_cesaroIter hF f M).sub
      continuous_const).abs (2 * B) (hgB M)
  have hg : ∀ M y, g M y = |cesaroIter P f M y - c| := fun M y => rfl
  have hgB' : ∀ M y, |g M y| ≤ 2 * B := fun M y => by
    rw [← Real.norm_eq_abs]; exact hgB M y
  -- step 1: `π(|P̄ᴹ f − π(f)|) → 0`
  have h1 : Tendsto (fun m : ℕ => ∫ y, g (m + 1) y ∂ν) atTop (𝓝 0) := by
    have hlim : ∀ y, Tendsto (fun m : ℕ => g (m + 1) y) atTop (𝓝 0) := fun y => by
      have h := ((hconv f y).sub_const c).abs
      rw [hcdef, sub_self, abs_zero] at h
      refine h.congr fun m => ?_
      rw [hg, cesaroIter_eq_cesaroFun P hfm hB]
      rfl
    have := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => 2 * B)
      (fun m => (g (m + 1)).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun m => Eventually.of_forall fun y => hgB (m + 1) y) (Eventually.of_forall hlim)
    rwa [integral_zero] at this
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds (show (0 : ℝ) < γ * η / 8 by positivity))).exists
  set M := m + 1 with hMdef
  have hM1 : 1 ≤ M := Nat.le_add_left 1 m
  -- step 2: `P̄ᴺ(x, |P̄ᴹ f − π(f)|) → π(|P̄ᴹ f − π(f)|)`
  have hγη : 0 < γ * η := mul_pos hγ hη
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((hconv (g M) x).eventually
    (gt_mem_nhds (show ∫ y, g M y ∂ν < γ * η / 4 by linarith)))
  -- step 3: the martingale part vanishes
  set R : ℕ → (ℕ → X) → ℝ := fun N ω => (N : ℝ)⁻¹ *
    (∑ i ∈ Finset.range M, |mdSum P (iterFun P f i) N ω| + 2 * B * M) with hRdef
  have hmd : ∀ i N, Measurable (mdSum P (iterFun P f i) N) := fun i N =>
    (measurable_mdSum P (measurable_iterFun P hfm i) N).mono ((natFilt (X := X)).le N) le_rfl
  have hRm : ∀ N, Measurable (R N) := fun N =>
    ((Finset.measurable_sum _ fun i _ => continuous_abs.measurable.comp (hmd i N)).add_const
      _).const_mul _
  have hRae : ∀ᵐ ω ∂Q, Tendsto (fun N => R N ω) atTop (𝓝 0) := by
    have hall : ∀ᵐ ω ∂Q, ∀ i, Tendsto (fun N : ℕ => mdSum P (iterFun P f i) N ω / N) atTop
        (𝓝 0) := ae_all_iff.2 fun i =>
      ae_tendsto_mdSum_div P _ (measurable_iterFun P hfm i) (abs_iterFun_le P hB i)
    filter_upwards [hall] with ω hω
    exact tendsto_mdRemainder P f B M hω
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_measureReal_of_ae_tendsto hRm hRae
    (half_pos hγ)).eventually (gt_mem_nhds (half_pos hη)))
  refine ⟨max (N₁ + 1) N₂, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn1 := hN₁ n (by omega)
  have hn2 := hN₂ (n + 1) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  -- the occupation average of `|P̄ᴹ f − π(f)|`
  set G : (ℕ → X) → ℝ := fun ω => ((n + 1 : ℕ) : ℝ)⁻¹ *
    ∑ k ∈ Finset.Icc 1 (n + 1), g M (ω k) with hGdef
  have hGm : Measurable G := (Finset.measurable_sum _ fun k _ =>
    (g M).continuous.measurable.comp (measurable_pi_apply k)).const_mul _
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hGint : Integrable G Q := Integrable.of_bound hGm.aestronglyMeasurable (2 * B)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 ω)]
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      calc ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (n + 1), g M (ω k)
          ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _k ∈ Finset.Icc 1 (n + 1), 2 * B := by
            gcongr with k
            exact (le_abs_self _).trans (hgB' M _)
        _ = 2 * B := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
              inv_mul_cancel₀ hn.ne', one_mul])
  have hEG : ∫ ω, G ω ∂Q = ∫ y, g M y ∂cesaroKernel P (n + 1) x :=
    integral_occAvg P x (g M).continuous.measurable (hgB' M) (n + 1)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hG0) hGint (γ / 2)
  rw [hEG] at hMarkov
  -- the inclusion
  have hsub : {ω | γ ≤ |((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (n + 1), f (ω k) - c|} ⊆
      {ω | γ / 2 ≤ |R (n + 1) ω|} ∪ {ω | γ / 2 ≤ G ω} := fun ω hω => by
    rw [mem_ofPred_eq] at hω
    by_contra hcon
    rw [mem_union, mem_ofPred_eq, mem_ofPred_eq, not_or, not_le, not_le] at hcon
    have hle := abs_occAvg_sub_le P hB c (Nat.le_add_left 1 n) hM1 ω
    have hR : R (n + 1) ω ≤ |R (n + 1) ω| := le_abs_self _
    have hGe : G ω = ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (n + 1), |cesaroIter P f M (ω k) - c| := rfl
    change _ ≤ R (n + 1) ω + _ at hle
    rw [← hGe] at hle
    linarith [hcon.1, hcon.2]
  calc Q.real {ω | γ ≤ |((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (n + 1), f (ω k) - c|}
      ≤ Q.real ({ω | γ / 2 ≤ |R (n + 1) ω|} ∪ {ω | γ / 2 ≤ G ω}) := measureReal_mono hsub
    _ ≤ Q.real {ω | γ / 2 ≤ |R (n + 1) ω|} + Q.real {ω | γ / 2 ≤ G ω} :=
        measureReal_union_le _ _
    _ < η / 2 + η / 2 := by
        refine add_lt_add_of_lt_of_le hn2 ?_
        have : γ / 2 * Q.real {ω | γ / 2 ≤ G ω} ≤ γ / 2 * (η / 2) := by
          refine hMarkov.trans ?_
          nlinarith
        exact le_of_mul_le_mul_left this (half_pos hγ)
    _ = η := add_halves η

/-- **Theorem 18.5.1 (i)** (MT p. 478): for an e-chain bounded in probability on average with a
reachable state, there is a unique invariant probability `π` (it is `Π(x*, ·)`), and for every
bounded continuous `f` and every initial state `x`, `(1/N) Σ_{k=1}^N f(Φₖ) → π(f)` in
`P_x`-probability. -/
theorem theorem_18_5_1_i {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ IsInvariant P ν ∧
      (∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = ν) ∧
      ∀ (f : X →ᵇ ℝ) (x : X) (γ : ℝ), 0 < γ →
        Tendsto (fun N : ℕ => (pathMeasure P (Measure.dirac x)).real
          {ω | γ ≤ |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∫ y, f y ∂ν|}) atTop (𝓝 0) := by
  have hνp : IsProbabilityMeasure (eChainLimit he x₀) := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  obtain ⟨-, -, hinv, -⟩ := theorem_12_0_1_ii he hb
  obtain ⟨π', hπ'p, -, huniq⟩ := (theorem_18_4_4_i he hb).2 ⟨x₀, hx⟩
  have heq : eChainLimit he x₀ = π' := huniq _ hνp (hinv x₀)
  refine ⟨eChainLimit he x₀, hνp, hinv x₀, fun μ hμ hμi => (huniq μ hμ hμi).trans heq.symm,
    fun f x γ hγ => tendsto_occAvg_inProb he hb hx f x hγ⟩

/-! ### The strong law, Theorem 18.5.1 (ii) -/

/-- **Uniform convergence on compacts** (used in (18.32)): for an e-chain bounded in probability
on average with a reachable state `x*` and `f ∈ C_c(X)`, `P̄ᴹ f → π(f)` uniformly on every
compact `K`. Equicontinuity of `{P̄ᴹ f}` (`eventually_abs_cesaroFun_sub_le`) and pointwise
convergence at finitely many points suffice. -/
theorem eventually_forall_abs_cesaroIter_sub_le {P : Kernel X X} [IsMarkovKernel P]
    (he : IsEChain P) (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀)
    (f : C_c(X, ℝ)) {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ y ∈ K, |cesaroIter P f M y - ∫ z, f z ∂eChainLimit he x₀| ≤ ε := by
  have hNE := proposition_12_1_1 hb
  have hconst := eChainLimit_eq_of_isReachable he hNE hx
  obtain ⟨B, -, hB⟩ := exists_abs_le_cc f
  have hfm : Measurable f := (map_continuous f).measurable
  set c := ∫ z, f z ∂eChainLimit he x₀ with hcdef
  have hlim : ∀ y, Tendsto (fun M => cesaroFun P M f y) atTop (𝓝 c) := fun y => by
    have := (theorem_12_4_1_i he).2 f y
    rwa [hconst y] at this
  have hU : ∀ y ∈ K, {z | ∀ n, |cesaroFun P n f y - cesaroFun P n f z| ≤ ε / 2} ∈ 𝓝 y :=
    fun y _ => eventually_abs_cesaroFun_sub_le he f y (half_pos hε)
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover _ hU
  have hev : ∀ᶠ M in atTop, ∀ y ∈ t, |cesaroFun P M f y - c| ≤ ε / 2 :=
    (Filter.eventually_all_finset t).2 fun y _ => by
      have := (hlim y).eventually (Metric.closedBall_mem_nhds c (half_pos hε))
      refine this.mono fun M hM => ?_
      rw [Real.dist_eq] at hM
      exact hM
  refine hev.mono fun M hM z hz => ?_
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcover hz)
  rw [mem_ofPred_eq] at hzy
  have h1 := hzy M
  have h2 := hM y hy
  rw [cesaroIter_eq_cesaroFun P hfm hB]
  have := abs_sub_le (cesaroFun P M f z) (cesaroFun P M f y) c
  rw [abs_sub_comm] at h1
  linarith

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **The strong law along one path** (the pathwise core of Theorem 18.5.1 (ii), MT p. 479): if
along a path `ω` every martingale `M_N^{(i)}` of (18.34) is `o(N)` and the occupation
probabilities are tight (in the eventual form: for every `δ > 0` some compact `K` has
`(1/N) #{k ≤ N : ωₖ ∉ K} ≤ δ` for all large `N`), then `(1/N) Σ_{k=1}^N f(ωₖ) → c` for every
`f ∈ C_c(X)` with `P̄ᴹ f → c` uniformly on compacts. -/
theorem tendsto_occAvg_of_tight (P : Kernel X X) [IsMarkovKernel P] (f : C_c(X, ℝ)) (c : ℝ)
    (hunif : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M in atTop, ∀ y ∈ K, |cesaroIter P f M y - c| ≤ ε) {ω : ℕ → X}
    (hmd : ∀ i, Tendsto (fun N : ℕ => mdSum P (iterFun P f i) N ω / N) atTop (𝓝 0))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k)) atTop (𝓝 c) := by
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_abs_le_cc f
  have hfm : Measurable f := (map_continuous f).measurable
  set B := max B₀ |c| with hBdef
  have hB : ∀ y, |f y| ≤ B := fun y => (hB₀ y).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := hB₀0.trans (le_max_left _ _)
  have hc : |c| ≤ B := le_max_right _ _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK, hKev⟩ := htight (ε / (8 * (B + 1))) (by positivity)
  obtain ⟨M, hMK, hM1⟩ := ((hunif K hK (ε / 4) (by positivity)).and
    (eventually_ge_atTop 1)).exists
  have hR := tendsto_mdRemainder P f B M hmd
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hR.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by
    positivity)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hKev
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hRN := hN₁ N (le_trans (le_max_left _ _) (le_of_max_le_left hN))
  have hKN := hN₂ N (le_trans (le_max_right _ _) (le_of_max_le_left hN))
  have hle := abs_occAvg_sub_le P hB c hN1 hM1 ω
  -- the bound on the averaged `|P̄ᴹ f − c|`
  have hpt : ∀ k ∈ Finset.Icc 1 N, |cesaroIter P f M (ω k) - c| ≤
      ε / 4 + 2 * B * Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) := fun k _ => by
    by_cases hk : ω k ∈ K
    · have := hMK (ω k) hk
      rw [indicator_of_notMem (show ω k ∉ Kᶜ from fun h => h hk), mul_zero, add_zero]
      exact this
    · rw [indicator_of_mem (show ω k ∈ Kᶜ from hk), mul_one]
      have h1 := abs_cesaroIter_le P hfm hB M (ω k)
      have h2 := abs_sub (cesaroIter P f M (ω k)) c
      linarith [show (0 : ℝ) ≤ ε / 4 by positivity]
  set cnt := ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) with hcnt
  have hsum : (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, |cesaroIter P f M (ω k) - c| ≤ ε / 2 := by
    have h1 : ∑ k ∈ Finset.Icc 1 N, |cesaroIter P f M (ω k) - c| ≤ N * (ε / 4) + 2 * B * cnt := by
      refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, ← Finset.mul_sum]
    have h2 : (N : ℝ)⁻¹ * (2 * B * cnt) ≤ ε / 4 := by
      have : 2 * B * ((N : ℝ)⁻¹ * cnt) ≤ 2 * B * (ε / (8 * (B + 1))) :=
        mul_le_mul_of_nonneg_left hKN (by positivity)
      have h3 : 2 * B * (ε / (8 * (B + 1))) ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    calc (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, |cesaroIter P f M (ω k) - c|
        ≤ (N : ℝ)⁻¹ * (N * (ε / 4) + 2 * B * cnt) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε / 4 + (N : ℝ)⁻¹ * (2 * B * cnt) := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
      _ ≤ ε / 2 := by linarith
  rw [Real.dist_eq]
  linarith

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **From a uniformly dense family to all of `C_c(X)`** (MT p. 480): if the occupation averages
of a path converge to `ν(Fₙ)` for every member of a uniformly dense family `{Fₙ} ⊆ C_c(X)` and `ν`
is a probability, they converge to `ν(f)` for every `f ∈ C_c(X)`. -/
theorem tendsto_occAvg_cc_of_dense {F : ℕ → C_c(X, ℝ)}
    (hF : ∀ f : C_c(X, ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x, |f x - F k x| ≤ ε) (ν : Measure X)
    [IsProbabilityMeasure ν] {ω : ℕ → X}
    (h : ∀ n, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, F n (ω k)) atTop
      (𝓝 (∫ y, F n y ∂ν))) (f : C_c(X, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k)) atTop
      (𝓝 (∫ y, f y ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := hF f (ε / 4) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (h j) (ε / 4) (by positivity)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₀ N (le_of_max_le_left hN)
  rw [Real.dist_eq] at h1 ⊢
  have hint : ∀ g : C_c(X, ℝ), Integrable g ν := fun g =>
    (map_continuous g).integrable_of_hasCompactSupport g.hasCompactSupport
  have h2 : |∫ y, f y ∂ν - ∫ y, F j y ∂ν| ≤ ε / 4 := by
    rw [← integral_sub (hint f) (hint (F j))]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => f y - F j y)
      (C := ε / 4) (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hj y)
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  have h3 : |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) -
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, F j (ω k)| ≤ ε / 4 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_inv, Nat.abs_cast]
    calc (N : ℝ)⁻¹ * |∑ k ∈ Finset.Icc 1 N, (f (ω k) - F j (ω k))|
        ≤ (N : ℝ)⁻¹ * ∑ _k ∈ Finset.Icc 1 N, ε / 4 := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hj _)
      _ = ε / 4 := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hNpos.ne', one_mul]
  have h4 := abs_sub_le ((N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k))
    ((N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, F j (ω k)) (∫ y, f y ∂ν)
  have h5 := abs_sub_le ((N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, F j (ω k)) (∫ y, F j y ∂ν)
    (∫ y, f y ∂ν)
  rw [abs_sub_comm (∫ y, F j y ∂ν)] at h5
  linarith

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- The occupation measure `μ̃_N = (1/N) Σ_{k=1}^N δ_{ωₖ}` of a path (18.30). -/
noncomputable def occMeasure (ω : ℕ → X) (N : ℕ) : Measure X :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.Icc 1 N, Measure.dirac (ω k)

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `μ̃_N` is a probability for `N ≥ 1`. -/
theorem isProbabilityMeasure_occMeasure (ω : ℕ → X) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (occMeasure ω N) := by
  constructor
  rw [occMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp_rw [measure_univ]
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, smul_eq_mul,
    ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega)) (ENNReal.natCast_ne_top N)]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `∫ g dμ̃_N = (1/N) Σ_{k=1}^N g(ωₖ)` for bounded measurable `g`. -/
theorem integral_occMeasure (ω : ℕ → X) (N : ℕ) {g : X → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) :
    ∫ y, g y ∂occMeasure ω N = (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, g (ω k) := by
  rw [occMeasure, integral_smul_measure, integral_finsetSum_measure, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  · congr 1
    exact Finset.sum_congr rfl fun k _ => integral_dirac' g (ω k) hg.stronglyMeasurable
  · intro k _
    exact Integrable.of_bound hg.aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)

omit [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Vague to weak** for occupation measures (MT p. 480): if the occupation averages of a path
converge to `ν(f)` for every `f ∈ C_c(X)` and `ν` is a probability, they converge to `ν(g)` for
every bounded continuous `g`, i.e. `μ̃_N → ν` weakly. -/
theorem tendsto_occAvg_bcf_of_cc {ν : Measure X} [IsProbabilityMeasure ν] {ω : ℕ → X}
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k))
      atTop (𝓝 (∫ y, f y ∂ν))) (g : X →ᵇ ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂ν)) := by
  have : ∀ n, IsProbabilityMeasure (occMeasure ω (n + 1)) := fun n =>
    isProbabilityMeasure_occMeasure ω (Nat.le_add_left 1 n)
  have hgB : ∀ y, |g y| ≤ ‖g‖ := fun y => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm y
  have hmain := tendsto_integral_bcf_of_cc (μs := fun n => occMeasure ω (n + 1)) (μ := ν)
    (fun f => by
      obtain ⟨B, -, hB⟩ := exists_abs_le_cc f
      refine ((h f).comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      rw [Function.comp_apply, integral_occMeasure ω (n + 1) (map_continuous f).measurable hB])
    g
  refine (tendsto_add_atTop_iff_nat 1).1 (hmain.congr fun n => ?_)
  rw [integral_occMeasure ω (n + 1) g.continuous.measurable hgB]

/-- **Theorem 18.5.1 (ii)** (MT p. 478), the strong law of large numbers: for an e-chain bounded in
probability on average with a reachable state `x*` and `π = Π(x*, ·)`, if from `x` the
occupation probabilities are almost surely tight, then `μ̃_N → π` weakly almost surely (18.31):
almost every path has `(1/N) Σ_{k=1}^N g(Φₖ) → π(g)` for every bounded continuous `g`.
Tightness is assumed in the eventual form of `tendsto_occAvg_of_tight`, which is implied by
tightness of the whole sequence `{μ̃_N}`. -/
theorem theorem_18_5_1_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀) (x : X)
    (htight : ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ δ : ℝ, 0 < δ → ∃ K : Set X,
      IsCompact K ∧ ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ) :
    ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ g : X →ᵇ ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, g (ω k)) atTop
        (𝓝 (∫ y, g y ∂eChainLimit he x₀)) := by
  have hνp : IsProbabilityMeasure (eChainLimit he x₀) := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  obtain ⟨F, hF⟩ := exists_dense_cc (X := X)
  have hall : ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ n i,
      Tendsto (fun N : ℕ => mdSum P (iterFun P (F n) i) N ω / N) atTop (𝓝 0) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i => by
      obtain ⟨B, -, hB⟩ := exists_abs_le_cc (F n)
      exact ae_tendsto_mdSum_div P _ (measurable_iterFun P (map_continuous (F n)).measurable i)
        (abs_iterFun_le P hB i)
  filter_upwards [hall, htight] with ω hω hωt
  refine tendsto_occAvg_bcf_of_cc (tendsto_occAvg_cc_of_dense hF _ fun n => ?_)
  exact tendsto_occAvg_of_tight P (F n) _
    (fun K hK ε hε => eventually_forall_abs_cesaroIter_sub_le he hb hx (F n) hK hε) (hω n) hωt

/-! ### Theorem 18.0.2 (ii) -/

/-- **Theorem 18.0.2 (ii)** (MT p. 463), for an e-chain with a reachable state `x*`: the following
are equivalent:
(a) there is a unique invariant probability `π`, and for every `x` and bounded continuous `f`,
`P̄ₖ(x, f) → π(f)` and `(1/n) Σ_{i=1}^n f(Φᵢ) → π(f)` in `P_x`-probability;
(b) the chain is bounded in probability on average;
(c) the chain is non-evanescent and `x*` is positive, in the Cesàro form `IsCesaroPositive` of
Proposition 18.4.2.
The statement is `(a) ↔ (b)` and `(b) ↔ (c)`; and under (b), if `x*` is aperiodic then
`Pᵏ(x, ·) → π = Π(x*, ·)` weakly for every `x` (18.5). -/
theorem theorem_18_0_2_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {x₀ : X}
    (hx : IsReachable P x₀) :
    ((∃ ν : Measure X, IsProbabilityMeasure ν ∧ IsInvariant P ν ∧
        (∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = ν) ∧
        (∀ x (f : X →ᵇ ℝ), Tendsto (fun n => ∫ y, f y ∂cesaroKernel P (n + 1) x) atTop
          (𝓝 (∫ y, f y ∂ν))) ∧
        ∀ (f : X →ᵇ ℝ) (x : X) (γ : ℝ), 0 < γ →
          Tendsto (fun N : ℕ => (pathMeasure P (Measure.dirac x)).real
            {ω | γ ≤ |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, f (ω k) - ∫ y, f y ∂ν|}) atTop
            (𝓝 0)) ↔ IsBoundedInProbabilityOnAverage P) ∧
      (IsBoundedInProbabilityOnAverage P ↔ IsNonEvanescent P ∧ IsCesaroPositive P x₀) ∧
      (IsBoundedInProbabilityOnAverage P → IsTopAperiodic P x₀ → ∀ x (f : X →ᵇ ℝ),
        Tendsto (fun k => ∫ y, f y ∂(P ^ k : Kernel X X) x) atTop
          (𝓝 (∫ y, f y ∂eChainLimit he x₀))) := by
  have hfinK := isFiniteKernel_eChainLimit he
  refine ⟨⟨fun ha => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hc => ?_⟩,
    fun hb hap x f => theorem_18_4_4_ii he hb hx hap x f⟩
  · -- (a) ⇒ (b): every `Π(x, ·)` is the Cesàro limit, hence `π`
    obtain ⟨ν, hνp, -, -, hconv, -⟩ := ha
    refine (theorem_12_4_1_iii he).2 fun x => ?_
    have heq : eChainLimit he x = ν := ext_of_integral_cc fun f => by
      have h1 := ((theorem_12_4_1_i he).2 f x).comp (tendsto_add_atTop_nat 1)
      have h2 := hconv x f.toBoundedContinuousFunction
      simp only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] at h2
      exact tendsto_nhds_unique h1 h2
    rw [heq, measure_univ]
  · -- (b) ⇒ (a)
    have hNE := proposition_12_1_1 hb
    have hconst := eChainLimit_eq_of_isReachable he hNE hx
    obtain ⟨ν, hνp, hinv, huniq, hlln⟩ := theorem_18_5_1_i he hb hx
    obtain ⟨-, -, -, hconv0⟩ := theorem_12_0_1_ii he hb
    have hνeq : eChainLimit he x₀ = ν := by
      obtain ⟨-, -, hinv0, -⟩ := theorem_12_0_1_ii he hb
      exact huniq _ ⟨(theorem_12_4_1_iii he).1 hb x₀⟩ (hinv0 x₀)
    refine ⟨ν, hνp, hinv, huniq, fun x f => ?_, hlln⟩
    have := hconv0 f x
    rwa [hconst x, hνeq] at this
  · -- (b) ⇒ (c)
    have hNE := proposition_12_1_1 hb
    exact ⟨hNE, (proposition_18_4_2 he hNE hx).2.1 hb⟩
  · -- (c) ⇒ (b)
    exact (proposition_18_4_2 he hc.1 hx).2.2 hc.2

end MeynTweedie.Positivity
