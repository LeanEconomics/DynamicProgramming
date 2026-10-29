/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.EChainLLN
import Positivity.GeometricDrift
import Positivity.BoundednessCriteria

/-!
# The drift criterion for the law of large numbers (MT §18.5, Theorem 18.5.2)

Meyn and Tweedie, p. 480. `X` is a locally compact, second-countable, metrizable Hausdorff space
with its Borel σ-algebra; the chain started at `x` lives on `pathMeasure P (Measure.dirac x)`.

**Results.**
* **Theorem 18.5.2** (`theorem_18_5_2`, p. 480): if a coercive `V` satisfies (V4),
  `PV ≤ ρV + b 1_C` with `ρ < 1`, `b < ∞`, then the chain is bounded in probability
  (`theorem_18_5_2_bounded`), the occupation probabilities `μ̃_N` of (18.30) are almost surely
  tight from every initial state, and for an e-chain with a reachable state `x*`,
  `μ̃_N → π = Π(x*, ·)` weakly almost surely (18.35).

**Proof.** The book gives no proof (it cites [259]). Here: `W = √V` satisfies
`PW ≤ √ρ W + √b` (`kfunR_sqrt_le_of_drift`, AM–GM) and `E_x[V(Φₖ)] ≤ V(x) + b/(1 − ρ)`
(`integral_coord_le_of_drift`), so the martingale differences `W(Φⱼ₊₁) − PW(Φⱼ)` are square
integrable with bounded second moments and `M_N^{(W)}/N → 0` almost surely
(`ae_tendsto_mdSum_sqrt_div`). Summing `W − PW` along the path then bounds
`(1/N) Σ_{k ≤ N} W(Φₖ)` by `(2 + √b)/(1 − √ρ)` for large `N`, and Markov's inequality on the
compact sublevel sets of `V` gives tightness (`tight_of_tendsto_mdSum_sqrt`,
`tight_of_eventually_tight`). Theorem 18.5.1 (ii) then gives (18.35).

**Tools.** `integrable_mul_of_sq`, `integrable_of_sq`, `measureReal_abs_ge_le_of_sq`
(Chebyshev); for martingale differences of an unbounded `h`: `integral_mul_mdTerm_of_integrable`
(orthogonality), `integrable_mdTerm_sq`, `integral_mdSum_sq_le_of_sq` (`E[Mₘ²] ≤ Km`),
`integral_block_sq_le` and `ae_tendsto_mdSum_div_of_sq` (the strong law, by Chebyshev's bound
along the squares and on the blocks between them, and Borel–Cantelli); `integrable_coe_nnreal`,
`integral_le_of_drift`.

**Hypotheses.** The set `C` of (V4) need not be compact.

**Correction.** None.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

/-! ### Square-integrable functions -/

/-- `|fg| ≤ (f² + g²)/2`: the product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf2 : Integrable (fun ω => f ω ^ 2) Q)
    (hg2 : Integrable (fun ω => g ω ^ 2) Q) : Integrable (fun ω => f ω * g ω) Q := by
  refine Integrable.mono' ((hf2.add hg2).div_const 2) (hf.mul hg).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]

/-- On a finite measure a square-integrable function is integrable (`|f| ≤ (f² + 1)/2`). -/
theorem integrable_of_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
    {f : Ω → ℝ} (hf : Measurable f) (hf2 : Integrable (fun ω => f ω ^ 2) Q) : Integrable f Q := by
  refine Integrable.mono' ((hf2.add (integrable_const 1)).div_const 2) hf.aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f ω| - 1), sq_abs (f ω)]

/-- **Chebyshev's inequality** for a square-integrable `Z`: `P(|Z| ≥ c) ≤ E[Z²]/c²`. -/
theorem measureReal_abs_ge_le_of_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {Z : Ω → ℝ} (hZ2 : Integrable (fun ω => Z ω ^ 2) Q) {c : ℝ}
    (hc : 0 < c) : Q.real {ω | c ≤ |Z ω|} ≤ (∫ ω, Z ω ^ 2 ∂Q) / c ^ 2 := by
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (Z ω))
    hZ2 (c ^ 2)
  have hsub : {ω | c ≤ |Z ω|} ⊆ {ω | c ^ 2 ≤ Z ω ^ 2} := fun ω hω => by
    rw [mem_ofPred_eq] at hω ⊢
    rw [← sq_abs (Z ω)]
    exact pow_le_pow_left₀ hc.le hω 2
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans hmk

variable {X : Type*} [MeasurableSpace X]

/-! ### Martingale differences of an unbounded function -/

/-- **Orthogonality** for an unbounded `h`: `E_μ[φ Dₙ₊₁] = 0` for `𝓕ₙ`-measurable `φ` when
`h(Φₙ₊₁)`, `φ h(Φₙ₊₁)` and `φ Ph(Φₙ)` are integrable (the Markov property (3.28)). -/
theorem integral_mul_mdTerm_of_integrable (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h) (n : ℕ)
    (hhi : Integrable (fun ω : ℕ → X => h (ω (n + 1))) (pathMeasure P μ))
    {φ : (ℕ → X) → ℝ} (hφ : Measurable[natFilt n] φ)
    (h1 : Integrable (fun ω => φ ω * h (ω (n + 1))) (pathMeasure P μ))
    (h2 : Integrable (fun ω => φ ω * kfunR P h (ω n)) (pathMeasure P μ)) :
    ∫ ω, φ ω * mdTerm P h n ω ∂pathMeasure P μ = 0 := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hle := (natFilt (X := X)).le n
  have hH : Measurable fun ω' : ℕ → X => h (ω' 1) := hh.comp (measurable_pi_apply 1)
  have hcond := markov_property P μ n hH hhi
  have hkf : ∀ z, ∫ ω', h (ω' 1) ∂pathKernel P z = kfunR P h z := fun z => by
    have := isMarkovKernel_pathKernel P
    rw [kfunR, show P z = (P ^ 1 : Kernel X X) z by rw [pow_one], ← pathKernel_map_coord P z 1,
      integral_map (measurable_pi_apply 1).aemeasurable hh.aestronglyMeasurable]
  have e1 : ∫ ω, φ ω * h (ω (n + 1)) ∂Q = ∫ ω, φ ω * kfunR P h (ω n) ∂Q := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := Q) (m := natFilt n)
      (f := φ) (g := fun ω => h (shift n ω 1)) hφ.stronglyMeasurable h1 hhi
    rw [← integral_condExp hle (f := fun ω => φ ω * h (ω (n + 1)))]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hcond] with ω h1 h2
    change Q[φ * fun ω => h (shift n ω 1)|natFilt n] ω = _
    rw [h1, Pi.mul_apply, h2, hkf]
  rw [show (fun ω => φ ω * mdTerm P h n ω) =
      fun ω => φ ω * h (ω (n + 1)) - φ ω * kfunR P h (ω n) from
      funext fun ω => by rw [mdTerm, mul_sub],
    integral_sub (f := fun ω => φ ω * h (ω (n + 1))) (g := fun ω => φ ω * kfunR P h (ω n)) h1 h2,
    e1, sub_self]

/-- `Dⱼ₊₁²` is integrable when `h(Φⱼ₊₁)²` and `(Ph(Φⱼ))²` are (`D² ≤ 2h(Φⱼ₊₁)² + 2(Ph(Φⱼ))²`). -/
theorem integrable_mdTerm_sq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {h : X → ℝ} (hh : Measurable h) {j : ℕ}
    (hh2 : Integrable (fun ω : ℕ → X => h (ω (j + 1)) ^ 2) (pathMeasure P μ))
    (hPh2 : Integrable (fun ω : ℕ → X => kfunR P h (ω j) ^ 2) (pathMeasure P μ)) :
    Integrable (fun ω => mdTerm P h j ω ^ 2) (pathMeasure P μ) := by
  have hTm : Measurable (mdTerm P h j) :=
    (measurable_mdTerm P hh (le_refl (j + 1))).mono ((natFilt (X := X)).le _) le_rfl
  refine Integrable.mono' ((hh2.add hPh2).const_mul 2) (hTm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_pow, sq_abs, mdTerm]
  nlinarith [sq_nonneg (h (ω (j + 1)) + kfunR P h (ω j))]

/-- **The `L²` bound for unbounded martingale differences**: if every `Dⱼ₊₁²` is integrable with
`E_μ[Dⱼ₊₁²] ≤ K`, then `Mₘ²` is integrable and `E_μ[Mₘ²] ≤ Km`. Here `h(Φⱼ₊₁)²` and `(Ph(Φⱼ))²`
are assumed integrable. -/
theorem integral_mdSum_sq_le_of_sq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h)
    (hh2 : ∀ j, Integrable (fun ω : ℕ → X => h (ω (j + 1)) ^ 2) (pathMeasure P μ))
    (hPh2 : ∀ j, Integrable (fun ω : ℕ → X => kfunR P h (ω j) ^ 2) (pathMeasure P μ))
    {K : ℝ} (hK : ∀ j, ∫ ω, mdTerm P h j ω ^ 2 ∂pathMeasure P μ ≤ K) (m : ℕ) :
    Integrable (fun ω => mdSum P h m ω ^ 2) (pathMeasure P μ) ∧
      ∫ ω, mdSum P h m ω ^ 2 ∂pathMeasure P μ ≤ K * m := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hle : ∀ n, natFilt (X := X) n ≤ MeasurableSpace.pi := fun n => (natFilt (X := X)).le n
  have hSm : ∀ m, Measurable (mdSum P h m) := fun m => (measurable_mdSum P hh m).mono (hle m) le_rfl
  have hTm : ∀ j, Measurable (mdTerm P h j) := fun j =>
    (measurable_mdTerm P hh (le_refl (j + 1))).mono (hle _) le_rfl
  have hhm : ∀ j, Measurable fun ω : ℕ → X => h (ω (j + 1)) := fun j =>
    hh.comp (measurable_pi_apply _)
  have hkm : ∀ j, Measurable fun ω : ℕ → X => kfunR P h (ω j) := fun j =>
    (measurable_kfunR P hh).comp (measurable_pi_apply _)
  have hT2 : ∀ j, Integrable (fun ω => mdTerm P h j ω ^ 2) Q := fun j =>
    integrable_mdTerm_sq P μ hh (hh2 j) (hPh2 j)
  induction m with
  | zero =>
    have h0 : (fun ω => mdSum P h 0 ω ^ 2) = fun _ => (0 : ℝ) := funext fun ω => by
      rw [mdSum, Finset.range_zero, Finset.sum_empty]; ring
    rw [h0, integral_zero, Nat.cast_zero, mul_zero]
    exact ⟨integrable_zero _ _ _, le_rfl⟩
  | succ m ih =>
    obtain ⟨i1, ih⟩ := ih
    have hsplit : (fun ω => mdSum P h (m + 1) ω ^ 2) = fun ω => mdSum P h m ω ^ 2 +
        2 * (mdSum P h m ω * mdTerm P h m ω) + mdTerm P h m ω ^ 2 := funext fun ω => by
      rw [mdSum, Finset.sum_range_succ, ← mdSum]; ring
    rw [hsplit]
    have i2' : Integrable (fun ω => mdSum P h m ω * mdTerm P h m ω) Q :=
      integrable_mul_of_sq (hSm m) (hTm m) i1 (hT2 m)
    have i2 : Integrable (fun ω => 2 * (mdSum P h m ω * mdTerm P h m ω)) Q := i2'.const_mul 2
    have i12 : Integrable (fun ω => mdSum P h m ω ^ 2 +
        2 * (mdSum P h m ω * mdTerm P h m ω)) Q := i1.add i2
    refine ⟨i12.add (hT2 m), ?_⟩
    have e1 := integral_add i12 (hT2 m)
    have e2 := integral_add i1 i2
    have e3 : ∫ ω, 2 * (mdSum P h m ω * mdTerm P h m ω) ∂Q = 0 := by
      rw [integral_const_mul, integral_mul_mdTerm_of_integrable P μ hh m
        (integrable_of_sq (hhm m) (hh2 m)) (measurable_mdSum P hh m)
        (integrable_mul_of_sq (hSm m) (hhm m) i1 (hh2 m))
        (integrable_mul_of_sq (hSm m) (hkm m) i1 (hPh2 m)), mul_zero]
    rw [e1, e2, e3, add_zero]
    have := hK m
    push_cast
    linarith

/-- **Block sums**: `E_μ[(Σ_{j<L} |D_{a+j+1}|)²] ≤ L²K` when every `E_μ[Dⱼ₊₁²] ≤ K`
(Cauchy–Schwarz). -/
theorem integral_block_sq_le (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {h : X → ℝ} (hh : Measurable h)
    (hT2 : ∀ j, Integrable (fun ω => mdTerm P h j ω ^ 2) (pathMeasure P μ))
    {K : ℝ} (hK : ∀ j, ∫ ω, mdTerm P h j ω ^ 2 ∂pathMeasure P μ ≤ K) (a L : ℕ) :
    Integrable (fun ω => (∑ j ∈ Finset.range L, |mdTerm P h (a + j) ω|) ^ 2)
        (pathMeasure P μ) ∧
      ∫ ω, (∑ j ∈ Finset.range L, |mdTerm P h (a + j) ω|) ^ 2 ∂pathMeasure P μ ≤
        (L : ℝ) ^ 2 * K := by
  set Q := pathMeasure P μ
  have hTm : ∀ j, Measurable (mdTerm P h j) := fun j =>
    (measurable_mdTerm P hh (le_refl (j + 1))).mono ((natFilt (X := X)).le _) le_rfl
  have hpt : ∀ ω, (∑ j ∈ Finset.range L, |mdTerm P h (a + j) ω|) ^ 2 ≤
      L * ∑ j ∈ Finset.range L, mdTerm P h (a + j) ω ^ 2 := fun ω => by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun j => |mdTerm P h (a + j) ω|)
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq_abs]
      at this
    linarith
  have hsum : Integrable (fun ω => (L : ℝ) * ∑ j ∈ Finset.range L, mdTerm P h (a + j) ω ^ 2) Q :=
    (integrable_finsetSum _ fun j _ => hT2 (a + j)).const_mul _
  have hint : Integrable (fun ω => (∑ j ∈ Finset.range L, |mdTerm P h (a + j) ω|) ^ 2) Q := by
    refine Integrable.mono' hsum ((Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (hTm (a + j))).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, (integral_mono hint hsum hpt).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun j _ => hT2 (a + j)]
  have : ∑ j ∈ Finset.range L, ∫ ω, mdTerm P h (a + j) ω ^ 2 ∂Q ≤ ∑ _j ∈ Finset.range L, K :=
    Finset.sum_le_sum fun j _ => hK (a + j)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

/-- **The strong law for square-integrable martingale differences**: if `h(Φⱼ₊₁)²` and
`(Ph(Φⱼ))²` are integrable and `E_μ[Dⱼ₊₁²] ≤ K` for all `j`, then `Mₘ/m → 0` almost surely.
Chebyshev's bound along the squares and on the blocks between them, and Borel–Cantelli. -/
theorem ae_tendsto_mdSum_div_of_sq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h : X → ℝ} (hh : Measurable h)
    (hh2 : ∀ j, Integrable (fun ω : ℕ → X => h (ω (j + 1)) ^ 2) (pathMeasure P μ))
    (hPh2 : ∀ j, Integrable (fun ω : ℕ → X => kfunR P h (ω j) ^ 2) (pathMeasure P μ))
    {K : ℝ} (hK : ∀ j, ∫ ω, mdTerm P h j ω ^ 2 ∂pathMeasure P μ ≤ K) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun m : ℕ => mdSum P h m ω / m) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P μ
  set Q := pathMeasure P μ
  have hT2 : ∀ j, Integrable (fun ω => mdTerm P h j ω ^ 2) Q := fun j =>
    integrable_mdTerm_sq P μ hh (hh2 j) (hPh2 j)
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => sq_nonneg (mdTerm P h 0 ω)).trans (hK 0)
  have hM := integral_mdSum_sq_le_of_sq P μ hh hh2 hPh2 hK
  have hB := integral_block_sq_le P μ hh hT2 hK
  -- the bad events along the squares
  have hsq : ∀ r : ℕ, ∀ᵐ ω ∂Q, ∀ᶠ k in atTop, ω ∉
      {ω | ((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ) ≤ |mdSum P h ((k + 1) ^ 2) ω|} ∪
      {ω | ((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ) ≤
        |(∑ j ∈ Finset.range (2 * k + 3), |mdTerm P h ((k + 1) ^ 2 + j) ω|)|} := fun r => by
    refine ae_eventually_notMem ?_
    have hb : ∀ k : ℕ, Q ({ω | ((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ) ≤ |mdSum P h ((k + 1) ^ 2) ω|} ∪
        {ω | ((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ) ≤
          |(∑ j ∈ Finset.range (2 * k + 3), |mdTerm P h ((k + 1) ^ 2 + j) ω|)|}) ≤
        ENNReal.ofReal (18 * K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := fun k => by
      rw [← ENNReal.ofReal_toReal (measure_ne_top Q _), ← measureReal_def]
      refine ENNReal.ofReal_le_ofReal ((measureReal_union_le _ _).trans ?_)
      have hc : (0 : ℝ) < ((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ) := by positivity
      have h1 := measureReal_abs_ge_le_of_sq (hM ((k + 1) ^ 2)).1 hc
      have h2 := measureReal_abs_ge_le_of_sq (Z := fun ω =>
        ∑ j ∈ Finset.range (2 * k + 3), |mdTerm P h ((k + 1) ^ 2 + j) ω|)
        ((hB ((k + 1) ^ 2) (2 * k + 3)).1) hc
      have e1 : (∫ ω, mdSum P h ((k + 1) ^ 2) ω ^ 2 ∂Q) / (((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ)) ^ 2
          ≤ 9 * K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
        refine (div_le_div_of_nonneg_right (hM ((k + 1) ^ 2)).2 (by positivity)).trans ?_
        have heq : K * (((k + 1) ^ 2 : ℕ) : ℝ) / ((((k + 1) ^ 2 : ℕ) : ℝ) / (r + 1)) ^ 2 =
            K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
          push_cast
          field_simp
        rw [heq]
        have : 0 ≤ K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by positivity
        linarith
      have e2 : (∫ ω, (∑ j ∈ Finset.range (2 * k + 3), |mdTerm P h ((k + 1) ^ 2 + j) ω|) ^ 2
          ∂Q) / (((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ)) ^ 2
          ≤ 9 * K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
        refine (div_le_div_of_nonneg_right (hB ((k + 1) ^ 2) (2 * k + 3)).2
          (by positivity)).trans ?_
        have hk : ((2 * k + 3 : ℕ) : ℝ) ≤ 3 * ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_iff₀ (by positivity)]
        have hsq : ((2 * k + 3 : ℕ) : ℝ) ^ 2 ≤ 9 * ((k + 1 : ℕ) : ℝ) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hk 2
          linarith [show (3 * ((k + 1 : ℕ) : ℝ)) ^ 2 = 9 * ((k + 1 : ℕ) : ℝ) ^ 2 by ring]
        have heq : 9 * K * (r + 1) ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) *
            (((k + 1) ^ 2 : ℕ) / (r + 1 : ℝ)) ^ 2 = 9 * ((k + 1 : ℕ) : ℝ) ^ 2 * K := by
          push_cast
          field_simp
        rw [heq]
        exact mul_le_mul_of_nonneg_right hsq hK0
      linarith
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
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (hω r)
  refine ⟨(K₀ + 1) ^ 2, fun m hm => ?_⟩
  have hn2 : Nat.sqrt m ^ 2 ≤ m := Nat.sqrt_le' m
  have hm2 : m < (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
  have hnK : K₀ + 1 ≤ Nat.sqrt m := Nat.le_sqrt'.2 hm
  obtain ⟨k, hk'⟩ : ∃ k, Nat.sqrt m = k + 1 := ⟨Nat.sqrt m - 1, by omega⟩
  rw [hk'] at hn2 hm2 hnK
  have hk := hK₀ k (by omega)
  rw [mem_union, mem_ofPred_eq, mem_ofPred_eq, not_or, not_le, not_le] at hk
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn2
  have hd3 : d ≤ 2 * k + 3 := by
    rw [show (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) by ring] at hm2
    omega
  have hsplit : mdSum P h m ω = mdSum P h ((k + 1) ^ 2) ω +
      ∑ j ∈ Finset.range d, mdTerm P h ((k + 1) ^ 2 + j) ω := by
    rw [hd, mdSum, mdSum, Finset.sum_range_add]
  have hblk : |∑ j ∈ Finset.range d, mdTerm P h ((k + 1) ^ 2 + j) ω| ≤
      |(∑ j ∈ Finset.range (2 * k + 3), |mdTerm P h ((k + 1) ^ 2 + j) ω|)| := by
    exact ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => |mdTerm P h ((k + 1) ^ 2 + j) ω|)
        (Finset.range_subset_range.2 hd3) fun j _ _ => abs_nonneg _)).trans (le_abs_self _)
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := lt_of_lt_of_le (by positivity) hn2
    exact_mod_cast this
  have hkm : (((k + 1) ^ 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hn2
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hmpos, div_lt_iff₀ hmpos, hsplit]
  have htri := abs_add_le (mdSum P h ((k + 1) ^ 2) ω)
    (∑ j ∈ Finset.range d, mdTerm P h ((k + 1) ^ 2 + j) ω)
  have hfin : 2 * ((((k + 1) ^ 2 : ℕ) : ℝ) / (r + 1)) ≤ ε * m := by
    have h1 : (((k + 1) ^ 2 : ℕ) : ℝ) / (r + 1) = 1 / (r + 1 : ℝ) * (((k + 1) ^ 2 : ℕ) : ℝ) := by
      ring
    rw [h1]
    have := mul_le_mul hr.le hkm (by positivity) (by positivity)
    linarith
  linarith

/-! ### The drift (V4) and its square root -/

omit [MeasurableSpace X] in
/-- For measurable `V ≥ 0` with `∫⁻ V dν < ∞`, the real function `V` is `ν`-integrable and
`∫ V dν = (∫⁻ V dν).toReal`. -/
theorem integrable_coe_nnreal {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {V : Y → ℝ≥0}
    (hVm : Measurable V) (hfin : ∫⁻ z, (V z : ℝ≥0∞) ∂ν ≠ ∞) :
    Integrable (fun z => (V z : ℝ)) ν ∧
      ∫ z, (V z : ℝ) ∂ν = (∫⁻ z, (V z : ℝ≥0∞) ∂ν).toReal := by
  have hm : AEMeasurable (fun z => (V z : ℝ≥0∞)) ν := hVm.coe_nnreal_ennreal.aemeasurable
  have e : (fun z => (V z : ℝ)) = fun z => ((V z : ℝ≥0∞)).toReal :=
    funext fun z => (ENNReal.coe_toReal _).symm
  rw [e]
  exact ⟨integrable_toReal_of_lintegral_ne_top hm hfin,
    integral_toReal hm (Eventually.of_forall fun _ => ENNReal.coe_lt_top)⟩

/-- **(V4) in real form**: if `∫⁻ V dP(y) ≤ ρV(y) + b` with `ρ, b < ∞`, then `V` is
`P(y, ·)`-integrable and `PV(y) ≤ ρV(y) + b` as reals. -/
theorem integral_le_of_drift {P : Kernel X X} {V : X → ℝ≥0} (hVm : Measurable V)
    {ρ b : ℝ≥0∞} (hρ : ρ ≠ ∞) (hb : b ≠ ∞)
    (hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b) (y : X) :
    Integrable (fun z => (V z : ℝ)) (P y) ∧
      ∫ z, (V z : ℝ) ∂P y ≤ ρ.toReal * V y + b.toReal := by
  have hfin : ρ * V y + b ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hρ ENNReal.coe_ne_top, hb⟩
  obtain ⟨hi, he⟩ := integrable_coe_nnreal hVm (ne_top_of_le_ne_top hfin (hdrift y))
  refine ⟨hi, ?_⟩
  rw [he]
  calc (∫⁻ z, (V z : ℝ≥0∞) ∂P y).toReal ≤ (ρ * V y + b).toReal :=
        ENNReal.toReal_mono hfin (hdrift y)
    _ = ρ.toReal * V y + b.toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top hρ ENNReal.coe_ne_top) hb, ENNReal.toReal_mul,
          ENNReal.coe_toReal]

/-- **The square root of a (V4) function** (used for Theorem 18.5.2): with `W = √V`, `W` is
`P(y, ·)`-integrable, `PW ≥ 0` and `PW(y) ≤ √ρ W(y) + √b`. The bound comes from
`W ≤ (V/t + t)/2` for `t > 0` (AM–GM), integrated and optimised over `t`. -/
theorem kfunR_sqrt_le_of_drift {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0}
    (hVm : Measurable V) {ρ b : ℝ≥0∞} (hρ : ρ ≠ ∞) (hb : b ≠ ∞)
    (hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b) (y : X) :
    Integrable (fun z => Real.sqrt (V z)) (P y) ∧ 0 ≤ kfunR P (fun z => Real.sqrt (V z)) y ∧
      kfunR P (fun z => Real.sqrt (V z)) y ≤
        Real.sqrt ρ.toReal * Real.sqrt (V y) + Real.sqrt b.toReal := by
  obtain ⟨hVi, hVle⟩ := integral_le_of_drift hVm hρ hb hdrift y
  have hwm : Measurable fun z => Real.sqrt (V z) :=
    Real.continuous_sqrt.measurable.comp (NNReal.continuous_coe.measurable.comp hVm)
  have hsq : ∀ z, Real.sqrt (V z) ^ 2 = V z := fun z => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hwi : Integrable (fun z => Real.sqrt (V z)) (P y) := by
    refine Integrable.mono' ((hVi.add (integrable_const 1)).div_const 2) hwm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [sq_nonneg (Real.sqrt (V z) - 1), hsq z]
  have h0 : 0 ≤ kfunR P (fun z => Real.sqrt (V z)) y :=
    integral_nonneg fun z => Real.sqrt_nonneg _
  refine ⟨hwi, h0, ?_⟩
  set T := Real.sqrt ρ.toReal * Real.sqrt (V y) + Real.sqrt b.toReal with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT2 : ρ.toReal * V y + b.toReal ≤ T ^ 2 := by
    have h1 : Real.sqrt ρ.toReal ^ 2 = ρ.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    have h2 : Real.sqrt b.toReal ^ 2 = b.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    have h3 : 0 ≤ Real.sqrt ρ.toReal * Real.sqrt (V y) * Real.sqrt b.toReal := by positivity
    have : T ^ 2 = Real.sqrt ρ.toReal ^ 2 * Real.sqrt (V y) ^ 2 + Real.sqrt b.toReal ^ 2 +
        2 * (Real.sqrt ρ.toReal * Real.sqrt (V y) * Real.sqrt b.toReal) := by
      rw [hTdef]; ring
    rw [this, h1, h2, hsq y]
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  set t := T + η with htdef
  have ht : 0 < t := by positivity
  have hpt : ∀ z, Real.sqrt (V z) ≤ ((V z : ℝ) / t + t) / 2 := fun z => by
    rw [div_add' _ _ _ ht.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (V z) - t), hsq z]
  have hint2 : Integrable (fun z => ((V z : ℝ) / t + t) / 2) (P y) :=
    ((hVi.div_const t).add (integrable_const t)).div_const 2
  calc kfunR P (fun z => Real.sqrt (V z)) y ≤ ∫ z, ((V z : ℝ) / t + t) / 2 ∂P y :=
        integral_mono hwi hint2 hpt
    _ = ((∫ z, (V z : ℝ) ∂P y) / t + t) / 2 := by
        rw [integral_div, integral_add (hVi.div_const t) (integrable_const t), integral_div,
          integral_const, probReal_univ, one_smul]
    _ ≤ (t ^ 2 / t + t) / 2 := by
        gcongr
        nlinarith
    _ = T + η := by
        rw [sq, mul_div_assoc, div_self ht.ne', mul_one, htdef]; ring

/-- **Moments along the path under (V4)**: `E_x[V(Φₖ)] ≤ V(x) + b/(1 − ρ)` for all `k`, and
`V(Φₖ)` is `P_x`-integrable. -/
theorem integral_coord_le_of_drift {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0}
    (hVm : Measurable V) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞)
    (hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b) (x : X) (k : ℕ) :
    Integrable (fun ω : ℕ → X => (V (ω k) : ℝ)) (pathMeasure P (Measure.dirac x)) ∧
      ∫ ω, (V (ω k) : ℝ) ∂pathMeasure P (Measure.dirac x) ≤
        ((V x : ℝ≥0∞) + b * (1 - ρ)⁻¹).toReal := by
  have := isMarkovKernel_pow P k
  have hfin : (V x : ℝ≥0∞) + b * (1 - ρ)⁻¹ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.mul_ne_top hb
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hρ).ne')⟩
  have hlaw : ∫⁻ ω, (V (ω k) : ℝ≥0∞) ∂pathMeasure P (Measure.dirac x) =
      ∫⁻ z, (V z : ℝ≥0∞) ∂(P ^ k) x := by
    rw [← lintegral_map hVm.coe_nnreal_ennreal (measurable_pi_apply k), pathMeasure_map_coord,
      Measure.dirac_bind (Kernel.measurable _)]
  have hle : ∫⁻ ω, (V (ω k) : ℝ≥0∞) ∂pathMeasure P (Measure.dirac x) ≤
      (V x : ℝ≥0∞) + b * (1 - ρ)⁻¹ := by
    rw [hlaw]
    have hgeo : ∑' j, ρ ^ j = (1 - ρ)⁻¹ := ENNReal.tsum_geometric ρ
    calc ∫⁻ z, (V z : ℝ≥0∞) ∂(P ^ k) x ≤ ρ ^ k * V x + b * ∑ j ∈ Finset.range k, ρ ^ j :=
          lintegral_pow_le_of_drift hVm.coe_nnreal_ennreal hdrift k x
      _ ≤ V x + b * (1 - ρ)⁻¹ := by
          gcongr
          · exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hρ.le)
          · rw [← hgeo]; exact ENNReal.sum_le_tsum _
  obtain ⟨hi, he⟩ := integrable_coe_nnreal (hVm.comp (measurable_pi_apply k))
    (ne_top_of_le_ne_top hfin hle)
  exact ⟨hi, he ▸ ENNReal.toReal_mono hfin hle⟩

/-- **The martingale of `√V` under (V4)** satisfies the strong law: `M_m^{(√V)}/m → 0`,
`P_x`-a.s. Its differences have `E_x[Dⱼ₊₁²] ≤ 6K + 4b` with `K = V(x) + b/(1 − ρ)`, since
`Dⱼ₊₁² ≤ 2V(Φⱼ₊₁) + 2(P√V(Φⱼ))²` and `(P√V)² ≤ 2ρV + 2b`. -/
theorem ae_tendsto_mdSum_sqrt_div {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0}
    (hVm : Measurable V) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞)
    (hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b) (x : X) :
    ∀ᵐ ω ∂pathMeasure P (Measure.dirac x),
      Tendsto (fun m : ℕ => mdSum P (fun z => Real.sqrt (V z)) m ω / m) atTop (𝓝 0) := by
  have hQ := isProbabilityMeasure_pathMeasure P (Measure.dirac x)
  set Q := pathMeasure P (Measure.dirac x)
  set w : X → ℝ := fun z => Real.sqrt (V z) with hwdef
  have hρt : ρ ≠ ∞ := (hρ.trans ENNReal.one_lt_top).ne
  set K₀ := ((V x : ℝ≥0∞) + b * (1 - ρ)⁻¹).toReal
  have hmom := integral_coord_le_of_drift hVm hρ hb hdrift x
  have hk := kfunR_sqrt_le_of_drift hVm hρt hb hdrift
  have hwm : Measurable w :=
    Real.continuous_sqrt.measurable.comp (NNReal.continuous_coe.measurable.comp hVm)
  have hsq : ∀ z, w z ^ 2 = V z := fun z => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hρ1 : ρ.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top hρ.le
  have hPw2 : ∀ y, kfunR P w y ^ 2 ≤ 2 * V y + 2 * b.toReal := fun y => by
    obtain ⟨-, h0, h1⟩ := hk y
    have e1 : Real.sqrt ρ.toReal ^ 2 = ρ.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    have e2 : Real.sqrt b.toReal ^ 2 = b.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    have h2 : kfunR P w y ^ 2 ≤ (Real.sqrt ρ.toReal * w y + Real.sqrt b.toReal) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have h3 : (Real.sqrt ρ.toReal * w y + Real.sqrt b.toReal) ^ 2 ≤
        2 * (Real.sqrt ρ.toReal ^ 2 * w y ^ 2) + 2 * Real.sqrt b.toReal ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt ρ.toReal * w y - Real.sqrt b.toReal)]
    rw [e1, e2, hsq y] at h3
    have h4 : ρ.toReal * (V y : ℝ) ≤ V y := mul_le_of_le_one_left (NNReal.coe_nonneg _) hρ1
    linarith
  have hh2 : ∀ j, Integrable (fun ω : ℕ → X => w (ω (j + 1)) ^ 2) Q := fun j => by
    have e : (fun ω : ℕ → X => w (ω (j + 1)) ^ 2) = fun ω => (V (ω (j + 1)) : ℝ) :=
      funext fun ω => hsq _
    rw [e]; exact (hmom (j + 1)).1
  have hPh2 : ∀ j, Integrable (fun ω : ℕ → X => kfunR P w (ω j) ^ 2) Q := fun j =>
    Integrable.mono' (((hmom j).1.const_mul 2).add (integrable_const (2 * b.toReal)))
      (((measurable_kfunR P hwm).comp (measurable_pi_apply j)).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [Pi.add_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hPw2 (ω j))
  have hK : ∀ j, ∫ ω, mdTerm P w j ω ^ 2 ∂Q ≤ 6 * K₀ + 4 * b.toReal := fun j => by
    have hbd : Integrable (fun ω : ℕ → X => 2 * (V (ω (j + 1)) : ℝ) +
        (4 * (V (ω j) : ℝ) + 4 * b.toReal)) Q :=
      ((hmom (j + 1)).1.const_mul 2).add (((hmom j).1.const_mul 4).add (integrable_const _))
    have hpt : ∀ ω, mdTerm P w j ω ^ 2 ≤ 2 * (V (ω (j + 1)) : ℝ) +
        (4 * (V (ω j) : ℝ) + 4 * b.toReal) := fun ω => by
      have := hPw2 (ω j)
      rw [mdTerm]
      nlinarith [sq_nonneg (w (ω (j + 1)) + kfunR P w (ω j)), hsq (ω (j + 1))]
    refine (integral_mono (integrable_mdTerm_sq P _ hwm (hh2 j) (hPh2 j)) hbd hpt).trans ?_
    rw [integral_add (f := fun ω : ℕ → X => 2 * (V (ω (j + 1)) : ℝ))
      (g := fun ω : ℕ → X => 4 * (V (ω j) : ℝ) + 4 * b.toReal) ((hmom (j + 1)).1.const_mul 2)
      (((hmom j).1.const_mul 4).add (integrable_const _)),
      integral_add (f := fun ω : ℕ → X => 4 * (V (ω j) : ℝ)) (g := fun _ => 4 * b.toReal)
      ((hmom j).1.const_mul 4) (integrable_const _),
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul]
    linarith [(hmom (j + 1)).2, (hmom j).2]
  exact ae_tendsto_mdSum_div_of_sq P _ hwm hh2 hPh2 hK

/-! ### Theorem 18.5.2 -/

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Tightness of the occupation measures along a path** (the pathwise core of
Theorem 18.5.2): under (V4) with a coercive `V`, if `M_N^{(√V)}/N → 0` along `ω`, then
`(1/N) Σ_{k=1}^N √V(ωₖ)` is eventually bounded by `(2 + √b)/(1 − √ρ)`, so for every `δ > 0` a
sublevel set `K` of `V` has `μ̃_N(Kᶜ) ≤ δ` for all large `N`. -/
theorem tight_of_tendsto_mdSum_sqrt {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0}
    (hVm : Measurable V) (hV : IsCoercive V) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) (hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b) {ω : ℕ → X}
    (hω : Tendsto (fun m : ℕ => mdSum P (fun z => Real.sqrt (V z)) m ω / m) atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ := by
  intro δ hδ
  set w : X → ℝ := fun z => Real.sqrt (V z) with hwdef
  have hρt : ρ ≠ ∞ := (hρ.trans ENNReal.one_lt_top).ne
  have hk := kfunR_sqrt_le_of_drift hVm hρt hb hdrift
  set c := Real.sqrt ρ.toReal with hcdef
  set d := Real.sqrt b.toReal with hddef
  have hc1 : c < 1 := by
    have : ρ.toReal < 1 := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal hρt ENNReal.one_ne_top).2 hρ
    rw [hcdef, ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt ENNReal.toReal_nonneg this
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  set C := (2 + d) / (1 - c) with hCdef
  have hC : 0 < C := div_pos (by linarith) (by linarith)
  set r := C / δ + 1 with hrdef
  have hr : 0 < r := by positivity
  have hCr : C / r ≤ δ := by
    rw [div_le_iff₀ hr, hrdef, mul_add, mul_div_cancel₀ _ hδ.ne', mul_one]
    linarith
  set R : ℝ≥0 := Real.toNNReal (r ^ 2) with hRdef
  refine ⟨closure {y | V y ≤ R}, hV R, ?_⟩
  have hind : ∀ y, (closure {y | V y ≤ R})ᶜ.indicator (fun _ => (1 : ℝ)) y ≤ w y / r :=
    fun y => by
      by_cases hy : y ∈ (closure {y | V y ≤ R})ᶜ
      · rw [indicator_of_mem hy, le_div_iff₀ hr, one_mul]
        have hy' : ¬ V y ≤ R := fun h => hy (subset_closure h)
        rw [not_le, hRdef, Real.toNNReal_lt_iff_lt_coe (sq_nonneg r)] at hy'
        exact (Real.lt_sqrt hr.le).2 hy' |>.le
      · rw [indicator_of_notMem hy]
        exact div_nonneg (Real.sqrt_nonneg _) hr.le
  have hev1 : ∀ᶠ N : ℕ in atTop, mdSum P w N ω / N ≤ 1 :=
    hω.eventually (ge_mem_nhds zero_lt_one)
  have hev2 : ∀ᶠ N : ℕ in atTop, kfunR P w (ω 0) ≤ N :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with N h1 h2 hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hid := sum_sub_sum_kfunR_eq P w N ω
  have hM : mdSum P w N ω ≤ N := by rwa [div_le_iff₀ hNpos, one_mul] at h1
  have hPsum : ∑ k ∈ Finset.Icc 1 N, kfunR P w (ω k) ≤
      c * ∑ k ∈ Finset.Icc 1 N, w (ω k) + d * N := by
    calc ∑ k ∈ Finset.Icc 1 N, kfunR P w (ω k) ≤ ∑ k ∈ Finset.Icc 1 N, (c * w (ω k) + d) :=
          Finset.sum_le_sum fun k _ => (hk (ω k)).2.2
      _ = c * ∑ k ∈ Finset.Icc 1 N, w (ω k) + d * N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
            Nat.add_sub_cancel, nsmul_eq_mul, mul_comm (N : ℝ) d]
  have hPN := (hk (ω N)).2.1
  have hSw : ∑ k ∈ Finset.Icc 1 N, w (ω k) ≤ C * N := by
    rw [hCdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  calc (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, (closure {y | V y ≤ R})ᶜ.indicator
        (fun _ => (1 : ℝ)) (ω k)
      ≤ (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, w (ω k) / r := by
        gcongr with k
        exact hind (ω k)
    _ = (N : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 N, w (ω k)) / r := by
        rw [← Finset.sum_div, mul_div_assoc]
    _ ≤ (N : ℝ)⁻¹ * (C * N) / r := by gcongr
    _ = C / r := by rw [← mul_assoc, mul_comm _ C, mul_assoc, inv_mul_cancel₀ hNpos.ne', mul_one]
    _ ≤ δ := hCr

omit [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Eventual tightness is tightness**: if for every `δ > 0` some compact `K` has
`μ̃_N(Kᶜ) ≤ δ` for all large `N`, then some compact `K'` has it for all `N` (add the finitely
many states visited before). -/
theorem tight_of_eventually_tight {ω : ℕ → X}
    (h : ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧ ∀ N : ℕ,
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ := by
  intro δ hδ
  obtain ⟨K, hK, hev⟩ := h δ hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨K ∪ ω '' Iio N₀, hK.union ((finite_Iio N₀).image ω).isCompact, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · refine le_trans ?_ (hN₀ N hN)
    gcongr
    exact subset_union_left
  · have h0 : ∑ k ∈ Finset.Icc 1 N, (K ∪ ω '' Iio N₀)ᶜ.indicator (fun _ => (1 : ℝ)) (ω k) = 0 :=
      Finset.sum_eq_zero fun k hk => indicator_of_notMem (s := (K ∪ ω '' Iio N₀)ᶜ)
        (fun hc => hc (Or.inr ⟨k,
        mem_Iio.2 (by have := (Finset.mem_Icc.1 hk).2; omega), rfl⟩)) _
    rw [h0, mul_zero]
    exact hδ.le

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Theorem 18.5.2**, first assertion (MT p. 480): if a coercive `V` satisfies (V4),
`PV ≤ ρV + b 1_C` with `ρ < 1` and `b < ∞`, the chain is bounded in probability
(`E_x[V(Φₖ)] ≤ V(x) + b/(1 − ρ)` and Markov's inequality on the sublevel sets of `V`). The set
`C` need not be compact. -/
theorem theorem_18_5_2_bounded {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0}
    (hVm : Measurable V) (hV : IsCoercive V) {ρ b : ℝ≥0∞} {C : Set X} (hρ : ρ < 1)
    (hb : b ≠ ∞) (h4 : DriftV4 P (fun x => (V x : ℝ≥0∞)) ρ b C) : IsBoundedInProbability P :=
  isBoundedInProbability_of_drift hVm hV hρ hb fun x =>
    (h4 x).trans (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x))

/-- **Theorem 18.5.2** (MT p. 480): if a coercive `V` satisfies (V4), `PV ≤ ρV + b 1_C` with
`ρ < 1` and `b < ∞`, then the chain is bounded in probability, and from every initial state the
occupation probabilities are almost surely tight. Hence for an e-chain with a reachable state,
`μ̃_N → π = Π(x*, ·)` weakly almost surely from every initial state (18.35). The book refers to
[259] for the proof; here tightness comes from the strong law for the martingale of `√V`, whose
differences are square integrable under (V4) (`ae_tendsto_mdSum_sqrt_div`,
`tight_of_tendsto_mdSum_sqrt`). The set `C` need not be compact. -/
theorem theorem_18_5_2 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0} (hVm : Measurable V)
    (hV : IsCoercive V)
    {ρ b : ℝ≥0∞} {C : Set X} (hρ : ρ < 1) (hb : b ≠ ∞)
    (h4 : DriftV4 P (fun x => (V x : ℝ≥0∞)) ρ b C) :
    IsBoundedInProbability P ∧
      (∀ x, ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧
        ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ) ∧
      ∀ (he : IsEChain P) {x₀ : X}, IsReachable P x₀ → ∀ x,
        ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ g : X →ᵇ ℝ,
          Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, g (ω k)) atTop
            (𝓝 (∫ y, g y ∂eChainLimit he x₀)) := by
  have hdrift : ∀ y, ∫⁻ z, (V z : ℝ≥0∞) ∂P y ≤ ρ * V y + b := fun y =>
    (h4 y).trans (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) y))
  have hbd := theorem_18_5_2_bounded hVm hV hρ hb h4
  have htight : ∀ x, ∀ᵐ ω ∂pathMeasure P (Measure.dirac x), ∀ δ : ℝ, 0 < δ →
      ∃ K : Set X, IsCompact K ∧ ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, Kᶜ.indicator (fun _ => (1 : ℝ)) (ω k) ≤ δ := fun x =>
    (ae_tendsto_mdSum_sqrt_div hVm hρ hb hdrift x).mono fun ω hω =>
      tight_of_tendsto_mdSum_sqrt hVm hV hρ hb hdrift hω
  exact ⟨hbd, fun x => (htight x).mono fun ω h => tight_of_eventually_tight h,
    fun he x₀ hx x => theorem_18_5_1_ii he hbd.onAverage hx x (htight x)⟩

end MeynTweedie.Positivity
