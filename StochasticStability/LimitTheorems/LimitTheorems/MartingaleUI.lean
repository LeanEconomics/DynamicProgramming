/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.CLTCriteria

/-!
# Maximal inequalities and block maxima of martingales (for MT Theorem D.6.4)

Tightness of the interpolated martingale `n^{−1/2} mₙ(t)` of (D.7) (MT p. 562) needs a bound on
the oscillation of the partial sums over short blocks. This module proves it for square-integrable
martingale differences `Dₖ` (`𝓕ₖ₊₁`-measurable, `E[Dₖ | 𝓕ₖ] = 0`) whose squares are uniformly
integrable, for example identically distributed ones (the case of the Markov chain martingale
`Mₙ(g)` (17.43) under `P_π`). The proof is by truncation: `Dₖ` is split into a bounded martingale
difference, controlled by a fourth-moment maximal inequality, and a martingale difference that is
small in `L²`.

**Martingale tools.**
* `martingale_partialSum`: partial sums of martingale differences are a martingale;
  `submartingale_convex_comp`: a convex function of a martingale is a submartingale (conditional
  Jensen).
* `measureReal_sup_abs_ge_le` (Doob's maximal inequality in moment form):
  `P(max_{j≤m} |Mⱼ| ≥ x) ≤ E[Mₘᵖ]/xᵖ` for even `p`; `measureReal_sup_abs_ge_le_sq`
  (Kolmogorov's inequality, MT Theorem D.6.3 (i) for `p = 2`).
* `integral_pow_four_sum_le`: `E[Sₘ⁴] ≤ 4 B⁴ m²` for martingale differences bounded by `B`.

**Truncation.** `bigPart D K k = Dₖ 1{|Dₖ| > K}`, `mdTail = bigPart − E[bigPart | 𝓕ₖ]`,
`mdHead = Dₖ − mdTail`; `mdTail_props`: both are martingale differences, `|mdHead| ≤ 2K` and
`E[mdTail²] ≤ 4 E[bigPart²]`.

**Uniform integrability.** `sqTail Q D K k = E[Dₖ² 1{Dₖ² ≥ K}]` and `IsUnifSqIntegrable Q D`
(`sup_k sqTail → 0`); `isUnifSqIntegrable_of_identDistrib`, `IsUnifSqIntegrable.const_mul`,
`IsUnifSqIntegrable.exists_sum_le` (`Σ_{k<n} E[Dₖ²] ≤ C n`), `integral_bigPart_sq_le`.

**Results.**
* `measureReal_block_max_le`: `P(max_{j≤m} |S_{k+j} − S_k| ≥ 2x) ≤ 4(2K)⁴m²/x⁴ +
  4mτ/x²` when `E[(Dⱼ 1{|Dⱼ| > K})²] ≤ τ` for all `j`, for every block start `k`
  (`shiftFiltration` moves the filtration).
* `exists_block_max_le`: for all `ε, η > 0` there is `δ ∈ (0, 1]` with
  `P(max_{j≤m} |S_{k+j} − S_k| ≥ ε√n) ≤ ηδ` for all `n ≥ 1`, `k` and `m ≤ 2δn`.
* `tendsto_integral_abs_avg_sq_sub_condExp`: `(1/n) Σ_{k<n} (Dₖ² − E[Dₖ² | 𝓕ₖ]) → 0` in `L¹`
  (used for (D.8)); `tendstoInMeasure_zero_of_integral_abs` (Markov's inequality).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Martingales built from martingale differences -/

/-- The partial sums `Sⱼ = Σ_{i<j} Dᵢ` of martingale differences (`Dᵢ` `𝓕ᵢ₊₁`-measurable,
integrable, `E[Dᵢ | 𝓕ᵢ] = 0`) form a martingale. -/
theorem martingale_partialSum {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hint : ∀ k, Integrable (D k) Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) :
    Martingale (fun j ω => ∑ i ∈ Finset.range j, D i ω) ℱ Q := by
  have hadapt : StronglyAdapted ℱ (fun j ω => ∑ i ∈ Finset.range j, D i ω) := fun j => by
    refine (Finset.measurable_sum _ fun i hi => ?_).stronglyMeasurable
    exact (hD i).measurable.mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) le_rfl
  have hSi : ∀ j, Integrable (fun ω => ∑ i ∈ Finset.range j, D i ω) Q := fun j =>
    integrable_finsetSum _ fun i _ => hint i
  refine martingale_nat hadapt hSi fun j => ?_
  have hsplit : (fun ω => ∑ i ∈ Finset.range (j + 1), D i ω) =
      fun ω => ∑ i ∈ Finset.range j, D i ω + D j ω := by
    ext ω; rw [Finset.sum_range_succ]
  rw [hsplit]
  have h1 : Q[fun ω => ∑ i ∈ Finset.range j, D i ω + D j ω | ℱ j] =ᵐ[Q]
      Q[fun ω => ∑ i ∈ Finset.range j, D i ω | ℱ j] + Q[D j | ℱ j] :=
    condExp_add (hSi j) (hint j) _
  have h2 : Q[fun ω => ∑ i ∈ Finset.range j, D i ω | ℱ j] =
      fun ω => ∑ i ∈ Finset.range j, D i ω :=
    condExp_of_stronglyMeasurable (ℱ.le j) (hadapt j) (hSi j)
  filter_upwards [h1, h0 j] with ω e1 e2
  rw [e1, Pi.add_apply, h2, e2, Pi.zero_apply, add_zero]

/-- A convex continuous function of a martingale is a submartingale (when integrable), by the
conditional Jensen inequality. -/
theorem submartingale_convex_comp {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ Q) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hφc : Continuous φ)
    (hint : ∀ j, Integrable (fun ω => φ (M j ω)) Q) :
    Submartingale (fun j ω => φ (M j ω)) ℱ Q := by
  refine submartingale_nat (fun j => hφc.comp_stronglyMeasurable (hM.stronglyMeasurable j))
    hint fun j => ?_
  have h1 := hM.condExp_ae_eq (Nat.le_succ j)
  have h2 := hφ.map_condExp_le_univ (ℱ.le j) hφc.lowerSemicontinuous (hM.integrable (j + 1))
    (hint (j + 1))
  filter_upwards [h1, h2] with ω e1 e2
  simp only [Function.comp_apply] at e2
  rw [← e1]
  exact e2

/-! ### Maximal inequalities -/

/-- **Doob's maximal inequality** in moment form: for a martingale `M` and an even power `p`
with `Mⱼᵖ` integrable, `P(max_{j≤m} |Mⱼ| ≥ x) ≤ E[Mₘᵖ] / xᵖ` for `x > 0`. -/
theorem measureReal_sup_abs_ge_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ Q) {p : ℕ} (hp : Even p)
    (hint : ∀ j, Integrable (fun ω => M j ω ^ p) Q) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Q.real {ω | x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |M j ω|} ≤ (∫ ω, M m ω ^ p ∂Q) / x ^ p := by
  have hsub := submartingale_convex_comp hM hp.convexOn_pow (continuous_pow p) hint
  have hnn : (0 : ℕ → Ω → ℝ) ≤ fun j ω => M j ω ^ p := fun j ω => hp.pow_nonneg _
  set ε : ℝ≥0 := (x ^ p).toNNReal with hε
  have hεx : (ε : ℝ) = x ^ p := Real.coe_toNNReal _ (by positivity)
  have h := maximal_ineq hsub hnn (ε := ε) m
  set B := {ω | (ε : ℝ) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
    fun k => M k ω ^ p} with hB
  have hsubset : {ω | x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |M j ω|} ⊆ B := by
    intro ω hω
    simp only [hB, mem_ofPred_eq] at hω ⊢
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun j => |M j ω|)
    rw [hjeq] at hω
    rw [hεx]
    calc x ^ p ≤ |M j ω| ^ p := pow_le_pow_left₀ hx.le hω p
      _ = M j ω ^ p := hp.pow_abs _
      _ ≤ _ := Finset.le_sup' (fun k => M k ω ^ p) hj
  have hint_m := hint m
  have hI0 : 0 ≤ ∫ ω in B, M m ω ^ p ∂Q := integral_nonneg fun ω => hp.pow_nonneg _
  have h2 : (ε : ℝ) * Q.real B ≤ ∫ ω in B, M m ω ^ p ∂Q := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hI0] at this
  have h3 : ∫ ω in B, M m ω ^ p ∂Q ≤ ∫ ω, M m ω ^ p ∂Q :=
    setIntegral_le_integral hint_m (Eventually.of_forall fun ω => hp.pow_nonneg _)
  rw [le_div_iff₀ (by positivity), mul_comm, ← hεx]
  calc (ε : ℝ) * Q.real _ ≤ (ε : ℝ) * Q.real B :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) ε.coe_nonneg
    _ ≤ _ := h2.trans h3

/-- **Kolmogorov's inequality** for martingale differences in `L²`:
`P(max_{j≤m} |Sⱼ| ≥ x) ≤ Σ_{k<m} E[Dₖ²] / x²`. -/
theorem measureReal_sup_abs_ge_le_sq {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {x : ℝ} (hx : 0 < x)
    (m : ℕ) :
    Q.real {ω | x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |∑ i ∈ Finset.range j, D i ω|} ≤
      (∑ k ∈ Finset.range m, ∫ ω, D k ω ^ 2 ∂Q) / x ^ 2 := by
  have hM := martingale_partialSum hD (fun k => (hL2 k).integrable one_le_two) h0
  have h := measureReal_sup_abs_ge_le hM even_two
    (fun j => (memLp_finsetSum _ fun i _ => hL2 i).integrable_sq) hx m
  rwa [integral_sq_sum_of_martingale hD hL2 h0 m] at h

/-- **The fourth moment of a bounded martingale**: if `|Dₖ| ≤ B` a.s., then
`E[Sₘ⁴] ≤ 4 B⁴ m²`. -/
theorem integral_pow_four_sum_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂Q, |D k ω| ≤ B) (m : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range m, D i ω) ^ 4 ∂Q ≤ 4 * B ^ 4 * m ^ 2 := by
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hall : ∀ᵐ ω ∂Q, ∀ k, |D k ω| ≤ B := ae_all_iff.2 hB
  set S : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range j, D i ω with hS
  have hSm : ∀ j, Measurable (S j) := fun j => Finset.measurable_sum _ fun i _ => hDm i
  have hSmF : ∀ j, StronglyMeasurable[ℱ j] (S j) := fun j => by
    refine (Finset.measurable_sum _ fun i hi => ?_).stronglyMeasurable
    exact (hD i).measurable.mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) le_rfl
  have hSb : ∀ j, ∀ᵐ ω ∂Q, |S j ω| ≤ j * B := fun j => by
    filter_upwards [hall] with ω hω
    calc |S j ω| ≤ ∑ i ∈ Finset.range j, |D i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, B := Finset.sum_le_sum fun i _ => hω i
      _ = j * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hint : ∀ (f : Ω → ℝ), Measurable f → ∀ C : ℝ, (∀ᵐ ω ∂Q, |f ω| ≤ C) →
      Integrable f Q := fun f hf C hC =>
    Integrable.of_bound hf.aestronglyMeasurable C (hC.mono fun ω h => by
      rwa [Real.norm_eq_abs])
  have hDL2 : ∀ k, MemLp (D k) 2 Q := fun k =>
    MemLp.of_bound (hDm k).aestronglyMeasurable B ((hB k).mono fun ω h => by
      rwa [Real.norm_eq_abs])
  have hB0 : 0 ≤ B := by
    obtain ⟨ω, hω⟩ := (hB 0).exists
    exact (abs_nonneg _).trans hω
  -- `E[Sⱼ²] ≤ j B²`
  have hS2 : ∀ j, ∫ ω, S j ω ^ 2 ∂Q ≤ j * B ^ 2 := by
    intro j
    rw [hS, integral_sq_sum_of_martingale hD hDL2 h0 j]
    calc ∑ k ∈ Finset.range j, ∫ ω, D k ω ^ 2 ∂Q ≤ ∑ k ∈ Finset.range j, B ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc ∫ ω, D k ω ^ 2 ∂Q ≤ ∫ _, B ^ 2 ∂Q := by
                refine integral_mono_ae (hDL2 k).integrable_sq (integrable_const _) ?_
                filter_upwards [hB k] with ω hω
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
            _ = B ^ 2 := by simp
      _ = j * B ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the recursion
  have hstep : ∀ j, ∫ ω, S (j + 1) ω ^ 4 ∂Q ≤ ∫ ω, S j ω ^ 4 ∂Q + 8 * B ^ 4 * j + 3 * B ^ 4 := by
    intro j
    have i4 : Integrable (fun ω => S j ω ^ 4) Q := hint _ ((hSm j).pow_const 4) ((j * B) ^ 4)
      ((hSb j).mono fun ω h => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
    have i3 : Integrable (fun ω => S j ω ^ 3 * D j ω) Q :=
      hint _ (((hSm j).pow_const 3).mul (hDm j)) ((j * B) ^ 3 * B)
        (by filter_upwards [hSb j, hB j] with ω h1 h2
            rw [abs_mul, abs_pow]
            exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 3) h2 (abs_nonneg _)
              (by positivity))
    have i2 : Integrable (fun ω => S j ω ^ 2) Q :=
      (memLp_finsetSum _ fun i _ => hDL2 i).integrable_sq
    have i4' : Integrable (fun ω => S (j + 1) ω ^ 4) Q :=
      hint _ ((hSm (j + 1)).pow_const 4) (((j + 1 : ℕ) * B) ^ 4)
        ((hSb (j + 1)).mono fun ω h => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
    have hcross : ∫ ω, S j ω ^ 3 * D j ω ∂Q = 0 :=
      integral_mul_eq_zero_of_condExp (ℱ.le j) ((hSmF j).pow 3) i3
        ((hDL2 j).integrable one_le_two) (h0 j)
    have hpt : ∀ᵐ ω ∂Q, S (j + 1) ω ^ 4 ≤
        S j ω ^ 4 + 4 * (S j ω ^ 3 * D j ω) + (8 * B ^ 2 * S j ω ^ 2 + 3 * B ^ 4) := by
      filter_upwards [hB j] with ω hω
      have hS1 : S (j + 1) ω = S j ω + D j ω := by
        simp only [hS]; rw [Finset.sum_range_succ]
      rw [hS1]
      have hD2 : D j ω ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      have hD4 : D j ω ^ 4 ≤ B ^ 4 := by
        have : D j ω ^ 4 = (D j ω ^ 2) ^ 2 := by ring
        rw [this, show B ^ 4 = (B ^ 2) ^ 2 by ring]
        exact pow_le_pow_left₀ (sq_nonneg _) hD2 2
      have key : (S j ω + D j ω) ^ 4 - S j ω ^ 4 - 4 * (S j ω ^ 3 * D j ω) ≤
          8 * S j ω ^ 2 * D j ω ^ 2 + 3 * D j ω ^ 4 := by
        nlinarith [sq_nonneg (S j ω * D j ω - D j ω ^ 2)]
      have h3 : 8 * S j ω ^ 2 * D j ω ^ 2 ≤ 8 * B ^ 2 * S j ω ^ 2 := by
        nlinarith [sq_nonneg (S j ω)]
      linarith
    have hR : Integrable (fun ω => 8 * B ^ 2 * S j ω ^ 2 + 3 * B ^ 4) Q :=
      (i2.const_mul _).add (integrable_const _)
    calc ∫ ω, S (j + 1) ω ^ 4 ∂Q
        ≤ ∫ ω, (S j ω ^ 4 + 4 * (S j ω ^ 3 * D j ω) + (8 * B ^ 2 * S j ω ^ 2 + 3 * B ^ 4)) ∂Q :=
          integral_mono_ae i4' ((i4.add (i3.const_mul 4)).add hR) hpt
      _ = ∫ ω, S j ω ^ 4 ∂Q + 4 * ∫ ω, S j ω ^ 3 * D j ω ∂Q +
            (8 * B ^ 2 * ∫ ω, S j ω ^ 2 ∂Q + 3 * B ^ 4) := by
          rw [integral_add (f := fun ω => S j ω ^ 4 + 4 * (S j ω ^ 3 * D j ω))
            (g := fun ω => 8 * B ^ 2 * S j ω ^ 2 + 3 * B ^ 4) (i4.add (i3.const_mul 4)) hR,
            integral_add (f := fun ω => S j ω ^ 4) (g := fun ω => 4 * (S j ω ^ 3 * D j ω)) i4
              (i3.const_mul 4), integral_const_mul,
            integral_add (f := fun ω => 8 * B ^ 2 * S j ω ^ 2) (g := fun _ => 3 * B ^ 4)
              (i2.const_mul _) (integrable_const _), integral_const_mul]
          simp
      _ ≤ ∫ ω, S j ω ^ 4 ∂Q + 4 * 0 + (8 * B ^ 2 * (j * B ^ 2) + 3 * B ^ 4) := by
          rw [hcross]
          gcongr
          exact hS2 j
      _ = ∫ ω, S j ω ^ 4 ∂Q + 8 * B ^ 4 * j + 3 * B ^ 4 := by ring
  have hind : ∀ m : ℕ, ∫ ω, S m ω ^ 4 ∂Q ≤ B ^ 4 * (4 * m ^ 2 - m) := by
    intro m
    induction m with
    | zero => simp [hS]
    | succ m ih =>
      refine (hstep m).trans ?_
      push_cast
      nlinarith
  refine (hind m).trans ?_
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [pow_nonneg hB0 4]

/-- A bounded martingale-difference sum has integrable powers. -/
theorem integrable_pow_sum_of_bdd {Q : Measure Ω} [IsFiniteMeasure Q] {D : ℕ → Ω → ℝ}
    (hDm : ∀ k, Measurable (D k)) {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂Q, |D k ω| ≤ B) (p j : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range j, D i ω) ^ p) Q := by
  have hall : ∀ᵐ ω ∂Q, ∀ k, |D k ω| ≤ B := ae_all_iff.2 hB
  refine Integrable.of_bound (((Finset.measurable_sum _ fun i _ => hDm i).pow_const p)
    |>.aestronglyMeasurable) ((j * B) ^ p) ?_
  filter_upwards [hall] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ p
  calc |∑ i ∈ Finset.range j, D i ω| ≤ ∑ i ∈ Finset.range j, |D i ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j, B := Finset.sum_le_sum fun i _ => hω i
    _ = j * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Truncation of martingale differences -/

/-- The large part `Dₖ 1{|Dₖ| > K}` of `Dₖ`. -/
noncomputable def bigPart (D : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if K < |D k ω| then D k ω else 0

/-- The conditionally centred large part `Dₖ 1{|Dₖ| > K} − E[Dₖ 1{|Dₖ| > K} | 𝓕ₖ]`. -/
noncomputable def mdTail (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (K : ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  bigPart D K k ω - Q[bigPart D K k | ℱ k] ω

/-- The bounded part `Dₖ − mdTail`. -/
noncomputable def mdHead (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (K : ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  D k ω - mdTail Q ℱ D K k ω

/-- Properties of the truncation: both parts are martingale differences, the head is bounded by
`2K`, the tail is in `L²` with `E[tail²] ≤ 4 E[Dₖ² 1{|Dₖ| > K}]`. -/
theorem mdTail_props {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {K : ℝ} (hK : 0 ≤ K)
    (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (mdTail Q ℱ D K k) ∧ MemLp (mdTail Q ℱ D K k) 2 Q ∧
      Q[mdTail Q ℱ D K k | ℱ k] =ᵐ[Q] 0 ∧
      ∫ ω, mdTail Q ℱ D K k ω ^ 2 ∂Q ≤ 4 * ∫ ω, bigPart D K k ω ^ 2 ∂Q ∧
      StronglyMeasurable[ℱ (k + 1)] (mdHead Q ℱ D K k) ∧
      Q[mdHead Q ℱ D K k | ℱ k] =ᵐ[Q] 0 ∧ ∀ᵐ ω ∂Q, |mdHead Q ℱ D K k ω| ≤ 2 * K := by
  have hDk : Measurable[ℱ (k + 1)] (D k) := (hD k).measurable
  have hbigF : StronglyMeasurable[ℱ (k + 1)] (bigPart D K k) :=
    (Measurable.ite (measurableSet_lt measurable_const (continuous_abs.measurable.comp hDk)) hDk
      measurable_const).stronglyMeasurable
  have hbigm : Measurable (bigPart D K k) := hbigF.measurable.mono (ℱ.le (k + 1)) le_rfl
  have hbigle : ∀ ω, |bigPart D K k ω| ≤ |D k ω| := fun ω => by
    unfold bigPart; split_ifs <;> simp
  have hbig2 : MemLp (bigPart D K k) 2 Q := (hL2 k).of_le hbigm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hbigle ω)
  have hbigi : Integrable (bigPart D K k) Q := hbig2.integrable one_le_two
  have hce2 : MemLp (Q[bigPart D K k | ℱ k]) 2 Q := hbig2.condExp one_le_two
  have hcesm : StronglyMeasurable[ℱ k] (Q[bigPart D K k | ℱ k]) := stronglyMeasurable_condExp
  have hTF : StronglyMeasurable[ℱ (k + 1)] (mdTail Q ℱ D K k) := by
    have h1 : StronglyMeasurable[ℱ (k + 1)] (Q[bigPart D K k | ℱ k]) :=
      (hcesm.measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl).stronglyMeasurable
    exact (hbigF.measurable.sub h1.measurable).stronglyMeasurable
  have hT2 : MemLp (mdTail Q ℱ D K k) 2 Q := hbig2.sub hce2
  have hTi : Integrable (mdTail Q ℱ D K k) Q := hT2.integrable one_le_two
  have hT0 : Q[mdTail Q ℱ D K k | ℱ k] =ᵐ[Q] 0 := by
    have h1 : Q[mdTail Q ℱ D K k | ℱ k] =ᵐ[Q]
        Q[bigPart D K k | ℱ k] - Q[Q[bigPart D K k | ℱ k] | ℱ k] :=
      condExp_sub hbigi integrable_condExp _
    have h2 : Q[Q[bigPart D K k | ℱ k] | ℱ k] = Q[bigPart D K k | ℱ k] :=
      condExp_of_stronglyMeasurable (ℱ.le k) hcesm integrable_condExp
    filter_upwards [h1] with ω e1
    rw [e1, h2, Pi.sub_apply, sub_self, Pi.zero_apply]
  have hTsq : ∫ ω, mdTail Q ℱ D K k ω ^ 2 ∂Q ≤ 4 * ∫ ω, bigPart D K k ω ^ 2 ∂Q := by
    have hJ := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ (ℱ.le k)
      (continuous_pow 2).lowerSemicontinuous hbigi hbig2.integrable_sq (m := ℱ k)
    have hce : ∫ ω, (Q[bigPart D K k | ℱ k]) ω ^ 2 ∂Q ≤ ∫ ω, bigPart D K k ω ^ 2 ∂Q := by
      calc ∫ ω, (Q[bigPart D K k | ℱ k]) ω ^ 2 ∂Q
          ≤ ∫ ω, (Q[(fun x : ℝ => x ^ 2) ∘ bigPart D K k | ℱ k]) ω ∂Q :=
            integral_mono_ae hce2.integrable_sq integrable_condExp hJ
        _ = ∫ ω, bigPart D K k ω ^ 2 ∂Q := integral_condExp (ℱ.le k)
    calc ∫ ω, mdTail Q ℱ D K k ω ^ 2 ∂Q
        ≤ ∫ ω, (2 * bigPart D K k ω ^ 2 + 2 * (Q[bigPart D K k | ℱ k]) ω ^ 2) ∂Q := by
          refine integral_mono hT2.integrable_sq
            ((hbig2.integrable_sq.const_mul 2).add (hce2.integrable_sq.const_mul 2))
            fun ω => ?_
          simp only [mdTail]
          nlinarith [sq_nonneg (bigPart D K k ω + (Q[bigPart D K k | ℱ k]) ω)]
      _ = 2 * ∫ ω, bigPart D K k ω ^ 2 ∂Q + 2 * ∫ ω, (Q[bigPart D K k | ℱ k]) ω ^ 2 ∂Q := by
          rw [integral_add (f := fun ω => 2 * bigPart D K k ω ^ 2)
            (g := fun ω => 2 * (Q[bigPart D K k | ℱ k]) ω ^ 2)
            (hbig2.integrable_sq.const_mul 2) (hce2.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 4 * ∫ ω, bigPart D K k ω ^ 2 ∂Q := by linarith
  -- the head
  have hHF : StronglyMeasurable[ℱ (k + 1)] (mdHead Q ℱ D K k) :=
    (hDk.sub hTF.measurable).stronglyMeasurable
  have hH0 : Q[mdHead Q ℱ D K k | ℱ k] =ᵐ[Q] 0 := by
    have h1 : Q[mdHead Q ℱ D K k | ℱ k] =ᵐ[Q] Q[D k | ℱ k] - Q[mdTail Q ℱ D K k | ℱ k] :=
      condExp_sub ((hL2 k).integrable one_le_two) hTi _
    filter_upwards [h1, h0 k, hT0] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3, Pi.zero_apply, sub_zero]
  have hHb : ∀ᵐ ω ∂Q, |mdHead Q ℱ D K k ω| ≤ 2 * K := by
    set sm : Ω → ℝ := fun ω => D k ω - bigPart D K k ω with hsm
    have hsmb : ∀ ω, |sm ω| ≤ K := fun ω => by
      simp only [hsm, bigPart]
      split_ifs with h
      · simp only [sub_self, abs_zero]; exact hK
      · push Not at h; simpa using h
    have hsmi : Integrable sm Q := ((hL2 k).integrable one_le_two).sub hbigi
    have hb1 : ∀ᵐ ω ∂Q, |(Q[sm | ℱ k]) ω| ≤ K := by
      exact ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ k) (R := K) (f := sm)
        (Eventually.of_forall fun ω => hsmb ω)
    have hbig_eq : bigPart D K k = fun ω => D k ω - sm ω := by
      ext ω; simp only [hsm]; ring
    have hce_eq : Q[bigPart D K k | ℱ k] =ᵐ[Q] Q[D k | ℱ k] - Q[sm | ℱ k] := by
      rw [hbig_eq]; exact condExp_sub ((hL2 k).integrable one_le_two) hsmi _
    filter_upwards [hce_eq, hb1, h0 k] with ω e1 e2 e3
    have : mdHead Q ℱ D K k ω = sm ω - (Q[sm | ℱ k]) ω := by
      simp only [mdHead, mdTail, hsm]
      rw [e1, Pi.sub_apply, e3, Pi.zero_apply]
      ring
    rw [this]
    calc |sm ω - (Q[sm | ℱ k]) ω| ≤ |sm ω| + |(Q[sm | ℱ k]) ω| := abs_sub _ _
      _ ≤ K + K := add_le_add (hsmb ω) e2
      _ = 2 * K := by ring
  exact ⟨hTF, hT2, hT0, hTsq, hHF, hH0, hHb⟩

/-! ### The block-maximum bound -/

/-- The filtration `j ↦ 𝓕_{k+j}`, seen from time `k`. -/
def shiftFiltration (ℱ : Filtration ℕ mΩ) (k : ℕ) : Filtration ℕ mΩ :=
  ⟨fun j => ℱ (k + j), fun _ _ hij => ℱ.mono (Nat.add_le_add_left hij k), fun j => ℱ.le (k + j)⟩

/-! ### Uniform integrability of the squares -/

/-- The squared tail `E[Dₖ² 1{Dₖ² ≥ K}]`. -/
noncomputable def sqTail (Q : Measure Ω) (D : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω ∂Q

/-- **Uniform integrability of the squares** `Dₖ²`: `sup_k E[Dₖ² 1{Dₖ² ≥ K}] → 0` as `K → ∞`.
It holds for identically distributed square-integrable `Dₖ`
(`isUnifSqIntegrable_of_identDistrib`) and for uniformly bounded ones. -/
def IsUnifSqIntegrable (Q : Measure Ω) (D : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, sqTail Q D K k ≤ ε

omit [MeasurableSpace Ω] in
/-- Pointwise: `y² 1{y² ≥ K}` is antitone in `K`. -/
theorem indicator_sq_antitone (D : ℕ → Ω → ℝ) {K K' : ℝ} (hKK : K ≤ K') (k : ℕ) (ω : Ω) :
    {ω | K' ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω ≤
      {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω :=
  Set.indicator_le_indicator_of_subset (fun _ h => hKK.trans h) (fun _ => sq_nonneg _) ω

/-- `sqTail` is antitone in the level. -/
theorem sqTail_antitone {Q : Measure Ω} {D : ℕ → Ω → ℝ} (hDm : ∀ k, Measurable (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) {K K' : ℝ} (hKK : K ≤ K') (k : ℕ) :
    sqTail Q D K' k ≤ sqTail Q D K k :=
  integral_mono ((hL2 k).integrable_sq.indicator
    (measurableSet_le measurable_const ((hDm k).pow_const 2)))
    ((hL2 k).integrable_sq.indicator (measurableSet_le measurable_const ((hDm k).pow_const 2)))
    (indicator_sq_antitone D hKK k)

/-- Uniform integrability holds from every level on. -/
theorem IsUnifSqIntegrable.exists_forall_ge {Q : Measure Ω} {D : ℕ → Ω → ℝ}
    (hUI : IsUnifSqIntegrable Q D) (hDm : ∀ k, Measurable (D k)) (hL2 : ∀ k, MemLp (D k) 2 Q)
    {ε : ℝ} (hε : 0 < ε) : ∃ K, 0 ≤ K ∧ ∀ K', K ≤ K' → ∀ k, sqTail Q D K' k ≤ ε := by
  obtain ⟨K, hK⟩ := hUI ε hε
  exact ⟨max K 0, le_max_right _ _, fun K' hK' k =>
    (sqTail_antitone hDm hL2 ((le_max_left _ _).trans hK') k).trans (hK k)⟩

/-- Identically distributed square-integrable `Dₖ` have uniformly integrable squares. -/
theorem isUnifSqIntegrable_of_identDistrib {Q : Measure Ω} [IsProbabilityMeasure Q]
    {D : ℕ → Ω → ℝ} (hDm : Measurable (D 0)) (hL2 : MemLp (D 0) 2 Q)
    (hid : ∀ k, IdentDistrib (D k) (D 0) Q Q) : IsUnifSqIntegrable Q D := by
  intro ε hε
  have h := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun K : ℕ => {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2))
    (f := fun _ => (0 : ℝ)) (fun ω => D 0 ω ^ 2)
    (fun K => ((hDm.pow_const 2).indicator (measurableSet_le measurable_const
      (hDm.pow_const 2))).aestronglyMeasurable) hL2.integrable_sq
    (fun K => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω _ => sq_nonneg _) _)]
      exact Set.indicator_le_self' (fun ω _ => sq_nonneg _) ω)
    (Eventually.of_forall fun ω => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (D 0 ω ^ 2)
      filter_upwards [eventually_ge_atTop N] with K hK
      have h1 : D 0 ω ^ 2 < K := hN.trans_le (by exact_mod_cast hK)
      rw [Set.indicator_of_notMem (show ω ∉ {ω | (K : ℝ) ≤ D 0 ω ^ 2} by
        simp only [mem_ofPred_eq, not_le]; exact h1)])
  simp only [integral_zero] at h
  obtain ⟨K, hK⟩ := (h.eventually (gt_mem_nhds hε)).exists
  refine ⟨K, fun k => ?_⟩
  have hu : Measurable fun y : ℝ => {y : ℝ | (K : ℝ) ≤ y ^ 2}.indicator (fun y => y ^ 2) y :=
    (measurable_id.pow_const 2).indicator (measurableSet_le measurable_const
      (measurable_id.pow_const 2))
  have e := ((hid k).comp hu).integral_eq
  have hcomp : ∀ j, sqTail Q D K j =
      ∫ x, {y : ℝ | (K : ℝ) ≤ y ^ 2}.indicator (fun y => y ^ 2) (D j x) ∂Q := fun _ => rfl
  rw [hcomp k]
  simp only [Function.comp_def] at e
  rw [e, ← hcomp 0]
  exact hK.le

/-- `E[(Dₖ 1{|Dₖ| > K})²] ≤ E[Dₖ² 1{Dₖ² ≥ K²}]`. -/
theorem integral_bigPart_sq_le {Q : Measure Ω} {D : ℕ → Ω → ℝ} (hDm : ∀ k, Measurable (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    ∫ ω, bigPart D K k ω ^ 2 ∂Q ≤ sqTail Q D (K ^ 2) k := by
  have hbm : Measurable (bigPart D K k) := Measurable.ite (measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hDm k))) (hDm k) measurable_const
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    ((hL2 k).integrable_sq.indicator (measurableSet_le measurable_const ((hDm k).pow_const 2)))
    (Eventually.of_forall fun ω => ?_)
  simp only [bigPart]
  split_ifs with h
  · have h1 : K ^ 2 ≤ D k ω ^ 2 := by
      rw [← sq_abs (D k ω)]; exact pow_le_pow_left₀ hK h.le 2
    rw [Set.indicator_of_mem (show ω ∈ {ω | K ^ 2 ≤ D k ω ^ 2} from h1)]
  · rw [zero_pow two_ne_zero]
    exact Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω

omit [MeasurableSpace Ω] in
/-- Pointwise `y² − min(y², K) ≤ y² 1{y² ≥ K}` for `K ≥ 0`. -/
theorem sq_sub_min_le_indicator (D : ℕ → Ω → ℝ) {K : ℝ} (hK : 0 ≤ K) (k : ℕ) (ω : Ω) :
    D k ω ^ 2 - min (D k ω ^ 2) K ≤ {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω := by
  by_cases h : K ≤ D k ω ^ 2
  · rw [Set.indicator_of_mem (show ω ∈ {ω | K ≤ D k ω ^ 2} from h), min_eq_right h]
    linarith
  · push Not at h
    rw [Set.indicator_of_notMem (show ω ∉ {ω | K ≤ D k ω ^ 2} by
      simp only [mem_ofPred_eq, not_le]; exact h), min_eq_left h.le, sub_self]

/-- A uniform bound on second moments: `E[Dₖ²] ≤ K + E[Dₖ² 1{Dₖ² ≥ K}]`. -/
theorem integral_sq_le_add_sqTail {Q : Measure Ω} [IsProbabilityMeasure Q] {D : ℕ → Ω → ℝ}
    (hDm : ∀ k, Measurable (D k)) (hL2 : ∀ k, MemLp (D k) 2 Q) {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    ∫ ω, D k ω ^ 2 ∂Q ≤ K + sqTail Q D K k := by
  have hi : Integrable (fun ω => {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω) Q :=
    (hL2 k).integrable_sq.indicator (measurableSet_le measurable_const ((hDm k).pow_const 2))
  calc ∫ ω, D k ω ^ 2 ∂Q ≤ ∫ ω, (K + {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω) ∂Q :=
        integral_mono (hL2 k).integrable_sq ((integrable_const K).add hi) fun ω => by
          by_cases h : K ≤ D k ω ^ 2
          · rw [Set.indicator_of_mem (show ω ∈ {ω | K ≤ D k ω ^ 2} from h)]
            linarith
          · push Not at h
            rw [Set.indicator_of_notMem (show ω ∉ {ω | K ≤ D k ω ^ 2} by
              simp only [mem_ofPred_eq, not_le]; exact h)]
            linarith
    _ = K + sqTail Q D K k := by
        rw [integral_add (integrable_const K) hi, integral_const, probReal_univ, one_smul]; rfl

/-- Uniform integrability of the squares gives `Σ_{k<n} E[Dₖ²] ≤ C n`. -/
theorem IsUnifSqIntegrable.exists_sum_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {D : ℕ → Ω → ℝ} (hUI : IsUnifSqIntegrable Q D) (hDm : ∀ k, Measurable (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) :
    ∃ C, ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n := by
  obtain ⟨K, hK0, hK⟩ := hUI.exists_forall_ge hDm hL2 one_pos
  refine ⟨K + 1, fun n => ?_⟩
  calc ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ ∑ _k ∈ Finset.range n, (K + 1) :=
        Finset.sum_le_sum fun k _ => (integral_sq_le_add_sqTail hDm hL2 hK0 k).trans
          (by linarith [hK K le_rfl k])
    _ = (K + 1) * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- Uniform integrability of the squares is preserved by scaling. -/
theorem IsUnifSqIntegrable.const_mul {Q : Measure Ω} {D : ℕ → Ω → ℝ}
    (hUI : IsUnifSqIntegrable Q D) (a : ℝ) :
    IsUnifSqIntegrable Q (fun k ω => a * D k ω) := by
  intro ε hε
  rcases eq_or_ne a 0 with rfl | ha
  · refine ⟨1, fun k => ?_⟩
    have : (fun ω => {ω | (1 : ℝ) ≤ (0 * D k ω) ^ 2}.indicator
        (fun ω => (0 * D k ω) ^ 2) ω) = fun _ => 0 := by
      ext ω; simp
    rw [sqTail, this, integral_zero]; exact hε.le
  have ha2 : 0 < a ^ 2 := by positivity
  obtain ⟨K, hK⟩ := hUI (ε / a ^ 2) (by positivity)
  refine ⟨a ^ 2 * K, fun k => ?_⟩
  have e : (fun ω => {ω | a ^ 2 * K ≤ (a * D k ω) ^ 2}.indicator (fun ω => (a * D k ω) ^ 2) ω)
      = fun ω => a ^ 2 * {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω := by
    ext ω
    by_cases h : K ≤ D k ω ^ 2
    · have h' : a ^ 2 * K ≤ (a * D k ω) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left h ha2.le
      rw [Set.indicator_of_mem (show ω ∈ {ω | a ^ 2 * K ≤ (a * D k ω) ^ 2} from h'),
        Set.indicator_of_mem (show ω ∈ {ω | K ≤ D k ω ^ 2} from h), mul_pow]
    · have h' : ¬ (a ^ 2 * K ≤ (a * D k ω) ^ 2) := by
        rw [mul_pow]; intro h''; exact h ((mul_le_mul_iff_of_pos_left ha2).1 h'')
      rw [Set.indicator_of_notMem (show ω ∉ {ω | a ^ 2 * K ≤ (a * D k ω) ^ 2} from h'),
        Set.indicator_of_notMem (show ω ∉ {ω | K ≤ D k ω ^ 2} from h), mul_zero]
  have h1 := hK k
  rw [sqTail] at h1 ⊢
  rw [e, integral_const_mul]
  calc a ^ 2 * ∫ ω, {ω | K ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω ∂Q
      ≤ a ^ 2 * (ε / a ^ 2) := mul_le_mul_of_nonneg_left h1 ha2.le
    _ = ε := by field_simp

/-- **The block-maximum bound**: for square-integrable martingale differences, every truncation
level `K ≥ 0` with `E[(Dⱼ 1{|Dⱼ| > K})²] ≤ τ` for all `j`, block start `k`, length `m` and
`x > 0`, `P(max_{j≤m} |S_{k+j} − S_k| ≥ 2x) ≤ 4 (2K)⁴ m² / x⁴ + 4 m τ / x²`. -/
theorem measureReal_block_max_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {K τ : ℝ} (hK : 0 ≤ K)
    (hτ : ∀ j, ∫ ω, bigPart D K j ω ^ 2 ∂Q ≤ τ) (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    Q.real {ω | 2 * x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |∑ i ∈ Finset.range j, D (k + i) ω|} ≤
      4 * (2 * K) ^ 4 * m ^ 2 / x ^ 4 + 4 * m * τ / x ^ 2 := by
  set G := shiftFiltration ℱ k with hG
  set H : ℕ → Ω → ℝ := fun i => mdHead Q ℱ D K (k + i) with hHdef
  set T : ℕ → Ω → ℝ := fun i => mdTail Q ℱ D K (k + i) with hTdef
  have hp := fun i => mdTail_props hD hL2 h0 hK (k + i)
  have hHF : ∀ i, StronglyMeasurable[G (i + 1)] (H i) := fun i => (hp i).2.2.2.2.1
  have hH0 : ∀ i, Q[H i | G i] =ᵐ[Q] 0 := fun i => (hp i).2.2.2.2.2.1
  have hHb : ∀ i, ∀ᵐ ω ∂Q, |H i ω| ≤ 2 * K := fun i => (hp i).2.2.2.2.2.2
  have hTF : ∀ i, StronglyMeasurable[G (i + 1)] (T i) := fun i => (hp i).1
  have hT2 : ∀ i, MemLp (T i) 2 Q := fun i => (hp i).2.1
  have hT0 : ∀ i, Q[T i | G i] =ᵐ[Q] 0 := fun i => (hp i).2.2.1
  have hHm : ∀ i, Measurable (H i) := fun i =>
    (hHF i).measurable.mono (G.le (i + 1)) le_rfl
  have hHi : ∀ i, Integrable (H i) Q := fun i =>
    Integrable.of_bound (hHm i).aestronglyMeasurable (2 * K)
      ((hHb i).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hMH := martingale_partialSum hHF hHi hH0
  -- the two maximal bounds
  have hA := measureReal_sup_abs_ge_le hMH (p := 4) (by decide)
    (fun j => integrable_pow_sum_of_bdd hHm hHb 4 j) hx m
  have hA' : (∫ ω, (∑ i ∈ Finset.range m, H i ω) ^ 4 ∂Q) / x ^ 4 ≤
      4 * (2 * K) ^ 4 * m ^ 2 / x ^ 4 :=
    div_le_div_of_nonneg_right (integral_pow_four_sum_le hHF hH0 hHb m) (by positivity)
  have hB := measureReal_sup_abs_ge_le_sq hTF hT2 hT0 hx m
  have hB' : (∑ i ∈ Finset.range m, ∫ ω, T i ω ^ 2 ∂Q) / x ^ 2 ≤ 4 * m * τ / x ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ∑ i ∈ Finset.range m, ∫ ω, T i ω ^ 2 ∂Q
        ≤ ∑ _i ∈ Finset.range m, 4 * τ :=
          Finset.sum_le_sum fun i _ => ((hp i).2.2.2.1).trans
            (mul_le_mul_of_nonneg_left (hτ (k + i)) (by norm_num))
      _ = 4 * m * τ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the decomposition of the event
  have hsplit : ∀ i ω, D (k + i) ω = H i ω + T i ω := fun i ω => by
    simp only [hHdef, hTdef, mdHead]; ring
  have hsub : {ω | 2 * x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |∑ i ∈ Finset.range j, D (k + i) ω|} ⊆
      {ω | x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        fun j => |∑ i ∈ Finset.range j, H i ω|} ∪
      {ω | x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        fun j => |∑ i ∈ Finset.range j, T i ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun j => |∑ i ∈ Finset.range j, D (k + i) ω|)
    rw [hjeq] at hω
    have e : ∑ i ∈ Finset.range j, D (k + i) ω =
        ∑ i ∈ Finset.range j, H i ω + ∑ i ∈ Finset.range j, T i ω := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => hsplit i ω
    rw [e] at hω
    have h3 := abs_add_le (∑ i ∈ Finset.range j, H i ω) (∑ i ∈ Finset.range j, T i ω)
    by_cases h4 : x ≤ |∑ i ∈ Finset.range j, H i ω|
    · exact Or.inl (h4.trans (Finset.le_sup' (fun j => |∑ i ∈ Finset.range j, H i ω|) hj))
    · push Not at h4
      exact Or.inr ((show x ≤ |∑ i ∈ Finset.range j, T i ω| by linarith).trans
        (Finset.le_sup' (fun j => |∑ i ∈ Finset.range j, T i ω|) hj))
  calc Q.real _ ≤ Q.real _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (hA.trans hA') (hB.trans hB')

/-- **Small block maxima**: for square-integrable martingale differences with uniformly
integrable squares, for all `ε, η > 0` there is `δ ∈ (0, 1]` such that for every `n ≥ 1`, block
start `k` and block length `m ≤ 2δn`, `P(max_{j≤m} |S_{k+j} − S_k| ≥ ε √n) ≤ η δ`. -/
theorem exists_block_max_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ n : ℕ, 1 ≤ n → ∀ k m : ℕ, (m : ℝ) ≤ 2 * δ * n →
      Q.real {ω | ε * √(n : ℝ) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        fun j => |∑ i ∈ Finset.range j, D (k + i) ω|} ≤ η * δ := by
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  obtain ⟨K₀, hK₀0, hK₀⟩ := hUI.exists_forall_ge hDm hL2
    (show (0 : ℝ) < η * ε ^ 2 / 64 by positivity)
  set K := √K₀ with hKdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set τ := η * ε ^ 2 / 64 with hτ
  have hτb : ∀ j, ∫ ω, bigPart D K j ω ^ 2 ∂Q ≤ τ := fun j =>
    (integral_bigPart_sq_le hDm hL2 hK0 j).trans (hK₀ _ (by rw [hKdef, Real.sq_sqrt hK₀0]) j)
  set A : ℝ := 4 * (2 * K) ^ 4 with hA
  have hA0 : 0 ≤ A := by positivity
  set δ₀ := η * ε ^ 4 / (128 * (A + 1)) with hδ₀
  set δ := min 1 δ₀ with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδA : 128 * A * δ ≤ η * ε ^ 4 := by
    have h1 : 128 * (A + 1) * δ₀ = η * ε ^ 4 := by
      rw [hδ₀]; field_simp
    have h2 : δ ≤ δ₀ := min_le_right _ _
    nlinarith
  refine ⟨δ, hδ0, min_le_left _ _, fun n hn k m hm => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set x := ε * √(n : ℝ) / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx2 : x ^ 2 = ε ^ 2 * n / 4 := by
    rw [hx, div_pow, mul_pow, Real.sq_sqrt hn0.le]; ring
  have hx4 : x ^ 4 = ε ^ 4 * n ^ 2 / 16 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; ring
  have hset : {ω | ε * √(n : ℝ) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |∑ i ∈ Finset.range j, D (k + i) ω|} =
      {ω | 2 * x ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun j => |∑ i ∈ Finset.range j, D (k + i) ω|} := by
    rw [hx]; ring_nf
  rw [hset]
  refine (measureReal_block_max_le hD hL2 h0 hK0 hτb k m hx0).trans ?_
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : 4 * (2 * K) ^ 4 * m ^ 2 / x ^ 4 ≤ η * δ / 2 := by
    rw [div_le_iff₀ (by positivity), hx4, ← hA]
    have hm2 : (m : ℝ) ^ 2 ≤ 4 * δ ^ 2 * n ^ 2 := by nlinarith
    calc A * m ^ 2 ≤ A * (4 * δ ^ 2 * n ^ 2) := mul_le_mul_of_nonneg_left hm2 hA0
      _ = 4 * δ * n ^ 2 * (A * δ) := by ring
      _ ≤ 4 * δ * n ^ 2 * (η * ε ^ 4 / 128) := by
          gcongr; linarith
      _ = η * δ / 2 * (ε ^ 4 * n ^ 2 / 16) := by ring
  have h2 : 4 * m * τ / x ^ 2 ≤ η * δ / 2 := by
    rw [div_le_iff₀ (by positivity), hx2]
    calc 4 * m * τ ≤ 4 * (2 * δ * n) * (η * ε ^ 2 / 64) := by gcongr
      _ = η * δ / 2 * (ε ^ 2 * n / 4) := by ring
  linarith

/-! ### Conditional variances and squares -/

/-- Convergence in `L¹` to `0` implies convergence in probability (Markov's inequality). -/
theorem tendstoInMeasure_zero_of_integral_abs {Q : Measure Ω} [IsFiniteMeasure Q]
    {f : ℕ → Ω → ℝ} (hf : ∀ n, Integrable (f n) Q)
    (h : Tendsto (fun n => ∫ ω, |f n ω| ∂Q) atTop (𝓝 0)) :
    TendstoInMeasure Q f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hb : ∀ n, Q {ω | ε ≤ ‖f n ω - (0 : Ω → ℝ) ω‖} ≤
      ENNReal.ofReal ((∫ ω, |f n ω| ∂Q) / ε) := fun n => by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := Q) (f := fun ω => |f n ω|)
      (Eventually.of_forall fun ω => abs_nonneg _) (hf n).abs ε
    have hset : {ω | ε ≤ ‖f n ω - (0 : Ω → ℝ) ω‖} = {ω | ε ≤ |f n ω|} := by
      ext ω; simp [Real.norm_eq_abs]
    rw [hset, ← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hε, mul_comm]
    exact h1
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ ω, |f n ω| ∂Q) / ε)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (h.div_const ε)
    rwa [zero_div, ENNReal.ofReal_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) hb

/-- **Squares versus conditional variances**: for square-integrable `Dₖ` (`𝓕ₖ₊₁`-measurable)
with uniformly integrable squares, `(1/n) Σ_{k<n} (Dₖ² − E[Dₖ² | 𝓕ₖ]) → 0` in `L¹`. The bounded
part `min(Dₖ², K)` gives martingale differences with `L²`-norm of the average at most `K/√n`; the
rest has `L¹`-norm at most `2 sup_k E[(Dₖ² − K)⁺]`. -/
theorem tendsto_integral_abs_avg_sq_sub_condExp {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (hUI : IsUnifSqIntegrable Q D) :
    Tendsto (fun n : ℕ => ∫ ω, |(∑ k ∈ Finset.range n,
      (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n| ∂Q) atTop (𝓝 0) := by
  have hDF : ∀ k, Measurable[ℱ (k + 1)] (D k) := fun k => (hD k).measurable
  have hDm : ∀ k, Measurable (D k) := fun k => (hDF k).mono (ℱ.le (k + 1)) le_rfl
  have hYi : ∀ k, Integrable (fun ω => D k ω ^ 2) Q := fun k => (hL2 k).integrable_sq
  -- the bound for a fixed truncation level
  have hbound : ∀ (K τ : ℝ), 0 ≤ K → (∀ k, ∫ ω, (D k ω ^ 2 - min (D k ω ^ 2) K) ∂Q ≤ τ) →
      ∀ (η : ℝ), 0 < η → ∀ n : ℕ, 1 ≤ n →
      ∫ ω, |(∑ k ∈ Finset.range n, (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n| ∂Q ≤
        (K ^ 2 / (n * η) + η) / 2 + 2 * τ := by
    intro K τ hK hτK η hη n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set A : ℕ → Ω → ℝ := fun k ω => min (D k ω ^ 2) K with hA
    set B : ℕ → Ω → ℝ := fun k ω => D k ω ^ 2 - min (D k ω ^ 2) K with hB
    have hAF : ∀ k, Measurable[ℱ (k + 1)] (A k) := fun k =>
      ((hDF k).pow_const 2).min measurable_const
    have hAm : ∀ k, Measurable (A k) := fun k => (hAF k).mono (ℱ.le (k + 1)) le_rfl
    have hA0K : ∀ k ω, 0 ≤ A k ω ∧ A k ω ≤ K := fun k ω =>
      ⟨le_min (sq_nonneg _) hK, min_le_right _ _⟩
    have hAi : ∀ k, Integrable (A k) Q := fun k =>
      Integrable.of_bound (hAm k).aestronglyMeasurable K (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA0K k ω).1]; exact (hA0K k ω).2)
    have hBi : ∀ k, Integrable (B k) Q := fun k => (hYi k).sub (hAi k)
    have hB0 : ∀ k ω, 0 ≤ B k ω := fun k ω => sub_nonneg.2 (min_le_left _ _)
    -- the martingale part
    set a : ℕ → Ω → ℝ := fun k ω => A k ω - Q[A k | ℱ k] ω with ha
    have hcA : ∀ k, ∀ᵐ ω ∂Q, 0 ≤ Q[A k | ℱ k] ω ∧ Q[A k | ℱ k] ω ≤ K := fun k => by
      have h1 := condExp_nonneg (m := ℱ k) (μ := Q)
        (Eventually.of_forall fun ω => (hA0K k ω).1 : 0 ≤ᵐ[Q] A k)
      have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ k) (R := K) (f := A k)
        (Eventually.of_forall fun ω => by
          rw [abs_of_nonneg (hA0K k ω).1]; exact (hA0K k ω).2)
      filter_upwards [h1, h2] with ω e1 e2
      exact ⟨by simpa using e1, (le_abs_self _).trans e2⟩
    have haF : ∀ k, StronglyMeasurable[ℱ (k + 1)] (a k) := fun k =>
      ((hAF k).sub ((stronglyMeasurable_condExp (m := ℱ k) (μ := Q) (f := A k)).measurable.mono
        (ℱ.mono (Nat.le_succ k)) le_rfl)).stronglyMeasurable
    have hab : ∀ k, ∀ᵐ ω ∂Q, |a k ω| ≤ K := fun k => by
      filter_upwards [hcA k] with ω e
      simp only [ha]
      rw [abs_le]
      constructor <;> linarith [(hA0K k ω).1, (hA0K k ω).2, e.1, e.2]
    have hamL2 : ∀ k, MemLp (a k) 2 Q := fun k =>
      MemLp.of_bound ((haF k).measurable.mono (ℱ.le (k + 1)) le_rfl).aestronglyMeasurable K
        ((hab k).mono fun ω h => by rwa [Real.norm_eq_abs])
    have ha0 : ∀ k, Q[a k | ℱ k] =ᵐ[Q] 0 := fun k => by
      have h1 : Q[a k | ℱ k] =ᵐ[Q] Q[A k | ℱ k] - Q[Q[A k | ℱ k] | ℱ k] :=
        condExp_sub (hAi k) integrable_condExp _
      have h2 : Q[Q[A k | ℱ k] | ℱ k] = Q[A k | ℱ k] :=
        condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
      filter_upwards [h1] with ω e1
      rw [e1, h2, Pi.sub_apply, sub_self, Pi.zero_apply]
    have hsqa : ∫ ω, (∑ k ∈ Finset.range n, a k ω) ^ 2 ∂Q ≤ n * K ^ 2 := by
      rw [integral_sq_sum_of_martingale haF hamL2 ha0 n]
      calc ∑ k ∈ Finset.range n, ∫ ω, a k ω ^ 2 ∂Q ≤ ∑ _k ∈ Finset.range n, K ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            calc ∫ ω, a k ω ^ 2 ∂Q ≤ ∫ _, K ^ 2 ∂Q := by
                  refine integral_mono_ae (hamL2 k).integrable_sq (integrable_const _) ?_
                  filter_upwards [hab k] with ω hω
                  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
              _ = K ^ 2 := by simp
        _ = n * K ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hSa2 : MemLp (fun ω => ∑ k ∈ Finset.range n, a k ω) 2 Q :=
      memLp_finsetSum _ fun k _ => hamL2 k
    have hpart1 : ∫ ω, |(∑ k ∈ Finset.range n, a k ω) / n| ∂Q ≤ (K ^ 2 / (n * η) + η) / 2 := by
      have hpt : ∀ ω, |(∑ k ∈ Finset.range n, a k ω) / n| ≤
          ((∑ k ∈ Finset.range n, a k ω) ^ 2 / (n ^ 2 * η) + η) / 2 := fun ω => by
        set y := (∑ k ∈ Finset.range n, a k ω) / n with hy
        have e : (∑ k ∈ Finset.range n, a k ω) ^ 2 / (n ^ 2 * η) = y ^ 2 / η := by
          rw [hy, div_pow]; field_simp
        rw [e]
        have h1 : 0 ≤ (|y| - η) ^ 2 := sq_nonneg _
        have h2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), div_add' _ _ _ hη.ne', le_div_iff₀ hη]
        nlinarith
      calc ∫ ω, |(∑ k ∈ Finset.range n, a k ω) / n| ∂Q
          ≤ ∫ ω, ((∑ k ∈ Finset.range n, a k ω) ^ 2 / (n ^ 2 * η) + η) / 2 ∂Q :=
            integral_mono (hSa2.integrable one_le_two |>.div_const _).abs
              (((hSa2.integrable_sq.div_const _).add (integrable_const _)).div_const _) hpt
        _ = ((∫ ω, (∑ k ∈ Finset.range n, a k ω) ^ 2 ∂Q) / (n ^ 2 * η) + η) / 2 := by
            rw [integral_div, integral_add (hSa2.integrable_sq.div_const _) (integrable_const _),
              integral_div, integral_const, probReal_univ, one_smul]
        _ ≤ ((n * K ^ 2) / (n ^ 2 * η) + η) / 2 := by gcongr
        _ = (K ^ 2 / (n * η) + η) / 2 := by field_simp
    -- the tail part
    set b : ℕ → Ω → ℝ := fun k ω => B k ω - Q[B k | ℱ k] ω with hb
    have hbi : ∀ k, Integrable (b k) Q := fun k => (hBi k).sub integrable_condExp
    have hbabs : ∀ k, ∫ ω, |b k ω| ∂Q ≤ 2 * τ := fun k => by
      have h1 := condExp_nonneg (m := ℱ k) (μ := Q)
        (Eventually.of_forall fun ω => hB0 k ω : 0 ≤ᵐ[Q] B k)
      calc ∫ ω, |b k ω| ∂Q ≤ ∫ ω, (B k ω + Q[B k | ℱ k] ω) ∂Q := by
            refine integral_mono_ae (hbi k).abs ((hBi k).add integrable_condExp) ?_
            filter_upwards [h1] with ω e
            simp only [Pi.zero_apply] at e
            simp only [hb]
            rw [abs_le]
            constructor <;> linarith [hB0 k ω, e]
        _ ≤ 2 * τ := by
            rw [integral_add (hBi k) integrable_condExp, integral_condExp (ℱ.le k)]
            linarith [hτK k]
    have hpart2 : ∫ ω, |(∑ k ∈ Finset.range n, b k ω) / n| ∂Q ≤ 2 * τ := by
      have hpt : ∀ ω, |(∑ k ∈ Finset.range n, b k ω) / n| ≤
          (∑ k ∈ Finset.range n, |b k ω|) / n := fun ω => by
        rw [abs_div, abs_of_pos hn0]
        exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn0.le
      calc ∫ ω, |(∑ k ∈ Finset.range n, b k ω) / n| ∂Q
          ≤ ∫ ω, (∑ k ∈ Finset.range n, |b k ω|) / n ∂Q :=
            integral_mono ((integrable_finsetSum _ fun k _ => hbi k).div_const _).abs
              ((integrable_finsetSum _ fun k _ => (hbi k).abs).div_const _) hpt
        _ = (∑ k ∈ Finset.range n, ∫ ω, |b k ω| ∂Q) / n := by
            rw [integral_div, integral_finsetSum _ fun k _ => (hbi k).abs]
        _ ≤ (∑ _k ∈ Finset.range n, 2 * τ) / n :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hbabs k) hn0.le
        _ = 2 * τ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    -- the decomposition
    have hdec : ∀ k, ∀ᵐ ω ∂Q, D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω = a k ω + b k ω :=
      fun k => by
        have hY : (fun ω => D k ω ^ 2) = fun ω => A k ω + B k ω := by
          ext ω; simp only [hA, hB]; ring
        have h1 : Q[fun ω => A k ω + B k ω | ℱ k] =ᵐ[Q] Q[A k | ℱ k] + Q[B k | ℱ k] :=
          condExp_add (hAi k) (hBi k) _
        rw [hY]
        filter_upwards [h1] with ω e
        rw [e, Pi.add_apply]
        simp only [ha, hb]
        ring
    have hdec' : ∀ᵐ ω ∂Q, (∑ k ∈ Finset.range n, (D k ω ^ 2 -
        Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n =
        (∑ k ∈ Finset.range n, a k ω) / n + (∑ k ∈ Finset.range n, b k ω) / n := by
      filter_upwards [ae_all_iff.2 hdec] with ω hω
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun k _ => hω k
    calc ∫ ω, |(∑ k ∈ Finset.range n, (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n| ∂Q
        = ∫ ω, |(∑ k ∈ Finset.range n, a k ω) / n + (∑ k ∈ Finset.range n, b k ω) / n| ∂Q :=
          integral_congr_ae (hdec'.mono fun ω h => by simp only; rw [h])
      _ ≤ ∫ ω, (|(∑ k ∈ Finset.range n, a k ω) / n| + |(∑ k ∈ Finset.range n, b k ω) / n|) ∂Q :=
          integral_mono (((hSa2.integrable one_le_two).div_const _).add
            ((integrable_finsetSum _ fun k _ => hbi k).div_const _)).abs
            (((hSa2.integrable one_le_two).div_const _).abs.add
              ((integrable_finsetSum _ fun k _ => hbi k).div_const _).abs)
            fun ω => abs_add_le _ _
      _ = ∫ ω, |(∑ k ∈ Finset.range n, a k ω) / n| ∂Q +
          ∫ ω, |(∑ k ∈ Finset.range n, b k ω) / n| ∂Q :=
          integral_add ((hSa2.integrable one_le_two).div_const _).abs
            ((integrable_finsetSum _ fun k _ => hbi k).div_const _).abs
      _ ≤ (K ^ 2 / (n * η) + η) / 2 + 2 * τ := add_le_add hpart1 hpart2
  -- the limit
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨K, hK0, hK⟩ := hUI.exists_forall_ge hDm hL2 (show (0 : ℝ) < δ / 8 by positivity)
  have hτK : ∀ k, ∫ ω, (D k ω ^ 2 - min (D k ω ^ 2) K) ∂Q ≤ δ / 8 := fun k =>
    (integral_mono (((hL2 k).integrable_sq).sub ((hL2 k).integrable_sq.inf (integrable_const K)
      |>.congr (Eventually.of_forall fun ω => rfl)))
      ((hL2 k).integrable_sq.indicator (measurableSet_le measurable_const ((hDm k).pow_const 2)))
      (sq_sub_min_le_indicator D hK0 k)).trans (hK K le_rfl k)
  obtain ⟨N, hN⟩ := exists_nat_gt (K ^ 2 / (δ / 4 * (δ / 4)))
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hb := hbound K (δ / 8) hK0 hτK (δ / 4) (by positivity) n hn1
  have h0 : 0 ≤ ∫ ω, |(∑ k ∈ Finset.range n,
      (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n| ∂Q :=
    integral_nonneg fun ω => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have hK2 : K ^ 2 / (n * (δ / 4)) < δ / 4 := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith
  linarith

end MeynTweedie.LimitTheorems
