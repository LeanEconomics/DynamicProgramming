/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.KolmogorovAnscombe
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.IdentDistribIndep

/-!
# Exponential inequalities and block independence for the LIL

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/LILExponential.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Probabilistic tools for the upper half of the Hartman–Wintner LIL (`LILUpper`) and the blocking
arguments of the lower half (`LILLower`) and of MT (17.36), p. 442.

* `exp_le_one_add_add_sq`: `eˣ ≤ 1 + x + x²(1 + |x|)/2` for `|x| ≤ 1`.
* `integral_exp_le_of_abs_le`: Kolmogorov's upper exponential bound
  `E[e^{λY}] ≤ exp(λ² E[Y²](1 + λc)/2)` for `|Y| ≤ c`, `E[Y] = 0`, `0 ≤ λ`, `λc ≤ 1`;
  `integral_exp_sum_le`: the same for sums of independent variables.
* **The exponential maximal inequality** (`exp_maximal_ineq`):
  `e^{λt} P(max_{k ≤ N} Sₖ ≥ t) ≤ E[e^{λ S_N}]` for independent centred bounded summands (the
  first-passage argument of Kolmogorov's inequality, MT Theorem D.6.3, applied to `e^{λSₖ}`).
* `iIndep_iSup_blocks`: independent σ-algebras grouped along pairwise disjoint index sets are
  independent.
* `identDistrib_shift`, `identDistrib_shift_sum`: shifts of an i.i.d. sequence, and their partial
  sums, have the law of the sequence.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### An exponential bound -/

/-- `eˣ ≤ 1 + x + x²(1 + |x|)/2` for `|x| ≤ 1`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 * (1 + |x|) / 2 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  rw [e] at h
  have h2 : |x| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ) =
      |x| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [h2] at h
  have h3 : |x| ^ 3 = x ^ 2 * |x| := by
    rw [pow_succ, ← sq_abs x]
  have h4 := (abs_le.1 h).2
  have h5 : 0 ≤ x ^ 2 * |x| := by positivity
  nlinarith

/-- **The moment generating function of a bounded centred variable**: if `|Y| ≤ c`,
`E[Y] = 0`, `λ ≥ 0` and `λc ≤ 1`, then `E[e^{λY}] ≤ exp(λ² E[Y²] (1 + λc)/2)`. -/
theorem integral_exp_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : Ω → ℝ} (hm : Measurable Y) {c l : ℝ}
    (hb : ∀ ω, |Y ω| ≤ c) (h0 : ∫ ω, Y ω ∂Q = 0) (hl : 0 ≤ l) (hlc : l * c ≤ 1) :
    ∫ ω, Real.exp (l * Y ω) ∂Q ≤
      Real.exp (l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2) := by
  have hYi : Integrable Y Q :=
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb ω)
  have hY2i : Integrable (fun ω => Y ω ^ 2) Q :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (c ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2)
  have hpt : ∀ ω, Real.exp (l * Y ω) ≤
      1 + l * Y ω + (l ^ 2 * (1 + l * c) / 2) * Y ω ^ 2 := fun ω => by
    have habs : |l * Y ω| ≤ l * c := by
      rw [abs_mul, abs_of_nonneg hl]; exact mul_le_mul_of_nonneg_left (hb ω) hl
    have h1 := exp_le_one_add_add_sq (habs.trans hlc)
    have h2 : (l * Y ω) ^ 2 * (1 + |l * Y ω|) / 2 ≤ (l * Y ω) ^ 2 * (1 + l * c) / 2 := by
      have := sq_nonneg (l * Y ω)
      nlinarith
    nlinarith
  have hrhs : Integrable (fun ω => 1 + l * Y ω + (l ^ 2 * (1 + l * c) / 2) * Y ω ^ 2) Q :=
    ((integrable_const 1).add (hYi.const_mul l)).add (hY2i.const_mul _)
  have hexpi : Integrable (fun ω => Real.exp (l * Y ω)) Q := by
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp
      (hm.const_mul l)).aestronglyMeasurable (Real.exp (l * c))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have := (abs_le.1 (hb ω)).2
    exact mul_le_mul_of_nonneg_left this hl
  have h1 := integral_mono hexpi hrhs hpt
  set K := l ^ 2 * (1 + l * c) / 2 with hK
  have hA : Integrable (fun ω => 1 + l * Y ω) Q := (integrable_const 1).add (hYi.const_mul l)
  have hB : Integrable (fun ω => K * Y ω ^ 2) Q := hY2i.const_mul K
  have hI : ∫ ω, (1 + l * Y ω + K * Y ω ^ 2) ∂Q = 1 + K * ∫ ω, Y ω ^ 2 ∂Q := by
    rw [integral_add hA hB, integral_add (integrable_const 1) (hYi.const_mul l),
      integral_const_mul, integral_const_mul, h0]
    simp
  rw [hI] at h1
  refine h1.trans ?_
  have := Real.add_one_le_exp (l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2)
  have e : K * ∫ ω, Y ω ^ 2 ∂Q = l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2 := by
    rw [hK]; ring
  linarith

/-! ### The exponential maximal inequality -/

/-- A sum of variables with `|Yⱼ| ≤ cⱼ` is bounded by `Σ cⱼ`. -/
theorem abs_sum_le_of_abs_le {Ω : Type*} {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hb : ∀ j ω, |Y j ω| ≤ c j) (s : Finset ℕ) (ω : Ω) :
    |∑ j ∈ s, Y j ω| ≤ ∑ j ∈ s, c j :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb j ω)

/-- **The exponential maximal inequality**: for independent centred bounded `Yⱼ`, `λ ≥ 0` and
any `t`, `e^{λt} P(max_{k ≤ N} Σ_{j<k} Yⱼ ≥ t) ≤ E[exp(λ Σ_{j<N} Yⱼ)]` (Doob's inequality for
the submartingale `exp(λ Sₖ)`, proved through the first-passage decomposition). -/
theorem exp_maximal_ineq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j)) {c : ℕ → ℝ}
    (hb : ∀ j ω, |Y j ω| ≤ c j) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) {l t : ℝ}
    (hl : 0 ≤ l) :
    Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
      ∫ ω, Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) ∂Q := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, Y j ω with hS
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  -- bounded variables are integrable
  have hbd : ∀ (s : Finset ℕ), Integrable (fun ω => Real.exp (l * ∑ j ∈ s, Y j ω)) Q := by
    intro s
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp
      ((Finset.measurable_sum _ fun j _ => hm j).const_mul l)).aestronglyMeasurable
      (Real.exp (l * ∑ j ∈ s, c j)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left ((abs_le.1 (abs_sum_le_of_abs_le hb s ω)).2) hl
  have hYi : ∀ j, Integrable (Y j) Q := fun j =>
    Integrable.of_bound (hm j).aestronglyMeasurable (c j) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb j ω)
  -- the first-passage events
  set A : ℕ → Set Ω := fun k => {ω | t ≤ S k ω} ∩ ⋂ i ∈ Finset.range k, {ω | S i ω < t}
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const (hSm k)).inter
      (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt (hSm i) measurable_const)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) A := by
    intro k _ l' _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · have h3 : S k ω < t := mem_iInter₂.1 h2.2 k (Finset.mem_range.2 h)
      have h4 : t ≤ S k ω := h1.1
      linarith
    · have h3 : S l' ω < t := mem_iInter₂.1 h1.2 l' (Finset.mem_range.2 h)
      have h4 : t ≤ S l' ω := h2.1
      linarith
  have hE : {ω | ∃ k ≤ N, t ≤ S k ω} = ⋃ k ∈ Finset.range (N + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk, hkt⟩
      have hex : ∃ k, t ≤ S k ω := ⟨k, hkt⟩
      refine ⟨Nat.find hex, by have := Nat.find_min' hex hkt; omega, Nat.find_spec hex, ?_⟩
      refine mem_iInter₂.2 fun i hi => ?_
      have := Nat.find_min hex (Finset.mem_range.1 hi)
      exact not_le.1 this
    · rintro ⟨k, hk, h1, -⟩
      exact ⟨k, by omega, h1⟩
  -- on `A k`, `E[e^{λ S_N} ; A k] ≥ E[e^{λ S_k} ; A k] ≥ e^{λ t} P(A k)`
  have hkey : ∀ k ≤ N, Real.exp (l * t) * Q.real (A k) ≤
      ∫ ω in A k, Real.exp (l * S N ω) ∂Q := by
    intro k hk
    set R : Ω → ℝ := fun ω => ∑ j ∈ Finset.Ico k N, Y j ω with hR
    have hSN : ∀ ω, S N ω = S k ω + R ω := fun ω => by
      simp only [hS, hR]
      rw [Finset.sum_range_add_sum_Ico _ hk]
    set U : Ω → ℝ := (A k).indicator (fun ω => Real.exp (l * S k ω)) with hU
    set V : Ω → ℝ := fun ω => Real.exp (l * R ω) with hV
    have hUi : Integrable U Q := (hbd (Finset.range k)).indicator (hAm k)
    have hVi : Integrable V Q := hbd (Finset.Ico k N)
    have hind' : IndepFun U V Q := by
      have hW := hind.indepFun_finset (Finset.range k) (Finset.Ico k N)
        (by rw [Finset.disjoint_left]; intro j hj1 hj2
            simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega) hm
      set F : (Finset.range k → ℝ) → ℝ := fun v =>
        ({v | t ≤ ∑ j : Finset.range k, v j} ∩ ⋂ i ∈ Finset.range k,
          {v | ∑ j : Finset.range k, (if (j : ℕ) < i then v j else 0) < t}).indicator
          (fun v => Real.exp (l * ∑ j : Finset.range k, v j)) v with hF
      have hFm : Measurable F := by
        refine Measurable.indicator (Real.continuous_exp.measurable.comp
          ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).const_mul l))
          ((measurableSet_le measurable_const
            (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)).inter
          (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt
            (Finset.measurable_sum _ fun j _ => by
              by_cases hj : (j : ℕ) < i
              · simp only [hj, ite_true]; exact measurable_pi_apply j
              · simp only [hj, ite_false]; exact measurable_const) measurable_const))
      have hGm : Measurable fun w : Finset.Ico k N → ℝ =>
          Real.exp (l * ∑ j : Finset.Ico k N, w j) :=
        Real.continuous_exp.measurable.comp
          ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).const_mul l)
      have hc := hW.comp hFm hGm
      convert hc using 1
      · ext ω
        simp only [hU, hF, Function.comp_apply]
        have hsk : ∑ j : Finset.range k, Y j ω = S k ω := by
          rw [Finset.sum_coe_sort (Finset.range k) (fun j => Y j ω)]
        have hsi : ∀ i ∈ Finset.range k,
            ∑ j : Finset.range k, (if (j : ℕ) < i then Y j ω else 0) = S i ω := fun i hi =>
          sum_coe_sort_ite_lt Y (Finset.mem_range.1 hi).le ω
        by_cases hω : ω ∈ A k
        · rw [indicator_of_mem hω, indicator_of_mem]
          · rw [hsk]
          · refine ⟨by simp only [mem_ofPred_eq, hsk]; exact hω.1, mem_iInter₂.2 fun i hi => ?_⟩
            simp only [mem_ofPred_eq, hsi i hi]
            exact mem_iInter₂.1 hω.2 i hi
        · rw [indicator_of_notMem hω, indicator_of_notMem]
          rintro ⟨h1, h2⟩
          refine hω ⟨by simp only [mem_ofPred_eq, ← hsk]; exact h1, mem_iInter₂.2 fun i hi => ?_⟩
          have := mem_iInter₂.1 h2 i hi
          simp only [mem_ofPred_eq, hsi i hi] at this
          exact this
      · ext ω
        simp only [hV, hR, Function.comp_apply]
        rw [Finset.sum_coe_sort (Finset.Ico k N) (fun j => Y j ω)]
    -- `E[e^{λR}] ≥ 1`
    have hV1 : 1 ≤ ∫ ω, V ω ∂Q := by
      have hRi : Integrable R Q := integrable_finsetSum _ fun j _ => hYi j
      have hR0 : ∫ ω, R ω ∂Q = 0 := by
        rw [hR, integral_finsetSum _ fun j _ => hYi j]
        exact Finset.sum_eq_zero fun j _ => h0 j
      have h1 : ∫ ω, (1 + l * R ω) ∂Q ≤ ∫ ω, V ω ∂Q :=
        integral_mono ((integrable_const 1).add (hRi.const_mul l)) hVi fun ω => by
          have := Real.add_one_le_exp (l * R ω)
          simp only [hV]; linarith
      rw [integral_add (integrable_const 1) (hRi.const_mul l), integral_const_mul, hR0] at h1
      simpa using h1
    have hU0 : 0 ≤ ∫ ω, U ω ∂Q :=
      integral_nonneg fun ω => indicator_nonneg (fun ω _ => (Real.exp_pos _).le) ω
    have hlow : Real.exp (l * t) * Q.real (A k) ≤ ∫ ω, U ω ∂Q := by
      rw [hU, integral_indicator (hAm k)]
      have hc : ∫ _ω in A k, Real.exp (l * t) ∂Q = Real.exp (l * t) * Q.real (A k) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [← hc]
      refine setIntegral_mono_on (integrable_const _).integrableOn
        (hbd (Finset.range k)).integrableOn (hAm k) fun ω hω => ?_
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω.1 hl)
    have hprod : ∫ ω in A k, Real.exp (l * S N ω) ∂Q = (∫ ω, U ω ∂Q) * ∫ ω, V ω ∂Q := by
      rw [← hind'.integral_fun_mul_eq_mul_integral hUi.aestronglyMeasurable
        hVi.aestronglyMeasurable, ← integral_indicator (hAm k)]
      congr 1
      ext ω
      by_cases hω : ω ∈ A k
      · simp only [indicator_of_mem hω, hU, hV, hSN, mul_add, Real.exp_add]
      · simp only [indicator_of_notMem hω, hU, zero_mul]
    rw [hprod]
    nlinarith
  -- sum over `k`
  calc Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ ∑ j ∈ Finset.range k, Y j ω}
      = Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ S k ω} := rfl
    _ = ∑ k ∈ Finset.range (N + 1), Real.exp (l * t) * Q.real (A k) := by
        rw [hE, measureReal_biUnion_finset hdisj fun k _ => hAm k, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (N + 1), ∫ ω in A k, Real.exp (l * S N ω) ∂Q :=
        Finset.sum_le_sum fun k hk => hkey k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = ∫ ω in ⋃ k ∈ Finset.range (N + 1), A k, Real.exp (l * S N ω) ∂Q :=
        (integral_biUnion_finset _ (fun k _ => hAm k) hdisj
          fun k _ => (hbd (Finset.range N)).integrableOn).symm
    _ ≤ ∫ ω, Real.exp (l * S N ω) ∂Q :=
        setIntegral_le_integral (hbd (Finset.range N))
          (Eventually.of_forall fun ω => (Real.exp_pos _).le)

/-- The moment generating function of a sum of independent centred bounded variables:
if `|Yⱼ| ≤ C` and `E[Yⱼ²] ≤ s²` for `j < N`, `λ ≥ 0` and `λC ≤ 1`, then
`E[exp(λ Σ_{j<N} Yⱼ)] ≤ exp(N λ² s² (1 + λC)/2)`. -/
theorem integral_exp_sum_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    {c : ℕ → ℝ} (hb : ∀ j ω, |Y j ω| ≤ c j) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ)
    {l C s2 : ℝ} (hl : 0 ≤ l) (hcC : ∀ j < N, c j ≤ C) (hlC : l * C ≤ 1)
    (hs2 : ∀ j < N, ∫ ω, Y j ω ^ 2 ∂Q ≤ s2) :
    ∫ ω, Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) ∂Q ≤
      Real.exp (N * (l ^ 2 * s2 * (1 + l * C) / 2)) := by
  have h := hind.mgf_sum hm (Finset.range N) (t := l)
  unfold mgf at h
  have e : (fun ω => Real.exp (l * (∑ i ∈ Finset.range N, Y i) ω)) =
      fun ω => Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) := by
    ext ω; rw [Finset.sum_apply]
  rw [e] at h
  rw [h]
  obtain ⟨ω₀, -⟩ := nonempty_of_measure_ne_zero (μ := Q) (s := univ)
    (by rw [measure_univ]; exact one_ne_zero)
  have hC0 : ∀ j < N, 0 ≤ c j := fun j _ => (abs_nonneg _).trans (hb j ω₀)
  calc ∏ j ∈ Finset.range N, ∫ ω, Real.exp (l * Y j ω) ∂Q
      ≤ ∏ _j ∈ Finset.range N, Real.exp (l ^ 2 * s2 * (1 + l * C) / 2) := by
        refine Finset.prod_le_prod₀ (fun j _ => integral_nonneg fun ω => (Real.exp_pos _).le)
          fun j hj => ?_
        have hjN := Finset.mem_range.1 hj
        have hlc : l * c j ≤ 1 := (mul_le_mul_of_nonneg_left (hcC j hjN) hl).trans hlC
        refine (integral_exp_le_of_abs_le (hm j) (hb j) (h0 j) hl hlc).trans ?_
        apply Real.exp_le_exp.2
        have h1 : 1 + l * c j ≤ 1 + l * C := by
          have := mul_le_mul_of_nonneg_left (hcC j hjN) hl; linarith
        have h2 : 0 ≤ ∫ ω, Y j ω ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
        have h3 : 0 ≤ 1 + l * c j := by have := mul_nonneg hl (hC0 j hjN); linarith
        have h4 := hs2 j hjN
        have h5 : 0 ≤ l ^ 2 := sq_nonneg l
        have h6 : (∫ ω, Y j ω ^ 2 ∂Q) * (1 + l * c j) ≤ s2 * (1 + l * C) :=
          mul_le_mul h4 h1 h3 (h2.trans h4)
        have := mul_le_mul_of_nonneg_left h6 h5
        nlinarith
    _ = Real.exp (N * (l ^ 2 * s2 * (1 + l * C) / 2)) := by
        rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]

/-! ### Independence of blocks and shifts of i.i.d. sequences -/

/-- Independent σ-algebras grouped along pairwise disjoint index sets give independent
σ-algebras: `(⨆_{i ∈ I k} mᵢ)ₖ` is independent when `(mᵢ)` is and the `I k` are disjoint. -/
theorem iIndep_iSup_blocks {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    {m : ι → MeasurableSpace Ω} (h_le : ∀ i, m i ≤ mΩ) (hind : iIndep m Q) {I : κ → Set ι}
    (hI : Pairwise (Function.onFun Disjoint I)) :
    iIndep (fun k => ⨆ i ∈ I k, m i) Q := by
  classical
  have := hind.isProbabilityMeasure
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | insert a s has ih =>
    intro f hf
    rw [Finset.set_biInter_insert, Finset.prod_insert has]
    have hT : Disjoint (I a) (⋃ k ∈ s, I k) := by
      rw [Set.disjoint_iUnion₂_right]
      intro k hk
      exact hI (fun h => has (h ▸ hk))
    have hindT := indep_iSup_of_disjoint h_le hind hT
    have hle : ∀ k ∈ s, (⨆ i ∈ I k, m i) ≤ ⨆ i ∈ ⋃ k ∈ s, I k, m i := fun k hk =>
      iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ ⋃ k ∈ s, I k) => m i) i
        (mem_iUnion₂.2 ⟨k, hk, hi⟩)
    have hmeas : MeasurableSet[⨆ i ∈ ⋃ k ∈ s, I k, m i] (⋂ k ∈ s, f k) :=
      Finset.measurableSet_biInter (m := ⨆ i ∈ ⋃ k ∈ s, I k, m i) s fun k hk =>
        hle k hk _ (hf k (Finset.mem_insert_of_mem hk))
    rw [(Indep_iff _ _ Q).1 hindT _ _ (hf a (Finset.mem_insert_self a s)) hmeas,
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

/-- For i.i.d. `Xⱼ`, the shifted sequence `(X_{c+j})ⱼ` has the law of `(Xⱼ)ⱼ`. -/
theorem identDistrib_shift {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (c : ℕ) :
    IdentDistrib (fun ω j => X (c + j) ω) (fun ω j => X j ω) Q Q :=
  IdentDistrib.pi (fun j => (hident (c + j)).trans (hident j).symm)
    (hind.precomp (add_right_injective c)) hind

/-- For i.i.d. `Xⱼ`, the shifted partial sums `Σ_{j<ℓ} X_{c+j}` have the law of `Σ_{j<ℓ} Xⱼ`. -/
theorem identDistrib_shift_sum {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (c ℓ : ℕ) :
    IdentDistrib (fun ω => ∑ j ∈ Finset.range ℓ, X (c + j) ω)
      (fun ω => ∑ j ∈ Finset.range ℓ, X j ω) Q Q :=
  (identDistrib_shift hind hident c).comp
    (u := fun v : ℕ → ℝ => ∑ j ∈ Finset.range ℓ, v j)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)

end MeynTweedie.GeneralizedDrift
