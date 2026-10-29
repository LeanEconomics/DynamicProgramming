/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.IdentDistrib

/-!
# Kolmogorov's inequality and a random-index CLT step (MT Theorem D.6.3, §17.2.2)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/KolmogorovAnscombe.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

The proof of Theorem 17.2.2 (p. 431) replaces the random number `ℓₙ` of completed cycles by the
deterministic `n* = ⌊π(α) n⌋` using Kolmogorov's inequality (Theorem D.6.3). Mathlib has Doob's
maximal inequality but not Kolmogorov's in this form, so both are proved here for independent
real random variables on a probability space.

* `integral_sq_sum_range`: for independent centred `Yⱼ ∈ L²`, `E[(Σ_{j<N} Yⱼ)²] = Σ_{j<N} E[Yⱼ²]`.
* **Kolmogorov's inequality** (`kolmogorov_ineq`, MT Theorem D.6.3):
  `t² P(max_{k ≤ N} |Sₖ| ≥ t) ≤ Σ_{j<N} E[Yⱼ²]`.
* `kolmogorov_ineq_shift`: the same for the sums `Σ_{j<k} Y_{a+j}` started at `a`.
* **The random-index step** (`tendstoInMeasure_anscombe`, the argument (17.19)–(17.20)): for
  i.i.d. centred `Yⱼ ∈ L²` and random indices `Kₙ` with `Kₙ/n → c > 0` almost surely,
  `(S_{Kₙ} − S_{⌊cn⌋})/√n → 0` in probability.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Orthogonality of sums -/

/-- For independent centred `Yⱼ ∈ L²`, `E[(Σ_{j<N} Yⱼ)²] = Σ_{j<N} E[Yⱼ²]`. -/
theorem integral_sq_sum_range {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range N, Y j ω) ^ 2 ∂Q = ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hS2 : MemLp (fun ω => ∑ j ∈ Finset.range N, Y j ω) 2 Q :=
      memLp_finsetSum _ fun j _ => hL2 j
    have hind' : IndepFun (fun ω => ∑ j ∈ Finset.range N, Y j ω) (Y N) Q := by
      have := hind.indepFun_sum_range_succ hm N
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    have hcross : ∫ ω, (∑ j ∈ Finset.range N, Y j ω) * Y N ω ∂Q = 0 := by
      rw [hind'.integral_fun_mul_eq_mul_integral hS2.aestronglyMeasurable
        (hL2 N).aestronglyMeasurable, h0 N, mul_zero]
    have hexp : (fun ω => (∑ j ∈ Finset.range (N + 1), Y j ω) ^ 2) = fun ω =>
        (∑ j ∈ Finset.range N, Y j ω) ^ 2 + 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω) +
          Y N ω ^ 2 := by
      ext ω; rw [Finset.sum_range_succ]; ring
    have hi1 : Integrable (fun ω => (∑ j ∈ Finset.range N, Y j ω) ^ 2) Q := hS2.integrable_sq
    have hi2 : Integrable (fun ω => 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω)) Q :=
      (hS2.integrable_mul (hL2 N)).const_mul 2
    have hi3 : Integrable (fun ω => Y N ω ^ 2) Q := (hL2 N).integrable_sq
    have e1 := integral_add (hi1.add hi2) hi3
    have e2 := integral_add hi1 hi2
    have e3 : ∫ ω, 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω) ∂Q = 0 := by
      rw [integral_const_mul, hcross, mul_zero]
    simp only [Pi.add_apply] at e1 e2
    rw [hexp, e1, e2, e3, ih, Finset.sum_range_succ]
    ring

/-! ### Kolmogorov's inequality -/

/-- The partial sum over `range i` of a vector indexed by `range k`, for `i ≤ k`. -/
theorem sum_coe_sort_ite_lt {Ω : Type*} (Y : ℕ → Ω → ℝ) {i k : ℕ} (hik : i ≤ k) (ω : Ω) :
    ∑ j : Finset.range k, (if (j : ℕ) < i then Y j ω else 0) = ∑ j ∈ Finset.range i, Y j ω := by
  rw [Finset.sum_coe_sort (Finset.range k) (fun j => if j < i then Y j ω else 0),
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Kolmogorov's inequality** (MT Theorem D.6.3): for independent centred `Yⱼ ∈ L²` and
`t > 0`, `t² P(max_{k ≤ N} |Σ_{j<k} Yⱼ| ≥ t) ≤ Σ_{j<N} E[Yⱼ²]`. -/
theorem kolmogorov_ineq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y j ω|} ≤
      ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, Y j ω with hS
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  have hS2 : ∀ k, MemLp (S k) 2 Q := fun k => memLp_finsetSum _ fun j _ => hL2 j
  -- the first-passage events
  set A : ℕ → Set Ω := fun k => {ω | t ≤ |S k ω|} ∩ ⋂ i ∈ Finset.range k, {ω | |S i ω| < t}
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const (continuous_abs.measurable.comp (hSm k))).inter
      (Finset.measurableSet_biInter _ fun i _ =>
        measurableSet_lt (continuous_abs.measurable.comp (hSm i)) measurable_const)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) A := by
    intro k _ l _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · have h3 : |S k ω| < t := mem_iInter₂.1 h2.2 k (Finset.mem_range.2 h)
      have h4 : t ≤ |S k ω| := h1.1
      linarith
    · have h3 : |S l ω| < t := mem_iInter₂.1 h1.2 l (Finset.mem_range.2 h)
      have h4 : t ≤ |S l ω| := h2.1
      linarith
  have hE : {ω | ∃ k ≤ N, t ≤ |S k ω|} = ⋃ k ∈ Finset.range (N + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk, hkt⟩
      have hex : ∃ k, t ≤ |S k ω| := ⟨k, hkt⟩
      refine ⟨Nat.find hex, by have := Nat.find_min' hex hkt; omega, Nat.find_spec hex, ?_⟩
      refine mem_iInter₂.2 fun i hi => ?_
      have := Nat.find_min hex (Finset.mem_range.1 hi)
      exact not_le.1 this
    · rintro ⟨k, hk, h1, -⟩
      exact ⟨k, by omega, h1⟩
  -- on `A k`, `E[S_N² ; A k] ≥ E[S_k² ; A k] ≥ t² P(A k)`
  have hkey : ∀ k ≤ N, t ^ 2 * Q.real (A k) ≤ ∫ ω in A k, S N ω ^ 2 ∂Q := by
    intro k hk
    have hlow : t ^ 2 * Q.real (A k) ≤ ∫ ω in A k, S k ω ^ 2 ∂Q := by
      have hc : ∫ _ω in A k, t ^ 2 ∂Q = t ^ 2 * Q.real (A k) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [← hc]
      refine setIntegral_mono_on (integrable_const _).integrableOn
        (hS2 k).integrable_sq.integrableOn
        (hAm k) fun ω hω => ?_
      have h1 : t ≤ |S k ω| := hω.1
      have : t ^ 2 ≤ |S k ω| ^ 2 := pow_le_pow_left₀ ht.le h1 2
      rwa [sq_abs] at this
    -- the remainder `R = S_N − S_k` is independent of `1_{A k} S_k`
    set R : Ω → ℝ := fun ω => ∑ j ∈ Finset.Ico k N, Y j ω with hR
    have hR2 : MemLp R 2 Q := memLp_finsetSum _ fun j _ => hL2 j
    have hR0 : ∫ ω, R ω ∂Q = 0 := by
      rw [hR, integral_finsetSum _ fun j _ => (hL2 j).integrable one_le_two]
      exact Finset.sum_eq_zero fun j _ => h0 j
    have hSN : ∀ ω, S N ω = S k ω + R ω := fun ω => by
      simp only [hS, hR]
      rw [Finset.sum_range_add_sum_Ico _ hk]
    set U : Ω → ℝ := (A k).indicator (S k) with hU
    have hU2 : MemLp U 2 Q := (hS2 k).indicator (hAm k)
    have hind' : IndepFun U R Q := by
      have hV := hind.indepFun_finset (Finset.range k) (Finset.Ico k N)
        (by rw [Finset.disjoint_left]; intro j hj1 hj2
            simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega) hm
      set F : (Finset.range k → ℝ) → ℝ := fun v =>
        ({v | t ≤ |∑ j : Finset.range k, v j|} ∩ ⋂ i ∈ Finset.range k,
          {v | |∑ j : Finset.range k, (if (j : ℕ) < i then v j else 0)| < t}).indicator
          (fun v => ∑ j : Finset.range k, v j) v with hF
      have hFm : Measurable F := by
        refine Measurable.indicator (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
          ((measurableSet_le measurable_const (continuous_abs.measurable.comp
            (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))).inter
          (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt
            (continuous_abs.measurable.comp
            (Finset.measurable_sum _ fun j _ => by
              by_cases hj : (j : ℕ) < i
              · simp only [hj, ite_true]; exact measurable_pi_apply j
              · simp only [hj, ite_false]; exact measurable_const)) measurable_const))
      have hGm : Measurable fun w : Finset.Ico k N → ℝ => ∑ j : Finset.Ico k N, w j :=
        Finset.measurable_sum _ fun j _ => measurable_pi_apply j
      have hc := hV.comp hFm hGm
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
          · exact hsk.symm
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
        simp only [hR, Function.comp_apply]
        rw [Finset.sum_coe_sort (Finset.Ico k N) (fun j => Y j ω)]
    have hcross : ∫ ω, U ω * R ω ∂Q = 0 := by
      rw [hind'.integral_fun_mul_eq_mul_integral hU2.aestronglyMeasurable
        hR2.aestronglyMeasurable, hR0, mul_zero]
    have hup : ∫ ω in A k, S k ω ^ 2 ∂Q ≤ ∫ ω in A k, S N ω ^ 2 ∂Q := by
      rw [← integral_indicator (hAm k), ← integral_indicator (hAm k)]
      have hdec : (A k).indicator (fun ω => S N ω ^ 2) = fun ω =>
          (A k).indicator (fun ω => S k ω ^ 2) ω + 2 * (U ω * R ω) +
            (A k).indicator (fun ω => R ω ^ 2) ω := by
        ext ω
        by_cases hω : ω ∈ A k
        · simp only [indicator_of_mem hω, hU, hSN]; ring
        · simp only [indicator_of_notMem hω, hU]; ring
      have hi1 : Integrable ((A k).indicator fun ω => S k ω ^ 2) Q :=
        (hS2 k).integrable_sq.indicator (hAm k)
      have hi2 : Integrable (fun ω => 2 * (U ω * R ω)) Q :=
        (hU2.integrable_mul hR2).const_mul 2
      have hi3 : Integrable ((A k).indicator fun ω => R ω ^ 2) Q :=
        hR2.integrable_sq.indicator (hAm k)
      have e1 := integral_add (hi1.add hi2) hi3
      have e2 := integral_add hi1 hi2
      have e3 : ∫ ω, 2 * (U ω * R ω) ∂Q = 0 := by rw [integral_const_mul, hcross, mul_zero]
      simp only [Pi.add_apply] at e1 e2
      rw [hdec, e1, e2, e3]
      have : 0 ≤ ∫ ω, (A k).indicator (fun ω => R ω ^ 2) ω ∂Q :=
        integral_nonneg fun ω => indicator_nonneg (fun ω _ => sq_nonneg _) ω
      linarith
    exact hlow.trans hup
  -- sum over `k`
  have hsum : t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |S k ω|} ≤ ∫ ω, S N ω ^ 2 ∂Q := by
    rw [hE, measureReal_biUnion_finset hdisj fun k _ => hAm k, Finset.mul_sum]
    calc ∑ k ∈ Finset.range (N + 1), t ^ 2 * Q.real (A k)
        ≤ ∑ k ∈ Finset.range (N + 1), ∫ ω in A k, S N ω ^ 2 ∂Q :=
          Finset.sum_le_sum fun k hk => hkey k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
      _ = ∫ ω in ⋃ k ∈ Finset.range (N + 1), A k, S N ω ^ 2 ∂Q :=
          (integral_biUnion_finset _ (fun k _ => hAm k) hdisj
            fun k _ => (hS2 N).integrable_sq.integrableOn).symm
      _ ≤ ∫ ω, S N ω ^ 2 ∂Q :=
          setIntegral_le_integral (hS2 N).integrable_sq
            (Eventually.of_forall fun ω => sq_nonneg _)
  calc t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y j ω|}
      = t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |S k ω|} := rfl
    _ ≤ ∫ ω, S N ω ^ 2 ∂Q := hsum
    _ = ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := integral_sq_sum_range hind hm hL2 h0 N

/-- Kolmogorov's inequality for the sums `Σ_{j<k} Y_{a+j}` started at index `a`. -/
theorem kolmogorov_ineq_shift {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (a N : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y (a + j) ω|} ≤
      ∑ j ∈ Finset.range N, ∫ ω, Y (a + j) ω ^ 2 ∂Q :=
  kolmogorov_ineq (Y := fun j => Y (a + j))
    (hind.precomp (g := fun j => a + j) fun i j h => by simpa using h)
    (fun j => hm _) (fun j => hL2 _) (fun j => h0 _) N ht

/-! ### The random-index step -/

/-- Two indices within `W` of each other lie in the window `[N − W, N − W + 2W]`, and the
difference of the partial sums up to them is a difference of sums inside the window. -/
theorem sum_range_sub_eq_window (y : ℕ → ℝ) {K N W : ℕ} (h1 : K ≤ N + W) (h2 : N ≤ K + W) :
    N - W ≤ K ∧ K - (N - W) ≤ 2 * W ∧ N - (N - W) ≤ 2 * W ∧
      ∑ j ∈ Finset.range K, y j - ∑ j ∈ Finset.range N, y j =
        ∑ j ∈ Finset.range (K - (N - W)), y (N - W + j) -
          ∑ j ∈ Finset.range (N - (N - W)), y (N - W + j) := by
  set a := N - W with ha
  have hK : a ≤ K := by omega
  have hN : a ≤ N := by omega
  refine ⟨hK, by omega, by omega, ?_⟩
  have eK : ∑ j ∈ Finset.range K, y j =
      ∑ j ∈ Finset.range a, y j + ∑ j ∈ Finset.range (K - a), y (a + j) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hK]
  have eN : ∑ j ∈ Finset.range N, y j =
      ∑ j ∈ Finset.range a, y j + ∑ j ∈ Finset.range (N - a), y (a + j) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hN]
  rw [eK, eN]; ring

/-- **The random-index step** (MT p. 431, (17.19)–(17.20)): for i.i.d. centred `Yⱼ ∈ L²` and
random indices `Kₙ` with `Kₙ/n → c > 0` almost surely, `(S_{Kₙ} − S_{⌊cn⌋})/√n → 0` in
probability. The proof is the book's, through Kolmogorov's inequality on a window around
`⌊cn⌋`. -/
theorem tendstoInMeasure_anscombe {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) Q Q) (hL2 : MemLp (Y 0) 2 Q)
    (h0 : ∫ ω, Y 0 ω ∂Q = 0) {K : ℕ → Ω → ℕ} (hKm : ∀ n, Measurable (K n)) {c : ℝ}
    (hc : 0 < c) (hK : ∀ᵐ ω ∂Q, Tendsto (fun n => (K n ω : ℝ) / n) atTop (𝓝 c)) :
    TendstoInMeasure Q (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ j ∈ Finset.range (K n ω), Y j ω -
      ∑ j ∈ Finset.range ⌊c * n⌋₊, Y j ω)) atTop (fun _ => 0) := by
  have hL2j : ∀ j, MemLp (Y j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have h0j : ∀ j, ∫ ω, Y j ω ∂Q = 0 := fun j => (hident j).integral_eq.trans h0
  set σ2 := ∫ ω, Y 0 ω ^ 2 ∂Q with hσ2
  have hσ2j : ∀ j, ∫ ω, Y j ω ^ 2 ∂Q = σ2 := fun j =>
    ((hident j).comp (measurable_id.pow_const 2)).integral_eq
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun ω => sq_nonneg _
  -- `Kₙ/n → c` in probability
  have hKp : TendstoInMeasure Q (fun n ω => (K n ω : ℝ) / n) atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae (fun (n : ℕ) =>
      (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hKm n)).div_const
        (n : ℝ)).aestronglyMeasurable) hK
  rw [tendstoInMeasure_iff_dist] at hKp ⊢
  intro ε hε
  -- it suffices to bound the real probabilities
  suffices hreal : Tendsto (fun n : ℕ => Q.real {ω | ε ≤ dist ((√(n : ℝ))⁻¹ *
      (∑ j ∈ Finset.range (K n ω), Y j ω - ∑ j ∈ Finset.range ⌊c * n⌋₊, Y j ω)) 0}) atTop
      (𝓝 0) by
    have := (ENNReal.tendsto_ofReal hreal)
    rw [ENNReal.ofReal_zero] at this
    exact this.congr fun n => ofReal_measureReal
  rw [Metric.tendsto_atTop]
  intro η hη
  -- choose the window size `δ`
  set δ : ℝ := min 1 (η * ε ^ 2 / (48 * (σ2 + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδle : 16 * δ * σ2 / ε ^ 2 ≤ η / 3 := by
    have h1 : δ ≤ η * ε ^ 2 / (48 * (σ2 + 1)) := min_le_right _ _
    have h2 : 16 * δ * σ2 ≤ 16 * (η * ε ^ 2 / (48 * (σ2 + 1))) * (σ2 + 1) := by
      have : 16 * δ * σ2 ≤ 16 * δ * (σ2 + 1) := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc 16 * δ * σ2 ≤ 16 * (η * ε ^ 2 / (48 * (σ2 + 1))) * (σ2 + 1) := h2
      _ = η / 3 * ε ^ 2 := by field_simp; ring
  -- `P(|Kₙ/n − c| ≥ δ) → 0`
  have hB := hKp δ hδpos
  have hB' : Tendsto (fun n : ℕ => Q.real {ω | δ ≤ dist ((K n ω : ℝ) / n) c}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [Metric.tendsto_atTop] at hB'
  obtain ⟨n₁, hn₁⟩ := hB' (η / 3) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (48 * σ2 / (η * ε ^ 2) + 2 / δ)
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₁ : n₁ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₂ : n₂ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  -- the window
  set N := ⌊c * n⌋₊ with hN
  set W := ⌈δ * n⌉₊ + 1 with hW
  set a := N - W with ha
  set D : Ω → ℝ := fun ω => (√(n : ℝ))⁻¹ *
    (∑ j ∈ Finset.range (K n ω), Y j ω - ∑ j ∈ Finset.range N, Y j ω) with hD
  set B := {ω | δ ≤ dist ((K n ω : ℝ) / n) c} with hBdef
  set M := {ω | ∃ l ≤ 2 * W, ε * √(n : ℝ) / 2 ≤ |∑ j ∈ Finset.range l, Y (a + j) ω|} with hM
  have hsub : {ω | ε ≤ dist (D ω) 0} ⊆ B ∪ M := by
    intro ω hω
    by_cases hωB : ω ∈ B
    · exact Or.inl hωB
    right
    simp only [hBdef, mem_ofPred_eq, not_le, Real.dist_eq] at hωB
    -- `|Kₙ − N| ≤ W`
    have hKn : |(K n ω : ℝ) - c * n| < δ * n := by
      have : |(K n ω : ℝ) / n - c| * n < δ * n := mul_lt_mul_of_pos_right hωB hnpos
      rwa [← abs_of_pos hnpos, ← abs_mul, abs_of_pos hnpos, sub_mul,
        div_mul_cancel₀ _ hnpos.ne'] at this
    have hN1 : (N : ℝ) ≤ c * n := Nat.floor_le (by positivity)
    have hN2 : c * n < N + 1 := Nat.lt_floor_add_one _
    have hW1 : δ * n ≤ ⌈δ * n⌉₊ := Nat.le_ceil _
    rw [abs_lt] at hKn
    have hk1 : K n ω ≤ N + W := by
      have : (K n ω : ℝ) < N + W := by push_cast [hW]; linarith
      exact_mod_cast this.le
    have hk2 : N ≤ K n ω + W := by
      have : (N : ℝ) < K n ω + W := by push_cast [hW]; linarith
      exact_mod_cast this.le
    obtain ⟨-, hl1, hl2, heq⟩ := sum_range_sub_eq_window (fun j => Y j ω) hk1 hk2
    -- one of the two window sums is large
    have hDω : ε ≤ |D ω| := by simpa [Real.dist_eq] using hω
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnpos
    have hbig : ε * √(n : ℝ) ≤ |∑ j ∈ Finset.range (K n ω), Y j ω -
        ∑ j ∈ Finset.range N, Y j ω| := by
      have : |D ω| = (√(n : ℝ))⁻¹ * |∑ j ∈ Finset.range (K n ω), Y j ω -
          ∑ j ∈ Finset.range N, Y j ω| := by
        rw [hD, abs_mul, abs_of_pos (inv_pos.2 hsq)]
      rw [this, inv_mul_eq_div, le_div_iff₀ hsq] at hDω
      exact hDω
    simp only [heq] at hbig
    by_contra hnot
    simp only [hM, mem_ofPred_eq, not_exists, not_and, not_le] at hnot
    have h1 := hnot _ hl1
    have h2 := hnot _ hl2
    have := abs_sub (∑ j ∈ Finset.range (K n ω - a), Y (a + j) ω)
      (∑ j ∈ Finset.range (N - a), Y (a + j) ω)
    linarith
  -- Kolmogorov on the window
  have hMbound : Q.real M ≤ 8 * δ * σ2 / ε ^ 2 + 16 * σ2 / (ε ^ 2 * n) := by
    have hk := kolmogorov_ineq_shift hind hm hL2j h0j a (2 * W) (t := ε * √(n : ℝ) / 2)
      (by positivity)
    simp_rw [hσ2j, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hk
    have hsq : (ε * √(n : ℝ) / 2) ^ 2 = ε ^ 2 * n / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
    rw [hsq] at hk
    have hWle : ((2 * W : ℕ) : ℝ) ≤ 2 * (δ * n + 2) := by
      have : (⌈δ * n⌉₊ : ℝ) < δ * n + 1 := Nat.ceil_lt_add_one (by positivity)
      push_cast [hW]; linarith
    have hpos : 0 < ε ^ 2 * n / 4 := by positivity
    have hM' : Q.real M ≤ ((2 * W : ℕ) : ℝ) * σ2 / (ε ^ 2 * n / 4) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact hk
    calc Q.real M ≤ ((2 * W : ℕ) : ℝ) * σ2 / (ε ^ 2 * n / 4) := hM'
      _ ≤ 2 * (δ * n + 2) * σ2 / (ε ^ 2 * n / 4) := by gcongr
      _ = 8 * δ * σ2 / ε ^ 2 + 16 * σ2 / (ε ^ 2 * n) := by field_simp; ring
  have htail : 16 * σ2 / (ε ^ 2 * n) ≤ η / 3 := by
    have h1 : 48 * σ2 / (η * ε ^ 2) < n := by
      have : (n₂ : ℝ) ≤ n := by exact_mod_cast hnn₂
      have h3 : 48 * σ2 / (η * ε ^ 2) + 2 / δ < n := hn₂.trans_le this
      have : 0 ≤ 2 / δ := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h816 : 8 * δ * σ2 / ε ^ 2 ≤ 16 * δ * σ2 / ε ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hδpos.le hσ0]
  have hBn := hn₁ n hnn₁
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hBn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc Q.real {ω | ε ≤ dist (D ω) 0} ≤ Q.real (B ∪ M) := measureReal_mono hsub
    _ ≤ Q.real B + Q.real M := measureReal_union_le _ _
    _ < η / 3 + (η / 3 + η / 3) := by linarith
    _ = η := by ring

end MeynTweedie.GeneralizedDrift
