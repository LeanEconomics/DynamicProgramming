/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.OrnsteinCoupling
import Positivity.AperiodicErgodic
import Positivity.ErgodicTheorem

/-!
# Null recurrent chains: Orey's and Jain's theorems (MT §18.1.2, Theorem 18.0.1)

Meyn and Tweedie, pp. 462, 467–469. The state space is countably generated.

**At an atom.**
* `tvNorm_comp_pow_succ_sub_atom_le` (the total variation form of (18.14)):
  `‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖ ≤ 2 (P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁ (n + 1))`, from the
  Regenerative Decomposition (13.47); `realConv_lastExitSeq_one_succ`: `t₁(m + 1) = tail(m)`.
* `tendsto_tvNorm_sub_atom`: if `α ∋ a` is reached almost surely from `a` and from `λ`, and the
  return-time law is aperiodic, `‖λPⁿ − Pⁿ(a, ·)‖ → 0`, by Theorem 18.1.1 in the tail form
  `theorem_18_1_1_ii`; no finite mean return time is needed.

**Results.**
* **Theorem 18.1.2** (Orey, p. 467): for an aperiodic Harris chain, `theorem_18_1_2`, (18.13),
  `∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0`; `theorem_18_1_2_measures`: `‖λPⁿ − μPⁿ‖ → 0`;
  `theorem_18_1_2_dirac`: from two states. The proof is the book's: a split skeleton with an
  aperiodic atom (strong aperiodicity), then the contraction of the total variation norm
  (`tvNorm_comp_pow_add_le`). `tendsto_lintegral_of_le_const` handles the integrand of (18.13),
  whose measurability is not needed.
* **Theorem 18.1.3** (Jain, p. 468): `theorem_18_1_3`, for an aperiodic Harris null chain and an
  invariant `π ≠ 0`, `sup_A λPⁿ(A)/(π(A) + ε) → 0` (18.15). `IsNull.measure_univ_eq_top`: a null
  chain has `π(X) = ∞`; `measure_mul_le_of_forall_le` is the integral step (18.19) and
  `jain_arith` the final contradiction. The core `tendsto_iSup_div_of_measure_univ_eq_top` needs
  only a subinvariant `π` with `π(X) = ∞`.
* **Theorem 18.0.1** (`theorem_18_0_1`, p. 462): the two statements (18.1), (18.2) together.

**Hypotheses.** Theorem 18.1.3 is stated for an "aperiodic and null recurrent" chain; its proof
uses Theorem 18.1.2, which needs the Harris property, and it is proved here for Harris chains.
Without the Harris property it is false: `theorem_18_1_3_counterexample` in `NullNotHarris`.
The book's use of Egorov's theorem (uniform convergence on a set of large `π`-measure) is
replaced by the increasing sets `D_N = ⋂_{k ≥ N} G_k` of points where the convergence (18.17)
has taken place by stage `N`: `π(D_N) ↑ π(X) = ∞`; no σ-finiteness of `π` is used.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Orey's theorem at an atom -/

/-- `t_{1_A} ≤ t_1`. -/
theorem lastExitSeq_indicator_le (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (A : Set X) (k : ℕ) :
    lastExitSeq P hα a (A.indicator 1) k ≤ lastExitSeq P hα a 1 k := by
  rcases k with _ | k
  · simp
  · rw [lastExitSeq_succ, lastExitSeq_succ]
    refine ENNReal.toReal_mono (lintegral_tabooKernel_ne_top P hα a ENNReal.one_ne_top
      (fun _ => le_rfl) k) (lintegral_mono fun y => ?_)
    by_cases hy : y ∈ A <;> simp [hy]

/-- The total variation form of (18.14): for an atom `α ∋ a` and a probability `λ`,
`‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖ ≤ 2 (P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁ (n + 1))`. -/
theorem tvNorm_comp_pow_succ_sub_atom_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) ≤
      2 * ((tabooSeq P hα.1 μ n univ).toReal +
        realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k -
          atomRenewal P α a k|) (lastExitSeq P hα.1 a 1) (n + 1)) := by
  have := isMarkovKernel_pow P (n + 1)
  rw [tvNorm_eq_two_mul_tvSup _ _ (by simp)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  have hind : ∀ y, A.indicator (1 : X → ℝ≥0∞) y ≤ 1 := fun y => by
    by_cases hy : y ∈ A <;> simp [hy]
  have h := regenerative_decomposition_47 hα ha μ ENNReal.one_ne_top hind n
  simp only [lintegral_indicator_one hA] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top (measure_ne_top μ univ)
      (tabooSeq_apply_le P hα.1 μ n univ)) (measure_mono (subset_univ A))
  · rw [realConv_eq_sum_range, realConv_eq_sum_range]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (lastExitSeq_indicator_le P hα.1 a A _) (abs_nonneg _)

/-- `t₁(m + 1) = tail(m)` for the return-time law, so `g ∗ t₁ (n + 1) = g ∗ tail (n)`. -/
theorem realConv_lastExitSeq_one_succ (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) (g : ℕ → ℝ) (n : ℕ) :
    realConv g (lastExitSeq P hα a 1) (n + 1) =
      realConv g (renewalTail (entryLaw P hα (Measure.dirac a))) n := by
  rw [realConv_eq_sum_range, realConv_eq_sum_range, Finset.sum_range_succ, Nat.sub_self,
    lastExitSeq_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [show n + 1 - k = (n - k) + 1 by omega, lastExitSeq_succ, renewalTail_entryLaw]
  simp

/-- **Orey's theorem at an atom** (the first part of the proof of Theorem 18.1.2, MT p. 467):
if the atom `α ∋ a` is reached almost surely from `a` and from `λ`, and its return-time law is
aperiodic, then `‖λPⁿ − Pⁿ(a, ·)‖ → 0`. No finiteness of the mean return time is needed. -/
theorem tendsto_tvNorm_sub_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hLa : hitProb P α a = 1)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∫⁻ x, hitProb P α x ∂μ = 1) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) ((P ^ n : Kernel X X) a)) atTop
      (𝓝 0) := by
  set p := entryLaw P hα.1 (Measure.dirac a) with hpdef
  have hp : IsIncrementLaw p := isIncrementLaw_entryLaw P hα.1 hLa
  have hu : atomRenewal P α a = realRenewalSeq p := atomRenewal_eq_realRenewalSeq hα ha
  have hE := hasSum_entryLaw P hα.1 μ
  rw [hμ, ENNReal.toReal_one] at hE
  have hδ : HasSum deltaSeq 1 := by
    have : deltaSeq = fun n => if n = 0 then (1 : ℝ) else 0 := funext fun n => rfl
    rw [this]; exact hasSum_ite_eq 0 1
  have hδ0 : ∀ n, 0 ≤ deltaSeq n := fun n => by unfold deltaSeq; split_ifs <;> norm_num
  have hcoup := theorem_18_1_1_ii hp hap (entryLaw_nonneg P hα.1 μ) hE hδ0 hδ
  simp only [delayedRenewal, realConv_deltaSeq_left] at hcoup
  have hA : Tendsto (fun n => (tabooSeq P hα.1 μ n univ).toReal) atTop (𝓝 0) := by
    simp_rw [tabooSeq_univ_toReal P hα.1 μ, measureReal_def, measure_univ, ENNReal.toReal_one]
    have := (hE.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub 1
    simpa using this
  have hbound := (hA.add hcoup).const_mul 2
  simp only [add_zero, mul_zero] at hbound
  rw [← tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_) hbound
  refine (tvNorm_comp_pow_succ_sub_atom_le hα ha μ n).trans (le_of_eq ?_)
  rw [realConv_lastExitSeq_one_succ, hu]

/-! ### Orey's theorem -/

/-- Lebesgue integrals of nonnegative functions bounded by a constant and tending to `0`
pointwise tend to `0`, with no measurability: a measurable minorant with the same integral
(`exists_measurable_le_lintegral_eq`) is dominated. -/
theorem tendsto_lintegral_of_le_const {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ n x, f n x ≤ C)
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 0) := by
  choose g hg hgf hgeq using fun n => exists_measurable_le_lintegral_eq (μ := μ) (f n)
  simp_rw [hgeq]
  have h := tendsto_lintegral_of_dominated_convergence (fun _ => C) hg
    (fun n => Filter.Eventually.of_forall fun x => (hgf n x).trans (hfC n x))
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top hC (measure_ne_top μ univ))
    (Filter.Eventually.of_forall fun x => tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (hf x) (fun n => zero_le) fun n => hgf n x)
  simpa using h

/-- `‖λPⁿ − μPⁿ‖` is non-increasing along `n`, in the sense
`‖λPⁿ⁺ʳ − μPⁿ⁺ʳ‖ ≤ ‖λPⁿ − μPⁿ‖` (the contraction property, MT p. 468). -/
theorem tvNorm_comp_pow_add_le (P : Kernel X X) [IsMarkovKernel P] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n r : ℕ) :
    tvNorm ((P ^ (n + r) : Kernel X X) ∘ₘ μ) ((P ^ (n + r) : Kernel X X) ∘ₘ ν) ≤
      tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) ((P ^ n : Kernel X X) ∘ₘ ν) := by
  have := isMarkovKernel_pow P n
  have := isMarkovKernel_pow P r
  rw [pow_add_eq, ← Measure.comp_assoc, ← Measure.comp_assoc]
  exact tvNorm_comp_le _ _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.1.2** (Orey's theorem, MT p. 467), for initial laws: for an aperiodic Harris
chain and any probabilities `λ`, `μ`, `‖λPⁿ − μPⁿ‖ → 0`. The proof is the book's: on a split
skeleton with an aperiodic atom (`tendsto_tvNorm_sub_atom`), then back to the chain by the
contraction of the total variation norm. -/
theorem theorem_18_1_2_measures {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) ((P ^ n : Kernel X X) ∘ₘ ν)) atTop
      (𝓝 0) := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hH.1 hap
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have hHm : IsHarris (P ^ m : Kernel X X) ψ := (theorem_9_1_6 hH.1 hap).1 hH m hm
  obtain ⟨c, hc⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hca : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hL : ∀ x, hitProb (P ^ m : Kernel X X) M.C x = 1 :=
    hHm.hitProb_eq_one M.measurableSet_C hψC
  have hLs := M.hitProb_checkAlpha_eq_one hL
  have hapc := M.isAperiodicLaw_entryLaw_checkAlpha hνC (c := c)
  have hsk : ∀ (σ : Measure X) [IsProbabilityMeasure σ],
      Tendsto (fun k => tvNorm ((M.splitKernel ^ k : Kernel _ _) ∘ₘ M.split σ)
        ((M.splitKernel ^ k : Kernel _ _) (c, true))) atTop (𝓝 0) := fun σ _ => by
    have := M.isProbabilityMeasure_split σ
    refine tendsto_tvNorm_sub_atom M.isAtom_checkAlpha hca (hLs _) hapc (M.split σ) ?_
    simp_rw [hLs]
    rw [lintegral_one, measure_univ]
  have hboth := (hsk μ).add (hsk ν)
  rw [add_zero] at hboth
  have hskel : Tendsto (fun k => tvNorm ((P ^ (m * k) : Kernel X X) ∘ₘ μ)
      ((P ^ (m * k) : Kernel X X) ∘ₘ ν)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => tvNorm_nonneg _ _) (fun k => ?_) hboth
    have := isMarkovKernel_pow M.splitKernel k
    have := M.isProbabilityMeasure_split μ
    have := M.isProbabilityMeasure_split ν
    have h1 := tvNorm_map_le measurable_fst
      ((M.splitKernel ^ k : Kernel _ _) ∘ₘ M.split μ)
      ((M.splitKernel ^ k : Kernel _ _) ∘ₘ M.split ν)
    rw [split_comp_pow_map_fst, split_comp_pow_map_fst, ← pow_mul] at h1
    refine h1.trans ((tvNorm_triangle _ ((M.splitKernel ^ k : Kernel _ _) (c, true)) _).trans ?_)
    rw [tvNorm_comm ((M.splitKernel ^ k : Kernel _ _) (c, true))]
  have hdiv : Tendsto (fun n => n / m) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_) (hskel.comp hdiv)
  simp only [Function.comp_apply]
  have h := tvNorm_comp_pow_add_le P μ ν (m * (n / m)) (n - m * (n / m))
  rwa [Nat.add_sub_cancel' (Nat.mul_div_le n m)] at h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.1.2** (Orey's theorem, MT p. 467) from two initial states:
`‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0` for an aperiodic Harris chain. -/
theorem theorem_18_1_2_dirac {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) (x y : X) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) atTop
      (𝓝 0) := by
  have h := theorem_18_1_2_measures hH hap (Measure.dirac x) (Measure.dirac y)
  simp_rw [dirac_kernel] at h
  exact h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.1.2** (Orey's theorem, MT p. 467), (18.13): for an aperiodic Harris chain and
initial probabilities `λ`, `μ`, `∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0` (as an integral of
`[0, ∞]`-valued functions; no measurability of the integrand is needed). -/
theorem theorem_18_1_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Tendsto (fun n => ∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) ∂ν ∂μ) atTop (𝓝 0) := by
  have hb : ∀ n x y, ENNReal.ofReal
      (tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) ≤ 2 := fun n x y => by
    have := isMarkovKernel_pow P n
    have h : tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ≤ 2 := by
      have := tvNorm_le_add_measureReal ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at this
      linarith
    exact (ENNReal.ofReal_le_ofReal h).trans_eq (by simp)
  have hinner : ∀ x, Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) ∂ν) atTop (𝓝 0) := fun x =>
    tendsto_lintegral_of_le_const ν (C := 2) ENNReal.ofNat_ne_top (fun n y => hb n x y) fun y => by
      simpa using ENNReal.tendsto_ofReal (theorem_18_1_2_dirac hH hap x y)
  refine tendsto_lintegral_of_le_const μ (C := 2) ENNReal.ofNat_ne_top (fun n x => ?_) hinner
  calc ∫⁻ y, ENNReal.ofReal (tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) ∂ν
      ≤ ∫⁻ _, 2 ∂ν := lintegral_mono fun y => hb n x y
    _ = 2 := by rw [lintegral_const, measure_univ, mul_one]

/-! ### Theorem 18.1.3 -/

/-- A null chain has no nonzero finite invariant measure: a nonzero invariant `π` has
`π(X) = ∞` (MT p. 468, "the fact that `π(X) = ∞`"). -/
theorem IsNull.measure_univ_eq_top {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hnull : IsNull P ψ) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π ≠ 0) :
    π univ = ∞ := by
  by_contra hfin
  have h0 : π univ ≠ 0 := fun h => hπ0 (Measure.measure_univ_eq_zero.1 h)
  refine hnull.2 ⟨(π univ)⁻¹ • π, ⟨?_⟩, hπ.smul _⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]

/-- The integral step (18.19): if `s ≤ Pⁿ(y, B) + η` on `D`, then `π(D) (s − η) ≤ π(B)` for a
subinvariant `π`. -/
theorem measure_mul_le_of_forall_le {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsSubinvariant P π) {B D : Set X} (hB : MeasurableSet B) (n : ℕ)
    {s η : ℝ≥0∞} (h : ∀ y ∈ D, s ≤ (P ^ n : Kernel X X) y B + η) :
    π D * (s - η) ≤ π B := by
  have hinv : IsSubinvariant (P ^ n : Kernel X X) π := hπ.pow n
  calc π D * (s - η) = ∫⁻ _ in D, (s - η) ∂π := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in D, (P ^ n : Kernel X X) y B ∂π :=
        setLIntegral_mono (Kernel.measurable_coe _ hB) fun y hy => tsub_le_iff_right.2 (h y hy)
    _ ≤ ∫⁻ y, (P ^ n : Kernel X X) y B ∂π := setLIntegral_le_lintegral _ _
    _ ≤ π B := by
        rw [← Measure.bind_apply hB (Kernel.aemeasurable _)]
        exact hinv B

/-- The arithmetic of (18.19): with `δ(b + ε) < s`, `η = δε/2` and `d > δ⁻¹`, the inequality
`d (s − η) ≤ b` is impossible for finite `b`. -/
theorem jain_arith {δ ε b s d : ℝ≥0∞} (hδ : 0 < δ) (hδt : δ ≠ ∞) (hε : 0 < ε) (hεt : ε ≠ ∞)
    (hbt : b ≠ ∞) (hst : s ≠ ∞) (hs : δ * (b + ε) < s) (hd : δ⁻¹ < d)
    (hle : d * (s - δ * ε / 2) ≤ b) : False := by
  have hηt : δ * ε / 2 ≠ ∞ := ENNReal.div_ne_top (ENNReal.mul_ne_top hδt hεt) two_ne_zero
  have hε2 : ε / 2 ≠ 0 := ENNReal.div_ne_zero.2 ⟨hε.ne', ENNReal.ofNat_ne_top⟩
  have h1 : δ * (b + ε / 2) ≤ s - δ * ε / 2 := by
    refine ENNReal.le_sub_of_add_le_right hηt ?_
    have : δ * (b + ε / 2) + δ * ε / 2 = δ * (b + ε) := by
      rw [mul_div_assoc, ← mul_add, add_assoc, ENNReal.add_halves]
    rw [this]; exact hs.le
  have hpos : s - δ * ε / 2 ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ h1)
    exact ENNReal.mul_pos hδ.ne' (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hε2)
      le_add_self))
  have hsub : s - δ * ε / 2 ≠ ∞ := ENNReal.sub_ne_top hst
  have h2 : δ⁻¹ * (δ * (b + ε / 2)) = b + ε / 2 := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hδ.ne' hδt, one_mul]
  have h3 : b < b + ε / 2 := ENNReal.lt_add_right hbt hε2
  have h4 : δ⁻¹ * (s - δ * ε / 2) < d * (s - δ * ε / 2) :=
    (ENNReal.mul_lt_mul_iff_left hpos hsub).2 hd
  have : b < b := calc
    b < b + ε / 2 := h3
    _ = δ⁻¹ * (δ * (b + ε / 2)) := h2.symm
    _ ≤ δ⁻¹ * (s - δ * ε / 2) := mul_le_mul_right h1 _
    _ < d * (s - δ * ε / 2) := h4
    _ ≤ b := hle
  exact lt_irrefl b this

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The core of Theorem 18.1.3**: for an aperiodic Harris chain and a subinvariant `π` with
`π(X) = ∞`, `sup_A λPⁿ(A)/(π(A) + ε) → 0` for every probability `λ` and `ε > 0`. The uniform
convergence on a large set supplied by Egorov's theorem in the book is replaced by the sets
`D_N = ⋂_{k ≥ N} G_k`, whose union is `X`. -/
theorem tendsto_iSup_div_of_measure_univ_eq_top {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    (hπ : IsSubinvariant P π) (hinf : π univ = ∞) (μ : Measure X) [IsProbabilityMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n => ⨆ (A : Set X) (_ : MeasurableSet A),
      ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + ε)) atTop (𝓝 0) := by
  wlog hεt : ε ≠ ∞ generalizing ε with H
  · have h := H (ε := min ε 1) (lt_min hε one_pos) (ne_top_of_le_ne_top ENNReal.one_ne_top
      (min_le_right _ _))
    have hle : ∀ n, (⨆ (A : Set X) (_ : MeasurableSet A),
        ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + ε)) ≤ ⨆ (A : Set X) (_ : MeasurableSet A),
          ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + min ε 1) := fun n => by
      refine iSup₂_mono fun A _ => ENNReal.div_le_div_left ?_ _
      gcongr
      exact min_le_left ε 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le) hle
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set δ₀ := min δ 1 with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ one_pos
  have hδ₀t : δ₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hfreq : ∃ᶠ n in atTop, δ₀ < ⨆ (A : Set X) (_ : MeasurableSet A),
      ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + ε) :=
    hcon.mono fun n h => lt_of_le_of_lt (min_le_left _ _) (not_le.1 h)
  obtain ⟨φ, hφ, hφF⟩ := extraction_of_frequently_atTop hfreq
  have hBex : ∀ k, ∃ B, MeasurableSet B ∧
      δ₀ < ((P ^ φ k : Kernel X X) ∘ₘ μ) B / (π B + ε) := fun k => by
    obtain ⟨B, hB⟩ := lt_iSup_iff.1 (hφF k)
    obtain ⟨hBm, h⟩ := lt_iSup_iff.1 hB
    exact ⟨B, hBm, h⟩
  choose B hBm hBlt using hBex
  have hprob : ∀ k, IsProbabilityMeasure ((P ^ φ k : Kernel X X) ∘ₘ μ) := fun k => by
    have := isMarkovKernel_pow P (φ k); infer_instance
  have hst : ∀ k, ((P ^ φ k : Kernel X X) ∘ₘ μ) (B k) ≠ ∞ := fun k => measure_ne_top _ _
  have hmul : ∀ k, δ₀ * (π (B k) + ε) < ((P ^ φ k : Kernel X X) ∘ₘ μ) (B k) := fun k =>
    (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt (lt_of_lt_of_le hε le_add_self)))
      (Or.inr hδ₀.ne')).1 (hBlt k)
  have hπB : ∀ k, π (B k) ≠ ∞ := fun k h => by
    have := hmul k
    rw [h, top_add, ENNReal.mul_top hδ₀.ne'] at this
    exact absurd this (not_lt.2 le_top)
  set η := δ₀ * ε / 2 with hηdef
  have hηt : η ≠ ∞ := ENNReal.div_ne_top (ENNReal.mul_ne_top hδ₀t hεt) two_ne_zero
  have hη0 : 0 < η.toReal := ENNReal.toReal_pos (ENNReal.div_ne_zero.2
    ⟨(ENNReal.mul_pos hδ₀.ne' hε.ne').ne', ENNReal.ofNat_ne_top⟩) hηt
  set G : ℕ → Set X := fun k =>
    {y | ((P ^ φ k : Kernel X X) ∘ₘ μ) (B k) ≤ (P ^ φ k : Kernel X X) y (B k) + η} with hG
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_le measurable_const ((Kernel.measurable_coe _ (hBm k)).add_const η)
  have hev : ∀ y, ∀ᶠ k in atTop, y ∈ G k := fun y => by
    have hO := (theorem_18_1_2_measures hH hap μ (Measure.dirac y)).comp hφ.tendsto_atTop
    filter_upwards [hO.eventually (gt_mem_nhds hη0)] with k hk
    simp only [Function.comp_apply, dirac_kernel] at hk
    have := isMarkovKernel_pow P (φ k)
    have habs := abs_measureReal_sub_le_tvNorm ((P ^ φ k : Kernel X X) ∘ₘ μ)
      ((P ^ φ k : Kernel X X) y) (hBm k)
    simp only [measureReal_def] at habs
    change ((P ^ φ k : Kernel X X) ∘ₘ μ) (B k) ≤ (P ^ φ k : Kernel X X) y (B k) + η
    rw [← ENNReal.toReal_le_toReal (hst k) (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hηt⟩),
      ENNReal.toReal_add (measure_ne_top _ _) hηt]
    have hle := le_abs_self ((((P ^ φ k : Kernel X X) ∘ₘ μ) (B k)).toReal -
      ((P ^ φ k : Kernel X X) y (B k)).toReal)
    linarith
  set D : ℕ → Set X := fun N => ⋂ k, ⋂ (_ : N ≤ k), G k with hD
  have hDmono : Monotone D := fun N N' hNN' y hy =>
    mem_iInter₂.2 fun k hk => mem_iInter₂.1 hy k (le_trans hNN' hk)
  have hDU : ⋃ N, D N = univ := eq_univ_of_forall fun y => by
    obtain ⟨N, hN⟩ := (hev y).exists_forall_of_atTop
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun k hk => hN k hk⟩
  have hDlim := tendsto_measure_iUnion_atTop (μ := π) hDmono
  rw [hDU, hinf] at hDlim
  have hδinv : δ₀⁻¹ < ∞ := ENNReal.inv_lt_top.2 hδ₀
  obtain ⟨N, hN⟩ := (hDlim.eventually (lt_mem_nhds hδinv)).exists
  have hDN : ∀ y ∈ D N, ((P ^ φ N : Kernel X X) ∘ₘ μ) (B N) ≤
      (P ^ φ N : Kernel X X) y (B N) + η := fun y hy => mem_iInter₂.1 hy N le_rfl
  have hkey := measure_mul_le_of_forall_le hπ (hBm N) (φ N) hDN
  exact jain_arith hδ₀ hδ₀t hε hεt (hπB N) (hst N) (hmul N) hN hkey

/-- A null chain has no nonzero finite subinvariant measure. -/
theorem IsNull.measure_univ_eq_top_of_subinvariant {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hnull : IsNull P ψ) {π : Measure X} (hπ : IsSubinvariant P π)
    (hπ0 : π ≠ 0) : π univ = ∞ := by
  by_contra hfin
  exact absurd (hnull.measure_univ_eq_top (proposition_10_1_2_iv hπ hfin) hπ0) hfin

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.1.3** (Jain's theorem, MT p. 468), for Harris chains: if the chain is aperiodic,
Harris and null, and `π ≠ 0` is invariant, then for every initial probability `λ` and every
`ε > 0`, `sup_A λPⁿ(A)/(π(A) + ε) → 0`, (18.15). No σ-finiteness of `π` is used. -/
theorem theorem_18_1_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hnull : IsNull P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    (hπ : IsInvariant P π) (hπ0 : π ≠ 0) (μ : Measure X) [IsProbabilityMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n => ⨆ (A : Set X) (_ : MeasurableSet A),
      ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + ε)) atTop (𝓝 0) :=
  tendsto_iSup_div_of_measure_univ_eq_top hH hap hπ.isSubinvariant
    (hnull.measure_univ_eq_top hπ hπ0) μ hε

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.0.1** (MT p. 462): for an aperiodic Harris chain, (18.1)
`∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0`; and if the chain is null with invariant measure
`π ≠ 0`, (18.2) `sup_A λPⁿ(A)/(π(A) + ε) → 0`. -/
theorem theorem_18_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Tendsto (fun n => ∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)) ∂ν ∂μ) atTop (𝓝 0) ∧
    (IsNull P ψ → ∀ {π : Measure X}, IsInvariant P π → π ≠ 0 → ∀ {ε : ℝ≥0∞}, 0 < ε →
      Tendsto (fun n => ⨆ (A : Set X) (_ : MeasurableSet A),
        ((P ^ n : Kernel X X) ∘ₘ μ) A / (π A + ε)) atTop (𝓝 0)) :=
  ⟨theorem_18_1_2 hH hap μ ν, fun hnull _ hπ hπ0 _ hε => theorem_18_1_3 hH hnull hap hπ hπ0 μ hε⟩

end MeynTweedie.Positivity
