/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.DependentLIL
import LimitTheorems.SplitLimitTheorems
import LimitTheorems.CLTMoment


/-!
# The law of the iterated logarithm for Markov chains (MT §17.2–17.5, Theorem 17.0.1)

The LIL parts of Meyn and Tweedie, Theorems 17.2.2 (p. 430), 17.3.6 (p. 441), 17.5.3 (p. 452) and
17.0.1 (iv) (p. 422). The LIL is stated in the `ε`-form `HasLIL` of `IIDLIL`:
`limsup Sₙ(ḡ)/√(2 n log log n) = γ_g` and `liminf = −γ_g` (`HasLIL.limsup_eq`,
`HasLIL.liminf_eq` give the `Filter.limsup`/`liminf` form). The constant is the CLT constant in
each case, so the CLT and LIL hold together as in MT p. 422.

**Tools.**
* `cycleCount_eq_zero_of_lt`, `cycleCount_succ_le`: the number `ℓₙ` of completed cycles grows by
  at most one per step, so the random-index step `HasLIL.comp_index` applies.
* `tendsto_pathSum_sub_cycles`: the remainder (17.15) is `o(√n)` almost surely.
* `cltVariance_nonneg`; `eq_of_tendstoInDistribution_gaussianReal`: limits in distribution are
  unique, so two CLTs along the same sequence have the same variance.

**Results.**
* **Theorem 17.2.2**, the LIL (`theorem_17_2_2_lil`, p. 430): for a recurrent atom, the moment
  condition (17.14) and every initial law from which the atom is reached a.s., `Sₙ(ḡ)` obeys the
  LIL with constant `√(cltVariance P α a g)` (the CLT constant of `theorem_17_2_2`);
  `theorem_17_2_2_harris_lil`: from every initial state for a Harris chain with an accessible
  atom. The case `γ_g = 0` is included.
* **Theorem 17.3.6**, the LIL (`theorem_17_3_6_lil`, p. 441), for `m = 1`: for a positive Harris
  chain with a minorization on `C ∈ B⁺(X)` and the split moment condition (17.31), the LIL holds
  under every initial law, with the constant (17.32) of `theorem_17_3_6`.
* **Theorem 17.0.1 (iv)**, the LIL (`theorem_17_0_1_iv_lil`, p. 422), and **Theorem 17.5.3**, the
  LIL (`theorem_17_5_3_lil`, p. 452), for chains with a one-step minorization whose split chain
  satisfies (17.31): the split-chain variance (17.32) equals the variance (17.3) (resp.
  `π(ĝ² − (Pĝ)²)`), and the LIL holds from every initial state with that constant. Theorem
  17.5.4 has the hypotheses of Theorem 17.0.1 (ii), so its LIL is `theorem_17_0_1_iv_lil`.

**Hypotheses and omissions.** The book proves the LIL of Theorems 17.0.1 (iv), 17.5.3 and 17.5.4
from Theorem 17.3.6 for a split `m`-skeleton, with the moment bound (17.53) of Lemma 17.5.2 (ii).
The LILs here are the case `m = 1` (a one-step minorization on a set of positive `ψ`-measure),
with the split moment condition (17.31) as a hypothesis. The book's route for a general `m` is in
the `Skeleton…` modules: Theorem 17.3.6, the LIL, for a split `m`-skeleton
(`theorem_17_3_6_lil_general`, `SkeletonLimitTheorems`, through `hasLIL_oneDependent` of
`DependentLIL`; `theorem_17_3_6_lil_skeleton`, `SkeletonErgodic`), and Lemma 17.5.2 (ii) with the
LIL of Theorems 17.5.3, 17.5.4 and 17.0.1 (iv) under the book's hypotheses alone
(`theorem_17_5_3_lil_skeleton`, `theorem_17_5_4_lil_skeleton`, `theorem_17_0_1_iv_lil_skeleton`,
`SkeletonMoment`). The LIL for the examples of §17.6 (Proposition 17.6.1, Theorem 17.6.2) is
`proposition_17_6_1_lil_poisson` and `theorem_17_6_2_lil_poisson` (`MartingaleLILApplications`).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The number of cycles grows by at most one per step -/

omit [MeasurableSpace X] in
/-- `ℓₙ = 0` before the first visit to `α`. -/
theorem cycleCount_eq_zero_of_lt (α : Set X) {n : ℕ} {ω : ℕ → X} (hn : n < renewalTime α 0 ω) :
    cycleCount α n ω = 0 := by
  rw [cycleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  have hmono : StrictMono fun i => renewalTime α i ω :=
    strictMono_nat_of_lt_succ fun i => renewalTime_lt_succ α i ω
  have : renewalTime α 0 ω < renewalTime α (j + 1) ω := hmono (Nat.succ_pos j)
  omega

omit [MeasurableSpace X] in
/-- `ℓ_{n+1} ≤ ℓₙ + 1`: at most one cycle is completed at each time. -/
theorem cycleCount_succ_le (α : Set X) (n : ℕ) (ω : ℕ → X) :
    cycleCount α (n + 1) ω ≤ cycleCount α n ω + 1 := by
  by_cases h0 : renewalTime α 0 ω ≤ n
  · obtain ⟨j, h1, h2⟩ := exists_renewalTime_between α h0
    rw [cycleCount_eq α h1 h2]
    by_cases h3 : n + 1 < renewalTime α (j + 1) ω
    · rw [cycleCount_eq α (h1.trans (Nat.le_succ n)) h3]; omega
    · have h4 : renewalTime α (j + 1) ω = n + 1 := by omega
      have h5 : n + 1 < renewalTime α (j + 1 + 1) ω := by
        rw [← h4]; exact renewalTime_lt_succ α (j + 1) ω
      rw [cycleCount_eq α h4.le h5]
  · push Not at h0
    rw [cycleCount_eq_zero_of_lt α h0]
    by_cases h3 : n + 1 < renewalTime α 0 ω
    · rw [cycleCount_eq_zero_of_lt α h3]; omega
    · have h4 : renewalTime α 0 ω = n + 1 := by omega
      rw [cycleCount_eq α h4.le (by rw [← h4]; exact renewalTime_lt_succ α 0 ω)]
      omega

/-! ### Theorem 17.2.2: the LIL -/

/-- The pathwise error of the cycle decomposition is `o(√n)` almost surely: under (17.14),
`n^{−1/2} (Sₙ(ḡ) − Σ_{j < ℓₙ} sⱼ(ḡ)) → 0`, `P_μ`-a.s. (the remainder step of MT p. 431). -/
theorem tendsto_pathSum_sub_cycles (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {g : X → ℝ}
    (hgm : Measurable g) (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a)) (c : ℝ) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
      (pathSum (fun x => g x - c) n ω - ∑ j ∈ Finset.range (cycleCount α n ω),
        cycleSum α (fun x => g x - c) (cycle α (j + 1) ω))) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hν := ae_firstHit_ne_top_of_hitProb P hα.1 hrec
  set gb : X → ℝ := fun x => g x - c with hgb
  have hgbm : Measurable gb := hgm.sub measurable_const
  set ψ := cycleSum α fun x => |gb x| with hψ
  have hψm : Measurable ψ := measurable_cycleSum hα.1 (measurable_abs_of_measurable hgbm)
  have hψ2 : MemLp ψ 2 (cycleLaw P α a) := by
    refine (hg2.add (hL2.const_mul |c|)).of_le hψm.aestronglyMeasurable
      (Eventually.of_forall fun e => ?_)
    have h4 : 0 ≤ cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) :=
      add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
    have h5 : 0 ≤ ψ e := Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg h4, abs_of_nonneg h5]
    have : ψ e ≤ cycleSum α (fun x => |g x| + |c|) e :=
      Finset.sum_le_sum fun i _ => by
        simp only [hgb]; exact (abs_sub _ _)
    have h6 : cycleSum α (fun x => |g x| + |c|) e =
        cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) := by
      simp only [cycleSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast; ring
    linarith
  have hsl2 := tendsto_cycle_average P hα ha hν μ hμ (hψm.pow_const 2) hψ2.integrable_sq
  filter_upwards [hsl2] with ω hω
  set u : ℕ → ℝ := fun j => ψ (cycle α (j + 1) ω) ^ 2 with hu
  have hu1 : Tendsto (fun j : ℕ => u j / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_term_div_of_tendsto_average hω
  have hu2 := tendsto_index_div_of_le (fun j => sq_nonneg _) hu1 (k := fun n => cycleCount α n ω)
    (cycleCount_le α · ω)
  set C := |gb (ω 0)| + |cycleSum α gb (cycle α 0 ω)| with hC
  have hsqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hZ' : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * ψ (cycle α (cycleCount α n ω + 1) ω))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp
    have h2 := (hu2.mul h1)
    rw [zero_mul] at h2
    have h3 := (Real.continuous_sqrt.tendsto _).comp h2
    rw [Real.sqrt_zero] at h3
    refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hψ0 : 0 ≤ ψ (cycle α (cycleCount α n ω + 1) ω) :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [Function.comp_apply]
    rw [show u (cycleCount α n ω) / ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) =
        ψ (cycle α (cycleCount α n ω + 1) ω) ^ 2 / n by
      simp only [hu]; field_simp]
    rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq hψ0, inv_mul_eq_div]
  have hbound := (hsqrt.mul_const C).add hZ'
  rw [zero_mul, add_zero] at hbound
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop (renewalTime α 0 ω)] with n hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have h := abs_pathSum_sub_le α gb hn
  have : (√(n : ℝ))⁻¹ * |pathSum gb n ω - ∑ j ∈ Finset.range (cycleCount α n ω),
      cycleSum α gb (cycle α (j + 1) ω)| ≤
      (√(n : ℝ))⁻¹ * (C + ψ (cycle α (cycleCount α n ω + 1) ω)) :=
    mul_le_mul_of_nonneg_left (by simpa [hC, hψ] using h) (inv_nonneg.2 (Real.sqrt_nonneg _))
  linarith

/-- The asymptotic variance `γ_g²` is non-negative. -/
theorem cltVariance_nonneg (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X)
    (g : X → ℝ) (hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a)) :
    0 ≤ cltVariance P α a g :=
  div_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (zero_le_one.trans (one_le_cycleMeanLength P α a hL))

/-- **Theorem 17.2.2** (MT p. 430), the LIL part: let `α ∋ a` be a recurrent atom, `μ` an
initial law from which `α` is reached a.s., and suppose the moment condition (17.14). Then
`P_μ`-a.s. `Sₙ(ḡ)`, `ḡ = g − π(g)`, obeys the LIL with constant `γ_g = √(cltVariance P α a g)`:
`limsup Sₙ(ḡ)/√(2 n log log n) = γ_g` and `liminf = −γ_g` (in the `ε`-form `HasLIL`). The case
`γ_g = 0` is included. The proof is the book's: the i.i.d. LIL for the cycle sums, the
random-index step for `ℓₙ` (`ℓₙ/n → 1/m`), and the `o(√n)` remainder (17.15). -/
theorem theorem_17_2_2_lil (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a)) :
    ∀ᵐ ω ∂pathMeasure P μ, HasLIL (fun n => pathSum (fun x => g x - atomMean P α a g) n ω)
      (√(cltVariance P α a g)) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isProbabilityMeasure_cycleLaw P α a
  have hν := ae_firstHit_ne_top_of_hitProb P hα.1 hrec
  set c := atomMean P α a g with hc
  set gb : X → ℝ := fun x => g x - c with hgb
  have hgbm : Measurable gb := hgm.sub measurable_const
  set m := cycleMeanLength P α a with hmdef
  have hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a) :=
    hL2.integrable one_le_two
  have hm1 : 1 ≤ m := one_le_cycleMeanLength P α a hL
  have hm0 : 0 < m := by linarith
  -- the i.i.d. cycle sums
  set φ := cycleSum α gb with hφ
  have hφm : Measurable φ := measurable_cycleSum hα.1 hgbm
  have hφ2 : MemLp φ 2 (cycleLaw P α a) := memLp_cycleSum_centred P hα.1 a hgm hg2 hL2 c
  have hg1 : Integrable (cycleSum α g) (cycleLaw P α a) :=
    integrable_cycleSum_of_abs hα.1 hgm (hg2.integrable one_le_two)
  have hφ0 : ∫ e, φ e ∂cycleLaw P α a = 0 := integral_cycleSum_centred P α a hg1 hL
  set Y : ℕ → (ℕ → X) → ℝ := fun j ω => φ (cycle α (j + 1) ω) with hYdef
  have hYm : ∀ j, Measurable (Y j) := fun j => hφm.comp (measurable_cycle hα.1 (j + 1))
  have hind : iIndepFun Y (pathMeasure P μ) := iIndepFun_cycles P hα ha hν μ hμ hφm
  have hident : ∀ j, IdentDistrib (Y j) (Y 0) (pathMeasure P μ) (pathMeasure P μ) :=
    identDistrib_cycles P hα ha hν μ hμ hφm
  have hY0 : IdentDistrib (Y 0) φ (pathMeasure P μ) (cycleLaw P α a) :=
    ⟨(hYm 0).aemeasurable, hφm.aemeasurable, map_cycle_eq P hα ha hν μ hμ hφm 0⟩
  have hY02 : MemLp (Y 0) 2 (pathMeasure P μ) := hY0.memLp_iff.2 hφ2
  have hY0mean : ∫ ω, Y 0 ω ∂pathMeasure P μ = 0 := hY0.integral_eq.trans hφ0
  have hσ2 : ∫ ω, Y 0 ω ^ 2 ∂pathMeasure P μ = ∫ e, φ e ^ 2 ∂cycleLaw P α a :=
    (hY0.comp (measurable_id.pow_const 2)).integral_eq
  have hγ : cltVariance P α a g = (∫ e, φ e ^ 2 ∂cycleLaw P α a) / m := rfl
  -- the LIL for the cycle sums, along `ℓₙ`, and the remainder
  have hiid := hasLIL_iid hind hYm hident hY02 hY0mean
  have hK := tendsto_cycleCount_div P hα ha hrec μ hμ hL
  have hR := tendsto_pathSum_sub_cycles P hα ha hrec μ hμ hgm hg2 hL2 c
  filter_upwards [hiid, hK, hR] with ω h1 h2 h3
  have h4 := h1.comp_index (Real.sqrt_nonneg _) (fun n => cycleCount_succ_le α n ω)
    (by positivity) h2
  have heq : √(1 / m) * √(∫ ω, Y 0 ω ^ 2 ∂pathMeasure P μ) = √(cltVariance P α a g) := by
    rw [hσ2, hγ, ← Real.sqrt_mul (by positivity), one_div_mul_eq_div]
  rw [heq] at h4
  exact h4.of_tendsto_sub (tendsto_div_lilScale_of_sqrt h3)

/-- **Theorem 17.2.2**, the LIL from every initial state (MT p. 430): for a Harris chain with an
accessible atom `α ∋ a` and the moment condition (17.14), `Sₙ(ḡ)` obeys the LIL with constant
`√(cltVariance P α a g)`, `P_x`-a.s., for every `x`. -/
theorem theorem_17_2_2_harris_lil [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {α : Set X}
    (hacc : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a)) (x : X) :
    ∀ᵐ ω ∂pathMeasure P (Measure.dirac x),
      HasLIL (fun n => pathSum (fun x => g x - atomMean P α a g) n ω)
        (√(cltVariance P α a g)) := by
  have hhit : ∀ y, hitProb P α y = 1 := fun y =>
    le_antisymm (hitProb_le_one P α y) (by
      rw [← theorem_9_1_4 hH hacc.1.1 hacc.2.2 y]; exact harrisQ_le_hitProb P α y)
  refine theorem_17_2_2_lil P hacc.1 ha (hhit a) (Measure.dirac x) ?_ hgm hg2 hL2
  rw [pathMeasure_dirac]
  exact ae_firstHit_ne_top_of_hitProb_eq_one P hacc.1.1 (hhit x)

/-! ### Theorem 17.3.6: the LIL -/

/-- **Theorem 17.3.6** (MT p. 441), the LIL part, for `m = 1`: for a positive Harris chain with a
minorization on `C ∈ B⁺(X)` and invariant probability `π`, if the split chain satisfies the moment
condition (17.31), then under every initial law `μ`, `P_μ`-a.s., `Sₙ(g − π(g))` obeys the LIL
with constant `γ_g = √(cltVariance)`, `γ_g²` given by (17.32) (`atomMean_split_eq`), the same
constant as in the CLT `theorem_17_3_6`. -/
theorem theorem_17_3_6_lil [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (M : Minorization P)
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {a : X × Bool} (ha : a ∈ M.checkAlpha) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (cycleSum M.checkAlpha fun z => |g z.1|) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    (hL2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (fun e => (hitNat M.checkAlpha e : ℝ) + 1) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := M.isMarkovKernel_splitKernel
    ∀ᵐ ω ∂pathMeasure P μ, HasLIL (fun n => pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      (√(cltVariance M.splitKernel M.checkAlpha a fun z => g z.1)) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  have := isProbabilityMeasure_cycleLaw M.splitKernel M.checkAlpha a
  obtain ⟨hμ, -⟩ := ae_firstHit_split hph.1 M hψC μ
  have hLs := M.hitProb_checkAlpha_eq_one (hph.1.hitProb_eq_one M.measurableSet_C hψC)
  have h := theorem_17_2_2_lil M.splitKernel M.isAtom_checkAlpha ha (hLs a) (M.split μ) hμ
    (g := fun z : X × Bool => g z.1) (hgm.comp measurable_fst) hg2 hL2
  rw [(atomMean_split_eq hph M hψC hπ ha hgm (hg2.integrable one_le_two)
    (hL2.integrable one_le_two)).1] at h
  refine ae_of_split M μ (E := {ω | HasLIL (fun n => pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
    (√(cltVariance M.splitKernel M.checkAlpha a fun z => g z.1))})
    (measurableSet_hasLIL (fun n => measurable_pathSum (hgm.sub measurable_const) n) _) ?_
  filter_upwards [h] with ω hω
  exact hω

/-! ### Theorem 17.0.1 (iv): the LIL for strongly aperiodic `V`-uniformly ergodic chains -/

/-- Limits in distribution are unique: if `Wₙ ⇒ N(0, v₁)` and `Wₙ ⇒ N(0, v₂)`, then `v₁ = v₂`. -/
theorem eq_of_tendstoInDistribution_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {Q₁ Q₂ : Measure Ω} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂] (hQ : Q₁ = Q₂)
    {W : ℕ → Ω → ℝ} {v₁ v₂ : NNReal}
    (h₁ : TendstoInDistribution W atTop id (fun _ => Q₁) (gaussianReal 0 v₁))
    (h₂ : TendstoInDistribution W atTop id (fun _ => Q₂) (gaussianReal 0 v₂)) : v₁ = v₂ := by
  subst hQ
  have h := tendsto_nhds_unique h₁.tendsto h₂.tendsto
  have h' : gaussianReal 0 v₁ = gaussianReal 0 v₂ := by
    have := congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ)) h
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using this
  have hv : (v₁ : ℝ) = v₂ := by
    rw [← variance_id_gaussianReal (μ := 0) (v := v₁), h', variance_id_gaussianReal]
  exact NNReal.coe_injective hv

/-- **Theorem 17.0.1** (iv), the LIL (MT p. 422), for chains with a one-step minorization: under
the hypotheses of Theorem 17.0.1 (ii) (aperiodic, (V4) for a petite set, `g² ≤ V`), if moreover
`P` has a minorization on a set `C ∈ B⁺(X)` whose split chain satisfies the moment condition
(17.31), then (a) the split-chain variance (17.32) equals the series (17.3),
`cltVariance = asymptoticVariance P π g`, and (b) from every initial state, `Sₙ(ḡ)` obeys the LIL
with constant `γ_g = √(asymptoticVariance P π g)`. The variance identity (a) comes from the
uniqueness of limits in distribution, comparing the CLTs `theorem_17_3_6` and
`theorem_17_0_1_iv`. -/
theorem theorem_17_0_1_iv_lil [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ)
    {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞)
    {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g) (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x)
    (M : Minorization P) (hψC : 0 < ψ M.C) {a : X × Bool} (ha : a ∈ M.checkAlpha)
    (hg2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (cycleSum M.checkAlpha fun z => |g z.1|) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    (hL2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (fun e => (hitNat M.checkAlpha e : ℝ) + 1) 2
        (cycleLaw M.splitKernel M.checkAlpha a)) :
    haveI := M.isMarkovKernel_splitKernel
    cltVariance M.splitKernel M.checkAlpha a (fun z => g z.1) = asymptoticVariance P π g ∧
    ∀ x, ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(asymptoticVariance P π g)) := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_cycleLaw M.splitKernel M.checkAlpha a
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at this
    exact zero_ne_one this
  have hvar1 := cltVariance_nonneg M.splitKernel M.checkAlpha a (fun z => g z.1)
    (hL2.integrable one_le_two)
  have hvar2 := ((theorem_17_0_1 hph hπ).2 hap hV hV1 hVfin hρ hb hC h g hgm hg).2.1
  -- the two CLTs along the same sequence
  have hclt1 := theorem_17_3_6 hph M hψC hπ ha hgm hg2 hL2 (Z := id) HasLaw.id
    (Measure.dirac x₀)
  have hclt2 := theorem_17_0_1_iv hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg (Z := id)
    HasLaw.id x₀
  have := isProbabilityMeasure_pathMeasure P (Measure.dirac x₀)
  have heq := eq_of_tendstoInDistribution_gaussianReal (pathMeasure_dirac P x₀) hclt1 hclt2
  have hvar : cltVariance M.splitKernel M.checkAlpha a (fun z => g z.1) =
      asymptoticVariance P π g := by
    have := congrArg (fun v : NNReal => (v : ℝ)) heq
    simpa only [Real.coe_toNNReal _ hvar1, Real.coe_toNNReal _ hvar2] using this
  refine ⟨hvar, fun x => ?_⟩
  have hlil := theorem_17_3_6_lil hph M hψC hπ ha hgm hg2 hL2 (Measure.dirac x)
  rw [pathMeasure_dirac, hvar] at hlil
  exact hlil

/-- **Theorem 17.5.3**, the LIL (MT p. 452, "the CLT and LIL hold"), for chains with a one-step
minorization: under the CLT moment condition of `theorem_17_5_3_clt` and `|g| ≤ f`, if moreover
`P` has a minorization on a set `C' ∈ B⁺(X)` whose split chain satisfies (17.31), then the
split-chain variance (17.32) equals `γ_g² = π(ĝ² − (Pĝ)²)`, and from every initial state `Sₙ(ḡ)`
obeys the LIL with constant `γ_g`. -/
theorem theorem_17_5_3_lil [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞}
    {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞)
    (hdrift : DriftV3 P V f b C) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x)
    (M : Minorization P) (hψC : 0 < ψ M.C) {a : X × Bool} (ha : a ∈ M.checkAlpha)
    (hg2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (cycleSum M.checkAlpha fun z => |g z.1|) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    (hL2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (fun e => (hitNat M.checkAlpha e : ℝ) + 1) 2
        (cycleLaw M.splitKernel M.checkAlpha a)) :
    haveI := M.isMarkovKernel_splitKernel
    cltVariance M.splitKernel M.checkAlpha a (fun z => g z.1) =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π ∧
    ∀ x, ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_cycleLaw M.splitKernel M.checkAlpha a
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at this
    exact zero_ne_one this
  have hvar1 := cltVariance_nonneg M.splitKernel M.checkAlpha a (fun z => g z.1)
    (hL2.integrable one_le_two)
  have hvar2 := (theorem_17_5_3 hph.1.1 hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 hgm
    hgf).2.2.1
  have hclt1 := theorem_17_3_6 hph M hψC hπ ha hgm hg2 hL2 (Z := id) HasLaw.id
    (Measure.dirac x₀)
  have hclt2 := theorem_17_5_3_clt hph hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 hgm hgf
    (Z := id) HasLaw.id x₀
  have := isProbabilityMeasure_pathMeasure P (Measure.dirac x₀)
  have heq := eq_of_tendstoInDistribution_gaussianReal (pathMeasure_dirac P x₀) hclt1 hclt2
  have hvar : cltVariance M.splitKernel M.checkAlpha a (fun z => g z.1) =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := by
    have := congrArg (fun v : NNReal => (v : ℝ)) heq
    simpa only [Real.coe_toNNReal _ hvar1, Real.coe_toNNReal _ hvar2] using this
  refine ⟨hvar, fun x => ?_⟩
  have hlil := theorem_17_3_6_lil hph M hψC hπ ha hgm hg2 hL2 (Measure.dirac x)
  rw [pathMeasure_dirac, hvar] at hlil
  exact hlil

end MeynTweedie.LimitTheorems
