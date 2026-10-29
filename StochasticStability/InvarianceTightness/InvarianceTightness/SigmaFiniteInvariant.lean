/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.GeneralizedSampling
import InvarianceTightness.SupermartingaleDrift

/-!
# The existence of a σ-finite invariant measure (MT §12.3)

Meyn and Tweedie, §12.3, pp. 298–300. `X` is a locally compact, second-countable, metrizable
Hausdorff space with its Borel σ-algebra.

**The smoothed chain** (§12.3.1).
* `lowerSemicontinuous_mul_of_continuous`, `IsWeakFeller.lsc_killOp`: `P I_w` preserves lower
  semicontinuity for continuous finite `w ≥ 0` and weak Feller `P`.
* **Proposition 12.3.1** (`proposition_12_3_1`, p. 298): for continuous `h`, `P_h = U_h I_h` is
  weak Feller (and a transition kernel when `L ≡ 1`, `isMarkovKernel_balayage`).
* `isBoundedInProbabilityOnAverage_of_forall`: a kernel with `Q(x, K) = 1` for a compact `K` is
  bounded in probability on average.
* **Theorem 12.3.2** (`theorem_12_3_2`, p. 299): if `L(x, C) ≡ 1` (12.19) for a compact `C`, a
  weak Feller chain has a nonzero invariant measure finite on compact sets.

**Drift criteria** (§12.3.2).
* **Theorem 12.3.3** (`theorem_12_3_3`, p. 299): (V1) off a compact set, with `V` coercive, gives
  a nonzero invariant measure finite on compact sets; `le_cesaroKernel_of_forall`.
* **Theorem 12.3.4** (`theorem_12_3_4`, p. 299): (V2) with a compact `C` and `V(x₀) < ∞` gives an
  invariant probability; `lintegral_pow_add_le_of_V2` is the iteration
  `Pⁿ V(x) + n ≤ V(x) + b Σ_{k<n} Pᵏ(x, C)` behind (12.21). `eventually_le_cesaroKernel_of_V2`
  is its consequence `P̄ⁿ(x₀, C) ≥ (2b)⁻¹` for large `n`; `V2_coe_ne_zero`: (V2) with
  `V(x₀) < ∞` forces `b ≠ 0`.

**Corrections.**
* Theorem 12.3.3 is stated for (V1) without conditions on `V`, but its proof applies
  Theorem 12.1.2 to the sets `{V ≤ r}`, which needs them precompact. Without coercivity it
  fails: `theorem_12_3_3_counterexample` (the successor chain on `ℕ`, `V ≡ 0`, `C = ∅`; its only
  invariant measure is `0`). It is proved for coercive `V`, the setting of Theorem 9.4.1.
* The invariant measures of Theorems 12.3.2 and 12.3.3 are asserted nonzero here (the zero
  measure is trivially invariant and finite on compact sets).

**Hypotheses.** (V2) is written `∫ V dP(x) + 1 ≤ V(x) + b 1_C(x)` in `[0, ∞]`. Theorems 12.3.2
and 12.3.3 assume `X` nonempty.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

variable {X : Type*} [MeasurableSpace X]

/-! ### Proposition 12.3.1 -/

omit [MeasurableSpace X] in
/-- The product of a continuous finite `w ≥ 0` and a lower semicontinuous `u ≥ 0` is lower
semicontinuous. -/
theorem lowerSemicontinuous_mul_of_continuous [TopologicalSpace X] {w u : X → ℝ≥0∞}
    (hw : Continuous w) (hwt : ∀ x, w x ≠ ∞) (hu : LowerSemicontinuous u) :
    LowerSemicontinuous fun x => w x * u x := by
  intro x c hc
  change c < w x * u x at hc
  have hux : u x ≠ 0 := fun h0 => by rw [h0, mul_zero] at hc; exact not_lt_zero hc
  -- choose `b < u x` with `c < w x * b`
  have hS : IsOpen {b : ℝ≥0∞ | c < w x * b} :=
    isOpen_lt continuous_const (ENNReal.continuous_const_mul (hwt x))
  obtain ⟨l, hl, hlS⟩ := exists_Ioc_subset_of_mem_nhds (hS.mem_nhds hc) ⟨0, pos_iff_ne_zero.2 hux⟩
  obtain ⟨b, hlb, hbu⟩ := exists_between hl
  have hbS : c < w x * b := hlS ⟨hlb, hbu.le⟩
  have hbt : b ≠ ∞ := ne_top_of_lt hbu
  have hT : ∀ᶠ y in 𝓝 x, c < w y * b :=
    ((ENNReal.continuous_mul_const hbt).comp hw).continuousAt.eventually (lt_mem_nhds hbS)
  filter_upwards [hT, hu x b hbu] with y h1 h2
  exact h1.trans_le (by gcongr)


variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller `P` and a continuous `0 ≤ w < ∞`, `P I_w` maps lower semicontinuous
functions to lower semicontinuous functions. -/
theorem IsWeakFeller.lsc_killOp {P : Kernel X X} (hP : IsWeakFeller P) {w : X → ℝ≥0∞}
    (hw : Continuous w) (hwt : ∀ x, w x ≠ ∞) {u : X → ℝ≥0∞} (hu : LowerSemicontinuous u) :
    LowerSemicontinuous (killOp P w u) :=
  hP.lowerSemicontinuous_lintegral (lowerSemicontinuous_mul_of_continuous hw hwt hu)

variable [TopologicalSpace X] [BorelSpace X] [FirstCountableTopology X] in
/-- **Proposition 12.3.1** (MT p. 298): if `P` is weak Feller and `0 ≤ h ≤ 1` is continuous, then
`P_h = U_h I_h` is weak Feller: `P_h(x, O) = Σₖ (P I_{1−h})ᵏ P(h 1_O)(x)` is a sum of lower
semicontinuous functions. (With `L ≡ 1`, e.g. `Q ≡ 1`, `P_h` is moreover a transition kernel,
`isMarkovKernel_balayage`.) -/
theorem proposition_12_3_1 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {h : X → ℝ≥0∞} (hh : Continuous h) : IsWeakFeller (balayage P h) := by
  have hhm : Measurable h := hh.measurable
  have hw : Continuous (1 - h) := (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp hh
  have hwt : ∀ x, (1 - h) x ≠ ∞ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  intro O hO
  have heq : (fun x => balayage P h x O) =
      fun x => ∑' k, (killOp P (1 - h))^[k] (kfun P (O.indicator h)) x := by
    ext x
    rw [← lintegral_indicator_one hO.measurableSet,
      lintegral_genPotDensity P h hhm x (measurable_one.indicator hO.measurableSet)]
    have : (fun y => h y * O.indicator 1 y) = O.indicator h := by
      ext y; by_cases hy : y ∈ O <;> simp [hy]
    rw [this, lintegral_genPotKernel P hhm x (hhm.indicator hO.measurableSet)]
    rfl
  rw [heq]
  refine lowerSemicontinuous_tsum fun k => ?_
  have hbase : LowerSemicontinuous (kfun P (O.indicator h)) :=
    hP.lowerSemicontinuous_lintegral
      (lowerSemicontinuous_indicator_of_isOpen hO hh.lowerSemicontinuous)
  induction k with
  | zero => exact hbase
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hP.lsc_killOp hw hwt ih


/-! ### Theorem 12.3.2 -/

/-- For a transition kernel `Q` with `Q(x, K) = 1` for every `x`, `Qⁱ(x, K) = 1` for `i ≥ 1`. -/
theorem pow_apply_eq_one_of_forall (Q : Kernel X X) [IsMarkovKernel Q] {K : Set X}
    (hK : MeasurableSet K) (hQ : ∀ x, Q x K = 1) (i : ℕ) (x : X) : (Q ^ (i + 1)) x K = 1 := by
  have := isMarkovKernel_pow Q i
  rw [pow_succ_apply' Q i x hK]
  simp_rw [hQ]
  simp

/-- A kernel concentrated on a compact set `K` is bounded in probability on average. -/
theorem isBoundedInProbabilityOnAverage_of_forall [TopologicalSpace X] (Q : Kernel X X)
    [IsMarkovKernel Q] {K : Set X} (hK : IsCompact K) (hKm : MeasurableSet K)
    (hQ : ∀ x, Q x K = 1) : IsBoundedInProbabilityOnAverage Q := by
  intro x ε _
  refine ⟨K, hK, le_trans tsub_le_self (le_liminf_of_le (by isBoundedDefault)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩))⟩
  rw [cesaroKernel_apply Q n x hKm]
  have h1 : ∀ i ∈ Finset.Icc 1 n, (Q ^ i) x K = 1 := fun i hi => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := (Finset.mem_Icc.1 hi).1; omega⟩
    exact pow_apply_eq_one_of_forall Q hKm hQ j x
  have : ∑ i ∈ Finset.Icc 1 n, (Q ^ i) x K = n := by
    rw [Finset.sum_congr rfl h1]
    simp
  rw [this, ENNReal.inv_mul_cancel (by simp; omega) (by simp)]

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]

/-- **Theorem 12.3.2** (MT p. 299): for a weak Feller chain with a compact `C` that is reached
from every state, `L(x, C) ≡ 1` (12.19), there is a nonzero invariant measure that is finite on
compact sets. A Urysohn function `1_C ≤ h ≤ 1` with compact support makes `P_h` a weak Feller
transition kernel concentrated on `supp h` (Proposition 12.3.1); Theorem 12.1.2 gives it an
invariant probability `ν`, and `μ = νU_h` is the required measure (Theorem 12.2.3 (ii)): it is
finite on the open sets `{K_{1/2}(·, h) > ε}`, which cover `X`. -/
theorem theorem_12_3_2 [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {C : Set X} (hC : IsCompact C) (hL : ∀ x, hitProb P C x = 1) :
    ∃ μ : Measure X, μ ≠ 0 ∧ IsInvariant P μ ∧ ∀ K, IsCompact K → μ K < ∞ := by
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
  set h : X → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  have hhc : Continuous h := ENNReal.continuous_ofReal.comp f.continuous
  have hhm : Measurable h := hhc.measurable
  have h1 : h ≤ 1 := fun x => ENNReal.ofReal_le_one.2 (hf01 x).2
  have hCh : C.indicator 1 ≤ h := fun x => by
    by_cases hx : x ∈ C
    · have := hfC x
      rw [indicator_of_mem hx, Pi.one_apply] at this ⊢
      exact ENNReal.one_le_ofReal.2 this
    · rw [indicator_of_notMem hx]; exact zero_le
  have hL' : ∀ x, genL P h x = 1 := fun x => le_antisymm (genL_le_one P hhm h1 x) (by
    rw [← hL x, ← genL_indicator P hC.measurableSet]
    exact genL_mono P (measurable_one.indicator hC.measurableSet) hhm hCh h1 x)
  have hM := isMarkovKernel_balayage P hhm hL'
  have hF := proposition_12_3_1 hP hhc
  -- `P_h` lives on the support of `h`
  set K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  have hKm : MeasurableSet K := hK.measurableSet
  have hPK : ∀ x, balayage P h x K = 1 := fun x => by
    have hzero : balayage P h x Kᶜ = 0 := by
      rw [← lintegral_indicator_one hKm.compl,
        lintegral_genPotDensity P h hhm x (measurable_one.indicator hKm.compl)]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      by_cases hy : y ∈ K
      · rw [indicator_of_notMem (show y ∉ Kᶜ from fun h' => h' hy), mul_zero]
      · simp [h, image_eq_zero_of_notMem_tsupport hy]
    have hc := prob_compl_eq_one_sub (μ := balayage P h x) hKm
    rw [hzero] at hc
    exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 hc.symm)
  have hb := isBoundedInProbabilityOnAverage_of_forall _ hK hKm hPK
  obtain ⟨ν, hνp, hνinv⟩ := theorem_12_1_2_ii hF hb
  obtain ⟨hinv, hbound, hcover⟩ := theorem_12_2_3_ii P hhm h1 hνinv
  refine ⟨genPotKernel P h ∘ₘ ν, fun h0 => ?_, hinv, fun K' hK' => ?_⟩
  · have hint : ∫⁻ y, h y ∂(genPotKernel P h ∘ₘ ν) = 1 := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hhm.aemeasurable]
      change ∫⁻ x, genL P h x ∂ν = 1
      simp_rw [hL']
      simp
    rw [h0, lintegral_zero_measure] at hint
    exact zero_ne_one hint
  · set g := resolventH P h
    have hg : LowerSemicontinuous g :=
      (hP.isWeakFeller_sampledKernel _).lowerSemicontinuous_lintegral hhc.lowerSemicontinuous
    have hpos : ∀ x, 0 < g x := hcover fun x => by rw [hL' x]; exact one_ne_zero
    set U : ℕ → Set X := fun n => g ⁻¹' Ioi ((n + 1 : ℝ≥0∞)⁻¹)
    have hUo : ∀ n, IsOpen (U n) := fun n => hg.isOpen_preimage _
    have hUcov : K' ⊆ ⋃ n, U n := fun x _ => by
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x).ne'
      refine mem_iUnion.2 ⟨n, lt_of_le_of_lt ?_ hn⟩
      exact ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ n)
    have hdir : Directed (· ⊆ ·) U := Monotone.directed_le fun m n hmn x hx =>
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.succ_le_succ hmn)) hx
    obtain ⟨n, hn⟩ := hK'.elim_directed_cover U hUo hUcov hdir
    have hS : K' ⊆ {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ g x} := fun x hx =>
      (show (n + 1 : ℝ≥0∞)⁻¹ < g x from hn hx).le
    have h2 := hbound ((n + 1 : ℝ≥0∞)⁻¹)
    rw [measure_univ] at h2
    calc (genPotKernel P h ∘ₘ ν) K' ≤ (genPotKernel P h ∘ₘ ν) {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ g x} :=
          measure_mono hS
      _ ≤ 1 / (n + 1 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.le_div_iff_mul_le (b := (n + 1 : ℝ≥0∞)⁻¹) (Or.inl (by simp))
            (Or.inl (by simp)), mul_comm]
          exact h2
      _ < ∞ := by simp


/-! ### Drift criteria: Theorems 12.3.3 and 12.3.4 -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- If `Pᵏ(x, D) ≥ δ` for every `k`, then `P̄ⁿ(x, D) ≥ δ` for every `n ≥ 1`. -/
theorem le_cesaroKernel_of_forall {P : Kernel X X} {D : Set X} (hD : MeasurableSet D) {x : X}
    {δ : ℝ≥0∞} (h : ∀ k, δ ≤ (P ^ k) x D) {n : ℕ} (hn : 1 ≤ n) : δ ≤ cesaroKernel P n x D := by
  rw [cesaroKernel_apply P n x hD]
  have hsum : (n : ℝ≥0∞) * δ ≤ ∑ i ∈ Finset.Icc 1 n, (P ^ i) x D := by
    calc (n : ℝ≥0∞) * δ = ∑ _i ∈ Finset.Icc 1 n, δ := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => h i
  calc δ = (n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * δ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp; omega) (by simp), one_mul]
    _ ≤ _ := by gcongr

/-- **Theorem 12.3.3** (MT p. 299), with `V` coercive: for a weak Feller chain satisfying (V1),
`∫ V dP(x) ≤ V(x)` off a compact `C`, with `V` coercive, there is a nonzero invariant measure
finite on compact sets. If `L(·, C) ≡ 1` this is Theorem 12.3.2; otherwise some `y ∉ C` has
`P_y(Φ never enters C) > 0`, on that event `V(Φₖ)` stays bounded (the supermartingale of
Theorem 9.4.1), so `Pᵏ(y, {V ≤ n}) ≥ δ > 0` for all `k`, and Theorem 12.1.2 gives an invariant
probability. Without coercivity the theorem fails: `theorem_12_3_3_counterexample`. -/
theorem theorem_12_3_3 [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V) {C : Set X} (hC : IsCompact C)
    (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x) :
    ∃ μ : Measure X, μ ≠ 0 ∧ IsInvariant P μ ∧ ∀ K, IsCompact K → μ K < ∞ := by
  by_cases hall : ∀ x, hitProb P C x = 1
  · exact theorem_12_3_2 hP hC hall
  have hCm := hC.measurableSet
  have := isMarkovKernel_pathKernel P
  -- a state outside `C` from which `C` is missed with positive probability
  obtain ⟨y, hyC, hy⟩ : ∃ y ∉ C, hitProb P C y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hall fun x => ?_
    rw [hitProb_first_step P hCm x, setLIntegral_congr_fun hCm.compl fun z hz => hcon z hz,
      setLIntegral_const, one_mul, measure_add_measure_compl hCm, measure_univ]
  set Av := {ω : ℕ → X | ∀ i, ω i ∉ C}
  have hAvm : MeasurableSet Av := by
    have : Av = ⋂ i, {ω : ℕ → X | ω i ∈ Cᶜ} := by ext ω; simp [Av]
    rw [this]; exact MeasurableSet.iInter fun i => measurable_pi_apply i hCm.compl
  have hAv : 0 < pathKernel P y Av := by
    have hc : Av = {ω : ℕ → X | ∃ n, ω n ∈ C}ᶜ := by ext ω; simp [Av]
    have hm : MeasurableSet {ω : ℕ → X | ∃ n, ω n ∈ C} := by
      have : {ω : ℕ → X | ∃ n, ω n ∈ C} = ⋃ n, {ω : ℕ → X | ω n ∈ C} := by ext ω; simp
      rw [this]; exact MeasurableSet.iUnion fun n => measurable_pi_apply n hCm
    rw [hc, prob_compl_eq_one_sub hm, ← hitProbZero_eq_exists, hitProbZero_of_notMem P hCm hyC]
    exact tsub_pos_of_lt (lt_of_le_of_ne (by
      have := isMarkovKernel_pathKernel P; exact prob_le_one) hy)
  have hbdd := ae_bddAbove_of_avoid P (Measure.dirac y) hVm hCm hdrift
    (by rw [lintegral_dirac]; exact ENNReal.coe_ne_top)
  rw [pathMeasure_dirac] at hbdd
  set B : ℕ → Set (ℕ → X) := fun n => Av ∩ {ω | ∀ k, V (ω k) ≤ n}
  have hBm : ∀ n, MeasurableSet (B n) := fun n => by
    refine hAvm.inter ?_
    have : {ω : ℕ → X | ∀ k, V (ω k) ≤ n} = ⋂ k, {ω : ℕ → X | V (ω k) ≤ n} := by ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le (hVm.comp (measurable_pi_apply k)) measurable_const
  obtain ⟨n, hn⟩ : ∃ n, 0 < pathKernel P y (B n) := by
    by_contra hcon
    push Not at hcon
    have hnull : pathKernel P y (⋃ n, B n) = 0 :=
      measure_iUnion_null fun n => le_antisymm (hcon n) bot_le
    have hle : pathKernel P y Av ≤ pathKernel P y (⋃ n, B n) := by
      refine measure_mono_ae (hbdd.mono fun ω hω hωA => ?_)
      obtain ⟨r, hr⟩ := hω hωA
      obtain ⟨m, hm⟩ := exists_nat_ge r
      exact mem_iUnion.2 ⟨m, hωA, fun k => by
        have := (hr k).trans hm
        exact_mod_cast this⟩
    rw [hnull] at hle
    exact absurd hAv (not_lt.2 hle)
  set D := closure {x | V x ≤ n}
  have hDm : MeasurableSet D := isClosed_closure.measurableSet
  have hk : ∀ k, pathKernel P y (B n) ≤ (P ^ k) y D := fun k => by
    rw [← pathKernel_coord_mem P y k hDm]
    exact measure_mono fun ω hω => subset_closure (hω.2 k)
  obtain ⟨π, hπ, hπinv⟩ := exists_isInvariant_of_frequently hP (hV n) hn
    ((eventually_ge_atTop 1).mono fun m hm => le_cesaroKernel_of_forall hDm hk hm).frequently
  exact ⟨π, IsProbabilityMeasure.ne_zero π, hπinv, fun K _ => measure_lt_top π K⟩

/-- **Theorem 12.3.3 needs a coercive `V`** (MT p. 299). The successor chain on `ℕ` (discrete,
hence weak Feller) satisfies (V1) with `V ≡ 0` and the compact set `C = ∅`, but its only
invariant measure is `0`. (The book's proof uses coercivity of `V` when it invokes
Theorem 12.1.2.) -/
theorem theorem_12_3_3_counterexample :
    ∃ _ : IsMarkovKernel succKernel, IsWeakFeller succKernel ∧ IsCompact (∅ : Set ℕ) ∧
      (∀ x ∉ (∅ : Set ℕ), ∫⁻ _, ((0 : ℝ≥0) : ℝ≥0∞) ∂succKernel x ≤ ((0 : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ μ : Measure ℕ, IsInvariant succKernel μ → μ = 0 := by
  refine ⟨isMarkovKernel_succKernel, fun O _ => continuous_of_discreteTopology.lowerSemicontinuous,
    isCompact_empty, fun x _ => by simp, fun μ hμ => ?_⟩
  have hP : ∀ x A, succKernel x A = A.indicator 1 (x + 1) := fun x A => by
    have : succKernel x = Measure.dirac (x + 1) := Kernel.deterministic_apply _ _
    rw [this, Measure.dirac_apply' _ MeasurableSet.of_discrete]
  have hsing : ∀ n, μ {n} = 0 := by
    intro n
    induction n with
    | zero =>
      rw [← hμ, measure_kernel_apply _ _ MeasurableSet.of_discrete]
      simp [hP]
    | succ n ih =>
      rw [← hμ, measure_kernel_apply _ _ MeasurableSet.of_discrete]
      have : (fun x => succKernel x {n + 1}) = ({n} : Set ℕ).indicator 1 := by
        ext x; rw [hP]; by_cases hx : x = n <;> simp [hx]
      rw [this, lintegral_indicator_one MeasurableSet.of_discrete, ih]
  exact (Measure.ext_iff_singleton).2 fun n => by rw [hsing n]; rfl


omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- Iterating (V2), `PV + 1 ≤ V + b 1_C`: `Pⁿ V(x) + n ≤ V(x) + b Σ_{k<n} Pᵏ(x, C)`. -/
theorem lintegral_pow_add_le_of_V2 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞}
    (hVm : Measurable V) {C : Set X} (hC : MeasurableSet C) {b : ℝ≥0∞}
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) (x : X) (n : ℕ) :
    ∫⁻ y, V y ∂(P ^ n) x + n ≤ V x + b * ∑ k ∈ Finset.range n, (P ^ k) x C := by
  induction n with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ hVm]; simp
  | succ n ih =>
    have := isMarkovKernel_pow P n
    have hstep : ∫⁻ y, V y ∂(P ^ (n + 1)) x + 1 ≤ ∫⁻ y, V y ∂(P ^ n) x + b * (P ^ n) x C := by
      rw [show n + 1 = 1 + n by ring, Kernel.pow_add, pow_one, Kernel.lintegral_comp _ _ _ hVm]
      calc ∫⁻ z, ∫⁻ y, V y ∂P z ∂(P ^ n) x + 1
            = ∫⁻ z, (∫⁻ y, V y ∂P z + 1) ∂(P ^ n) x := by
              rw [lintegral_add_right _ measurable_const]; simp
        _ ≤ ∫⁻ z, (V z + b * C.indicator 1 z) ∂(P ^ n) x := lintegral_mono fun z => hV2 z
        _ = ∫⁻ y, V y ∂(P ^ n) x + b * (P ^ n) x C := by
            rw [lintegral_add_left hVm, lintegral_const_mul _ (measurable_one.indicator hC),
              lintegral_indicator_one hC]
    calc ∫⁻ y, V y ∂(P ^ (n + 1)) x + ((n + 1 : ℕ) : ℝ≥0∞)
        = (∫⁻ y, V y ∂(P ^ (n + 1)) x + 1) + n := by push_cast; ring
      _ ≤ (∫⁻ y, V y ∂(P ^ n) x + b * (P ^ n) x C) + n := by gcongr
      _ = (∫⁻ y, V y ∂(P ^ n) x + n) + b * (P ^ n) x C := by ring
      _ ≤ (V x + b * ∑ k ∈ Finset.range n, (P ^ k) x C) + b * (P ^ n) x C := by gcongr
      _ = V x + b * ∑ k ∈ Finset.range (n + 1), (P ^ k) x C := by
          rw [Finset.sum_range_succ, mul_add, add_assoc]


/-- `Σ_{k ≤ n} aₖ = a₀ + Σ_{k=1}^{n} aₖ`. -/
theorem sum_range_succ_eq_add_sum_Icc (a : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a k = a 0 + ∑ k ∈ Finset.Icc 1 n, a k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), add_assoc]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- **The lower bound (12.21)**: under (V2), `∫ V dP(x) + 1 ≤ V(x) + b 1_C(x)`, with `b ≠ 0` and
`V(x₀) < ∞`, `P̄ⁿ(x₀, C) ≥ 1/(2b)` for all large `n` (the book's `liminf ≥ 1/b`). Iterating (V2)
gives `n ≤ V(x₀) + b Σ_{k<n} Pᵏ(x₀, C)`. -/
theorem eventually_le_cesaroKernel_of_V2 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞}
    (hVm : Measurable V) {C : Set X} (hCm : MeasurableSet C) {b : ℝ≥0} (hb : b ≠ 0)
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    ∀ᶠ n in atTop, (2 * (b : ℝ≥0∞))⁻¹ ≤ cesaroKernel P n x₀ C := by
  have := isMarkovKernel_pow P
  set M : ℝ≥0∞ := V x₀ + b
  have hM : M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hx₀, ENNReal.coe_ne_top⟩
  have hn : ∀ n : ℕ, 1 ≤ n → (n : ℝ≥0∞) ≤ M + b * (n * cesaroKernel P n x₀ C) := by
    intro n hn1
    have h1 := lintegral_pow_add_le_of_V2 hVm hCm hV2 x₀ n
    have hsum : ∑ k ∈ Finset.range n, (P ^ k) x₀ C ≤ 1 + n * cesaroKernel P n x₀ C := by
      calc ∑ k ∈ Finset.range n, (P ^ k) x₀ C ≤ ∑ k ∈ Finset.range (n + 1), (P ^ k) x₀ C :=
            Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ n))
        _ = (P ^ 0) x₀ C + ∑ k ∈ Finset.Icc 1 n, (P ^ k) x₀ C :=
            sum_range_succ_eq_add_sum_Icc _ n
        _ ≤ 1 + n * cesaroKernel P n x₀ C := by
            rw [cesaroKernel_apply P n x₀ hCm, ← mul_assoc,
              ENNReal.mul_inv_cancel (by simp; omega) (by simp), one_mul]
            gcongr
            exact prob_le_one
    calc (n : ℝ≥0∞) ≤ ∫⁻ y, V y ∂(P ^ n) x₀ + n := le_add_self
      _ ≤ V x₀ + b * ∑ k ∈ Finset.range n, (P ^ k) x₀ C := h1
      _ ≤ V x₀ + b * (1 + n * cesaroKernel P n x₀ C) := by gcongr
      _ = M + b * (n * cesaroKernel P n x₀ C) := by rw [mul_add, mul_one, ← add_assoc]
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  set δ : ℝ≥0∞ := (2 * b)⁻¹
  have hbδ : (b : ℝ≥0∞) * δ = 2⁻¹ := by
    change (b : ℝ≥0∞) * (2 * (b : ℝ≥0∞))⁻¹ = 2⁻¹
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_comm (2⁻¹ : ℝ≥0∞),
      ← mul_assoc, ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top, one_mul]
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top (by simp) hM : 2 * M ≠ ∞)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hnN
  by_contra hlt
  push Not at hlt
  have h2 : (b : ℝ≥0∞) * (n * cesaroKernel P n x₀ C) ≤ n * 2⁻¹ :=
    calc (b : ℝ≥0∞) * (n * cesaroKernel P n x₀ C) ≤ b * (n * δ) := by gcongr
      _ = n * (b * δ) := by ring
      _ = n * 2⁻¹ := by rw [hbδ]
  have h3 : (n : ℝ≥0∞) ≤ M + n * 2⁻¹ := (hn n (by omega)).trans (by gcongr)
  have h4 : (n : ℝ≥0∞) * 2⁻¹ + n * 2⁻¹ ≤ M + n * 2⁻¹ := by
    rw [← div_eq_mul_inv, ENNReal.add_halves]; exact h3
  have hfin : (n : ℝ≥0∞) * 2⁻¹ ≠ ∞ := ENNReal.mul_ne_top (by simp) (by simp)
  have h5 : (n : ℝ≥0∞) * 2⁻¹ ≤ M := (ENNReal.add_le_add_iff_right hfin).1 h4
  have h6 : (n : ℝ≥0∞) ≤ 2 * M := by
    calc (n : ℝ≥0∞) = 2 * ((n : ℝ≥0∞) * 2⁻¹) := by
          rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            mul_one]
      _ ≤ 2 * M := by gcongr
  have h7 : (N : ℝ≥0∞) < n := by exact_mod_cast Nat.lt_of_succ_le hnN
  exact absurd (h6.trans_lt hN) (not_lt.2 h7.le)

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- (V2) with `b = 0` is inconsistent when `V(x₀) < ∞`: `n ≤ V(x₀)` for every `n`. -/
theorem V2_coe_ne_zero {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞}
    (hVm : Measurable V) {C : Set X} (hCm : MeasurableSet C) {b : ℝ≥0}
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    b ≠ 0 := by
  intro hb
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx₀
  have h1 := lintegral_pow_add_le_of_V2 hVm hCm hV2 x₀ N
  simp only [hb, ENNReal.coe_zero, zero_mul, add_zero] at h1
  exact absurd (le_add_self.trans h1) (not_le.2 hN)

/-- **Theorem 12.3.4** (MT p. 299): for a weak Feller chain satisfying the drift condition (V2),
`∫ V dP(x) + 1 ≤ V(x) + b 1_C(x)` with `C` compact and `V(x₀) < ∞` for one `x₀`, an invariant
probability exists. Iterating (V2) gives `n ≤ V(x₀) + b Σ_{k<n} Pᵏ(x₀, C)`, so
`P̄ⁿ(x₀, C) ≥ 1/(2b)` for large `n` (12.21), and Theorem 12.1.2 (i) applies. -/
theorem theorem_12_3_4 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {V : X → ℝ≥0∞} (hVm : Measurable V) {C : Set X} (hC : IsCompact C) {b : ℝ≥0}
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  have hb := V2_coe_ne_zero hVm hC.measurableSet hV2 hx₀
  have hδ : (0 : ℝ≥0∞) < (2 * (b : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top)
  exact exists_isInvariant_of_frequently hP hC (x := x₀) hδ
    (eventually_le_cesaroKernel_of_V2 hVm hC.measurableSet hb hV2 hx₀).frequently

end MeynTweedie.InvarianceTightness
