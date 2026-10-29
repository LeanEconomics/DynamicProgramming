/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SkeletonCycles

/-!
# Limit theorems through a split `m`-skeleton (MT §17.3, Theorems 17.3.2 and 17.3.6)

Meyn and Tweedie, pp. 436 and 440–443, for a general `m`: a minorization
`M : Minorization (P ^ m)` of the `m`-skeleton on `C ∈ B⁺(X)` (which exists for every
`ψ`-irreducible chain on a countably generated space, `theorem_5_2_3`), split as in
`SkeletonSplit` with the cycle sums of `SkeletonCycles`. These are the general-`m` versions of
`theorem_17_3_2` and `theorem_17_3_6` (`SplitLimitTheorems`, `m = 1`).

**Segments.** `countBelow T N` counts the completed segments `[T_j, T_{j+1})` of an increasing
sequence; `skelBound M j = T_j = m(σ_α̌(j)+1)`, `skelCount M N = ℓ_N` (MT p. 435);
`abs_skelPartialSum_sub_le` is (17.24)/(17.33) pathwise; `tendsto_countBelow_div` and
`skel_ae_tendsto_count_div` give (17.34), `ℓ_N/N → 1/Ě[s(1)] = δπ(C)/m`;
`skel_ae_tendsto_last_sq`: the last incomplete segment is `o(√N)`.

**Results.**
* **Theorem 17.3.2** (iii) ⇒ (i) (`theorem_17_3_2_general`, p. 436) for a general `m`: if the
  `m`-skeleton is Harris and `π` is invariant for `P` with `0 < π(C) < ∞` (finite or not), then
  `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every initial law, for `f, g ∈ L¹(π)`,
  `π(g) ≠ 0`; `skel_ae_tendsto_pathSum_div_count`: `Sₙ(h)/ℓₙ → δ⁻¹π(C)⁻¹ m π(h)`.
* `skelCLTVariance M π g`: the variance (17.32),
  `γ_g² = m⁻¹ π*(α̌) (Ě[s₀(ḡ)²] + 2 Ě[s₀(ḡ) s₁(ḡ)])`, `π*(α̌) = δπ(C)`, the expectations under
  the fresh law `P̌_{ν*}` (where the cycle sums `(s₋₁, s₀, …)` are stationary);
  `skelCLTVariance_nonneg`: `0 ≤ γ_g²`.
* **Theorem 17.3.6**, the CLT (`theorem_17_3_6_general`, p. 441) for a general `m`: for a Harris
  `m`-skeleton, an invariant probability `π` of `P` and the moment condition (17.31),
  `n^{−1/2} Sₙ(g − π(g)) ⇒ N(0, γ_g²)` under every initial law. No positivity of `γ_g²` is needed.
* **Theorem 17.3.6**, the LIL (`theorem_17_3_6_lil_general`, pp. 441–443) for a general `m`:
  under the same hypotheses `Sₙ(g − π(g))` obeys the LIL (`HasLIL` of `IIDLIL`) with the CLT
  constant `γ_g = √(skelCLTVariance M π g)`, from every initial law; from the LIL for stationary
  one-dependent sequences (`hasLIL_oneDependent`, `DependentLIL`), the random-index step
  `HasLIL.comp_index` (`countBelow_succ_le`: `ℓₙ` grows by at most one per step) and (17.33)
  (`skel_ae_tendsto_pathSum_sub_cycles`).
* `integrable_of_integrable_skelPreSum`: (17.31) implies `π(|g|) < ∞`.

**Hypotheses.** The book takes `Φ` ergodic and the split skeleton Harris (§17.3.1); here the
`m`-skeleton is assumed Harris (`IsHarris (P ^ m) ψ`), which is what the splitting uses, and
`ψ(C) > 0`. The book's (17.31) moment condition is stated under `P̌_{ν*}`, as here
(`skelFreshLaw`). `SkeletonErgodic` derives these hypotheses from the book's (an aperiodic Harris
chain, `exists_skeleton_split`), and `SkeletonMoment` derives (17.31) from the CLT moment
condition (Lemma 17.5.2 (ii)).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Counting the completed segments -/

/-- The number `#{j : T_{j+1} ≤ N}` of completed segments `[T_j, T_{j+1})` by time `N`. -/
def countBelow (T : ℕ → ℕ) (N : ℕ) : ℕ := ((Finset.range N).filter fun j => T (j + 1) ≤ N).card

/-- For strictly increasing `T`, `countBelow T N = j` when `T_j ≤ N < T_{j+1}`. -/
theorem countBelow_eq {T : ℕ → ℕ} (hT : StrictMono T) {N j : ℕ} (h1 : T j ≤ N)
    (h2 : N < T (j + 1)) : countBelow T N = j := by
  have hjN : j ≤ N := (show j ≤ T j from hT.id_le j).trans h1
  have : (Finset.range N).filter (fun i => T (i + 1) ≤ N) = Finset.range j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hi⟩
      by_contra hij
      push Not at hij
      have := hT.monotone (show j + 1 ≤ i + 1 by omega)
      omega
    · intro hi
      exact ⟨by omega, (hT.monotone (show i + 1 ≤ j by omega)).trans h1⟩
  rw [countBelow, this, Finset.card_range]

/-- `countBelow T N ≤ N`. -/
theorem countBelow_le (T : ℕ → ℕ) (N : ℕ) : countBelow T N ≤ N :=
  (Finset.card_filter_le _ _).trans (Finset.card_range N).le

/-- Every `N ≥ T₀` lies in a segment `[T_j, T_{j+1})`. -/
theorem exists_between_of_strictMono {T : ℕ → ℕ} (hT : StrictMono T) {N : ℕ} (hN : T 0 ≤ N) :
    ∃ j, T j ≤ N ∧ N < T (j + 1) := by
  classical
  have hex : ∃ j, N < T (j + 1) := ⟨N, by
    have : N + 1 ≤ T (N + 1) := hT.id_le (N + 1)
    omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; exact hN
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    rwa [Nat.sub_add_cancel h] at this

/-- `countBelow T` grows by at most one per step. -/
theorem countBelow_succ_le {T : ℕ → ℕ} (hT : StrictMono T) (N : ℕ) :
    countBelow T (N + 1) ≤ countBelow T N + 1 := by
  by_cases h0 : T 0 ≤ N
  · obtain ⟨j, h1, h2⟩ := exists_between_of_strictMono hT h0
    rw [countBelow_eq hT h1 h2]
    by_cases h3 : N + 1 < T (j + 1)
    · rw [countBelow_eq hT (h1.trans (Nat.le_succ N)) h3]; omega
    · have h4 : T (j + 1) = N + 1 := by omega
      have h5 : N + 1 < T (j + 1 + 1) := by
        have := hT (show j + 1 < j + 1 + 1 by omega); omega
      rw [countBelow_eq hT h4.le h5]
  · have : countBelow T (N + 1) = 0 := by
      rw [countBelow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      have := hT (show 0 < i + 1 by omega)
      omega
    rw [this]; omega

/-- **The renewal count**: if `(T_j + 1)/(j + 1) → μ > 0`, then `countBelow T N / N → 1/μ`. -/
theorem tendsto_countBelow_div {T : ℕ → ℕ} (hT : StrictMono T) {μ : ℝ} (hμ : 0 < μ)
    (h : Tendsto (fun j : ℕ => ((T j : ℝ) + 1) / ((j : ℝ) + 1)) atTop (𝓝 μ)) :
    Tendsto (fun N : ℕ => (countBelow T N : ℝ) / N) atTop (𝓝 (1 / μ)) := by
  obtain ⟨hlo, hhi⟩ := tendsto_index_div_renewal hμ h
  refine tendsto_of_renewal_sandwich hT ?_ hhi hlo
  filter_upwards [eventually_ge_atTop 1] with j hj n hn1 hn2
  rw [countBelow_eq hT hn1 hn2]
  have hT0 : (0 : ℝ) < T j := by
    have : j ≤ T j := hT.id_le j
    exact_mod_cast (show 0 < T j by omega)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hT0 (by exact_mod_cast hn1)
  constructor
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn0 (by exact_mod_cast hn2.le)
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT0 (by exact_mod_cast hn1)

/-- **The pathwise comparison** (MT (17.24), (17.33)): if `S` is a sum over a sequence cut at
the increasing times `T_j`, then for `T₀ ≤ N`, `|Σ_{t<N} hₜ − Σ_{i<ℓ_N} Σ_{T_i ≤ t < T_{i+1}} hₜ|
≤ |Σ_{t<T₀} hₜ| + Σ_{T_ℓ ≤ t < T_{ℓ+1}} |hₜ|` with `ℓ = ℓ_N` the number of completed
segments. -/
theorem abs_sum_sub_segments_le {T : ℕ → ℕ} (hT : StrictMono T) (h : ℕ → ℝ) {N : ℕ}
    (hN : T 0 ≤ N) :
    |∑ t ∈ Finset.range N, h t - ∑ i ∈ Finset.range (countBelow T N),
        ∑ t ∈ Finset.Ico (T i) (T (i + 1)), h t| ≤
      |∑ t ∈ Finset.range (T 0), h t| +
        ∑ t ∈ Finset.Ico (T (countBelow T N)) (T (countBelow T N + 1)), |h t| := by
  obtain ⟨j, h1, h2⟩ := exists_between_of_strictMono hT hN
  rw [countBelow_eq hT h1 h2]
  have hseg : ∀ k, ∑ t ∈ Finset.range (T k), h t =
      ∑ t ∈ Finset.range (T 0), h t + ∑ i ∈ Finset.range k,
        ∑ t ∈ Finset.Ico (T i) (T (i + 1)), h t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih,
        Finset.sum_range_add_sum_Ico _ (hT.monotone (Nat.le_succ k))]
  have hsplit : ∑ t ∈ Finset.range N, h t =
      ∑ t ∈ Finset.range (T j), h t + ∑ t ∈ Finset.Ico (T j) N, h t :=
    (Finset.sum_range_add_sum_Ico _ h1).symm
  rw [hsplit, hseg j]
  have e : ∑ t ∈ Finset.range (T 0), h t + ∑ i ∈ Finset.range j,
      ∑ t ∈ Finset.Ico (T i) (T (i + 1)), h t + ∑ t ∈ Finset.Ico (T j) N, h t -
      ∑ i ∈ Finset.range j, ∑ t ∈ Finset.Ico (T i) (T (i + 1)), h t =
      ∑ t ∈ Finset.range (T 0), h t + ∑ t ∈ Finset.Ico (T j) N, h t := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h2.le)
    fun _ _ _ => abs_nonneg _


/-- The number of completed segments tends to infinity. -/
theorem tendsto_countBelow_atTop {T : ℕ → ℕ} (hT : StrictMono T) :
    Tendsto (countBelow T) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun j => ⟨T j, fun N hN => ?_⟩
  obtain ⟨j', h1, h2⟩ := exists_between_of_strictMono hT ((hT.monotone (Nat.zero_le j)).trans hN)
  rw [countBelow_eq hT h1 h2]
  by_contra h
  push Not at h
  have := hT.monotone (show j' + 1 ≤ j by omega)
  omega

/-- **The ratio limit along the segments** (MT p. 436): if the averages of the segment sums `sᵢ`
converge to `L`, the overshoots `w_k` are `o(k)`, `ℓ_N → ∞`, and `Σ_{t<N}` differs from
`Σ_{i<ℓ_N} sᵢ` by at most `C + w_{ℓ_N}`, then `F_N/ℓ_N → L`. -/
theorem tendsto_div_count_of_segments {s w : ℕ → ℝ} {F : ℕ → ℝ} {ℓ : ℕ → ℕ} {L C : ℝ}
    (hu : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, s i) atTop (𝓝 L))
    (hw : Tendsto (fun k : ℕ => w k / ((k : ℝ) + 1)) atTop (𝓝 0))
    (hℓ : Tendsto ℓ atTop atTop)
    (hb : ∀ᶠ N in atTop, |F N - ∑ i ∈ Finset.range (ℓ N), s i| ≤ C + w (ℓ N)) :
    Tendsto (fun N => F N / ℓ N) atTop (𝓝 L) := by
  have h1 := hu.comp hℓ
  have hC : Tendsto (fun N => C / (ℓ N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hℓ)
  have h3 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
    have : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    field_simp
  have hW : Tendsto (fun N => w (ℓ N) / (ℓ N : ℝ)) atTop (𝓝 0) := by
    have := (hw.mul h3).comp hℓ
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hℓ.eventually (eventually_ge_atTop 1)] with N hN
    have : (ℓ N : ℝ) ≠ 0 := by exact_mod_cast (show ℓ N ≠ 0 by omega)
    have : (ℓ N : ℝ) + 1 ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp
  have hR : Tendsto (fun N => (F N - ∑ i ∈ Finset.range (ℓ N), s i) / ℓ N) atTop (𝓝 0) := by
    have hbound := hC.add hW
    rw [add_zero] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hb, hℓ.eventually (eventually_ge_atTop 1)] with N hN hN1
    have hpos : (0 : ℝ) < ℓ N := by exact_mod_cast (show 0 < ℓ N by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, ← add_div]
    exact div_le_div_of_nonneg_right hN hpos.le
  have := h1.add hR
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hℓ.eventually (eventually_ge_atTop 1)] with N hN
  have : (ℓ N : ℝ) ≠ 0 := by exact_mod_cast (show ℓ N ≠ 0 by omega)
  simp only [Function.comp_apply]
  field_simp
  ring

/-! ### The segments of the split `m`-skeleton -/

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} {m : ℕ}

/-- The segment boundaries `T_j = m(σ_α̌(j) + 1)` in original time. -/
noncomputable def skelBound [NeZero m] (M : Minorization (P ^ m)) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) : ℕ :=
  m * (renewalTime (skelAtom M) j ω + 1)

/-- The boundaries increase strictly. -/
theorem strictMono_skelBound [NeZero m] (M : Minorization (P ^ m)) (ω : ℕ → (Fin m → X) × Bool) :
    StrictMono fun j => skelBound M j ω :=
  strictMono_nat_of_lt_succ fun j => by
    have := renewalTime_lt_succ (skelAtom M) j ω
    have := NeZero.pos m
    simp only [skelBound]
    exact Nat.mul_lt_mul_of_pos_left (by omega) this

/-- `ℓ_N`: the number of cycle sums completed by original time `N`. -/
noncomputable def skelCount [NeZero m] (M : Minorization (P ^ m)) (N : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) : ℕ :=
  countBelow (fun j => skelBound M j ω) N

/-- `skelBound` is measurable. -/
theorem measurable_skelBound [NeZero m] (M : Minorization (P ^ m)) (j : ℕ) :
    Measurable (skelBound M j) :=
  (measurable_const.mul ((measurable_renewalTime (measurableSet_skelAtom M) j).add_const 1) :
    Measurable fun ω => m * (renewalTime (skelAtom M) j ω + 1))

/-- `ℓ_N` is measurable. -/
theorem measurable_skelCount [NeZero m] (M : Minorization (P ^ m)) (N : ℕ) :
    Measurable (skelCount M N) := by
  have : skelCount M N = fun ω => ∑ j ∈ Finset.range N,
      if skelBound M (j + 1) ω ≤ N then 1 else 0 := by
    ext ω; rw [skelCount, countBelow, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_skelBound M (j + 1)) measurable_const

/-- The partial sums `Σ_{t<N} f(Φₜ)` of the recovered path. -/
noncomputable def skelPartialSum [NeZero m] (f : X → ℝ) (N : ℕ) (ω : ℕ → (Fin m → X) × Bool) : ℝ :=
  ∑ t ∈ Finset.range N, f (skelRecover ω t)

/-- **(17.24) and (17.33), pathwise**: for `T₀ ≤ N`,
`|Σ_{t<N} g(Φₜ) − Σ_{i<ℓ_N} sᵢ(g)| ≤ |s₋₁(g)| + s_{ℓ_N}(|g|)`. -/
theorem abs_skelPartialSum_sub_le [NeZero m] (M : Minorization (P ^ m)) (g : X → ℝ) {N : ℕ}
    {ω : ℕ → (Fin m → X) × Bool} (hN : skelBound M 0 ω ≤ N) :
    |skelPartialSum g N ω - ∑ i ∈ Finset.range (skelCount M N ω), skelCycle M g i ω| ≤
      |skelPreSum M g ω| + skelCycle M (fun x => |g x|) (skelCount M N ω) ω := by
  have h := abs_sum_sub_segments_le (strictMono_skelBound M ω) (fun t => g (skelRecover ω t)) hN
  simp only [skelBound] at h
  rw [renewalTime] at h
  simpa only [skelPartialSum, skelCount, skelBound, skelCycle_eq, skelPreSum] using h


/-! ### Laws of large numbers along the segments -/

variable [MeasurableSpace.CountablyGenerated X]

/-- Every cycle sum under `P_ρ` has the law of `s₋₁(f)` under `P̌_{λ_ν}`. -/
theorem skel_identDistrib_cycle [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (j : ℕ) :
    haveI := isMarkovKernel_skelKernel M
    IdentDistrib (skelCycle M f j) (skelPreSum M f) (pathMeasure (skelKernel M) ρ)
      (skelFreshLaw M) :=
  ⟨(measurable_skelCycle M hf j).aemeasurable, (measurable_skelPreSum M hf).aemeasurable,
    skel_map_cycle M hL hf ρ j⟩

/-- **The strong law for the cycle sums** (MT p. 436): `(1/k) Σ_{j<k} sⱼ(f) → Ě_{ν*}[s₋₁(f)]`
almost surely under every initial law. -/
theorem skel_ae_tendsto_cycle_average [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hfi : Integrable (skelPreSum M f) (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun k : ℕ => (k : ℝ)⁻¹ *
      ∑ j ∈ Finset.range k, skelCycle M f j ω) atTop
        (𝓝 (∫ ω, skelPreSum M f ω ∂skelFreshLaw M)) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hid := skel_identDistrib_cycle M hL hf ρ 0
  have h := (skel_isOneDependent M hL hf ρ).ae_tendsto_average (skel_isStationarySeq M hL hf ρ)
    (hid.integrable_iff.2 hfi)
  rwa [hid.integral_eq] at h

omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁(1) = m(σ_α̌ + 1)`. -/
theorem skelPreSum_one [NeZero m] (M : Minorization (P ^ m)) (ω : ℕ → (Fin m → X) × Bool) :
    skelPreSum M (fun _ => (1 : ℝ)) ω = m * ((hitNat (skelAtom M) ω : ℝ) + 1) := by
  simp [skelPreSum]

omit [MeasurableSpace.CountablyGenerated X] in
/-- `T_j = s₋₁(1) + Σ_{i<j} sᵢ(1)`. -/
theorem skelBound_eq [NeZero m] (M : Minorization (P ^ m)) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) :
    (skelBound M j ω : ℝ) = skelPreSum M (fun _ => (1 : ℝ)) ω +
      ∑ i ∈ Finset.range j, skelCycle M (fun _ => (1 : ℝ)) i ω := by
  rw [← sum_range_renewal_eq]
  simp [skelBound]

/-- **The segment boundaries grow linearly** (MT (17.34)): if `σ_α̌ ∈ L¹(P̌_{ν*})`, then
`(T_j + 1)/(j + 1) → Ě_{ν*}[s₋₁(1)]` almost surely. -/
theorem skel_ae_tendsto_bound_div [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hT : Integrable (fun ω => (hitNat (skelAtom M) ω : ℝ)) (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun j : ℕ => ((skelBound M j ω : ℝ) + 1) /
      ((j : ℝ) + 1)) atTop (𝓝 (∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M)) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_skelFreshLaw M
  have hi : Integrable (skelPreSum M (fun _ => (1 : ℝ))) (skelFreshLaw M) := by
    have : skelPreSum M (fun _ => (1 : ℝ)) = fun ω => m * ((hitNat (skelAtom M) ω : ℝ) + 1) :=
      funext (skelPreSum_one M)
    rw [this]
    exact (hT.add (integrable_const 1)).const_mul _
  have h := skel_ae_tendsto_cycle_average M hL measurable_const ρ hi
  filter_upwards [h] with ω hω
  set L := ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M
  have h2 : Tendsto (fun j : ℕ => (j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp; ring
  have h5 : Tendsto (fun j : ℕ => (skelPreSum M (fun _ => (1 : ℝ)) ω + 1) / ((j : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h4 := (hω.mul h2).add h5
  rw [mul_one, add_zero] at h4
  refine h4.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have : (j : ℝ) + 1 ≠ 0 := by positivity
  change _ = ((skelBound M j ω : ℝ) + 1) / ((j : ℝ) + 1)
  rw [skelBound_eq]
  field_simp
  ring

/-- **The number of completed cycles** (MT (17.34)): `ℓ_N/N → 1/Ě_{ν*}[s₋₁(1)]`
almost surely. -/
theorem skel_ae_tendsto_count_div [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hT : Integrable (fun ω => (hitNat (skelAtom M) ω : ℝ)) (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun N : ℕ => (skelCount M N ω : ℝ) / N) atTop
      (𝓝 (1 / ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M)) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_skelFreshLaw M
  have hpos : 0 < ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M := by
    have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have : ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M ≥
        ∫ _ω, (m : ℝ) ∂skelFreshLaw M := by
      refine integral_mono (integrable_const _) ?_ fun ω => ?_
      · have : skelPreSum M (fun _ => (1 : ℝ)) = fun ω =>
            m * ((hitNat (skelAtom M) ω : ℝ) + 1) := funext (skelPreSum_one M)
        rw [this]; exact (hT.add (integrable_const 1)).const_mul _
      · rw [skelPreSum_one]
        have : (0 : ℝ) ≤ hitNat (skelAtom M) ω := Nat.cast_nonneg _
        nlinarith
    rw [integral_const, probReal_univ, one_smul] at this
    linarith
  filter_upwards [skel_ae_tendsto_bound_div M hL ρ hT] with ω hω
  exact tendsto_countBelow_div (strictMono_skelBound M ω) hpos hω

/-- **The last segment is negligible**: if `s₋₁(|g|) ∈ L²(P̌_{ν*})`, then
`s_{ℓ_N}(|g|)²/(N + 1) → 0` almost surely. -/
theorem skel_ae_tendsto_last_sq [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {g : X → ℝ} (hg : Measurable g) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun N : ℕ =>
      skelCycle M (fun x => |g x|) (skelCount M N ω) ω ^ 2 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hgm : Measurable fun x => |g x| := measurable_abs_of_measurable hg
  have hid : ∀ j, IdentDistrib (skelCycle M (fun x => |g x|) j)
      (skelCycle M (fun x => |g x|) 0) (pathMeasure (skelKernel M) ρ)
        (pathMeasure (skelKernel M) ρ) := fun j =>
    (skel_identDistrib_cycle M hL hgm ρ j).trans (skel_identDistrib_cycle M hL hgm ρ 0).symm
  have h := ae_tendsto_sq_div_of_identDistrib hid
    ((skel_identDistrib_cycle M hL hgm ρ 0).memLp_iff.2 hg2)
  filter_upwards [h] with ω hω
  exact tendsto_index_div_of_le (fun j => sq_nonneg _) hω (countBelow_le _)


omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `Sₙ(g) = Σ_{t<n+1} g(Φₜ) − g(Φ₀)` on the recovered path. -/
theorem pathSum_skelRecover [NeZero m] (g : X → ℝ) (n : ℕ) (ω : ℕ → (Fin m → X) × Bool) :
    pathSum g n (skelRecover ω) = skelPartialSum g (n + 1) ω - g (skelRecover ω 0) := by
  rw [skelPartialSum, Finset.sum_range_succ', pathSum]
  ring

/-- **The averages of a function along the original time scale** (MT p. 436): under the
hypotheses of (17.23), `Sₙ(h)/ℓ_{n+1} → Ě[s(h)] = δ⁻¹ π(C)⁻¹ m π(h)` almost surely. -/
theorem skel_ae_tendsto_pathSum_div_count [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0)
    (hπC : π M.C ≠ ∞) {h : X → ℝ} (hm : Measurable h) (hi : Integrable h π)
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun n : ℕ =>
      pathSum h n (skelRecover ω) / skelCount M (n + 1) ω) atTop
        (𝓝 (m * (∫ x, h x ∂π) / (M.δ * π M.C).toReal)) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have ham : Measurable fun x => |h x| := measurable_abs_of_measurable hm
  obtain ⟨hI, hE⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC hm hi
  obtain ⟨hIa, -⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC ham hi.abs
  filter_upwards [skel_ae_tendsto_cycle_average M hL hm ρ hI,
    skel_ae_tendsto_cycle_average M hL ham ρ hIa] with ω h1 h2
  rw [hE] at h1
  have hw : Tendsto (fun k : ℕ => skelCycle M (fun x => |h x|) k ω / ((k : ℝ) + 1)) atTop
      (𝓝 0) := tendsto_term_div_of_tendsto_average (h2.congr fun n => by rw [div_eq_inv_mul])
  have hF := tendsto_div_count_of_segments h1 hw
    (tendsto_countBelow_atTop (strictMono_skelBound M ω))
    (F := fun N => skelPartialSum h N ω) (C := |skelPreSum M h ω|)
    (eventually_atTop.2 ⟨skelBound M 0 ω, fun N hN => abs_skelPartialSum_sub_le M h hN⟩)
  have hF1 := hF.comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n : ℕ => h (skelRecover ω 0) / (skelCount M (n + 1) ω : ℝ)) atTop
      (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
        ((tendsto_countBelow_atTop (strictMono_skelBound M ω)).comp (tendsto_add_atTop_nat 1)))
  have := hF1.sub h0
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [pathSum_skelRecover, sub_div]
  rfl

/-- **Theorem 17.3.2** (iii) ⇒ (i) (MT p. 436), for a general `m`: if the `m`-skeleton is Harris
and has a minorization on `C ∈ B⁺(X)`, and `π` is an invariant measure of `P` with
`0 < π(C) < ∞` (finite or not), then for `f, g ∈ L¹(π)` with `π(g) ≠ 0`,
`Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every initial law. The proof is the book's: the
even and the odd cycle sums of the split `m`-skeleton obey the strong law. -/
theorem theorem_17_3_2_general [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0)
    (hπC : π M.C ≠ ∞) {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f π) (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_skelInit M μ
  have hE : MeasurableSet {ω : ℕ → X | Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π))} :=
    measurableSet_tendsto (𝓝 _) fun n => (measurable_pathSum hfm n).div (measurable_pathSum hgm n)
  rw [← skel_map_recover M μ, ae_map_iff measurable_skelRecover.aemeasurable hE]
  have hc : ((M.δ * π M.C).toReal) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨mul_ne_zero M.δ_pos.ne' hπ0, ENNReal.mul_ne_top M.δ_ne_top hπC⟩
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  filter_upwards [skel_ae_tendsto_pathSum_div_count M hH hψC hπ hπ0 hπC hfm hfi _,
    skel_ae_tendsto_pathSum_div_count M hH hψC hπ hπ0 hπC hgm hgi _] with ω h1 h2
  have hB : m * (∫ x, g x ∂π) / (M.δ * π M.C).toReal ≠ 0 :=
    div_ne_zero (mul_ne_zero hm0 hg) hc
  have := h1.div h2 hB
  have e : m * (∫ x, f x ∂π) / (M.δ * π M.C).toReal / (m * (∫ x, g x ∂π) /
      (M.δ * π M.C).toReal) = (∫ y, f y ∂π) / ∫ y, g y ∂π := by
    field_simp
  rw [e] at this
  refine this.congr' ?_
  filter_upwards [((tendsto_countBelow_atTop (strictMono_skelBound M ω)).comp
    (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop 1)] with n hn
  have : (skelCount M (n + 1) ω : ℝ) ≠ 0 := by
    simp only [Function.comp_apply] at hn
    exact_mod_cast (show skelCount M (n + 1) ω ≠ 0 by unfold skelCount; omega)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ this]


/-! ### The CLT for a general `m` (Theorem 17.3.6) -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁(|g − c|) ≤ s₋₁(|g|) + |c| m(σ_α̌ + 1)`. -/
theorem skelPreSum_abs_sub_le [NeZero m] (M : Minorization (P ^ m)) (g : X → ℝ) (c : ℝ)
    (ω : ℕ → (Fin m → X) × Bool) :
    skelPreSum M (fun x => |g x - c|) ω ≤
      skelPreSum M (fun x => |g x|) ω + |c| * (m * ((hitNat (skelAtom M) ω : ℝ) + 1)) := by
  rw [← skelPreSum_one, skelPreSum, skelPreSum, skelPreSum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => by rw [mul_one]; exact abs_sub _ _

omit [MeasurableSpace.CountablyGenerated X] in
/-- `|s₋₁(g)| ≤ s₋₁(|g|)`. -/
theorem abs_skelPreSum_le [NeZero m] (M : Minorization (P ^ m)) (g : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) : |skelPreSum M g ω| ≤ skelPreSum M (fun x => |g x|) ω :=
  Finset.abs_sum_le_sum_abs _ _

omit [MeasurableSpace.CountablyGenerated X] in
/-- The second-moment condition carries over to the centred function. -/
theorem memLp_skelPreSum_abs_sub [NeZero m] (M : Minorization (P ^ m)) {g : X → ℝ}
    (hg : Measurable g) (c : ℝ) {Q : Measure (ℕ → (Fin m → X) × Bool)} [IsFiniteMeasure Q]
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 Q)
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 Q) :
    MemLp (skelPreSum M fun x => |g x - c|) 2 Q := by
  have hB : MemLp (fun ω => skelPreSum M (fun x => |g x|) ω +
      |c| * (m * ((hitNat (skelAtom M) ω : ℝ) + 1))) 2 Q :=
    hg2.add (((hT2.add (memLp_const 1)).const_mul _).const_mul _)
  refine hB.of_le (measurable_skelPreSum M
    (measurable_abs_of_measurable (hg.sub measurable_const))).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ skelPreSum M (fun x => |g x - c|) ω := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : 0 ≤ skelPreSum M (fun x => |g x|) ω := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by positivity)]
  exact skelPreSum_abs_sub_le M g c ω

/-- **The CLT variance (17.32)** for a general `m`:
`γ_g² = m⁻¹ π*(α̌) (Ě[s₀(ḡ)²] + 2 Ě[s₀(ḡ) s₁(ḡ)])` with `π*(α̌) = δ π(C)`, `ḡ = g − π(g)`, and
the stationary cycle sums `(s₀, s₁) = (s₋₁, s₀)` under the fresh law `P̌_{ν*}`. -/
noncomputable def skelCLTVariance [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (π : Measure X) (g : X → ℝ) : ℝ :=
  (M.δ * π M.C).toReal / m * (∫ ω, skelPreSum M (fun x => g x - ∫ y, g y ∂π) ω ^ 2
    ∂skelFreshLaw M + 2 * ∫ ω, skelPreSum M (fun x => g x - ∫ y, g y ∂π) ω *
      skelCycle M (fun x => g x - ∫ y, g y ∂π) 0 ω ∂skelFreshLaw M)


/-- The moment condition (17.31) forces `π(|g|) < ∞`: by (17.23),
`Ě_{ν*}[s₋₁(|g|)] = δ⁻¹ π(C)⁻¹ m π(|g|)`. -/
theorem integrable_of_integrable_skelPreSum [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m)) {ψ : Measure X}
    (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0) (hπC : π M.C ≠ ∞) {g : X → ℝ}
    (hgm : Measurable g) (h : Integrable (skelPreSum M fun x => |g x|) (skelFreshLaw M)) :
    Integrable g π := by
  have ham : Measurable fun x => |g x| := measurable_abs_of_measurable hgm
  have hE := lintegral_skelPreSumE_fresh M hH hψC hπ hπ0 hπC
    (f := fun x => ENNReal.ofReal |g x|) (ENNReal.measurable_ofReal.comp ham)
  have h1 : ∫⁻ ω, ENNReal.ofReal (skelPreSum M (fun x => |g x|) ω) ∂skelFreshLaw M ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_skelPreSum M ham).aestronglyMeasurable
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 h
  simp_rw [ofReal_skelPreSum M (fun x => abs_nonneg (g x))] at h1
  rw [hE] at h1
  have hc : (M.δ * π M.C)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.mul_ne_top M.δ_ne_top hπC)
  have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h2 : ∫⁻ x, ENNReal.ofReal |g x| ∂π ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top hm, ENNReal.mul_top hc] at h1
    exact h1 rfl
  have h3 := (lintegral_ofReal_ne_top_iff_integrable ham.aestronglyMeasurable
    (Eventually.of_forall fun x => abs_nonneg (g x))).1 h2
  exact (integrable_norm_iff hgm.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using h3)


/-- `E_ρ[s₀ s₁] = Ě_{ν*}[s₋₁ s₀]` for every initial law. -/
theorem skel_integral_mul_cycle [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    ∫ ω, skelCycle M f 0 ω * skelCycle M f 1 ω ∂pathMeasure (skelKernel M) ρ =
      ∫ ω, skelPreSum M f ω * skelCycle M f 0 ω ∂skelFreshLaw M := by
  have := isMarkovKernel_skelKernel M
  have h := skel_map_cycles M hL hf ρ 0
  have hv1 : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelCycle M f (0 + j) ω :=
    measurable_pi_iff.2 fun j => measurable_skelCycle M hf _
  have hv2 : Measurable fun (w : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelSeq M f w j :=
    measurable_pi_iff.2 fun j => measurable_skelSeq M hf j
  have hu : Measurable fun v : ℕ → ℝ => v 0 * v 1 :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have e1 := integral_map (μ := pathMeasure (skelKernel M) ρ) hv1.aemeasurable
    hu.aestronglyMeasurable
  have e2 := integral_map (μ := skelFreshLaw M) hv2.aemeasurable hu.aestronglyMeasurable
  rw [h, e2] at e1
  rw [show (∫ ω, skelPreSum M f ω * skelCycle M f 0 ω ∂skelFreshLaw M) =
    ∫ x, skelSeq M f x 0 * skelSeq M f x 1 ∂skelFreshLaw M from rfl]
  simpa using e1.symm

/-- `γ_g² ≥ 0` (MT Theorem 17.3.6: `0 ≤ γ_g² < ∞`). -/
theorem skelCLTVariance_nonneg [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M))
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M)) :
    0 ≤ skelCLTVariance M π g := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isProbabilityMeasure_skelFreshLaw M
  have := M.isProbabilityMeasure_ν
  have := isProbabilityMeasure_skelInit M M.ν
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hπ0 : π M.C ≠ 0 := ((hπ.pow m).isSubinvariant.pos_of_pos hH.1.2.1
    (IsProbabilityMeasure.ne_zero π) M.measurableSet_C hψC).ne'
  have hgi := integrable_of_integrable_skelPreSum M hH hψC hπ hπ0 (measure_ne_top π _) hgm
    (hg2.integrable one_le_two)
  set c := ∫ y, g y ∂π
  have hgbm : Measurable fun x => g x - c := hgm.sub measurable_const
  set ρ := skelInit M M.ν
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hOD := skel_isOneDependent M hL hgbm ρ
  have hST := skel_isStationarySeq M hL hgbm ρ
  have hid0 := skel_identDistrib_cycle M hL hgbm ρ 0
  have hgb2 : MemLp (skelPreSum M fun x => g x - c) 2 (skelFreshLaw M) :=
    (memLp_skelPreSum_abs_sub M hgm c hg2 hT2).of_le
      (measurable_skelPreSum M hgbm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ skelPreSum M
          (fun x => |g x - c|) ω from Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact abs_skelPreSum_le M _ ω)
  obtain ⟨-, hmean⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 (measure_ne_top π _) hgbm
    (hgi.sub (integrable_const c))
  rw [integral_sub hgi (integrable_const c), integral_const, probReal_univ, one_smul,
    sub_self, mul_zero, zero_div] at hmean
  have h0 := hOD.oneDepVariance_nonneg hST (hid0.memLp_iff.2 hgb2) (hid0.integral_eq.trans hmean)
  have hsq := (hid0.comp (measurable_id.pow_const 2)).integral_eq
  simp only [Function.comp_apply, id] at hsq
  rw [oneDepVariance, skel_integral_mul_cycle M hL hgbm ρ, hsq] at h0
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg m)) h0


/-- **Theorem 17.3.6** (MT p. 441), the CLT part, for a general `m`: let the `m`-skeleton be
Harris with a minorization `Pᵐ(x, ·) ≥ δ ν` on `C ∈ B⁺(X)`, let `π` be an invariant probability of
`P`, and let the CLT moment condition for the split chain (17.31) hold:
`Ě_{ν*}[(Σ_{n ≤ σ_α̌} Zₙ(|g|))²] < ∞` and `Ě_{ν*}[σ_α̌²] < ∞`. Then
`n^{−1/2} Sₙ(g − π(g)) ⇒ N(0, γ_g²)` under every initial law, with `γ_g²` the variance (17.32)
(`skelCLTVariance`). The proof is the book's (17.33)–(17.36): the pathwise reduction to the
one-dependent cycle sums, the random-index step through Kolmogorov's inequality for their even and
odd subsequences, and the CLT for stationary one-dependent sequences. -/
theorem theorem_17_3_6_general [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M))
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z' : Ω' → ℝ}
    (hZ' : HasLaw Z' (gaussianReal 0 (skelCLTVariance M π g).toNNReal) P')
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω) atTop Z'
      (fun _ => pathMeasure P μ) P' := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isProbabilityMeasure_skelFreshLaw M
  have := isProbabilityMeasure_pathMeasure P μ
  have := isProbabilityMeasure_skelInit M μ
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hπ0 : π M.C ≠ 0 := ((hπ.pow m).isSubinvariant.pos_of_pos hH.1.2.1
    (IsProbabilityMeasure.ne_zero π) M.measurableSet_C hψC).ne'
  have hπC : π M.C ≠ ∞ := measure_ne_top π _
  have hgi := integrable_of_integrable_skelPreSum M hH hψC hπ hπ0 hπC hgm
    (hg2.integrable one_le_two)
  set c := ∫ y, g y ∂π with hcdef
  set gb : X → ℝ := fun x => g x - c with hgb
  have hgbm : Measurable gb := hgm.sub measurable_const
  set ρ := skelInit M μ with hρ
  set Q := pathMeasure (skelKernel M) ρ with hQ
  have : IsProbabilityMeasure Q := isProbabilityMeasure_pathMeasure _ _
  set Z : ℕ → (ℕ → (Fin m → X) × Bool) → ℝ := fun j => skelCycle M gb j with hZdef
  have hZm : ∀ j, Measurable (Z j) := fun j => measurable_skelCycle M hgbm j
  have hOD : IsOneDependent Z Q := skel_isOneDependent M hL hgbm ρ
  have hST : IsStationarySeq Z Q := skel_isStationarySeq M hL hgbm ρ
  have hid0 := skel_identDistrib_cycle M hL hgbm ρ 0
  have hgba2 : MemLp (skelPreSum M fun x => |gb x|) 2 (skelFreshLaw M) :=
    memLp_skelPreSum_abs_sub M hgm c hg2 hT2
  have hgb2 : MemLp (skelPreSum M gb) 2 (skelFreshLaw M) :=
    hgba2.of_le (measurable_skelPreSum M hgbm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ skelPreSum M
          (fun x => |gb x|) ω from Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact abs_skelPreSum_le M _ ω)
  have hZ2 : MemLp (Z 0) 2 Q := hid0.memLp_iff.2 hgb2
  obtain ⟨-, hmean⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC hgbm
    (hgi.sub (integrable_const c))
  rw [integral_sub hgi (integrable_const c), integral_const, probReal_univ, one_smul,
    sub_self, mul_zero, zero_div] at hmean
  have h0 : ∫ ω, Z 0 ω ∂Q = 0 := hid0.integral_eq.trans hmean
  -- the variances
  set σ2 := oneDepVariance Z Q with hσ2
  have hσ0 : 0 ≤ σ2 := hOD.oneDepVariance_nonneg hST hZ2 h0
  obtain ⟨-, hmean1⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC
    (f := fun _ => (1 : ℝ)) measurable_const (integrable_const 1)
  rw [integral_const, probReal_univ, one_smul, mul_one] at hmean1
  set κ := (M.δ * π M.C).toReal / m with hκ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hc0 : 0 < (M.δ * π M.C).toReal :=
    ENNReal.toReal_pos (mul_ne_zero M.δ_pos.ne' hπ0) (ENNReal.mul_ne_top M.δ_ne_top hπC)
  have hκ0 : 0 < κ := div_pos hc0 hm0
  have hκeq : 1 / ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M = κ := by
    rw [hmean1, hκ]; field_simp
  have hγ : skelCLTVariance M π g = κ * σ2 := by
    have hsq := (hid0.comp (measurable_id.pow_const 2)).integral_eq
    simp only [Function.comp_apply, id] at hsq
    rw [hσ2, oneDepVariance, skel_integral_mul_cycle M hL hgbm ρ, hsq]
    rfl
  -- the number of completed cycles
  have hT1 : Integrable (fun ω => (hitNat (skelAtom M) ω : ℝ)) (skelFreshLaw M) :=
    hT2.integrable one_le_two
  have hK : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (skelCount M (n + 1) ω : ℝ) / n) atTop (𝓝 κ) := by
    filter_upwards [skel_ae_tendsto_count_div M hL ρ hT1] with ω hω
    rw [hκeq] at hω
    have h1 := hω.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      push_cast; field_simp
    have := h1.mul h2
    rw [mul_one] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Function.comp_apply]
    field_simp
  have hR := hOD.tendstoInMeasure_randomIndex hZm hST hZ2 h0
    (K := fun n => skelCount M (n + 1)) (fun n => measurable_skelCount M (n + 1)) hκ0 hK
  -- the CLT along the deterministic index
  set Z₀ : Ω' → ℝ := fun ω' => (√κ)⁻¹ * Z' ω' with hZ₀def
  have hZ₀ : HasLaw Z₀ (gaussianReal 0 σ2.toNNReal) P' := by
    have h := gaussianReal_const_mul hZ' (√κ)⁻¹
    rw [mul_zero] at h
    convert h using 2
    rw [hγ]
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, inv_pow, Real.sq_sqrt hκ0.le]
    rw [Real.coe_toNNReal _ hσ0, Real.coe_toNNReal _ (mul_nonneg hκ0.le hσ0)]
    field_simp
  have hCLT := hOD.tendstoInDistribution hZm hST hZ2 h0 hZ₀
  set N : ℕ → ℕ := fun n => 2 * ⌊κ / 2 * n⌋₊ with hN
  have hNt : Tendsto N atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ⌊κ / 2 * n⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
    exact tendsto_atTop_atTop.2 fun b => by
      obtain ⟨n0, hn0⟩ := tendsto_atTop_atTop.1 h1 b
      exact ⟨n0, fun n hn => (hn0 n hn).trans (by simp only [hN]; omega)⟩
  have hcn : Tendsto (fun n : ℕ => √(N n : ℝ) / √(n : ℝ)) atTop (𝓝 (√κ)) := by
    have h1 : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 (2 * (κ / 2))) := by
      have := ((tendsto_nat_floor_mul_div_atTop (show 0 ≤ κ / 2 by positivity)).comp
        tendsto_natCast_atTop_atTop).const_mul 2
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hN]
      push_cast; ring
    rw [show 2 * (κ / 2) = κ by ring] at h1
    have h2' := (Real.continuous_sqrt.tendsto _).comp h1
    refine h2'.congr fun n => ?_
    rw [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  have hX := tendstoInDistribution_const_mul_seq (tendstoInDistribution_comp_index hCLT hNt) hcn
  have hZeq : (fun ω' => √κ * Z₀ ω') = Z' := by
    ext ω'
    have : √κ ≠ 0 := (Real.sqrt_pos.2 hκ0).ne'
    simp only [hZ₀def]
    field_simp
  rw [hZeq] at hX
  set X' : ℕ → (ℕ → (Fin m → X) × Bool) → ℝ := fun n ω =>
    (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range (N n), Z k ω with hX'def
  have hXeq : (fun n ω => √(N n : ℝ) / √(n : ℝ) *
      ((√(N n : ℝ))⁻¹ * ∑ k ∈ Finset.range (N n), Z k ω)) = X' := by
    ext n ω
    rcases Nat.eq_zero_or_pos (N n) with h0' | hpos
    · simp [hX'def, h0']
    · have hn : n ≠ 0 := by
        rintro rfl; simp [hN] at hpos
      have h1 : √(N n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hpos)).ne'
      have h2 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
      simp only [hX'def]
      field_simp
  rw [hXeq] at hX
  -- the random index
  set V : ℕ → (ℕ → (Fin m → X) × Bool) → ℝ := fun n ω =>
    (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range (skelCount M (n + 1) ω), Z j ω with hVdef
  have hVm : ∀ n, Measurable (V n) := fun n =>
    measurable_const.mul (measurable_sum_range_random hZm (measurable_skelCount M (n + 1)))
  have hV : TendstoInDistribution V atTop Z' (fun _ => Q) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub V Z' hX ?_
      fun n => (hVm n).aemeasurable
    convert hR using 1
    ext n ω
    simp only [hVdef, hX'def, Pi.sub_apply, hN]
    ring
  -- the pathwise error
  have hlast := skel_ae_tendsto_last_sq M hL hgbm ρ hgba2
  have hR1 : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
      (pathSum gb n (skelRecover ω) - ∑ j ∈ Finset.range (skelCount M (n + 1) ω), Z j ω))
      atTop (𝓝 0) := by
    filter_upwards [hlast] with ω hω
    set C := |gb (skelRecover ω 0)| + |skelPreSum M gb ω| with hC
    have hsqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    set u : ℕ → ℝ := fun N => skelCycle M (fun x => |gb x|) (skelCount M N ω) ω with hu
    have hu0 : ∀ N, 0 ≤ u N := fun N => by
      simp only [hu]; rw [skelCycle_eq]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hW : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * u (n + 1)) atTop (𝓝 0) := by
      have h1 := hω.comp (tendsto_add_atTop_nat 1)
      have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + 2 * (1 / (n : ℝ))) atTop (𝓝 (1 + 2 * 0)) :=
          tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul 2)
        rw [mul_zero, add_zero] at this
        refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
        have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        push_cast; field_simp; ring
      have h3 := h1.mul h2
      rw [zero_mul] at h3
      have h4 := (Real.continuous_sqrt.tendsto _).comp h3
      rw [Real.sqrt_zero] at h4
      refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
      simp only [Function.comp_apply]
      rw [show u (n + 1) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) * ((((n + 1 : ℕ) : ℝ) + 1) / n) =
          u (n + 1) ^ 2 / n by field_simp]
      rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq (hu0 _), inv_mul_eq_div]
    have hbound := (hsqrt.mul_const C).add hW
    rw [zero_mul, add_zero] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (skelBound M 0 ω)] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
    have h := abs_skelPartialSum_sub_le M gb (N := n + 1) (hn.trans (Nat.le_succ n))
    rw [pathSum_skelRecover]
    have e : skelPartialSum gb (n + 1) ω - gb (skelRecover ω 0) -
        ∑ j ∈ Finset.range (skelCount M (n + 1) ω), Z j ω =
        (skelPartialSum gb (n + 1) ω - ∑ j ∈ Finset.range (skelCount M (n + 1) ω),
          skelCycle M gb j ω) - gb (skelRecover ω 0) := by
      simp only [hZdef]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    simp only [hC, hu]
    linarith
  have hfinal : TendstoInMeasure Q
      ((fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum gb n (skelRecover ω)) - V) atTop 0 := by
    refine (tendstoInMeasure_of_tendsto_ae (fun n => ?_) hR1).congr_left (fun n => ?_)
    · exact (measurable_const.mul (((measurable_pathSum hgbm n).comp measurable_skelRecover).sub
        (measurable_sum_range_random hZm (measurable_skelCount M (n + 1))))).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply, hVdef]; ring
  have hQd := tendstoInDistribution_of_tendstoInMeasure_sub _ Z' hV hfinal
    fun n => (measurable_const.mul ((measurable_pathSum hgbm n).comp
      measurable_skelRecover)).aemeasurable
  exact tendstoInDistribution_of_map measurable_skelRecover (skel_map_recover M μ)
    (fun n => measurable_const.mul (measurable_pathSum hgbm n)) hQd


/-! ### The LIL for a general `m` -/

/-- `ℓ_{n+1}/n → 1/Ě[s₋₁(1)]` almost surely. -/
theorem skel_ae_tendsto_count_succ_div [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hT : Integrable (fun ω => (hitNat (skelAtom M) ω : ℝ)) (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun n : ℕ => (skelCount M (n + 1) ω : ℝ) / n)
      atTop (𝓝 (1 / ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M)) := by
  have := isMarkovKernel_skelKernel M
  filter_upwards [skel_ae_tendsto_count_div M hL ρ hT] with ω hω
  have h1 := hω.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast; field_simp
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Function.comp_apply]
  field_simp

/-- **(17.33)**: `n^{−1/2} (Sₙ(g) − Σ_{j<ℓ_{n+1}} sⱼ(g)) → 0` almost surely, if
`s₋₁(|g|) ∈ L²(P̌_{ν*})`. -/
theorem skel_ae_tendsto_pathSum_sub_cycles [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {g : X → ℝ} (hg : Measurable g) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
      (pathSum g n (skelRecover ω) - ∑ j ∈ Finset.range (skelCount M (n + 1) ω),
        skelCycle M g j ω)) atTop (𝓝 0) := by
  have := isMarkovKernel_skelKernel M
  filter_upwards [skel_ae_tendsto_last_sq M hL hg ρ hg2] with ω hω
  set C := |g (skelRecover ω 0)| + |skelPreSum M g ω| with hC
  have hsqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  set u : ℕ → ℝ := fun N => skelCycle M (fun x => |g x|) (skelCount M N ω) ω with hu
  have hu0 : ∀ N, 0 ≤ u N := fun N => by
    simp only [hu]; rw [skelCycle_eq]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hW : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * u (n + 1)) atTop (𝓝 0) := by
    have h1 := hω.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 + 2 * (1 / (n : ℝ))) atTop (𝓝 (1 + 2 * 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul 2)
      rw [mul_zero, add_zero] at this
      refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      push_cast; field_simp; ring
    have h3 := h1.mul h2
    rw [zero_mul] at h3
    have h4 := (Real.continuous_sqrt.tendsto _).comp h3
    rw [Real.sqrt_zero] at h4
    refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    simp only [Function.comp_apply]
    rw [show u (n + 1) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) * ((((n + 1 : ℕ) : ℝ) + 1) / n) =
        u (n + 1) ^ 2 / n by field_simp]
    rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq (hu0 _), inv_mul_eq_div]
  have hbound := (hsqrt.mul_const C).add hW
  rw [zero_mul, add_zero] at hbound
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop (skelBound M 0 ω)] with n hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  have h := abs_skelPartialSum_sub_le M g (N := n + 1) (hn.trans (Nat.le_succ n))
  rw [pathSum_skelRecover]
  have e : skelPartialSum g (n + 1) ω - g (skelRecover ω 0) -
      ∑ j ∈ Finset.range (skelCount M (n + 1) ω), skelCycle M g j ω =
      (skelPartialSum g (n + 1) ω - ∑ j ∈ Finset.range (skelCount M (n + 1) ω),
        skelCycle M g j ω) - g (skelRecover ω 0) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  simp only [hC, hu]
  linarith

/-- **Theorem 17.3.6**, the LIL (MT p. 441–443), for a general `m`: under the hypotheses of
`theorem_17_3_6_general`, `Sₙ(g − π(g))` obeys the law of the iterated logarithm with constant
`γ_g = √(skelCLTVariance M π g)` (the CLT constant (17.32)) almost surely, from every initial law.
The proof uses the LIL for stationary one-dependent sequences (`hasLIL_oneDependent`), the
random-index step (`HasLIL.comp_index`; `ℓₙ` grows by at most one per step) and (17.33). -/
theorem theorem_17_3_6_lil_general [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M))
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, HasLIL (fun n => pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      (√(skelCLTVariance M π g)) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isProbabilityMeasure_skelFreshLaw M
  have := isProbabilityMeasure_skelInit M μ
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hπ0 : π M.C ≠ 0 := ((hπ.pow m).isSubinvariant.pos_of_pos hH.1.2.1
    (IsProbabilityMeasure.ne_zero π) M.measurableSet_C hψC).ne'
  have hπC : π M.C ≠ ∞ := measure_ne_top π _
  have hgi := integrable_of_integrable_skelPreSum M hH hψC hπ hπ0 hπC hgm
    (hg2.integrable one_le_two)
  set c := ∫ y, g y ∂π with hcdef
  set gb : X → ℝ := fun x => g x - c with hgb
  have hgbm : Measurable gb := hgm.sub measurable_const
  set ρ := skelInit M μ with hρ
  set Q := pathMeasure (skelKernel M) ρ with hQ
  have : IsProbabilityMeasure Q := isProbabilityMeasure_pathMeasure _ _
  set Z : ℕ → (ℕ → (Fin m → X) × Bool) → ℝ := fun j => skelCycle M gb j with hZdef
  have hZm : ∀ j, Measurable (Z j) := fun j => measurable_skelCycle M hgbm j
  have hOD : IsOneDependent Z Q := skel_isOneDependent M hL hgbm ρ
  have hST : IsStationarySeq Z Q := skel_isStationarySeq M hL hgbm ρ
  have hid0 := skel_identDistrib_cycle M hL hgbm ρ 0
  have hgba2 : MemLp (skelPreSum M fun x => |gb x|) 2 (skelFreshLaw M) :=
    memLp_skelPreSum_abs_sub M hgm c hg2 hT2
  have hgb2 : MemLp (skelPreSum M gb) 2 (skelFreshLaw M) :=
    hgba2.of_le (measurable_skelPreSum M hgbm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ skelPreSum M
          (fun x => |gb x|) ω from Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact abs_skelPreSum_le M _ ω)
  have hZ2 : MemLp (Z 0) 2 Q := hid0.memLp_iff.2 hgb2
  obtain ⟨-, hmean⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC hgbm
    (hgi.sub (integrable_const c))
  rw [integral_sub hgi (integrable_const c), integral_const, probReal_univ, one_smul,
    sub_self, mul_zero, zero_div] at hmean
  have h0 : ∫ ω, Z 0 ω ∂Q = 0 := hid0.integral_eq.trans hmean
  obtain ⟨-, hlil⟩ := hasLIL_oneDependent hZm hOD hST hZ2 h0
  obtain ⟨-, hmean1⟩ := theorem_17_3_1_general_mean M hH hψC hπ hπ0 hπC
    (f := fun _ => (1 : ℝ)) measurable_const (integrable_const 1)
  rw [integral_const, probReal_univ, one_smul, mul_one] at hmean1
  set κ := (M.δ * π M.C).toReal / m with hκ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hc0 : 0 < (M.δ * π M.C).toReal :=
    ENNReal.toReal_pos (mul_ne_zero M.δ_pos.ne' hπ0) (ENNReal.mul_ne_top M.δ_ne_top hπC)
  have hκ0 : 0 < κ := div_pos hc0 hm0
  have hκeq : 1 / ∫ ω, skelPreSum M (fun _ => (1 : ℝ)) ω ∂skelFreshLaw M = κ := by
    rw [hmean1, hκ]; field_simp
  have hγ : skelCLTVariance M π g = κ * (∫ ω, Z 0 ω ^ 2 ∂Q + 2 * ∫ ω, Z 0 ω * Z 1 ω ∂Q) := by
    have hsq := (hid0.comp (measurable_id.pow_const 2)).integral_eq
    simp only [Function.comp_apply, id] at hsq
    rw [skel_integral_mul_cycle M hL hgbm ρ, hsq]
    rfl
  have hK := skel_ae_tendsto_count_succ_div M hL ρ (hT2.integrable one_le_two)
  have hR := skel_ae_tendsto_pathSum_sub_cycles M hL hgbm ρ hgba2
  have hE : MeasurableSet {ω : ℕ → X | HasLIL (fun n => pathSum gb n ω)
      (√(skelCLTVariance M π g))} :=
    measurableSet_hasLIL (fun n => measurable_pathSum hgbm n) _
  rw [← skel_map_recover M μ, ae_map_iff measurable_skelRecover.aemeasurable hE]
  filter_upwards [hlil, hK, hR] with ω h1 h2 h3
  rw [hκeq] at h2
  have h4 := h1.comp_index (Real.sqrt_nonneg _)
    (T := fun n => skelCount M (n + 1) ω)
    (fun n => countBelow_succ_le (strictMono_skelBound M ω) (n + 1)) hκ0 h2
  have heq : √κ * √(∫ ω, Z 0 ω ^ 2 ∂Q + 2 * ∫ ω, Z 0 ω * Z 1 ω ∂Q) =
      √(skelCLTVariance M π g) := by
    rw [hγ, Real.sqrt_mul hκ0.le]
  rw [heq] at h4
  exact h4.of_tendsto_sub (tendsto_div_lilScale_of_sqrt h3)

end MeynTweedie.LimitTheorems
