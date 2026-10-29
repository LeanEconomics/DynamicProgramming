/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.NullPeriodic

/-!
# Characterizing positivity using `Pⁿ` (MT §18.2)

Copied for Chapter 19 from the Chapter 18 project
(`Positivity/PositivityPn.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, pp. 469–471. The state space is countably generated where the period, the
maximal Harris set or Theorem 18.1.3 is used.

**Definitions** (pp. 470–471). `IsNullState`, `IsPositiveState`: `Pⁿ(α, α) → 0`, resp.
`lim sup Pⁿ(α, α) > 0`; `IsNullSet`, `IsPositiveSet`: `Pⁿ(x, A) → 0`, resp.
`lim sup Pⁿ(x, A) > 0`, for every `x ∈ A`.

**Tools.**
* `tendsto_zero_iff_limsup_eq_zero`, `limsup_pos_of_tendsto_comp`.
* `IsUniformlyTransient.tendsto_pow`: a uniformly transient set is visited with vanishing
  probability; `IsPetite.isUniformlyTransient_inter_compl`: a petite set meets the complement of
  a maximal Harris set in a uniformly transient set (Proposition 9.1.7 (i)).
* `tendsto_pow_of_firstEntrance`: if `Pⁿ(w, B) → 0` on `H ⊇ B`, then everywhere (the
  first-entrance decomposition (8.18) and dominated convergence).
* `absorbKernel_isHarris_of_maximalHarris`: the chain restricted to a maximal Harris set is
  Harris.
* `IsNull.tendsto_pow_of_isPetite`: for a null chain, `Pⁿ(x, C) → 0` for every petite `C` and
  every `x`.

**Countable spaces** (§18.2.1).
* (18.20) ⇒ (18.21): `potKernel_eq_top_of_limsup_pos`.
* (18.23): `limsup_pow_add_ge` (corrected, see below).
* **Theorem 18.2.1** (p. 470): `theorem_18_2_1` (positive iff some state is positive),
  `theorem_18_2_1_positive` (`P^{nd+r}(x, y) → dπ(y) > 0` for some `r = r(x, y) < d`),
  `theorem_18_2_1_null` (`Pⁿ(x, y) → 0`); `positive_or_null_states`: all states are positive or
  all are null.

**General spaces** (§18.2.2).
* **Theorem 18.2.2** (p. 471): (i) `theorem_18_2_2_i`, a `ψ`-irreducible chain is positive iff
  every `B ∈ B⁺(X)` is positive (`IsPositive.isPositiveSet` for one direction, through
  Theorem 13.3.4 (ii)); (ii) `theorem_18_2_2_ii`, a null chain has all its petite sets null and
  `X` is a countable union of null sets.

**Correction.** (18.23) is printed with a strict inequality,
`lim sup P^{r+s+n}(w, z) > Pʳ(w, x) [lim sup Pⁿ(x, y)] Pˢ(y, z)`; for the one-point chain both
sides are `1` (`eq_18_23_counterexample`). The non-strict inequality `limsup_pow_add_ge` is what
the solidarity argument needs.

**Hypotheses.** The proof of Theorem 18.2.2 (ii) in the book applies Theorem 18.1.3, which
needs aperiodicity and the Harris property. The proof here covers chains of any period that are
not Harris: `C ∩ N` is uniformly transient for the non-Harris part `N`, and on the maximal Harris
set the chain is a Harris null chain, handled on each cycle class (`NullPeriodic`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Null and positive sets -/

/-- A set `A` is **null** (MT p. 471) if `Pⁿ(x, A) → 0` for every `x ∈ A`. -/
def IsNullSet (P : Kernel X X) (A : Set X) : Prop :=
  ∀ x ∈ A, Tendsto (fun n => (P ^ n : Kernel X X) x A) atTop (𝓝 0)

/-- A set `A` is **positive** (MT p. 471) if `lim sup Pⁿ(x, A) > 0` for every `x ∈ A`. -/
def IsPositiveSet (P : Kernel X X) (A : Set X) : Prop :=
  ∀ x ∈ A, 0 < limsup (fun n => (P ^ n : Kernel X X) x A) atTop

/-- A sequence in `[0, ∞]` tends to `0` iff its `lim sup` is `0`. -/
theorem tendsto_zero_iff_limsup_eq_zero {f : ℕ → ℝ≥0∞} :
    Tendsto f atTop (𝓝 0) ↔ limsup f atTop = 0 := by
  constructor
  · intro h; exact h.limsup_eq
  · intro h
    refine tendsto_of_le_liminf_of_limsup_le (zero_le) (le_of_eq h)
      (isBoundedUnder_of_eventually_le (Eventually.of_forall fun _ => le_top))
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun _ => zero_le))

/-- A nonempty null set is not positive. -/
theorem IsNullSet.not_isPositiveSet {P : Kernel X X} {A : Set X} (hA : IsNullSet P A)
    (hne : A.Nonempty) : ¬ IsPositiveSet P A := fun hpos => by
  obtain ⟨x, hx⟩ := hne
  have := hpos x hx
  rw [tendsto_zero_iff_limsup_eq_zero.1 (hA x hx)] at this
  exact lt_irrefl _ this

/-! ### Tools -/

/-- A uniformly transient set is visited with vanishing probability:
`Pⁿ(x, D) → 0` for every `x` (`U(x, D) < ∞`, Proposition 8.3.1 (i)). -/
theorem IsUniformlyTransient.tendsto_pow {P : Kernel X X} [IsMarkovKernel P] {D : Set X}
    (hD : IsUniformlyTransient P D) (x : X) :
    Tendsto (fun n => (P ^ n : Kernel X X) x D) atTop (𝓝 0) := by
  obtain ⟨hDm, M, hM, hb⟩ := hD
  have hU := proposition_8_3_1_i P hDm hb x
  have hfin : potKernel P x D ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hM⟩) hU
  rw [potKernel, Kernel.sum_apply, Measure.sum_apply _ hDm] at hfin
  rw [← tendsto_add_atTop_iff_nat 1]
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin

variable [MeasurableSpace.CountablyGenerated X] in
/-- A petite set meets the complement of a maximal Harris set in a uniformly transient set (the
second part of Proposition 9.1.7 (i), which needs no recurrence of the petite set). -/
theorem IsPetite.isUniformlyTransient_inter_compl {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C)
    {H : Set X} (hHar : IsMaximalHarrisSet P ψ H) : IsUniformlyTransient P (C ∩ Hᶜ) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨hHm, hHne, habs, -, -⟩ := hHar
  have hnull : ψ Hᶜ = 0 := proposition_4_2_3_i hψ.2.1 hHm hHne habs
  obtain ⟨a, ν, hpet⟩ := hC
  obtain ⟨b, ψb, hpetb, hψb⟩ := proposition_5_5_5_i P hψ hpet
  have hequiv := hψ.equiv hψb
  have hνH : 0 < ψb H := by
    have hn : ψb Hᶜ = 0 := hequiv.2 hnull
    have hu : 0 < ψb univ := pos_iff_ne_zero.2 fun h => hψb.1 (Measure.measure_univ_eq_zero.1 h)
    calc 0 < ψb univ := hu
      _ = ψb (H ∪ Hᶜ) := by rw [union_compl_self]
      _ ≤ ψb H + ψb Hᶜ := measure_union_le _ _
      _ = ψb H := by rw [hn, add_zero]
  obtain ⟨M, ε, hε, hge⟩ := hpetb.exists_pow_absorbing_ge hHm habs hνH
  exact isUniformlyTransient_of_escape P hHm habs (hCm.inter hHm.compl) inter_subset_right hε
    fun x hx => hge x hx.1

/-- **First entrance to `H`.** If `Pⁿ(w, B) → 0` for every `w ∈ H`, then `Pⁿ(x, B) → 0` for every
`x`, for `B ⊆ H`: decompose `Pⁿ⁺¹(x, B)` over the first entrance to `H` (8.18). -/
theorem tendsto_pow_of_firstEntrance {P : Kernel X X} [IsMarkovKernel P] {H B : Set X}
    (hH : MeasurableSet H) (hB : MeasurableSet B) (hBH : B ⊆ H)
    (h : ∀ w ∈ H, Tendsto (fun n => (P ^ n : Kernel X X) w B) atTop (𝓝 0)) (x : X) :
    Tendsto (fun n => (P ^ n : Kernel X X) x B) atTop (𝓝 0) := by
  set T : ℕ → Measure X := fun j => tabooKernel P hH j x with hT
  have hsum : ∑' j, T j H ≤ 1 := by
    rw [hT]; simp only; rw [← hitProb_eq_tsum P hH x]; exact hitProb_le_one P H x
  have hsumt : ∑' j, T j H ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hsum
  -- the taboo term
  have h1 : Tendsto (fun n => T n B) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsumt) (fun n => zero_le)
      fun n => measure_mono hBH
  -- the convolution term
  set g : ℕ → ℕ → ℝ≥0∞ := fun n j =>
    if j < n then ∫⁻ w in H, (P ^ (n - j) : Kernel X X) w B ∂T j else 0 with hg
  have hgle : ∀ n j, g n j ≤ T j H := fun n j => by
    simp only [hg]
    split_ifs
    · calc ∫⁻ w in H, (P ^ (n - j) : Kernel X X) w B ∂T j ≤ ∫⁻ _ in H, 1 ∂T j :=
            setLIntegral_mono measurable_const fun w _ => by
              have := isMarkovKernel_pow P (n - j); exact prob_le_one
        _ = T j H := by rw [setLIntegral_const, one_mul]
    · exact zero_le
  have hgj : ∀ j, Tendsto (fun n => g n j) atTop (𝓝 0) := fun j => by
    have hd := tendsto_lintegral_of_dominated_convergence (μ := (T j).restrict H) (fun _ => 1)
      (fun n => Kernel.measurable_coe (P ^ (n + 1) : Kernel X X) hB)
      (fun n => Eventually.of_forall fun w => by
        have := isMarkovKernel_pow P (n + 1); exact prob_le_one)
      (by
        rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
        exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (tabooKernel_apply_le_one P hH j x H))
      (by
        refine (ae_restrict_iff' hH).2 (Eventually.of_forall fun w hw => ?_)
        exact (h w hw).comp (tendsto_add_atTop_nat 1))
    simp only [lintegral_zero] at hd
    rw [← tendsto_add_atTop_iff_nat (j + 1)]
    refine hd.congr fun n => ?_
    simp only [hg, show j < n + (j + 1) by omega, ↓reduceIte,
      show n + (j + 1) - j = n + 1 by omega]
  have h2 : Tendsto (fun n => ∑' j, g n j) atTop (𝓝 0) := by
    have hd := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
      (fun j => T j H) (F := fun n j => g n j) (fun n => measurable_of_countable _)
      (fun n => Eventually.of_forall fun j => hgle n j)
      (by rw [lintegral_count]; exact hsumt)
      (Eventually.of_forall fun j => hgj j)
    simp only [lintegral_zero, lintegral_count] at hd
    exact hd
  rw [← tendsto_add_atTop_iff_nat 1]
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  rw [pow_succ_eq_firstEntrance P hH n x, Measure.add_apply, Measure.finsetSum_apply]
  congr 1
  rw [tsum_eq_sum (s := Finset.range n) fun j hj => by
    simp only [hg, show ¬ j < n from fun h => hj (Finset.mem_range.2 h), ↓reduceIte]]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [hg, Finset.mem_range.1 hj, ↓reduceIte]
  rw [Measure.bind_apply hB (Kernel.aemeasurable _)]

/-! ### The chain restricted to a maximal Harris set -/

/-- For a maximal Harris set `H` with `ψ(Hᶜ) = 0`, the chain moving by `P` on `H` and jumping to a
probability `σ` carried by `H` off `H` is Harris (no positivity is assumed; compare
`absorbKernel_maximalHarris`). -/
theorem absorbKernel_isHarris_of_maximalHarris {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {H : Set X}
    (hHmax : IsMaximalHarrisSet P ψ H) (hHnull : ψ Hᶜ = 0) (σ : Measure X)
    [IsProbabilityMeasure σ] (hσ : σ Hᶜ = 0) :
    haveI := isMarkovKernel_absorbKernel P hHmax.1 σ
    IsHarris (absorbKernel P hHmax.1 σ) ψ := by
  have hH := hHmax.1
  have := isMarkovKernel_absorbKernel P hH σ
  set K := absorbKernel P hH σ with hKdef
  have hQ : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hH).2 (hHmax.2.2.1 x hx)
  have hψH : 0 < ψ H := by
    have hu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
    calc 0 < ψ univ := hu
      _ ≤ ψ H + ψ Hᶜ := by rw [← union_compl_self H]; exact measure_union_le _ _
      _ = ψ H := by rw [hHnull, add_zero]
  have hLH : ∀ x ∈ H, ∀ A, MeasurableSet A → 0 < ψ A → hitProb K A x = 1 :=
    fun x hx A hA hψA => by
      rw [hitProb_absorbKernel_of_mem hH hQ hA hx]
      exact le_antisymm (hitProb_le_one _ _ _)
        ((hHmax.2.2.2.2 A hA hψA x hx).symm.le.trans (harrisQ_le_hitProb P A x))
  have hLall : ∀ x, ∀ A, MeasurableSet A → 0 < ψ A → hitProb K A x = 1 := fun x A hA hψA => by
    by_cases hxH : x ∈ H
    · exact hLH x hxH A hA hψA
    · have hKx : K x = σ := absorbKernel_of_notMem P hH σ hxH
      rw [hitProb_first_step K hA x, hKx]
      have hae : ∀ᵐ y ∂σ, y ∈ Aᶜ → hitProb K A y = 1 := by
        have : ∀ᵐ y ∂σ, y ∈ H := by rw [ae_iff]; exact hσ
        filter_upwards [this] with y hy _
        exact hLH y hy A hA hψA
      rw [setLIntegral_congr_fun_ae hA.compl hae, setLIntegral_one,
        measure_add_measure_compl hA, measure_univ]
  have hirr : IsPhiIrreducible K ψ := fun A hA hpos x => by
    rw [hLall x A hA hpos]; exact one_pos
  have hmax : IsMaximalIrreducibility K ψ := by
    refine ⟨hψ.1, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
    by_contra hne
    have hnull := hψ.hitSet_null hA h0
    obtain ⟨x, hxH, hx⟩ : ∃ x ∈ H, ¬ 0 < hitProb P A x := by
      by_contra hall
      push Not at hall
      exact hψH.ne' (nonpos_iff_eq_zero.1 (hnull ▸ measure_mono fun y hy => hall y hy))
    have h1 := hφ A hA (pos_iff_ne_zero.2 hne) x
    rw [hitProb_absorbKernel_of_mem hH hQ hA hxH] at h1
    exact hx h1
  exact ⟨hmax, fun A hA hψA => (proposition_9_1_1 K hA fun x _ => hLall x A hA hψA).2⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Null chains do not stay in petite sets**: for a null chain, `Pⁿ(x, C) → 0` for every
petite `C` and every `x` (the proof of Theorem 18.2.2 (ii), MT p. 471). A transient chain has
uniformly transient petite sets (Theorem 8.3.5). A null recurrent chain splits as `H ∪ N`
(Theorem 9.1.5): `C ∩ N` is uniformly transient, and on the Harris set `H` the chain is a Harris
null chain, to which Theorem 18.1.3 applies on each cycle class
(`tendsto_pow_of_isHarris_of_isNull`); the chain enters `H` through a first entrance. -/
theorem IsNull.tendsto_pow_of_isPetite {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hnull : IsNull P ψ) {C : Set X} (hC : IsPetite P C) (x : X) :
    Tendsto (fun n => (P ^ n : Kernel X X) x C) atTop (𝓝 0) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  rcases theorem_8_3_4 P hnull.1 with hrec | htr
  swap
  · exact (theorem_8_3_5 P htr.2 hC).tendsto_pow x
  obtain ⟨H, hHmax, -, hHnull⟩ := theorem_9_1_5 hrec
  have hHm := hHmax.1
  have hQ : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hHm).2 (hHmax.2.2.1 x hx)
  obtain ⟨w₀, hw₀⟩ := hHmax.2.1
  set σ := P w₀ with hσdef
  have hσ : σ Hᶜ = 0 := hQ w₀ hw₀
  have := isMarkovKernel_absorbKernel P hHm σ
  set K := absorbKernel P hHm σ with hKdef
  have hKH : IsHarris K ψ := absorbKernel_isHarris_of_maximalHarris hnull.1 hHmax hHnull σ hσ
  set π := invMeasure P hrec
  have hπ := isInvariantMeasure_invMeasure hrec
  have hπ0 := invMeasure_ne_zero hrec
  have hπH : π Hᶜ = 0 := (theorem_10_4_9_equiv hrec hπ hπ0).1 hHnull
  have hπK : IsInvariantMeasure K π := ⟨hπ.1, by
    unfold IsInvariant
    rw [comp_congr_of_compl_eq_zero hπH fun y hy => absorbKernel_of_mem P hHm σ hy]
    exact hπ.2⟩
  have hKc : ∀ y, K y Hᶜ = 0 := fun y => by
    by_cases hy : y ∈ H
    · rw [hKdef, absorbKernel_of_mem P hHm σ hy]; exact hQ y hy
    · rw [hKdef, absorbKernel_of_notMem P hHm σ hy]; exact hσ
  have hnullK : IsNull K ψ := by
    refine ⟨hKH.1, fun ⟨ν, hν, hνinv⟩ => hnull.2 ⟨ν, hν, ?_⟩⟩
    have hνH : ν Hᶜ = 0 := by
      rw [← hνinv, Measure.bind_apply hHm.compl (Kernel.aemeasurable _)]
      simp [hKc]
    unfold IsInvariant at hνinv ⊢
    rw [← comp_congr_of_compl_eq_zero hνH fun y hy => absorbKernel_of_mem P hHm σ hy]
    exact hνinv
  have hπC : π (C ∩ H) ≠ ∞ :=
    ne_top_of_le_ne_top (hπ.isSubinvariantMeasure.measure_lt_top_of_petite hnull.1 hC).ne
      (measure_mono inter_subset_left)
  have h2 : Tendsto (fun n => (P ^ n : Kernel X X) x (C ∩ H)) atTop (𝓝 0) := by
    refine tendsto_pow_of_firstEntrance hHm (hCm.inter hHm) inter_subset_right
      (fun w hw => ?_) x
    have h := tendsto_pow_of_isHarris_of_isNull hKH hnullK hπK hπ0 (hCm.inter hHm) hπC w
    refine h.congr fun n => ?_
    rw [hKdef, absorbKernel_pow_of_mem hHm hQ n w hw]
  have h1 := (hC.isUniformlyTransient_inter_compl hnull.1 hHmax).tendsto_pow x
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun n => zero_le)
    fun n => ?_
  calc (P ^ n : Kernel X X) x C ≤ (P ^ n : Kernel X X) x (C ∩ Hᶜ ∪ C ∩ H) :=
        measure_mono fun y hy => by
          by_cases h : y ∈ H
          · exact Or.inr ⟨hy, h⟩
          · exact Or.inl ⟨hy, h⟩
    _ ≤ _ := measure_union_le _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.2.2 (ii)** (MT p. 471): if the chain is null, every petite set is null, and `X`
is covered by countably many null sets. -/
theorem theorem_18_2_2_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hnull : IsNull P ψ) :
    (∀ C, IsPetite P C → IsNullSet P C) ∧
      ∃ B : ℕ → Set X, (∀ j, IsNullSet P (B j)) ∧ ⋃ j, B j = univ := by
  refine ⟨fun C hC x _ => hnull.tendsto_pow_of_isPetite hC x, ?_⟩
  obtain ⟨c, ψc, -, Cs, -, hpet, hcov⟩ := proposition_5_5_5_iii_cover P hnull.1
  exact ⟨Cs, fun j x _ => hnull.tendsto_pow_of_isPetite ⟨_, _, hpet j⟩ x, hcov⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a positive chain, every `B ∈ B⁺(X)` is positive (the "positive" half of
Theorem 18.2.2 (i)). The book uses `lim P^{nd+r}(x, A) = dπ(A ∩ D_r)` on `D₀ ∩ H` and
`L(x, D₀ ∩ H) > 0`; here, from `x`, the chain enters the complement of the `ψ`-null set of
Theorem 13.3.4 (ii) at some time `k + 1`, after which the phase averages of `Pⁿ(·, B)` converge
to `π(B) > 0`. -/
theorem IsPositive.isPositiveSet {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {B : Set X} (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    IsPositiveSet P B := by
  intro x _
  obtain ⟨hψ, π, hπp, hπinv⟩ := hpos
  obtain ⟨d, hper⟩ := exists_isPeriod P hψ
  have hd : 0 < d := hper.1
  obtain ⟨N, hNm, hψN, hconv⟩ := theorem_13_3_4_ii ⟨hψ, π, hπp, hπinv⟩ hper hπinv
  have hrec := proposition_10_1_1 ⟨hψ, π, hπp, hπinv⟩
  have hπB : π B ≠ 0 := fun h0 => hψB.ne'
    ((theorem_10_4_9_equiv hrec ⟨inferInstance, hπinv⟩ (IsProbabilityMeasure.ne_zero π)).2 h0)
  by_contra hlim
  have hlim0 : limsup (fun n => (P ^ n : Kernel X X) x B) atTop = 0 :=
    nonpos_iff_eq_zero.1 (not_lt.1 hlim)
  have htend := tendsto_zero_iff_limsup_eq_zero.2 hlim0
  have hψNc : 0 < ψ Nᶜ := by
    have hu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
    calc 0 < ψ univ := hu
      _ ≤ ψ N + ψ Nᶜ := by rw [← union_compl_self N]; exact measure_union_le _ _
      _ = ψ Nᶜ := by rw [hψN, zero_add]
  obtain ⟨k, hk⟩ := (hitProb_pos_iff P hNm.compl x).1 (hψ.2.1 Nᶜ hNm.compl hψNc x)
  have := isMarkovKernel_pow P (k + 1)
  set c := (P ^ (k + 1) : Kernel X X) x Nᶜ with hc
  have hct : c ≠ ∞ := measure_ne_top _ _
  set μ := c⁻¹ • ((P ^ (k + 1) : Kernel X X) x).restrict Nᶜ with hμ
  have hμp : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hk.ne' hct]⟩
  have hμN : μ N = 0 := by
    rw [hμ, Measure.smul_apply, Measure.restrict_apply hNm, inter_compl_self, measure_empty,
      smul_zero]
  have hcv := hconv μ hμN
  -- the phase averages at `B`
  set a : ℕ → ℝ≥0∞ := fun n => ((d : ℝ≥0∞)⁻¹ •
    ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ) B with ha
  have hfin : ∀ n, IsFiniteMeasure ((d : ℝ≥0∞)⁻¹ •
      ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ) := fun n =>
    isFiniteMeasure_phaseAvg (P := P) hd n μ
  have hreal : Tendsto (fun n => (a n).toReal) atTop (𝓝 (π B).toReal) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hcv
    have := abs_measureReal_sub_le_tvNorm ((d : ℝ≥0∞)⁻¹ •
      ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ) π hB
    simpa [measureReal_def, ha, Real.norm_eq_abs] using this
  -- and they tend to `0`
  have hbound : ∀ m, ((P ^ m : Kernel X X) ∘ₘ μ) B ≤
      c⁻¹ * (P ^ (k + 1 + m) : Kernel X X) x B := fun m => by
    rw [hμ, Measure.comp_smul, Measure.smul_apply, smul_eq_mul,
      Kernel.pow_add_apply_eq_lintegral P (k + 1) m x hB, Measure.bind_apply hB
        (Kernel.aemeasurable _)]
    gcongr
    exact Measure.restrict_le_self
  have hzero : Tendsto a atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => (d : ℝ≥0∞)⁻¹ * ∑ r ∈ range d,
        c⁻¹ * (P ^ (k + 1 + (d * n + r)) : Kernel X X) x B) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => ∑ r ∈ range d,
          c⁻¹ * (P ^ (k + 1 + (d * n + r)) : Kernel X X) x B) atTop (𝓝 0) := by
        have hidx : ∀ r : ℕ, Tendsto (fun n => k + 1 + (d * n + r)) atTop atTop := fun r =>
          tendsto_atTop_mono (fun n => by change n ≤ _; nlinarith) tendsto_id
        have := tendsto_finsetSum (range d) fun r _ =>
          ENNReal.Tendsto.const_mul (htend.comp (hidx r))
            (Or.inr (ENNReal.inv_ne_top.2 hk.ne'))
        simpa using this
      have := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.inv_ne_top.2
        (Nat.cast_ne_zero.2 hd.ne' : (d : ℝ≥0∞) ≠ 0)))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => zero_le) fun n => ?_
    simp only [ha, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    gcongr with r
    exact hbound _
  have hreal0 : Tendsto (fun n => (a n).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hzero
    rw [ENNReal.toReal_zero] at this
    exact this
  have hlimeq := tendsto_nhds_unique hreal hreal0
  exact hπB ((ENNReal.toReal_eq_zero_iff _).1 hlimeq |>.resolve_right (measure_ne_top _ _))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 18.2.2 (i)** (MT p. 471): a `ψ`-irreducible chain is positive iff every set in
`B⁺(X)` is positive. -/
theorem theorem_18_2_2_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    IsPositive P ψ ↔ ∀ B, MeasurableSet B → 0 < ψ B → IsPositiveSet P B := by
  refine ⟨fun hpos B hB hψB => hpos.isPositiveSet hB hψB, fun h => ?_⟩
  by_contra hnp
  have hnull := (isPositive_or_isNull hψ).resolve_left hnp
  obtain ⟨C, hC, hψC⟩ := exists_petite_pos hψ
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  exact ((theorem_18_2_2_ii hnull).1 C hC).not_isPositiveSet
    (nonempty_of_measure_ne_zero hψC.ne') (h C hCm hψC)

/-! ### Countable spaces (§18.2.1) -/

/-- (18.20) ⇒ (18.21) (MT p. 469): if `lim sup Pⁿ(x, A) > 0` then `U(x, A) = Σ Pⁿ(x, A) = ∞`. -/
theorem potKernel_eq_top_of_limsup_pos {P : Kernel X X} {A : Set X} (hA : MeasurableSet A)
    {x : X} (h : 0 < limsup (fun n => (P ^ n : Kernel X X) x A) atTop) :
    potKernel P x A = ∞ := by
  by_contra hfin
  rw [potKernel, Kernel.sum_apply, Measure.sum_apply _ hA] at hfin
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin
  rw [tendsto_add_atTop_iff_nat 1 (f := fun n => (P ^ n : Kernel X X) x A)] at h0
  rw [tendsto_zero_iff_limsup_eq_zero.1 h0] at h
  exact lt_irrefl _ h

/-- A state `α` is **null** (MT p. 470) if `Pⁿ(α, α) → 0`. -/
def IsNullState (P : Kernel X X) (α : X) : Prop :=
  Tendsto (fun n => (P ^ n : Kernel X X) α {α}) atTop (𝓝 0)

/-- A state `α` is **positive** (MT p. 470) if `lim sup Pⁿ(α, α) > 0`. -/
def IsPositiveState (P : Kernel X X) (α : X) : Prop :=
  0 < limsup (fun n => (P ^ n : Kernel X X) α {α}) atTop

/-- A null state is not positive. -/
theorem IsNullState.not_isPositiveState {P : Kernel X X} {α : X} (h : IsNullState P α) :
    ¬ IsPositiveState P α := fun hp => by
  rw [IsPositiveState, tendsto_zero_iff_limsup_eq_zero.1 h] at hp
  exact lt_irrefl _ hp

/-- A subsequence limit bounds the `lim sup` from below: if `f(φ(n)) → L > 0` along
`φ → ∞`, then `lim sup f > 0`. -/
theorem limsup_pos_of_tendsto_comp {f : ℕ → ℝ≥0∞} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {L : ℝ≥0∞} (hL : 0 < L) (h : Tendsto (f ∘ φ) atTop (𝓝 L)) : 0 < limsup f atTop := by
  by_contra h0
  have h1 := (tendsto_zero_iff_limsup_eq_zero.2 (nonpos_iff_eq_zero.1 (not_lt.1 h0))).comp hφ
  exact hL.ne' (tendsto_nhds_unique h h1)

variable [Countable X] [MeasurableSingletonClass X]

omit [Countable X] in
/-- The **solidarity inequality** (18.23) in its correct, non-strict form:
`Pʳ(w, x) [lim sup Pⁿ(x, y)] Pˢ(y, z) ≤ lim sup P^{r+s+n}(w, z)`. -/
theorem limsup_pow_add_ge (P : Kernel X X) [IsMarkovKernel P] (r s : ℕ) (w x y z : X) :
    (P ^ r : Kernel X X) w {x} * limsup (fun n => (P ^ n : Kernel X X) x {y}) atTop *
        (P ^ s : Kernel X X) y {z} ≤
      limsup (fun n => (P ^ (r + s + n) : Kernel X X) w {z}) atTop := by
  have hle : ∀ n, (P ^ r : Kernel X X) w {x} * (P ^ n : Kernel X X) x {y} *
      (P ^ s : Kernel X X) y {z} ≤ (P ^ (r + s + n) : Kernel X X) w {z} := fun n => by
    calc (P ^ r : Kernel X X) w {x} * (P ^ n : Kernel X X) x {y} * (P ^ s : Kernel X X) y {z}
        ≤ (P ^ (r + n) : Kernel X X) w {y} * (P ^ s : Kernel X X) y {z} := by
          gcongr; exact pow_add_singleton_ge P r n w x y
      _ ≤ (P ^ (r + n + s) : Kernel X X) w {z} := pow_add_singleton_ge P (r + n) s w y z
      _ = (P ^ (r + s + n) : Kernel X X) w {z} := by rw [show r + n + s = r + s + n by ring]
  calc (P ^ r : Kernel X X) w {x} * limsup (fun n => (P ^ n : Kernel X X) x {y}) atTop *
        (P ^ s : Kernel X X) y {z}
      = limsup (fun n => (P ^ r : Kernel X X) w {x} * (P ^ n : Kernel X X) x {y} *
          (P ^ s : Kernel X X) y {z}) atTop := by
        have h1 := isMarkovKernel_pow P r
        have h2 := isMarkovKernel_pow P s
        rw [ENNReal.limsup_mul_const_of_ne_top (measure_ne_top _ _),
          ENNReal.limsup_const_mul_of_ne_top (measure_ne_top _ _)]
        ring
    _ ≤ _ := limsup_le_limsup (Eventually.of_forall hle)

/-- **Correction to (18.23)** (MT p. 470): the inequality is printed strict,
`lim sup P^{r+s+n}(w, z) > Pʳ(w, x) [lim sup Pⁿ(x, y)] Pˢ(y, z)`; it fails for the one-point
chain (irreducible), where both sides equal `1` for all `r, s`. The correct form is
`limsup_pow_add_ge`. -/
theorem eq_18_23_counterexample :
    ∃ (P : Kernel Unit Unit) (_ : IsMarkovKernel P), IsIrreducibleChain P ∧
      ∀ r s : ℕ, ¬ ((P ^ r : Kernel Unit Unit) () {()} *
        limsup (fun n => (P ^ n : Kernel Unit Unit) () {()}) atTop *
          (P ^ s : Kernel Unit Unit) () {()} <
        limsup (fun n => (P ^ (r + s + n) : Kernel Unit Unit) () {()}) atTop) := by
  have hM : IsMarkovKernel (Kernel.id : Kernel Unit Unit) := inferInstance
  have h1 : ∀ m, ((Kernel.id : Kernel Unit Unit) ^ m) () {()} = 1 := fun m => by
    have := isMarkovKernel_pow (Kernel.id : Kernel Unit Unit) m
    rw [show ({()} : Set Unit) = Set.univ from Set.ext fun u => by simp, measure_univ]
  refine ⟨Kernel.id, hM, ⟨(), eq_univ_of_forall fun u => ?_⟩, fun r s h => ?_⟩
  · exact ⟨Leads.refl _ _, Leads.refl _ _⟩
  · simp only [h1, mul_one, limsup_const] at h
    exact lt_irrefl 1 h

variable [Nonempty X]

omit [Countable X] [Nonempty X] in
/-- Every singleton is petite (it is small with `ν = P(y, ·)`). -/
theorem isPetite_singleton (P : Kernel X X) [IsMarkovKernel P] (y : X) : IsPetite P {y} :=
  ⟨_, _, proposition_5_5_3 (m := 1) (ν := P y)
    ⟨measurableSet_singleton y, one_pos, IsProbabilityMeasure.ne_zero _, fun x hx => by
      rw [mem_singleton_iff.1 hx, pow_one]⟩⟩

omit [Nonempty X] in
/-- **Theorem 18.2.1**, the null case (MT p. 470): for a null chain on a countable space,
`Pⁿ(x, y) → 0` for all `x, y`. -/
theorem theorem_18_2_1_null {P : Kernel X X} [IsMarkovKernel P]
    (hnull : IsNull P Measure.count) (x y : X) :
    Tendsto (fun n => (P ^ n : Kernel X X) x {y}) atTop (𝓝 0) :=
  hnull.tendsto_pow_of_isPetite (isPetite_singleton P y) x

/-- **Theorem 18.2.1**, the positive case (MT p. 470): for a positive irreducible chain on a
countable space with period `d` and invariant probability `π`, for all `x, y` there is
`0 ≤ r < d` with `P^{nd+r}(x, y) → dπ(y) > 0`. -/
theorem theorem_18_2_1_positive {P : Kernel X X} [IsMarkovKernel P]
    (hirr : IsIrreducibleChain P) (hpos : IsPositive P Measure.count) :
    ∃ d : ℕ, 0 < d ∧ ∀ x y : X, ∃ r : ℕ, r < d ∧
      Tendsto (fun n => (P ^ (d * n + r) : Kernel X X) x {y}) atTop
        (𝓝 ((d : ℝ≥0∞) * stationaryDist P hpos {y})) ∧
        0 < (d : ℝ≥0∞) * stationaryDist P hpos {y} := by
  set π := stationaryDist P hpos with hπdef
  have hπp := isProbabilityMeasure_stationaryDist hpos
  have hπ := isInvariant_stationaryDist hpos
  have hrec := proposition_10_1_1 hpos
  have hH := isHarris_of_countable hirr hrec
  obtain ⟨d, hper⟩ := exists_isPeriod P hpos.1
  obtain ⟨D, hD⟩ := hper.2.1
  have hd : 0 < d := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hequiv := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hcov : ∀ z : X, ∃ i, z ∈ D i := fun z => by
    by_contra h
    push Not at h
    have : z ∈ (⋃ i, D i)ᶜ := by simpa using h
    have h0 := hD.null_compl
    rw [Measure.count_eq_zero_iff] at h0
    rw [h0] at this
    exact this
  refine ⟨d, hd, fun x y => ?_⟩
  obtain ⟨j, hj⟩ := hcov x
  obtain ⟨l, hl⟩ := hcov y
  refine ⟨(l - j).val, ZMod.val_lt _, ?_, ?_⟩
  · set r := (l - j).val
    have hrl : j + (r : ZMod d) = l := by simp [r]
    have := isMarkovKernel_pow P r
    have hμ : (P ^ r : Kernel X X) x (D l)ᶜ = 0 := by
      have := hD.pow_compl_eq_zero r hj; rwa [hrl] at this
    have hconv := hD.tendsto_tvNorm_pow_mul hd hper ⟨hH, hpos⟩ hπ l ((P ^ r : Kernel X X) x) hμ
    have hlimv : cycleInv π D l {y} = d * π {y} := by
      rw [cycleInv, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton y),
        inter_eq_left.2 (singleton_subset_iff.2 hl), smul_eq_mul]
    have hfin : ∀ n, IsFiniteMeasure ((P ^ (d * n) : Kernel X X) ∘ₘ (P ^ r : Kernel X X) x) :=
      fun n => by have := isMarkovKernel_pow P (d * n); infer_instance
    have hcI : IsFiniteMeasure (cycleInv π D l) := by
      have := hD.isProbabilityMeasure_cycleInv hd hrec hπ l; infer_instance
    have hreal : Tendsto (fun n => ((P ^ (d * n + r) : Kernel X X) x {y}).toReal) atTop
        (𝓝 (cycleInv π D l {y}).toReal) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hconv
      have heq : (P ^ (d * n) : Kernel X X) ∘ₘ (P ^ r : Kernel X X) x =
          (P ^ (d * n + r) : Kernel X X) x := by
        rw [← dirac_kernel (P ^ r : Kernel X X) x, Measure.comp_assoc, ← pow_add_eq,
          dirac_kernel, add_comm r]
      rw [heq]
      have := isMarkovKernel_pow P (d * n + r)
      have h := abs_measureReal_sub_le_tvNorm ((P ^ (d * n + r) : Kernel X X) x)
        (cycleInv π D l) (measurableSet_singleton y)
      simpa [measureReal_def, Real.norm_eq_abs] using h
    have hne : cycleInv π D l {y} ≠ ∞ := measure_ne_top _ _
    rw [← hlimv]
    have h2 := (ENNReal.tendsto_ofReal hreal)
    rw [ENNReal.ofReal_toReal hne] at h2
    refine h2.congr fun n => ?_
    have := isMarkovKernel_pow P (d * n + r)
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · refine ENNReal.mul_pos (by exact_mod_cast hd.ne') fun h0 => ?_
    have := hequiv.2 h0
    rw [Measure.count_singleton] at this
    exact one_ne_zero this

/-- **Theorem 18.2.1** (MT p. 470): an irreducible chain on a countable space is positive iff some
state is positive. -/
theorem theorem_18_2_1 {P : Kernel X X} [IsMarkovKernel P] (hirr : IsIrreducibleChain P) :
    IsPositive P Measure.count ↔ ∃ α, IsPositiveState P α := by
  have hψ := isMaximalIrreducibility_count P hirr
  constructor
  · intro hpos
    obtain ⟨α⟩ := ‹Nonempty X›
    refine ⟨α, ?_⟩
    obtain ⟨d, hd, h⟩ := theorem_18_2_1_positive hirr hpos
    obtain ⟨r, -, hlim, hposl⟩ := h α α
    exact limsup_pos_of_tendsto_comp (φ := fun n => d * n + r)
      (tendsto_atTop_mono (fun n => by change n ≤ _; nlinarith) tendsto_id) hposl hlim
  · rintro ⟨α, hα⟩
    by_contra hnp
    have hnull := (isPositive_or_isNull hψ).resolve_left hnp
    exact (show IsNullState P α from theorem_18_2_1_null hnull α α).not_isPositiveState hα

/-- The solidarity of §18.2.1 (MT p. 470): in an irreducible chain on a countable space, either
every state is positive or every state is null. -/
theorem positive_or_null_states {P : Kernel X X} [IsMarkovKernel P]
    (hirr : IsIrreducibleChain P) :
    (∀ α, IsPositiveState P α) ∨ ∀ α, IsNullState P α := by
  rcases isPositive_or_isNull (isMaximalIrreducibility_count P hirr) with hpos | hnull
  · left
    intro α
    obtain ⟨d, hd, h⟩ := theorem_18_2_1_positive hirr hpos
    obtain ⟨r, -, hlim, hposl⟩ := h α α
    exact limsup_pos_of_tendsto_comp (φ := fun n => d * n + r)
      (tendsto_atTop_mono (fun n => by change n ≤ _; nlinarith) tendsto_id) hposl hlim
  · exact Or.inr fun α => theorem_18_2_1_null hnull α α

end MeynTweedie.GeneralizedDrift
