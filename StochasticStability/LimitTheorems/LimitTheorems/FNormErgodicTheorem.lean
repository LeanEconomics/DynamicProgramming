/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.FNormErgodic
import LimitTheorems.PeriodicErgodic

/-!
# The `f`-Norm Ergodic Theorem (MT Theorem 14.0.1, §14.3)

Meyn and Tweedie, pp. 336–337 and 349–352. The state space is countably generated, `ψ` is a
maximal irreducibility measure, and `f : X → [0, ∞]` is measurable with `f ≥ 1`.

**The `f`-regular states.** `fRegular_states_eq`: for a positive aperiodic chain with
`π(f) < ∞` and an `f`-regular `C ∈ B⁺(X)` (Theorem 14.2.11), the `f`-regular states are exactly
`{G_C(·, f) < ∞}`, a full absorbing set.

**Results.**
* **Proposition 14.3.1** (p. 349), for a positive chain with a minorization on `C ∈ B⁺(X)`,
  `ν(C) > 0` (strong aperiodicity): (i) `proposition_14_3_1_i`, if `π(f) = ∞` then `Pᵏ(x, f) → ∞`
  for every `x`; (ii) `proposition_14_3_1_ii`, if `π(f) < ∞`, almost every state is `f`-regular
  and `‖Pᵏ(x, ·) − π‖_f → 0` for every `f`-regular `x`; (iii) `proposition_14_3_1_iii`, an
  `f`-regular chain is `f`-ergodic.
* **Theorem 14.3.3** (p. 350), for a positive aperiodic chain: (i) `theorem_14_3_3_i`; (ii)
  `theorem_14_3_3_ii`; (iii) `theorem_14_3_3_iii` (`f`-regular ⇒ `f`-ergodic) and
  `theorem_14_3_3_iii_converse` (an `f`-ergodic chain is `f`-regular on a full absorbing set).
* **Theorem 14.3.4** (`theorem_14_3_4`, p. 350), (14.24).
* **Theorem 14.3.5** (`theorem_14_3_5`, p. 351), (14.25).
* **Theorem 14.0.1** (the `f`-Norm Ergodic Theorem, p. 336): `theorem_14_0_1` (the equivalence of
  (i) positivity with `π(f) < ∞`, (ii) (14.2) for a non-empty petite set and (iii) (14.3) for a
  petite set and a `V` finite somewhere), and `theorem_14_0_1_consequences` (`S_V` is full and
  absorbing, sublevel sets of `V` are `f`-regular, (14.4), and (14.5) when `π(V) < ∞`).

**Corrections.**
* Theorem 14.0.1 (ii) needs `C ≠ ∅`, as Theorems 11.0.1 and 14.2.4: `∅` is petite and satisfies
  (14.2) vacuously.
* "Any sublevel set of `V` satisfies (14.2)" needs the sublevel set to be in `B⁺(X)`:
  `theorem_14_0_1_counterexample` is a positive Harris aperiodic chain on `Bool` with a solution of
  (14.3) (`f ≡ 1`) whose sublevel set `{true}` has `E_true[τ_{true}] = ∞`. Every sublevel set is
  `f`-regular (Theorem 14.2.3), which is (14.2) for sublevel sets in `B⁺(X)`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-! ### The `f`-regular states -/

/-- **The `f`-regular states** (MT Theorems 14.2.5, 14.3.3): for a positive aperiodic chain with
`π(f) < ∞` there is an `f`-regular `C ∈ B⁺(X)`, `V = G_C(·, f)` solves (V3) for the petite set
`C`, and the `f`-regular states are exactly `{V < ∞}`, a full absorbing set. -/
theorem exists_fRegular_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ C : Set X, IsFRegularSet P ψ f C ∧ 0 < ψ C ∧ IsPetite P C ∧
      ∃ b : ℝ≥0∞, b ≠ ∞ ∧ DriftV3 P (gKernelFn P C f) f b C ∧
        {x | IsFRegularState P ψ f x} = {x | gKernelFn P C f x ≠ ∞} ∧
        IsFull ψ {x | gKernelFn P C f x ≠ ∞} ∧ IsAbsorbing P {x | gKernelFn P C f x ≠ ∞} := by
  obtain ⟨C, hC, hψC⟩ := exists_fRegularSet_pos hpos hap hπ hf hπf
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_14_2_3_ii hpos.1 hf hf1 hC hψC
  obtain ⟨M, hM, hbound⟩ := hC.2 C hC.1 hψC
  have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
  obtain ⟨-, -, -, hfull, habs, -⟩ := theorem_14_2_5 hpos.1 hf hf1 hC hψC
  refine ⟨C, hC, hψC, hpet, b, hb, hdrift, ?_, hfull, habs⟩
  ext x
  simp only [mem_ofPred_eq]
  refine ⟨fun hx => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp)
    (hx C hC.1 hψC), hM⟩) (gKernelFn_le_two_mul hC.1 hf hfC x), fun hx =>
    isFRegularState_of_driftV3 hpos.1 (measurable_gKernelFn hC.1 hf) hf hb hpet hdrift hx⟩

/-! ### `Pᵏ(x, f) → ∞` when `π(f) = ∞` -/

/-- For a positive aperiodic chain with `π(f) = ∞`, `Pᵏ(x, f) → ∞` for every `x`
(MT Proposition 14.3.1 (i) and Theorem 14.3.3 (i)): `Pᵏ(y, f ∧ M) → π(f ∧ M)` off a `ψ`-null set
(total variation convergence), and Fatou's lemma from a time `n₀` with `P^{n₀}(x, ·)` charging the
good set. -/
theorem tendsto_lintegral_top_of_isPositive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π = ∞)
    (x : X) : Tendsto (fun k => ∫⁻ y, f y ∂(P ^ k : Kernel X X) x) atTop (𝓝 ∞) := by
  obtain ⟨N, hNm, hψN, hconv⟩ := tendsto_tvNorm_of_isPositive hpos hap hπ
  -- on the good set the truncations converge
  have hgood : ∀ y ∉ N, Tendsto (fun k => ∫⁻ z, f z ∂(P ^ k : Kernel X X) y) atTop (𝓝 ∞) := by
    intro y hy
    have htv := hconv (Measure.dirac y) (by rw [Measure.dirac_apply' _ hNm,
      indicator_of_notMem hy])
    simp_rw [dirac_kernel] at htv
    refine ENNReal.tendsto_nhds_top fun K => ?_
    -- choose a truncation level with `π(f ∧ M) > K + 1`
    have hsup : ⨆ M : ℕ, ∫⁻ z, min (f z) M ∂π = ∞ := by
      rw [← lintegral_iSup (fun M => hf.min measurable_const) fun a b hab z =>
        min_le_min le_rfl (by exact_mod_cast hab)]
      rw [← hπf]
      congr 1
      funext z
      refine le_antisymm (iSup_le fun M => min_le_left _ _) ?_
      by_cases hz : f z = ∞
      · rw [hz]
        refine le_of_forall_lt fun c hc => ?_
        obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hc.ne
        exact lt_of_lt_of_le hM (le_iSup_of_le M (by simp))
      · obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hz
        exact le_iSup_of_le M (le_of_eq (min_eq_left hM.le).symm)
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ((K + 1 : ℕ) : ℝ≥0∞) < ∫⁻ z, min (f z) M ∂π := by
      by_contra hc
      push Not at hc
      have := iSup_le hc
      rw [hsup] at this
      exact ENNReal.natCast_ne_top _ (top_le_iff.1 this)
    -- `Pᵏ(y, f ∧ M) → π(f ∧ M)`
    set g : X → ℝ := fun z => (min (f z) M).toReal with hg
    have hgm : Measurable g := (hf.min measurable_const).ennreal_toReal
    have hgb : ∀ z, |g z| ≤ M := fun z => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg M)
        (by rw [ENNReal.ofReal_natCast]; exact min_le_right _ _)
    have hMpos : (0 : ℝ) < M + 1 := by positivity
    have : ∀ n, IsFiniteMeasure ((P ^ n : Kernel X X) y) := fun n => by
      have := isMarkovKernel_pow P n; infer_instance
    have hlim := tendsto_integral_of_tendsto_tvNorm htv hgm hMpos
      (fun z => (hgb z).trans (by linarith))
    have hfinM : ∀ (ρ : Measure X) [IsProbabilityMeasure ρ],
        ∫⁻ z, min (f z) M ∂ρ = ENNReal.ofReal (∫ z, g z ∂ρ) := fun ρ _ => by
      rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_bound hgm.aestronglyMeasurable
        (M : ℝ) (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgb z))
        (Eventually.of_forall fun z => ENNReal.toReal_nonneg)]
      refine lintegral_congr fun z => ?_
      rw [hg, ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top M)
        (min_le_right _ _))]
    have hlimE : Tendsto (fun k => ∫⁻ z, min (f z) M ∂(P ^ k : Kernel X X) y) atTop
        (𝓝 (∫⁻ z, min (f z) M ∂π)) := by
      have : ∀ k, IsProbabilityMeasure ((P ^ k : Kernel X X) y) := fun k => by
        have := isMarkovKernel_pow P k; infer_instance
      simp_rw [fun k => hfinM ((P ^ k : Kernel X X) y), hfinM π]
      exact ENNReal.tendsto_ofReal hlim
    have hev := hlimE.eventually (lt_mem_nhds hM)
    filter_upwards [hev] with k hk
    calc (K : ℝ≥0∞) < ((K + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self K
      _ < ∫⁻ z, min (f z) M ∂(P ^ k : Kernel X X) y := hk
      _ ≤ ∫⁻ z, f z ∂(P ^ k : Kernel X X) y := lintegral_mono fun z => min_le_left _ _
  -- the good set is charged from `x` at some time `n₀`
  have hψNc : 0 < ψ Nᶜ := by
    refine pos_iff_ne_zero.2 fun h0 => hpos.1.1 ?_
    rw [← Measure.measure_univ_eq_zero, ← union_compl_self N]
    exact measure_union_null hψN h0
  obtain ⟨n₀, hn₀⟩ := (hitProb_pos_iff P hNm.compl x).1 (hpos.1.2.1 _ hNm.compl hψNc x)
  have hmeas : ∀ k, Measurable fun y => ∫⁻ z, f z ∂(P ^ k : Kernel X X) y := fun k =>
    hf.lintegral_kernel
  have hfatou : ∫⁻ y, liminf (fun k => ∫⁻ z, f z ∂(P ^ k : Kernel X X) y) atTop
      ∂(P ^ (n₀ + 1) : Kernel X X) x ≤
      liminf (fun k => ∫⁻ y, ∫⁻ z, f z ∂(P ^ k : Kernel X X) y ∂(P ^ (n₀ + 1) : Kernel X X) x)
        atTop := lintegral_liminf_le hmeas
  have hinf : ∫⁻ y, liminf (fun k => ∫⁻ z, f z ∂(P ^ k : Kernel X X) y) atTop
      ∂(P ^ (n₀ + 1) : Kernel X X) x = ∞ := by
    refine top_le_iff.1 ?_
    calc ∞ = ∫⁻ _ in Nᶜ, ∞ ∂(P ^ (n₀ + 1) : Kernel X X) x := by
          rw [setLIntegral_const, ENNReal.top_mul hn₀.ne']
      _ ≤ ∫⁻ y in Nᶜ, liminf (fun k => ∫⁻ z, f z ∂(P ^ k : Kernel X X) y) atTop
            ∂(P ^ (n₀ + 1) : Kernel X X) x :=
          setLIntegral_mono' hNm.compl fun y hy => le_of_eq ((hgood y hy).liminf_eq).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hcomp : ∀ k, ∫⁻ y, ∫⁻ z, f z ∂(P ^ k : Kernel X X) y ∂(P ^ (n₀ + 1) : Kernel X X) x =
      ∫⁻ z, f z ∂(P ^ (k + (n₀ + 1)) : Kernel X X) x := fun k => by
    rw [pow_add P k (n₀ + 1)]
    exact (Kernel.lintegral_comp (P ^ k) (P ^ (n₀ + 1)) x hf).symm
  rw [hinf] at hfatou
  simp_rw [hcomp] at hfatou
  rw [← tendsto_add_atTop_iff_nat (n₀ + 1)]
  exact tendsto_of_le_liminf_of_limsup_le hfatou le_top

/-! ### Proposition 14.3.1 -/

/-- **Proposition 14.3.1 (i)** (MT p. 349): for a positive chain with a minorization on
`C ∈ B⁺(X)`, `ν(C) > 0`, `π(f) = ∞` forces `Pᵏ(x, f) → ∞` for every `x`. -/
theorem proposition_14_3_1_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π = ∞) (x : X) :
    Tendsto (fun k => ∫⁻ y, f y ∂(P ^ k : Kernel X X) x) atTop (𝓝 ∞) :=
  tendsto_lintegral_top_of_isPositive hpos (isAperiodic_of_minorization hpos.1 M hψC hνC) hπ hf
    hπf x

/-- **Proposition 14.3.1 (ii)** (MT p. 349): for a positive chain with a minorization on
`C ∈ B⁺(X)`, `ν(C) > 0`, and `π(f) < ∞`, `f ≥ 1`, almost every state is `f`-regular, and
`‖Pᵏ(x, ·) − π‖_f → 0` for every `f`-regular state `x`. -/
theorem proposition_14_3_1_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    IsFull ψ {x | IsFRegularState P ψ f x} ∧ ∀ x, IsFRegularState P ψ f x →
      Tendsto (fun k => fNorm f ((P ^ k : Kernel X X) x) π) atTop (𝓝 0) := by
  obtain ⟨S, hS, hfull⟩ := M.exists_fRegular_cover hpos hψC hπ hf hπf
  obtain ⟨R, hRm, hψR, hconv⟩ := M.tendsto_fNorm hpos hψC hνC hπ hf hf1 hπf
  refine ⟨measure_mono_null (fun x hx => ?_) hfull, fun x hx => ?_⟩
  · simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion, not_exists] at hx ⊢
    intro n hn
    exact hx ((hS n).isFRegularState hn)
  · have h := hconv (Measure.dirac x) (by
      rw [lintegral_dirac' _ (measurable_fSumReturn P hRm hf)]; exact hx R hRm hψR)
    simp_rw [dirac_kernel] at h
    exact h

/-- **Proposition 14.3.1 (iii)** (MT p. 349): under the hypotheses of (ii), an `f`-regular chain is
`f`-ergodic. -/
theorem proposition_14_3_1_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hreg : IsFRegularChain P ψ f) :
    IsFErgodic P ψ f π := by
  have hπf := hreg.lintegral_ne_top (proposition_10_1_1 hpos) hf hf1 hπ
  obtain ⟨-, hconv⟩ := proposition_14_3_1_ii hpos M hψC hνC hπ hf hf1 hπf
  have hregc : IsRegularChain P ψ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    exact ⟨Cs, fun n => (hCs n).isRegularSet hf1, hcov⟩
  obtain ⟨Cs, hCs, hcov⟩ := hreg
  refine ⟨hf1, hregc.isPositiveHarris hpos.1, inferInstance, hπ, hπf, fun x => hconv x ?_⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  exact (hCs m).isFRegularState hm

/-! ### Theorem 14.3.3 -/

/-- **Theorem 14.3.3 (i)** (MT p. 350): for a positive aperiodic chain, `π(f) = ∞` forces
`Pᵏ(x, f) → ∞` for every `x`. -/
theorem theorem_14_3_3_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π = ∞)
    (x : X) : Tendsto (fun k => ∫⁻ y, f y ∂(P ^ k : Kernel X X) x) atTop (𝓝 ∞) :=
  tendsto_lintegral_top_of_isPositive hpos hap hπ hf hπf x

/-- **Theorem 14.3.3 (ii)** (MT p. 350): for a positive aperiodic chain with `π(f) < ∞`, `f ≥ 1`,
the set `S_f` of `f`-regular states is full and absorbing, and `‖Pᵏ(x, ·) − π‖_f → 0` for every
`x ∈ S_f`. -/
theorem theorem_14_3_3_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    IsFull ψ {x | IsFRegularState P ψ f x} ∧ IsAbsorbing P {x | IsFRegularState P ψ f x} ∧
      ∀ x, IsFRegularState P ψ f x →
        Tendsto (fun k => fNorm f ((P ^ k : Kernel X X) x) π) atTop (𝓝 0) := by
  obtain ⟨C, hC, hψC, hpet, b, hb, hdrift, heq, hfull, habs⟩ :=
    exists_fRegular_driftV3 hpos hap hπ hf hf1 hπf
  have hVm := measurable_gKernelFn hC.1 hf (P := P)
  refine ⟨heq ▸ hfull, heq ▸ habs, fun x hx => ?_⟩
  have hVx : gKernelFn P C f x ≠ ∞ := by
    have : x ∈ {x | IsFRegularState P ψ f x} := hx
    rw [heq] at this; exact this
  have h := tendsto_fNorm_of_driftV3 hpos hap hπ hVm hf hf1 hb hpet hdrift hπf (Measure.dirac x)
    (by rw [lintegral_dirac' _ hVm]; exact hVx)
  simp_rw [dirac_kernel] at h
  exact h

/-- **Theorem 14.3.3 (iii)** (MT p. 350): for an aperiodic chain (`ψ`-irreducible), an
`f`-regular chain (`f ≥ 1`) is `f`-ergodic. -/
theorem theorem_14_3_3_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hreg : IsFRegularChain P ψ f) :
    ∃ π : Measure X, IsFErgodic P ψ f π := by
  have hregc : IsRegularChain P ψ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    exact ⟨Cs, fun n => (hCs n).isRegularSet hf1, hcov⟩
  have hph := hregc.isPositiveHarris hψ
  obtain ⟨-, π, hπp, hπ⟩ := hph.2
  have hπf := hreg.lintegral_ne_top (proposition_10_1_1 hph.2) hf hf1 hπ
  obtain ⟨-, -, hconv⟩ := theorem_14_3_3_ii hph.2 hap hπ hf hf1 hπf
  obtain ⟨Cs, hCs, hcov⟩ := hreg
  refine ⟨π, hf1, hph, hπp, hπ, hπf, fun x => hconv x ?_⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  exact (hCs m).isFRegularState hm

/-- **Theorem 14.3.3 (iii)**, converse (MT p. 350): an `f`-ergodic aperiodic chain is `f`-regular
on a full absorbing set. -/
theorem theorem_14_3_3_iii_converse {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) {π : Measure X}
    (h : IsFErgodic P ψ f π) :
    ∃ S : Set X, IsFull ψ S ∧ IsAbsorbing P S ∧ IsFRegularOn P ψ f S := by
  obtain ⟨hf1, hph, hπp, hπ, hπf, -⟩ := h
  obtain ⟨C, hC, hψC, -, -, -, -, -, -, -⟩ := exists_fRegular_driftV3 hph.2 hap hπ hf hf1 hπf
  obtain ⟨-, -, -, hfull, habs, hon⟩ := theorem_14_2_5 hph.2.1 hf hf1 hC hψC
  exact ⟨_, hfull, habs, hon⟩

/-! ### Theorems 14.3.4 and 14.3.5 -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- `∫ λ(dx) ∫ μ(dy) (A (V(x) + V(y)) + B) = A (λ(V) + μ(V)) + B` for probabilities. -/
theorem lintegral_lintegral_affine {V : X → ℝ≥0∞} (hV : Measurable V) (A B : ℝ≥0∞)
    (l m : Measure X) [IsProbabilityMeasure l] [IsProbabilityMeasure m] :
    ∫⁻ x, ∫⁻ y, (A * (V x + V y) + B) ∂m ∂l = A * (∫⁻ x, V x ∂l + ∫⁻ y, V y ∂m) + B := by
  have h1 : ∀ x, ∫⁻ y, (A * (V x + V y) + B) ∂m = A * V x + (A * ∫⁻ y, V y ∂m + B) := fun x => by
    calc ∫⁻ y, (A * (V x + V y) + B) ∂m = ∫⁻ y, (A * V y + (A * V x + B)) ∂m :=
          lintegral_congr fun y => by ring
      _ = A * ∫⁻ y, V y ∂m + (A * V x + B) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ hV]
      _ = A * V x + (A * ∫⁻ y, V y ∂m + B) := by ring
  simp_rw [h1]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ hV]
  ring

omit [MeasurableSpace.CountablyGenerated X] in
/-- An `f`-regular probability `λ` has `λ(G_C(·, f)) < ∞` for an `f`-regular `C ∈ B⁺(X)`. -/
theorem lintegral_gKernelFn_ne_top {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : IsFRegularMeasure P ψ f μ) :
    ∫⁻ x, gKernelFn P C f x ∂μ ≠ ∞ := by
  obtain ⟨M, hM, hbound⟩ := hC.2 C hC.1 hψC
  have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono (gKernelFn_le_two_mul hC.1 hf hfC))
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (measurable_fSumReturn P hC.1 hf)]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (hμ C hC.1 hψC), hM⟩

/-- **Theorem 14.3.4** (MT p. 350), (14.24): for a positive aperiodic chain with `π(f) < ∞`,
`f ≥ 1`, and an `f`-regular `C ∈ B⁺(X)`, there is `M_f < ∞` such that for all probabilities `λ`,
`μ`, `Σ_{n ≥ 1} ∫ λ(dx) ∫ μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ M_f (λ(V) + μ(V) + 1)` with
`V = G_C(·, f)`; for `f`-regular `λ`, `μ` the right side is finite
(`lintegral_gKernelFn_ne_top`). The book assumes a positive Harris chain; positivity suffices. -/
theorem theorem_14_3_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ (l m : Measure X) [IsProbabilityMeasure l] [IsProbabilityMeasure m],
      ∑' n, ∫⁻ x, ∫⁻ y, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ∂m ∂l ≤ M * (∫⁻ x, gKernelFn P C f x ∂l + ∫⁻ y, gKernelFn P C f y ∂m + 1) := by
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_14_2_3_ii hpos.1 hf hf1 hC hψC
  have hVm := measurable_gKernelFn hC.1 hf (P := P)
  obtain ⟨A, B, hA, hB, hbd⟩ := tsum_fNorm_le_of_driftV3 hpos hap hπ hVm hf hf1 hb hpet hdrift hπf
  refine ⟨max A B, max_ne_top hA hB, fun l m _ _ => ?_⟩
  calc ∑' n, ∫⁻ x, ∫⁻ y, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ∂m ∂l
      ≤ ∫⁻ x, ∫⁻ y, ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x)
          ((P ^ (n + 1) : Kernel X X) y) ∂m ∂l :=
        (tsum_lintegral_le_lintegral_tsum l _).trans (lintegral_mono fun x =>
          tsum_lintegral_le_lintegral_tsum m _)
    _ ≤ ∫⁻ x, ∫⁻ y, (A * (gKernelFn P C f x + gKernelFn P C f y) + B) ∂m ∂l := by
        refine lintegral_mono fun x => lintegral_mono fun y => ?_
        have h1 := hbd x y
        rw [tsum_eq_zero_add' (f := fun n => fNorm f ((P ^ n : Kernel X X) x)
          ((P ^ n : Kernel X X) y)) ENNReal.summable] at h1
        exact le_add_self.trans h1
    _ = A * (∫⁻ x, gKernelFn P C f x ∂l + ∫⁻ y, gKernelFn P C f y ∂m) + B :=
        lintegral_lintegral_affine hVm A B l m
    _ ≤ max A B * (∫⁻ x, gKernelFn P C f x ∂l + ∫⁻ y, gKernelFn P C f y ∂m) + max A B * 1 :=
        add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) (by rw [mul_one]; exact le_max_right _ _)
    _ = max A B * (∫⁻ x, gKernelFn P C f x ∂l + ∫⁻ y, gKernelFn P C f y ∂m + 1) := by ring

omit [MeasurableSpace.CountablyGenerated X] in
/-- `‖λPⁿ − π‖_f ≤ ∫ λ(dx) ∫ π(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f` for an invariant probability `π`. -/
theorem fNorm_comp_pow_le_lintegral {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (f : X → ℝ≥0∞) (n : ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π ≤
      ∫⁻ x, ∫⁻ y, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π ∂μ := by
  have := isMarkovKernel_pow P n
  conv_lhs => rw [← hπ.pow n]
  exact fNorm_comp_le_lintegral (P ^ n) f μ π

/-- **Theorem 14.3.5** (MT p. 351), (14.25): for a positive aperiodic chain whose invariant
probability `π` is `f`-regular (`f ≥ 1`), `π(f) < ∞`, and for every `f`-regular `C ∈ B⁺(X)` there is
`B_f < ∞` with `Σₙ ‖λPⁿ − π‖_f ≤ B_f (λ(V) + 1)` for every probability `λ`, `V = G_C(·, f)`. -/
theorem theorem_14_3_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπreg : IsFRegularMeasure P ψ f π) :
    ∫⁻ x, f x ∂π ≠ ∞ ∧ ∀ C : Set X, IsFRegularSet P ψ f C → 0 < ψ C →
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ],
        ∑' n, fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π ≤ B * (∫⁻ x, gKernelFn P C f x ∂μ + 1) := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hpos.1.1 (Measure.measure_univ_eq_zero.1 h)
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := ne_top_of_le_ne_top (hπreg univ MeasurableSet.univ hψu)
    (lintegral_mono fun x => le_fSumReturn P univ hf x)
  refine ⟨hπf, fun C hC hψC => ?_⟩
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_14_2_3_ii hpos.1 hf hf1 hC hψC
  have hVm := measurable_gKernelFn hC.1 hf (P := P)
  have hπV := lintegral_gKernelFn_ne_top hf hC hψC hπreg
  obtain ⟨A, B, hA, hB, hbd⟩ := tsum_fNorm_le_of_driftV3 hpos hap hπ hVm hf hf1 hb hpet hdrift hπf
  set K := A * ∫⁻ y, gKernelFn P C f y ∂π + B with hK
  have hKne : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA hπV, hB⟩
  refine ⟨max A K, max_ne_top hA hKne, fun μ _ => ?_⟩
  calc ∑' n, fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π
      ≤ ∑' n, ∫⁻ x, ∫⁻ y, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π ∂μ :=
        ENNReal.tsum_le_tsum fun n => fNorm_comp_pow_le_lintegral hπ f n μ
    _ ≤ ∫⁻ x, ∫⁻ y, ∑' n, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π ∂μ :=
        (tsum_lintegral_le_lintegral_tsum μ _).trans (lintegral_mono fun x =>
          tsum_lintegral_le_lintegral_tsum π _)
    _ ≤ ∫⁻ x, ∫⁻ y, (A * (gKernelFn P C f x + gKernelFn P C f y) + B) ∂π ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hbd x y
    _ = A * ∫⁻ x, gKernelFn P C f x ∂μ + K := by
        rw [lintegral_lintegral_affine hVm A B μ π, hK]; ring
    _ ≤ max A K * ∫⁻ x, gKernelFn P C f x ∂μ + max A K * 1 :=
        add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) (by rw [mul_one]; exact le_max_right _ _)
    _ = max A K * (∫⁻ x, gKernelFn P C f x ∂μ + 1) := by ring

omit [MeasurableSpace.CountablyGenerated X] in
/-- `∫ G dδ_x ≤ G(x)` for every `G ≥ 0`, measurable or not. -/
theorem lintegral_dirac_le (x : X) (G : X → ℝ≥0∞) : ∫⁻ y, G y ∂Measure.dirac x ≤ G x := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral]
  exact iSup_le fun g => iSup_le fun hg => iSup_le fun hgG => by
    rw [lintegral_dirac' _ hg]; exact hgG x

omit [MeasurableSpace.CountablyGenerated X] in
/-- `‖Pⁿ(x, ·) − π‖_f ≤ ∫ π(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f` for an invariant probability `π`. -/
theorem fNorm_pow_le_lintegral {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    fNorm f ((P ^ n : Kernel X X) x) π ≤
      ∫⁻ y, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π := by
  have h := fNorm_comp_pow_le_lintegral hπ f n (Measure.dirac x)
  rw [dirac_kernel] at h
  exact h.trans (lintegral_dirac_le x _)

/-- **(iii) ⇒ (i) of Theorem 14.0.1**: (14.3) for a petite set and a `V` finite somewhere makes
the chain positive, and every invariant probability has `π(f) ≤ b π(C) < ∞`. -/
theorem isPositive_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hb : b ≠ ∞) {x₀ : X} (hx₀ : V x₀ ≠ ∞) (hdrift : DriftV3 P V f b C) :
    IsPositive P ψ ∧ ∀ π : Measure X, IsProbabilityMeasure π → IsInvariant P π →
      ∫⁻ x, f x ∂π ≠ ∞ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨-, hfull⟩ := lemma_14_2_1 hψ.2.1 hV hb hdrift hx₀
  -- a sublevel set of `V` lies in `B⁺(X)` and is regular
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < ψ {x | V x ≤ n} := by
    by_contra hcon
    push Not at hcon
    apply hψ.1
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc ψ univ ≤ ψ ((⋃ n : ℕ, {x | V x ≤ n}) ∪ {x | V x ≠ ∞}ᶜ) := by
          refine measure_mono fun x _ => ?_
          by_cases hx : V x = ∞
          · exact Or.inr (by simpa using hx)
          · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
            exact Or.inl (mem_iUnion.2 ⟨n, hn.le⟩)
      _ ≤ ψ (⋃ n : ℕ, {x | V x ≤ n}) + ψ {x | V x ≠ ∞}ᶜ := measure_union_le _ _
      _ = 0 := by
          rw [hfull, add_zero]
          exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon n)
  have hreg := (theorem_14_2_6_sublevel hψ hV hf hb hpet hdrift
    (ENNReal.natCast_ne_top n)).isRegularSet hf1
  have hpos := isPositive_of_isRegularSet hψ hreg hn
  exact ⟨hpos, fun π hπp hπ => ne_top_of_le_ne_top (ENNReal.mul_ne_top hb (measure_ne_top π C))
    (lintegral_le_of_driftV3 hpos hπ hV hf hb hCm hdrift hx₀)⟩

/-! ### Theorem 14.0.1: the `f`-Norm Ergodic Theorem -/

/-- **Theorem 14.0.1** (the `f`-Norm Ergodic Theorem, MT p. 336), the equivalences: for a
`ψ`-irreducible aperiodic chain and `f ≥ 1`, the following are equivalent:
(i) the chain is positive with an invariant probability `π` with `π(f) < ∞`;
(ii) some **non-empty** petite set `C` has `sup_{x ∈ C} E_x[Σ_{n<τ_C} f(Φₙ)] < ∞` (14.2);
(iii) some petite set `C`, `b < ∞` and `V ≥ 0` finite at some `x₀` satisfy (14.3),
`PV ≤ V − f + b 1_C`. -/
theorem theorem_14_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) :
    List.TFAE [∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π ∧ ∫⁻ x, f x ∂π ≠ ∞,
      ∃ C : Set X, IsPetite P C ∧ C.Nonempty ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧
        ∀ x ∈ C, fSumReturn P C f x ≤ M,
      ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧ Measurable V ∧ b ≠ ∞ ∧
        (∃ x₀, V x₀ ≠ ∞) ∧ DriftV3 P V f b C] := by
  tfae_have 1 → 2 := by
    rintro ⟨π, hπp, hπ, hπf⟩
    have hpos : IsPositive P ψ := ⟨hψ, π, hπp, hπ⟩
    obtain ⟨C, hC, hψC⟩ := exists_fRegularSet_pos hpos hap hπ hf hπf
    exact ⟨C, ((theorem_14_2_4 hψ hf hf1).2 ⟨hC, hψC⟩)⟩
  tfae_have 2 → 3 := by
    rintro ⟨C, hpet, ⟨c, hc⟩, M, hM, hbound⟩
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
    have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
    refine ⟨C, gKernelFn P C f, M + M, hpet, measurable_gKernelFn hCm hf,
      ENNReal.add_ne_top.2 ⟨hM, hM⟩, ⟨c, ?_⟩, driftV3_gKernelFn hCm hf fun x hx =>
        (tabooPotFn_le hCm hf hfC x).trans (add_le_add (hbound x hx) le_rfl)⟩
    rw [gKernelFn_of_mem hCm hf hc]
    exact ne_top_of_le_ne_top hM (hfC c hc)
  tfae_have 3 → 1 := by
    rintro ⟨C, V, b, hpet, hV, hb, ⟨x₀, hx₀⟩, hdrift⟩
    obtain ⟨⟨-, π, hπp, hπ⟩, hfin⟩ := isPositive_of_driftV3 hψ hf hf1 hpet hV hb hx₀ hdrift
    exact ⟨π, hπp, hπ, hfin π hπp hπ⟩
  tfae_finish

/-- **Theorem 14.0.1**, the consequences (MT p. 337): if (14.3) holds for a petite `C`, `b < ∞`
and `V` finite at some `x₀`, for a `ψ`-irreducible aperiodic chain and `f ≥ 1`, then with `π` the
invariant probability:
* `S_V = {V < ∞}` is absorbing and full;
* every sublevel set `{V ≤ ℓ}`, `ℓ < ∞`, is `f`-regular, so satisfies (14.2) when it lies in
  `B⁺(X)` (`theorem_14_0_1_counterexample`: not otherwise);
* (14.4): `‖Pⁿ(x, ·) − π‖_f → 0` for every `x ∈ S_V`;
* (14.5): if `π(V) < ∞`, there is `B_f < ∞` with `Σₙ ‖Pⁿ(x, ·) − π‖_f ≤ B_f (V(x) + 1)` for
  every `x`. -/
theorem theorem_14_0_1_consequences {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞}
    (hpet : IsPetite P C) (hV : Measurable V) (hb : b ≠ ∞) {x₀ : X} (hx₀ : V x₀ ≠ ∞)
    (hdrift : DriftV3 P V f b C) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) :
    IsAbsorbing P {x | V x ≠ ∞} ∧ IsFull ψ {x | V x ≠ ∞} ∧
      (∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → IsFRegularSet P ψ f {x | V x ≤ ℓ}) ∧
      (∀ x, V x ≠ ∞ → Tendsto (fun n => fNorm f ((P ^ n : Kernel X X) x) π) atTop (𝓝 0)) ∧
      (∫⁻ x, V x ∂π ≠ ∞ → ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x,
        ∑' n, fNorm f ((P ^ n : Kernel X X) x) π ≤ B * (V x + 1)) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨habs, hfull⟩ := lemma_14_2_1 hψ.2.1 hV hb hdrift hx₀
  obtain ⟨hpos, hfin⟩ := isPositive_of_driftV3 hψ hf hf1 hpet hV hb hx₀ hdrift
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := hfin π inferInstance hπ
  refine ⟨habs, hfull, fun ℓ hℓ => theorem_14_2_6_sublevel hψ hV hf hb hpet hdrift hℓ,
    fun x hx => ?_, fun hπV => ?_⟩
  · have h := tendsto_fNorm_of_driftV3 hpos hap hπ hV hf hf1 hb hpet hdrift hπf (Measure.dirac x)
      (by rw [lintegral_dirac' _ hV]; exact hx)
    simp_rw [dirac_kernel] at h
    exact h
  · obtain ⟨A, B, hA, hB, hbd⟩ := tsum_fNorm_le_of_driftV3 hpos hap hπ hV hf hf1 hb hpet hdrift
      hπf
    set K := A * ∫⁻ y, V y ∂π + B with hK
    have hKne : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA hπV, hB⟩
    refine ⟨max A K, max_ne_top hA hKne, fun x => ?_⟩
    calc ∑' n, fNorm f ((P ^ n : Kernel X X) x) π
        ≤ ∑' n, ∫⁻ y, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π :=
          ENNReal.tsum_le_tsum fun n => fNorm_pow_le_lintegral hπ f n x
      _ ≤ ∫⁻ y, ∑' n, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ∂π :=
          tsum_lintegral_le_lintegral_tsum π _
      _ ≤ ∫⁻ y, (A * (V x + V y) + B) ∂π := lintegral_mono fun y => hbd x y
      _ = A * V x + K := by
          have h1 : ∀ y, A * (V x + V y) + B = A * V y + (A * V x + B) := fun y => by ring
          simp_rw [h1]
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ hV, hK]
          ring
      _ ≤ max A K * V x + max A K * 1 :=
          add_le_add (mul_le_mul' (le_max_left _ _) le_rfl)
            (by rw [mul_one]; exact le_max_right _ _)
      _ = max A K * (V x + 1) := by ring

omit [MeasurableSpace.CountablyGenerated X] in
/-- **The counterexample to "every sublevel set of `V` satisfies (14.2)"** (Theorem 14.0.1, MT
p. 337). The chain on `Bool` that jumps to `false` is positive Harris and aperiodic, (14.3) holds
with `f ≡ 1`, `C = X`, `b = 5` and `V(true) = 1`, `V(false) = 5`, but the sublevel set
`{V ≤ 1} = {true}` has `E_true[Σ_{n<τ_{true}} 1] = E_true[τ_{true}] = ∞`. (It is not in `B⁺(X)`.) -/
theorem theorem_14_0_1_counterexample :
    IsPositiveHarris toFalseKernel (Measure.dirac false) ∧
      IsAperiodic toFalseKernel (Measure.dirac false) ∧ IsPetite toFalseKernel univ ∧
      DriftV3 toFalseKernel (fun x => if x then 1 else 5) (fun _ => 1) 5 univ ∧
      {x : Bool | (if x then (1 : ℝ≥0∞) else 5) ≤ 1} = {true} ∧
      fSumReturn toFalseKernel {true} (fun _ => 1) true = ∞ := by
  obtain ⟨hH, hinv, hpet, hdrift, hset, hmean⟩ := theorem_11_0_1_counterexample
  obtain ⟨M, hMC, hMν, -⟩ := exists_minorization_of_le (P := toFalseKernel) MeasurableSet.univ
    ⟨true, mem_univ _⟩ (ν' := Measure.dirac false) (fun x _ => by simp [toFalseKernel])
    (by simp)
  have hap := isAperiodic_of_minorization hH.1 M (by rw [hMC]; simp) (by rw [hMν]; exact one_pos)
  exact ⟨⟨hH, hH.1, Measure.dirac false, inferInstance, hinv⟩, hap, hpet, fun x => hdrift x, hset,
    by rw [fSumReturn_one]; exact hmean⟩

end MeynTweedie.LimitTheorems
