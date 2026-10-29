/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.FSplitChain

/-!
# `f`-ergodicity for general chains (MT §14.2.3, §14.3, Theorem 14.0.1)

Meyn and Tweedie, pp. 336–337 and 348–352. The state space is countably generated, `ψ` is a
maximal irreducibility measure and `f : X → [0, ∞]` is measurable with `f ≥ 1`. An aperiodic chain
has an `m`-skeleton with a minorization on a set in `B⁺(X)` (`exists_skeleton_minorization`); the
split chain of that skeleton carries the atom arguments of §14.1 (`FSplitChain`), and
Lemma 14.3.2 brings the results back to the chain.

**A criterion for `π(f) < ∞`.**
* **Theorem 14.3.7** (`theorem_14_3_7`, p. 352): if `π` is a finite invariant measure and
  `PV + f ≤ V + s` with `V < ∞` `π`-a.e., then `π(f) ≤ π(s)`. The proof truncates `V` at `n`
  and needs no ergodic theorem: `min(PV, n) + f 1_{V ≤ n} ≤ min(V, n) + s`, integrate against `π`,
  cancel `π(min(V, n)) ≤ n π(X)`, and let `n → ∞`.
* `lintegral_le_of_driftV3`: under (V3), `π(f) ≤ b π(C)`.

**Tools.**
* `isAperiodic_of_minorization`: a minorization `P ≥ δν` on `C ∈ B⁺(X)` with `ν(C) > 0` makes the
  chain aperiodic (`1 ∈ E_C`).
* `lemma_14_3_2_i_measure`: Lemma 14.3.2 (i) from an initial law.
* `tendsto_fNorm_of_driftV3`: for an aperiodic positive chain, (V3) with a petite `C` and
  `λ(V) < ∞` give `‖λPⁿ − π‖_f → 0` (the skeleton drift, Theorem 14.2.3 (i) for the skeleton, the
  split skeleton, Lemma 14.3.2).
* `tsum_fNorm_le_of_driftV3`: under the same hypotheses
  `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A (V(x) + V(y)) + B`.

**Results.**
* **Theorem 14.2.11** (`theorem_14_2_11`, p. 348): for a positive aperiodic chain with
  `π(f) < ∞` there are `f`-regular sets `S_f(n)` whose union is full.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Theorem 14.3.7 -/

/-- **Theorem 14.3.7** (MT p. 352): let `π` be a finite invariant measure and let `V`, `f ≥ 0` be
measurable and `s ≥ 0` arbitrary, with `PV + f ≤ V + s` and `V < ∞` `π`-a.e. Then
`π(f) ≤ π(s)`. (The book assumes a positive recurrent chain and finite-valued functions, and argues
through the ergodic theorems; the truncation argument here needs neither.) -/
theorem theorem_14_3_7 {P : Kernel X X} [IsMarkovKernel P] {π : Measure X} [IsFiniteMeasure π]
    (hπ : IsInvariant P π) {V f s : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    (hdrift : ∀ x, ∫⁻ y, V y ∂P x + f x ≤ V x + s x)
    (hVfin : ∀ᵐ x ∂π, V x ≠ ∞) : ∫⁻ x, f x ∂π ≤ ∫⁻ x, s x ∂π := by
  -- truncate at level `n`
  have hstep : ∀ n : ℕ, ∫⁻ x, {x | V x ≤ n}.indicator f x ∂π ≤ ∫⁻ x, s x ∂π := fun n => by
    set Vn : X → ℝ≥0∞ := fun x => min (V x) n with hVn
    have hVnm : Measurable Vn := hV.min measurable_const
    have hSm : MeasurableSet {x | V x ≤ n} := measurableSet_le hV measurable_const
    -- `P Vn ≤ min(PV, n)`
    have hPVn : ∀ x, ∫⁻ y, Vn y ∂P x ≤ min (∫⁻ y, V y ∂P x) n := fun x =>
      le_min (lintegral_mono fun y => min_le_left _ _) (by
        calc ∫⁻ y, Vn y ∂P x ≤ ∫⁻ _, (n : ℝ≥0∞) ∂P x := lintegral_mono fun y => min_le_right _ _
          _ = n := by rw [lintegral_const, measure_univ, mul_one])
    -- the pointwise inequality
    have hpt : ∀ x, ∫⁻ y, Vn y ∂P x + {x | V x ≤ n}.indicator f x ≤ Vn x + s x := fun x => by
      by_cases hx : V x ≤ n
      · rw [indicator_of_mem (show x ∈ {x | V x ≤ (n : ℝ≥0∞)} from hx)]
        have e : Vn x = V x := min_eq_left hx
        change ∫⁻ y, Vn y ∂P x + f x ≤ Vn x + s x
        rw [e]
        exact (add_le_add ((hPVn x).trans (min_le_left _ _)) le_rfl).trans (hdrift x)
      · rw [indicator_of_notMem (show x ∉ {x | V x ≤ (n : ℝ≥0∞)} from hx), add_zero]
        have e : Vn x = n := min_eq_right (not_le.1 hx).le
        change ∫⁻ y, Vn y ∂P x ≤ Vn x + s x
        rw [e]
        exact ((hPVn x).trans (min_le_right _ _)).trans le_self_add
    have hinv : ∫⁻ x, ∫⁻ y, Vn y ∂P x ∂π = ∫⁻ x, Vn x ∂π := by
      rw [lintegral_comp_kernel P π hVnm, hπ]
    have hfin : ∫⁻ x, Vn x ∂π ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
        (measure_ne_top π univ)) ?_
      calc ∫⁻ x, Vn x ∂π ≤ ∫⁻ _, (n : ℝ≥0∞) ∂π := lintegral_mono fun x => min_le_right _ _
        _ = n * π univ := lintegral_const _
    have hint := lintegral_mono (μ := π) hpt
    rw [lintegral_add_left hVnm.lintegral_kernel, hinv, lintegral_add_left hVnm] at hint
    exact (ENNReal.add_le_add_iff_left hfin).1 hint
  -- monotone convergence in `n`
  have hmono : Monotone fun n : ℕ => {x | V x ≤ n}.indicator f := fun m n hmn x =>
    indicator_le_indicator_of_subset (fun y hy => le_trans (show V y ≤ m from hy)
      (by exact_mod_cast hmn)) (fun _ => zero_le) x
  have hae : f =ᵐ[π] fun x => ⨆ n : ℕ, {x | V x ≤ n}.indicator f x := by
    filter_upwards [hVfin] with x hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    refine le_antisymm (le_iSup_of_le n ?_) (iSup_le fun n => indicator_le_self _ f x)
    rw [indicator_of_mem (show x ∈ {x | V x ≤ (n : ℝ≥0∞)} from hn.le)]
  rw [lintegral_congr_ae hae, lintegral_iSup (fun n => hf.indicator
    (measurableSet_le hV measurable_const)) hmono]
  exact iSup_le hstep

variable [MeasurableSpace.CountablyGenerated X] in
/-- Under (V3) with `V` finite at one point, a positive chain has `π(f) ≤ b π(C) < ∞`
(Theorem 14.3.7 with `s = b 1_C`). -/
theorem lintegral_le_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f) {b : ℝ≥0∞} (hb : b ≠ ∞)
    {C : Set X} (hCm : MeasurableSet C) (h : DriftV3 P V f b C) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    ∫⁻ x, f x ∂π ≤ b * π C := by
  obtain ⟨-, hfull⟩ := lemma_14_2_1 hpos.1.2.1 hV hb h hx₀
  have hrec := proposition_10_1_1 hpos
  have hequiv := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hVfin : ∀ᵐ x ∂π, V x ≠ ∞ := by
    rw [ae_iff]
    refine hequiv.1 (measure_mono_null (fun x hx => ?_) hfull)
    simpa using hx
  have h1 := theorem_14_3_7 hπ hV hf h hVfin
  rwa [lintegral_indicator_const hCm] at h1

/-! ### Aperiodicity from a minorization -/

/-- A minorization `P(x, ·) ≥ δν` on `C ∈ B⁺(X)` with `ν(C) > 0` (strong aperiodicity with the small
set in `B⁺(X)`) makes the chain aperiodic: `1 ∈ E_C`, so `g.c.d. E_C = 1`. -/
theorem isAperiodic_of_minorization {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (M : Minorization P) (hψC : 0 < ψ M.C)
    (hνC : 0 < M.ν M.C) : IsAperiodic P ψ := by
  have := M.isProbabilityMeasure_ν
  have hsm : IsSmallSet P 1 (M.δ • M.ν) M.C := ⟨M.measurableSet_C, one_pos,
    smul_measure_ne_zero (IsProbabilityMeasure.ne_zero M.ν) M.δ_pos.ne', fun x hx =>
      Measure.le_intro fun A _ _ => by
        rw [pow_one, Measure.smul_apply, smul_eq_mul]; exact M.le_apply hx A⟩
  have hνC' : 0 < (M.δ • M.ν) M.C := by
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos M.δ_pos.ne' hνC.ne'
  have hper := isPeriod_gcd P hψ hsm hψC hνC'
  have h1 : setGcd (smallTimes P M.C (M.δ • M.ν)) ∣ 1 :=
    setGcd_dvd (smallTimes_isAddClosed P hνC') (mem_smallTimes_of_isSmallSet hsm) one_pos
      (mem_smallTimes_of_isSmallSet hsm)
  rwa [Nat.dvd_one.1 h1] at hper

/-! ### Lemma 14.3.2 from an initial law -/

/-- **Lemma 14.3.2 (i)** from an initial law: for an invariant probability `π`, `i < m` and a
probability `λ`, `‖λP^{km+i} − π‖_f ≤ ‖λP^{km} − π‖_{f^{(m)}}`. -/
theorem lemma_14_3_2_i_measure {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {m i : ℕ} (hi : i < m) (k : ℕ)
    (f : X → ℝ≥0∞) (μ : Measure X) [IsProbabilityMeasure μ] :
    fNorm f ((P ^ (k * m + i) : Kernel X X) ∘ₘ μ) π ≤
      fNorm (fSkel P m f) ((P ^ (k * m) : Kernel X X) ∘ₘ μ) π := by
  have := isMarkovKernel_pow P i
  have := isMarkovKernel_pow P (k * m)
  have h1 : (P ^ (k * m + i) : Kernel X X) ∘ₘ μ =
      (P ^ i : Kernel X X) ∘ₘ ((P ^ (k * m) : Kernel X X) ∘ₘ μ) := by
    rw [Measure.comp_assoc, add_comm, pow_add]; rfl
  have h2 : π = (P ^ i : Kernel X X) ∘ₘ π := (hπ.pow i).symm
  rw [h1]
  conv_lhs => rw [h2]
  exact (fNorm_comp_le (P ^ i) f _ π).trans
    (fNorm_mono (fun y => lintegral_pow_le_fSkel P hi f y) _ _)

/-! ### Convergence and summability from (V3) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Convergence from (V3)** (MT Theorems 14.3.3 (ii), 14.0.1, (14.4)): for an aperiodic positive
chain with invariant probability `π`, if (V3) holds for a petite set `C` and `π(f) < ∞`, `f ≥ 1`,
then `‖λPⁿ − π‖_f → 0` for every probability `λ` with `λ(V) < ∞`. -/
theorem tendsto_fNorm_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV3 P V f b C) (hπf : ∫⁻ x, f x ∂π ≠ ∞) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∫⁻ x, V x ∂μ ≠ ∞) :
    Tendsto (fun n => fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hpos.1 hap
  have := isMarkovKernel_pow P m
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ :=
    (theorem_10_4_5_positive hpos.1 hap).1.1 hpos m hm
  have hψm : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ := hposQ.1
  have hπQ : IsInvariant (P ^ m : Kernel X X) π := hπ.pow m
  have hf'm := measurable_fSkel P m hf
  have hπf' : ∫⁻ x, fSkel P m f x ∂π ≠ ∞ := by
    rw [lintegral_fSkel P hπ m hf]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hπf
  obtain ⟨R, hRm, hψR, hconv⟩ := M.tendsto_fNorm hposQ hψC hνC hπQ hf'm
    (one_le_fSkel P hm hf hf1) hπf'
  obtain ⟨C', b', hC', hb', hdrift'⟩ := driftV3_skeleton hpos.1 hap hV hf hf1 hb hC h hm
  obtain ⟨k, ν, hsm⟩ := hC'
  have hpet' : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsm⟩
  obtain ⟨c, hc, hbound⟩ := theorem_14_2_3_i (f := fun x => 2⁻¹ * fSkel P m f x) hψm hV
    (measurable_const.mul hf'm) hb' hpet' hdrift' hRm hψR
  have hsum : ∀ x, fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x ≤ 2 * (V x + c) := fun x => by
    have h1 := hbound x
    rw [fSumReturn_const_mul _ hRm hf'm] at h1
    calc fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x
        = 2 * (2⁻¹ * fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * (V x + c) := mul_le_mul' le_rfl h1
  have hμR : ∫⁻ x, fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hsum)
    rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const, lintegral_const,
      measure_univ, mul_one]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hμ, hc⟩)
  have hQ := hconv μ hμR
  have hdiv : Tendsto (fun n => n / m) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hQ.comp hdiv)
    (fun _ => zero_le) fun n => ?_
  simp only [Function.comp_apply, ← pow_mul]
  have hn : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  calc fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π
      = fNorm f ((P ^ (n / m * m + n % m) : Kernel X X) ∘ₘ μ) π := by rw [← hn]
    _ ≤ fNorm (fSkel P m f) ((P ^ (n / m * m) : Kernel X X) ∘ₘ μ) π :=
        lemma_14_3_2_i_measure hπ (Nat.mod_lt n (by omega)) (n / m) f μ
    _ = fNorm (fSkel P m f) ((P ^ (m * (n / m)) : Kernel X X) ∘ₘ μ) π := by rw [mul_comm]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Summability from (V3)** (MT Theorems 14.3.4, 14.0.1, (14.5)): for an aperiodic positive
chain, if (V3) holds for a petite set `C` and `π(f) < ∞`, `f ≥ 1`, there are `A, B < ∞` with
`Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A (V(x) + V(y)) + B` for all `x`, `y` (the sum over `n ≥ 0`). -/
theorem tsum_fNorm_le_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {V f : X → ℝ≥0∞} (hV : Measurable V) (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV3 P V f b C) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧ ∀ x y,
      ∑' n, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ≤ A * (V x + V y) + B := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hpos.1 hap
  have := isMarkovKernel_pow P m
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ :=
    (theorem_10_4_5_positive hpos.1 hap).1.1 hpos m hm
  have hψm : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ := hposQ.1
  have hπQ : IsInvariant (P ^ m : Kernel X X) π := hπ.pow m
  have hf'm := measurable_fSkel P m hf
  have hπf' : ∫⁻ x, fSkel P m f x ∂π ≠ ∞ := by
    rw [lintegral_fSkel P hπ m hf]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hπf
  obtain ⟨R, hRm, hψR, A₀, B₀, hA₀, hB₀, hbd⟩ := M.tsum_fNorm_le hposQ hψC hνC hπQ hf'm
    (one_le_fSkel P hm hf hf1) hπf'
  obtain ⟨C', b', hC', hb', hdrift'⟩ := driftV3_skeleton hpos.1 hap hV hf hf1 hb hC h hm
  obtain ⟨k, ν, hsm⟩ := hC'
  have hpet' : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsm⟩
  obtain ⟨c, hc, hbound⟩ := theorem_14_2_3_i (f := fun x => 2⁻¹ * fSkel P m f x) hψm hV
    (measurable_const.mul hf'm) hb' hpet' hdrift' hRm hψR
  have hsum : ∀ x, fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x ≤ 2 * (V x + c) := fun x => by
    have h1 := hbound x
    rw [fSumReturn_const_mul _ hRm hf'm] at h1
    calc fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x
        = 2 * (2⁻¹ * fSumReturn (P ^ m : Kernel X X) R (fSkel P m f) x) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * (V x + c) := mul_le_mul' le_rfl h1
  -- `f^{(m)} ≤ V + b m`
  have hfs : ∀ x, fSkel P m f x ≤ V x + b * m := fun x => by
    have h1 := driftV3_iterate hV hCm h m x
    refine le_add_self.trans (h1.trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_)))
    calc ∑ i ∈ range m, (P ^ i : Kernel X X) x C ≤ ∑ _i ∈ range m, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun i _ => by
            have := isMarkovKernel_pow P i
            exact prob_le_one
      _ = m := by simp
  have hmne : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  refine ⟨m * (1 + 2 * A₀), m * (2 * (b * m) + A₀ * (4 * c) + B₀),
    ENNReal.mul_ne_top hmne (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (by simp) hA₀⟩),
    ENNReal.mul_ne_top hmne (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hb hmne),
        ENNReal.mul_ne_top hA₀ (ENNReal.mul_ne_top (by simp) hc)⟩, hB₀⟩), fun x y => ?_⟩
  -- block the sum by the skeleton
  have hblock : ∀ j, ∑ i ∈ range m, fNorm f ((P ^ (m * j + i) : Kernel X X) x)
      ((P ^ (m * j + i) : Kernel X X) y) ≤
      m * fNorm (fSkel P m f) (((P ^ m) ^ j : Kernel X X) x) (((P ^ m) ^ j : Kernel X X) y) :=
    fun j => by
    calc ∑ i ∈ range m, fNorm f ((P ^ (m * j + i) : Kernel X X) x)
          ((P ^ (m * j + i) : Kernel X X) y)
        ≤ ∑ _i ∈ range m, fNorm (fSkel P m f) (((P ^ m) ^ j : Kernel X X) x)
            (((P ^ m) ^ j : Kernel X X) y) := Finset.sum_le_sum fun i hi => by
          have hi' := Finset.mem_range.1 hi
          have := isMarkovKernel_pow P i
          have := isMarkovKernel_pow P (m * j)
          have := isMarkovKernel_pow (P ^ m) j
          have e : ∀ z, (P ^ (m * j + i) : Kernel X X) z =
              (P ^ i : Kernel X X) ∘ₘ ((P ^ m) ^ j : Kernel X X) z := fun z => by
            rw [← pow_mul, add_comm, pow_add]; rfl
          rw [e x, e y]
          exact (fNorm_comp_le (P ^ i) f _ _).trans
            (fNorm_mono (fun z => lintegral_pow_le_fSkel P hi' f z) _ _)
      _ = m * fNorm (fSkel P m f) (((P ^ m) ^ j : Kernel X X) x)
            (((P ^ m) ^ j : Kernel X X) y) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h0 : fNorm (fSkel P m f) (((P ^ m) ^ 0 : Kernel X X) x) (((P ^ m) ^ 0 : Kernel X X) y) ≤
      (V x + b * m) + (V y + b * m) := by
    rw [pow_zero_apply, pow_zero_apply]
    refine (fNorm_le_add _ _ _).trans ?_
    rw [lintegral_dirac' _ hf'm, lintegral_dirac' _ hf'm]
    exact add_le_add (hfs x) (hfs y)
  calc ∑' n, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y)
      = ∑' j, ∑ i ∈ range m, fNorm f ((P ^ (m * j + i) : Kernel X X) x)
          ((P ^ (m * j + i) : Kernel X X) y) :=
        tsum_eq_tsum_sum_block (fun n => fNorm f ((P ^ n : Kernel X X) x)
          ((P ^ n : Kernel X X) y)) hm
    _ ≤ ∑' j, m * fNorm (fSkel P m f) (((P ^ m) ^ j : Kernel X X) x)
          (((P ^ m) ^ j : Kernel X X) y) := ENNReal.tsum_le_tsum hblock
    _ = m * (fNorm (fSkel P m f) (((P ^ m) ^ 0 : Kernel X X) x) (((P ^ m) ^ 0 : Kernel X X) y) +
          ∑' j, fNorm (fSkel P m f) (((P ^ m) ^ (j + 1) : Kernel X X) x)
            (((P ^ m) ^ (j + 1) : Kernel X X) y)) := by
        rw [ENNReal.tsum_mul_left, tsum_eq_zero_add' ENNReal.summable]
    _ ≤ m * (((V x + b * m) + (V y + b * m)) +
          (A₀ * (2 * (V x + c) + 2 * (V y + c)) + B₀)) :=
        mul_le_mul' le_rfl (add_le_add h0 ((hbd x y).trans (add_le_add (mul_le_mul' le_rfl
          (add_le_add (hsum x) (hsum y))) le_rfl)))
    _ = m * (1 + 2 * A₀) * (V x + V y) + m * (2 * (b * m) + A₀ * (4 * c) + B₀) := by ring

/-! ### Theorem 14.2.11 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.11** (MT p. 348): for a positive aperiodic chain with `π(f) < ∞` there are
`f`-regular sets `S_f(n)` whose union is full. The proof is the book's: the split `m`-skeleton
gives `f^{(m)}`-regular sets for the skeleton (`Minorization.exists_fRegular_cover`), which are
`f`-regular for the chain (Theorem 14.2.9). -/
theorem theorem_14_2_11 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ S : ℕ → Set X, (∀ n, IsFRegularSet P ψ f (S n)) ∧ IsFull ψ (⋃ n, S n) := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hpos.1 hap
  have := isMarkovKernel_pow P m
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ :=
    (theorem_10_4_5_positive hpos.1 hap).1.1 hpos m hm
  have hπf' : ∫⁻ x, fSkel P m f x ∂π ≠ ∞ := by
    rw [lintegral_fSkel P hπ m hf]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hπf
  obtain ⟨S, hS, hfull⟩ := M.exists_fRegular_cover hposQ hψC (hπ.pow m) (measurable_fSkel P m hf)
    hπf'
  exact ⟨S, fun n => IsFRegularSet.of_skeleton hf hm (hS n), hfull⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a positive aperiodic chain with `π(f) < ∞` there is an `f`-regular set in `B⁺(X)`. -/
theorem exists_fRegularSet_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ C, IsFRegularSet P ψ f C ∧ 0 < ψ C := by
  obtain ⟨S, hS, hfull⟩ := theorem_14_2_11 hpos hap hπ hf hπf
  by_contra hcon
  push Not at hcon
  apply hpos.1.1
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ zero_le
  calc ψ univ ≤ ψ ((⋃ n, S n) ∪ (⋃ n, S n)ᶜ) := by rw [union_compl_self]
    _ ≤ ψ (⋃ n, S n) + ψ (⋃ n, S n)ᶜ := measure_union_le _ _
    _ = 0 := by
        rw [hfull, add_zero]
        exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon (S n) (hS n))

end MeynTweedie.LimitTheorems
