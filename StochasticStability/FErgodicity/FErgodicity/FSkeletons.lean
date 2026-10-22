/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FRegularAtoms

/-!
# `f`-regularity and `m`-skeletons (MT §14.2.3, Lemma 14.3.2)

Meyn and Tweedie, pp. 347–350. For `m ≥ 1` the `m`-skeleton is the chain with kernel `Pᵐ`, and
`f^{(m)} = Σ_{i<m} Pⁱf` (14.22) is `fSkel P m f`. The state space is countably generated and `ψ` is
a maximal irreducibility measure.

**Tools.**
* `fSkel`, `measurable_fSkel`, `one_le_fSkel` (`f^{(m)} ≥ 1` when `f ≥ 1`), `fSkel_one`
  (`f^{(1)} = f`).
* `driftV3_iterate` ((14.21)): (V3) iterates to `PᵐV + f^{(m)} ≤ V + b Σ_{i<m} Pⁱ(·, C)`.
* `exists_forall_large_minorization`: for an aperiodic chain every petite set `C` has a single
  nonzero `ν` and a time `T` with `Pᵗ(x, ·) ≥ δ_t ν` on `C` for every `t ≥ T` (the proof of
  Theorem 5.5.7, at all large times).
* `fSumReturn_le_skeleton`: `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ E^{(m)}_x[Σ_{j<τ_B^{(m)}} f^{(m)}(Φ_{mj})]`
  (the first display of the proof of Theorem 14.2.9, by the Markov property at the times `mj`
  and `τ_B ≤ m τ_B^{(m)}`).
* `driftV3_skeleton`: (V3) for `P` and a petite `C` gives (V3) for `Pᵐ` with `½ f^{(m)}` and a set
  that is small for `Pᵐ` (the second half of the proof of Theorem 14.2.9).

**Results.**
* **Lemma 14.2.8** (`lemma_14_2_8`, p. 347): for an aperiodic chain, a petite `C`, `ε > 0`
  and `m ≥ 1`, there is a set `C_ε`, small for the `m`-skeleton, with
  `Σ_{i<m} Pⁱ(x, C) ≤ m 1_{C_ε}(x) + ε`.
* **Theorem 14.2.9** (`theorem_14_2_9`, p. 347): for an aperiodic chain and `C ∈ B⁺(X)`, `C` is
  `f`-regular iff it is `f^{(m)}`-regular for one, and then every, `m`-skeleton.
* **Theorem 14.2.10** (`theorem_14_2_10`, p. 348): the chain is `f`-regular iff each `m`-skeleton is
  `f^{(m)}`-regular; one skeleton suffices (`isFRegularChain_of_skeleton`).
* **Lemma 14.3.2** (p. 349): (i) `lemma_14_3_2_i`, `‖Pⁿ(x, ·) − π‖_f ≤ ‖P^{km}(x, ·) − π‖_{f^{(m)}}`
  for `n = km + i`, `0 ≤ i < m`; (ii) `lemma_14_3_2_ii`, convergence of the skeleton in
  `f^{(m)}`-norm gives convergence of the chain in `f`-norm; (iii) `lemma_14_3_2_iii`, an
  `f^{(m)}`-ergodic skeleton makes the chain `f`-ergodic.

**Hypotheses.** In Lemma 14.3.2 (iii) the chain itself is assumed `ψ`-irreducible with the same
maximal `ψ` (the book's standing assumption), and `f ≥ 1` (part of the definition of
`f`-ergodicity, which the skeleton's `f^{(m)} ≥ 1` does not give).
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The function `f^{(m)}` -/

/-- `f^{(m)} = Σ_{i<m} Pⁱf` (14.22), MT p. 347. -/
noncomputable def fSkel (P : Kernel X X) (m : ℕ) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∑ i ∈ range m, ∫⁻ y, f y ∂(P ^ i : Kernel X X) x

/-- `f^{(m)}` is measurable. -/
theorem measurable_fSkel (P : Kernel X X) (m : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fSkel P m f) :=
  Finset.measurable_sum _ fun _ _ => hf.lintegral_kernel

/-- `Pⁱf ≤ f^{(m)}` for `i < m`. -/
theorem lintegral_pow_le_fSkel (P : Kernel X X) {m i : ℕ} (hi : i < m) (f : X → ℝ≥0∞) (x : X) :
    ∫⁻ y, f y ∂(P ^ i : Kernel X X) x ≤ fSkel P m f x :=
  Finset.single_le_sum (f := fun i => ∫⁻ y, f y ∂(P ^ i : Kernel X X) x)
    (fun _ _ => zero_le) (Finset.mem_range.2 hi)

/-- `f ≤ f^{(m)}` for `m ≥ 1` (the term `i = 0`). -/
theorem le_fSkel (P : Kernel X X) {m : ℕ} (hm : 1 ≤ m) {f : X → ℝ≥0∞} (hf : Measurable f)
    (x : X) : f x ≤ fSkel P m f x := by
  have h := lintegral_pow_le_fSkel P (show 0 < m by omega) f x
  rwa [pow_zero_apply, lintegral_dirac' _ hf] at h

/-- `f^{(m)} ≥ 1` when `f ≥ 1` and `m ≥ 1`. -/
theorem one_le_fSkel (P : Kernel X X) {m : ℕ} (hm : 1 ≤ m) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (x : X) : 1 ≤ fSkel P m f x :=
  (hf1 x).trans (le_fSkel P hm hf x)

/-- `f^{(1)} = f`. -/
theorem fSkel_one (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) : fSkel P 1 f = f := by
  funext x
  unfold fSkel
  rw [Finset.sum_range_one, pow_zero_apply, lintegral_dirac' _ hf]

/-- `π(f^{(m)}) = m π(f)` for an invariant `π`. -/
theorem lintegral_fSkel (P : Kernel X X) {π : Measure X} (hπ : IsInvariant P π) (m : ℕ)
    {f : X → ℝ≥0∞} (hf : Measurable f) : ∫⁻ x, fSkel P m f x ∂π = m * ∫⁻ x, f x ∂π := by
  unfold fSkel
  rw [lintegral_finsetSum _ fun i _ => hf.lintegral_kernel]
  have h : ∀ i, ∫⁻ x, ∫⁻ y, f y ∂(P ^ i : Kernel X X) x ∂π = ∫⁻ x, f x ∂π := fun i => by
    rw [lintegral_comp_kernel _ π hf, hπ.pow i]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Iterating (V3) -/

/-- **(14.21)**: (V3) iterates to `PᵐV + f^{(m)} ≤ V + b Σ_{i<m} Pⁱ(·, C)`. -/
theorem driftV3_iterate {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    (hV : Measurable V) {b : ℝ≥0∞} {C : Set X} (hC : MeasurableSet C)
    (h : DriftV3 P V f b C) (m : ℕ) (x : X) :
    ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + fSkel P m f x ≤
      V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C := by
  induction m with
  | zero =>
    rw [pow_zero_apply, lintegral_dirac' _ hV]
    simp [fSkel]
  | succ m ih =>
    have := isMarkovKernel_pow P m
    -- integrate the one-step drift against `Pᵐ(x, ·)`
    have hstep : ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x +
        ∫⁻ y, f y ∂(P ^ m : Kernel X X) x ≤
        ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + b * (P ^ m : Kernel X X) x C := by
      rw [← lintegral_add_left hV.lintegral_kernel]
      calc ∫⁻ y, (∫⁻ z, V z ∂P y + f y) ∂(P ^ m : Kernel X X) x
          ≤ ∫⁻ y, (V y + C.indicator (fun _ => b) y) ∂(P ^ m : Kernel X X) x :=
            lintegral_mono fun y => h y
        _ = ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + b * (P ^ m : Kernel X X) x C := by
            rw [lintegral_add_left hV, lintegral_indicator_const hC]
    have hPV : ∫⁻ y, V y ∂(P ^ (m + 1) : Kernel X X) x =
        ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x := by
      rw [pow_succ']
      exact Kernel.lintegral_comp P (P ^ m) x hV
    have hfs : fSkel P (m + 1) f x = fSkel P m f x + ∫⁻ y, f y ∂(P ^ m : Kernel X X) x := by
      unfold fSkel; rw [Finset.sum_range_succ]
    rw [hPV, hfs, Finset.sum_range_succ, mul_add]
    calc ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x +
          (fSkel P m f x + ∫⁻ y, f y ∂(P ^ m : Kernel X X) x)
        = (∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x +
            ∫⁻ y, f y ∂(P ^ m : Kernel X X) x) + fSkel P m f x := by ring
      _ ≤ (∫⁻ y, V y ∂(P ^ m : Kernel X X) x + b * (P ^ m : Kernel X X) x C) + fSkel P m f x :=
          add_le_add hstep le_rfl
      _ = (∫⁻ y, V y ∂(P ^ m : Kernel X X) x + fSkel P m f x) +
            b * (P ^ m : Kernel X X) x C := by ring
      _ ≤ (V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C) + b * (P ^ m : Kernel X X) x C :=
          add_le_add ih le_rfl
      _ = V x + (b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C + b * (P ^ m : Kernel X X) x C) := by
          ring

/-! ### Lemma 14.2.8 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- For an aperiodic chain every petite set `C` has a nonzero `ν` and a time `T` such that for
every `t ≥ T` some `δ > 0` has `Pᵗ(x, ·) ≥ δ ν` for all `x ∈ C` (the proof of Theorem 5.5.7 at
all large times). -/
theorem exists_forall_large_minorization (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {A : Set X} (hA : IsPetite P A) :
    ∃ ν : Measure X, ν ≠ 0 ∧ ∃ T : ℕ, ∀ t ≥ T, ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x ∈ A, δ • ν ≤ (P ^ t : Kernel X X) x := by
  obtain ⟨a', ν', hpet'⟩ := hA
  obtain ⟨a, ψa, hpet, hmax⟩ := proposition_5_5_5_i P hψ hpet'
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  have ht : 0 < ψa C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψa C) 1
  obtain ⟨K, hK⟩ := exists_tail_le hpet.2.1 hε0
  refine ⟨ν, hC.2.2.1, N + K + 1, fun t ht => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, t = N + K + 1 + j := ⟨t - (N + K + 1), by omega⟩
  choose δ hδ hδle using fun k => (hN (N + (K - k) + 1 + j) (by omega)).2
  set δ' := min ((Finset.range K).inf δ) 1
  have hδ' : 0 < δ' := lt_min ((Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun k _ => hδ k)
    one_pos
  refine ⟨ε₀ * δ', ENNReal.mul_pos hε0.ne' hδ'.ne', fun x hx =>
    Measure.le_intro fun B hB _ => ?_⟩
  have hbound : ∀ k ∈ Finset.range K, (P ^ k) x C * (δ' * ν B) ≤
      (P ^ (N + K + 1 + j)) x B := fun k hk => by
    have hk' := Finset.mem_range.1 hk
    have hle : ∀ y ∈ C, δ' • ν ≤ (P ^ (N + (K - k) + 1 + j)) y := fun y hy =>
      (smul_measure_le_smul ((min_le_left _ _).trans (Finset.inf_le hk)) ν).trans (hδle k y hy)
    have := pow_add_ge_of_le P (m := k) hle x hB
    rw [show k + (N + (K - k) + 1 + j) = N + K + 1 + j by omega, Measure.smul_apply,
      smul_eq_mul] at this
    exact this
  have hhead := le_sum_head P K x hC.1 hεt hK h2 (hpet.2.2.2 x hx C)
  have hsum1 : ∑ k ∈ Finset.range K, a k ≤ 1 := hpet.2.1 ▸ ENNReal.sum_le_tsum _
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc]
  calc ε₀ * (δ' * ν B) ≤ (∑ k ∈ Finset.range K, a k * (P ^ k) x C) * (δ' * ν B) := by gcongr
    _ = ∑ k ∈ Finset.range K, a k * ((P ^ k) x C * (δ' * ν B)) := by
        rw [Finset.sum_mul]; simp_rw [mul_assoc]
    _ ≤ ∑ k ∈ Finset.range K, a k * (P ^ (N + K + 1 + j)) x B :=
        Finset.sum_le_sum fun k hk => by gcongr; exact hbound k hk
    _ = (∑ k ∈ Finset.range K, a k) * (P ^ (N + K + 1 + j)) x B := (Finset.sum_mul _ _ _).symm
    _ ≤ (P ^ (N + K + 1 + j)) x B := mul_le_of_le_one_left' hsum1

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Lemma 14.2.8** (MT p. 347): for an aperiodic chain, a petite set `C`, `m ≥ 1` and
`ε > 0`, there is a set `C_ε`, small for the `m`-skeleton, such that
`Σ_{i<m} Pⁱ(x, C) ≤ m 1_{C_ε}(x) + ε` for every `x`. -/
theorem lemma_14_2_8 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {C : Set X} (hC : IsPetite P C)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ Cε : Set X, IsSmall (P ^ m : Kernel X X) Cε ∧
      ∀ x, ∑ i ∈ range m, (P ^ i : Kernel X X) x C ≤ m * Cε.indicator 1 x + ε := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨ν, hν, T, hT⟩ := exists_forall_large_minorization P hψ hap hC
  -- the times `(T + 1) m − i`, `i < m`, are all large
  set k := T + 1 with hk
  choose δ hδ hδle using fun i : ℕ => hT (k * m - i % m) (by
    have : k * m ≥ T + m := by nlinarith
    have := Nat.mod_lt i (show m > 0 by omega)
    omega)
  set δ' := (Finset.range m).inf δ
  have hδ' : 0 < δ' := (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun i _ => hδ i
  set Cε := {x | ε ≤ ∑ i ∈ range m, (P ^ i : Kernel X X) x C} with hCε
  have hCεm : MeasurableSet Cε :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun i _ =>
      Kernel.measurable_coe _ hCm)
  refine ⟨Cε, ⟨k, (δ' * (ε * (m : ℝ≥0∞)⁻¹)) • ν, hCεm, by omega,
    smul_measure_ne_zero hν (ENNReal.mul_pos hδ'.ne' (ENNReal.mul_pos hε.ne'
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))).ne').ne', fun x hx => ?_⟩, fun x => ?_⟩
  · rw [← pow_mul, mul_comm m k]
    refine Measure.le_intro fun B hB _ => ?_
    -- `P^{km}(x, B) ≥ Pⁱ(x, C) δ' ν(B)` for every `i < m`
    have hi : ∀ i ∈ range m, (P ^ i : Kernel X X) x C * (δ' * ν B) ≤
        (P ^ (k * m) : Kernel X X) x B := fun i hi => by
      have hi' := Finset.mem_range.1 hi
      have hle : ∀ y ∈ C, δ' • ν ≤ (P ^ (k * m - i) : Kernel X X) y := fun y hy => by
        have h1 := hδle i y hy
        rw [Nat.mod_eq_of_lt hi'] at h1
        exact (smul_measure_le_smul (Finset.inf_le (Finset.mem_range.2 hi')) ν).trans h1
      have := pow_add_ge_of_le P (m := i) hle x hB
      rw [show i + (k * m - i) = k * m by
        have : k * m ≥ m := by nlinarith
        omega, Measure.smul_apply, smul_eq_mul] at this
      exact this
    have hsum : (∑ i ∈ range m, (P ^ i : Kernel X X) x C) * (δ' * ν B) ≤
        m * (P ^ (k * m) : Kernel X X) x B := by
      rw [Finset.sum_mul]
      calc ∑ i ∈ range m, (P ^ i : Kernel X X) x C * (δ' * ν B)
          ≤ ∑ _i ∈ range m, (P ^ (k * m) : Kernel X X) x B := Finset.sum_le_sum hi
        _ = m * (P ^ (k * m) : Kernel X X) x B := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [Measure.smul_apply, smul_eq_mul]
    calc δ' * (ε * (m : ℝ≥0∞)⁻¹) * ν B = (m : ℝ≥0∞)⁻¹ * (ε * (δ' * ν B)) := by ring
      _ ≤ (m : ℝ≥0∞)⁻¹ * ((∑ i ∈ range m, (P ^ i : Kernel X X) x C) * (δ' * ν B)) := by
          gcongr; exact hx
      _ ≤ (m : ℝ≥0∞)⁻¹ * (m * (P ^ (k * m) : Kernel X X) x B) := by gcongr
      _ = (P ^ (k * m) : Kernel X X) x B := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 (ENNReal.natCast_ne_top m), one_mul]
  · by_cases hx : x ∈ Cε
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      refine le_trans ?_ le_self_add
      calc ∑ i ∈ range m, (P ^ i : Kernel X X) x C ≤ ∑ _i ∈ range m, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun i _ => by
              have := isMarkovKernel_pow P i
              exact prob_le_one
        _ = m := by simp
    · rw [indicator_of_notMem hx, mul_zero, zero_add]
      exact (not_le.1 hx).le

/-! ### The skeleton drift -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(V3) for the skeleton** (proof of Theorem 14.2.9): if (V3) holds for `P`, a petite `C` and
`b < ∞`, and `f ≥ 1`, then for every `m ≥ 1` there are a set `C'`, small for `Pᵐ`, and `b' < ∞`
with `PᵐV + ½ f^{(m)} ≤ V + b' 1_{C'}`. -/
theorem driftV3_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V f : X → ℝ≥0∞}
    (hV : Measurable V) (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {b : ℝ≥0∞} (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) (h : DriftV3 P V f b C) {m : ℕ} (hm : 1 ≤ m) :
    ∃ (C' : Set X) (b' : ℝ≥0∞), IsSmall (P ^ m : Kernel X X) C' ∧ b' ≠ ∞ ∧
      DriftV3 (P ^ m : Kernel X X) V (fun x => 2⁻¹ * fSkel P m f x) b' C' := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  -- enlarge `b` to `b + 1 > 0`
  have h' : DriftV3 P V f (b + 1) C := fun x => (h x).trans (add_le_add le_rfl
    (indicator_le_indicator (le_self_add : b ≤ b + 1)))
  set B := b + 1 with hB
  have hB0 : B ≠ 0 := by simp [hB]
  have hBt : B ≠ ∞ := ENNReal.add_ne_top.2 ⟨hb, ENNReal.one_ne_top⟩
  set ε := (2 * B)⁻¹ with hε
  have hε0 : 0 < ε := ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) hBt)
  have hεt : ε ≠ ∞ := ENNReal.inv_ne_top.2 (by simp [hB0])
  obtain ⟨C', hC', hbound⟩ := lemma_14_2_8 P hψ hap hC hm hε0
  refine ⟨C', B * m, hC', ENNReal.mul_ne_top hBt (ENNReal.natCast_ne_top m), fun x => ?_⟩
  have hit := driftV3_iterate hV hCm h' m x
  have hBε : B * ε = 2⁻¹ := by
    rw [hε, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
      mul_comm B, mul_assoc, ENNReal.mul_inv_cancel hB0 hBt, mul_one]
  have hfs1 := one_le_fSkel P hm hf hf1 x
  have hhalf : 2⁻¹ * fSkel P m f x + 2⁻¹ ≤ fSkel P m f x := by
    calc 2⁻¹ * fSkel P m f x + 2⁻¹ ≤ 2⁻¹ * fSkel P m f x + 2⁻¹ * fSkel P m f x :=
          add_le_add le_rfl (by simpa using mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) hfs1)
      _ = fSkel P m f x := by rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero
          ENNReal.ofNat_ne_top, one_mul]
  have key : ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + 2⁻¹ * fSkel P m f x + 2⁻¹ ≤
      V x + C'.indicator (fun _ => B * m) x + 2⁻¹ := by
    calc ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + 2⁻¹ * fSkel P m f x + 2⁻¹
        ≤ ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + fSkel P m f x := by
          rw [add_assoc]; exact add_le_add le_rfl hhalf
      _ ≤ V x + B * ∑ i ∈ range m, (P ^ i : Kernel X X) x C := hit
      _ ≤ V x + B * (m * C'.indicator 1 x + ε) := add_le_add le_rfl (mul_le_mul' le_rfl
          (hbound x))
      _ = V x + C'.indicator (fun _ => B * m) x + 2⁻¹ := by
          rw [mul_add, hBε, ← add_assoc]
          congr 2
          by_cases hx : x ∈ C' <;> simp [hx, mul_comm]
  exact (ENNReal.add_le_add_iff_right (by simp)).1 key

/-! ### Theorem 14.2.9: the skeleton dominates the chain -/

omit [MeasurableSpace X] in
/-- `{j < τ_B ∘ s} ∈ 𝓕_{mj}`, where `s(ω) = (ω_{mj})_j` is the skeleton path. -/
theorem measurableSet_natFilt_lt_firstReturn_skeleton [MeasurableSpace X] {B : Set X}
    (hB : MeasurableSet B) (m j : ℕ) :
    MeasurableSet[natFilt (X := X) (m * j)]
      {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B (fun n => ω (m * n))} := by
  have h : {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B (fun n => ω (m * n))} =
      ⋂ j' ∈ Finset.Icc 1 j, {ω | ω (m * j') ∉ B} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_Icc]
    have hiff : (j : WithTop ℕ) < firstReturn B (fun n => ω (m * n)) ↔
        WithTop.some (j + 1) ≤ firstReturn B (fun n => ω (m * n)) := by
      cases firstReturn B (fun n => ω (m * n)) with
      | top => simp
      | coe t =>
        rw [Nat.cast_withTop, WithTop.coe_lt_coe, WithTop.coe_le_coe]
        omega
    rw [hiff, le_firstReturn_iff]
    exact ⟨fun h j' hj' => h j' hj'.1 (by omega), fun h j' h1 h2 => h j' ⟨h1, by omega⟩⟩
  rw [h]
  refine Finset.measurableSet_biInter _ fun j' hj' => ?_
  exact (measurableSet_coord_natFilt (Nat.mul_le_mul_left m (Finset.mem_Icc.1 hj').2) hB).compl

/-- Regrouping a sum over `ℕ` into blocks of length `m`. -/
theorem tsum_eq_tsum_sum_block (g : ℕ → ℝ≥0∞) {m : ℕ} (hm : 1 ≤ m) :
    ∑' k, g k = ∑' j, ∑ i ∈ range m, g (m * j + i) := by
  have : NeZero m := ⟨by omega⟩
  rw [← (Nat.divModEquiv m).symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun j => ?_
  rw [tsum_fintype, ← Fin.sum_univ_eq_sum_range (fun i => g (m * j + i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Nat.divModEquiv_symm_apply, mul_comm]

/-- **The skeleton dominates the chain** (MT p. 348, proof of Theorem 14.2.9): for `m ≥ 1`,
`E_x[Σ_{k<τ_B} f(Φ_k)] ≤ E^{(m)}_x[Σ_{j<τ_B^{(m)}} f^{(m)}(Φ_j)]`, by the Markov property at the
times `mj` and `τ_B ≤ m τ_B^{(m)}`. -/
theorem fSumReturn_le_skeleton {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    {B : Set X} (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    haveI := isMarkovKernel_pow P m
    fSumReturn P B f x ≤ fSumReturn (P ^ m : Kernel X X) B (fSkel P m f) x := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_pathKernel P
  set s : (ℕ → X) → (ℕ → X) := fun ω n => ω (m * n) with hsdef
  have hs : Measurable s := measurable_pi_iff.2 fun n => measurable_pi_apply (m * n)
  have hGm : ∀ j : ℕ, MeasurableSet {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B (s ω)} :=
    fun j => (natFilt (X := X)).le _ _ (measurableSet_natFilt_lt_firstReturn_skeleton hB m j)
  -- the right side on the original path space
  have hR : fSumReturn (P ^ m : Kernel X X) B (fSkel P m f) x =
      ∑' j : ℕ, ∑ i ∈ range m, ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
        f (ω (m * j + i)) ∂pathKernel P x := by
    have hcomp : ∀ a : ℕ → X, sumBefore (firstReturn B) (fun k ω => fSkel P m f (ω k)) (s a) =
        sumBefore (fun ω => firstReturn B (s ω)) (fun k ω => fSkel P m f (s ω k)) a := fun a => by
      simp only [sumBefore, Set.indicator_apply, mem_ofPred_eq]
    rw [fSumReturn, ← pathKernel_map_skeleton P m x,
      lintegral_map (measurable_sumBefore_firstReturn hB (measurable_fSkel P m hf)) hs,
      lintegral_congr hcomp, lintegral_sumBefore _ (fun j => hGm j)
        (F := fun k ω => fSkel P m f (s ω k)) fun j => (measurable_fSkel P m hf).comp
        ((measurable_pi_apply j).comp hs)]
    refine tsum_congr fun j => ?_
    simp only [fSkel, hsdef]
    rw [lintegral_finsetSum (f := fun i (ω : ℕ → X) => ∫⁻ y, f y ∂(P ^ i : Kernel X X) (ω (m * j)))
      _ fun i _ => hf.lintegral_kernel.comp (measurable_pi_apply (m * j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- the Markov property at time `mj`
    have hmk := markov_lintegral P (Measure.dirac x)
      (measurableSet_natFilt_lt_firstReturn_skeleton hB m j) (H := fun ω : ℕ → X => f (ω i))
      (hf.comp (measurable_pi_apply i))
    rw [pathMeasure_dirac] at hmk
    rw [show (∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B fun n => ω (m * n)},
      f (ω (m * j + i)) ∂pathKernel P x) = ∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) <
        firstReturn B fun n => ω (m * n)}, f (shift (m * j) ω i) ∂pathKernel P x from rfl, hmk]
    refine setLIntegral_congr_fun (hGm j) fun ω _ => ?_
    rw [lintegral_coord_eq_pow P (ω (m * j)) i hf]
  rw [hR, fSumReturn, lintegral_sumBefore _ (measurableSet_lt_firstReturn hB)
    (F := fun k (ω : ℕ → X) => f (ω k)) fun k => hf.comp (measurable_pi_apply k)]
  -- pathwise: `k < τ_B` forces `⌊k/m⌋ < τ_B^{(m)}`
  calc ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstReturn B ω}, f (ω k) ∂pathKernel P x
      = ∑' j : ℕ, ∑ i ∈ range m, ∫⁻ ω in {ω | ((m * j + i : ℕ) : WithTop ℕ) < firstReturn B ω},
          f (ω (m * j + i)) ∂pathKernel P x :=
        tsum_eq_tsum_sum_block (fun k : ℕ => ∫⁻ ω in {ω | (k : WithTop ℕ) < firstReturn B ω},
          f (ω k) ∂pathKernel P x) hm
    _ ≤ ∑' j : ℕ, ∑ i ∈ range m, ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
          f (ω (m * j + i)) ∂pathKernel P x := by
        refine ENNReal.tsum_le_tsum fun j => Finset.sum_le_sum fun i hi => ?_
        refine lintegral_mono_set fun ω hω => ?_
        simp only [mem_ofPred_eq] at hω ⊢
        by_contra hc
        push Not at hc
        -- some `1 ≤ j' ≤ j` has `Φ_{mj'} ∈ B`
        obtain ⟨t, ht⟩ : ∃ t : ℕ, firstReturn B (s ω) = t := by
          cases h : firstReturn B (s ω) with
          | top => rw [h] at hc; exact absurd hc (by simp)
          | coe t => exact ⟨t, rfl⟩
        have htj : t ≤ j := by rw [ht] at hc; exact_mod_cast hc
        have ht1 : 1 ≤ t := by
          have := one_le_firstReturn B (s ω); rw [ht] at this; exact WithTop.coe_le_coe.1 this
        have hmem : ω (m * t) ∈ B := (mem_of_firstReturn_eq ht : s ω t ∈ B)
        have hle := firstReturn_le_of_mem (A := B) (ω := ω) (j := m * t) (by nlinarith) hmem
        have : ((m * j + i : ℕ) : WithTop ℕ) < WithTop.some (m * t) := lt_of_lt_of_le hω hle
        have : m * j + i < m * t := WithTop.coe_lt_coe.1 this
        nlinarith

/-! ### Theorems 14.2.9 and 14.2.10 -/

/-- `E_x[Σ_{k<τ} 2⁻¹ g(Φ_k)] = 2⁻¹ E_x[Σ_{k<τ} g(Φ_k)]`. -/
theorem fSumReturn_const_mul (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {g : X → ℝ≥0∞} (hg : Measurable g) (c : ℝ≥0∞) (x : X) :
    fSumReturn P B (fun y => c * g y) x = c * fSumReturn P B g x := by
  rw [fSumReturn, fSumReturn]
  simp_rw [sumBefore_const_mul (firstReturn B) c (fun k ω => g (ω k))]
  exact lintegral_const_mul _ (measurable_sumBefore_firstReturn hB hg)

/-- A `½ g`-regular set is `g`-regular. -/
theorem IsFRegularSet.of_half {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) {C : Set X}
    (hC : IsFRegularSet P ψ (fun y => 2⁻¹ * g y) C) : IsFRegularSet P ψ g C := by
  refine ⟨hC.1, fun B hB hψB => ?_⟩
  obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
  refine ⟨2 * M, ENNReal.mul_ne_top (by simp) hM, fun x hx => ?_⟩
  have h2 := h x hx
  rw [fSumReturn_const_mul P hB hg] at h2
  calc fSumReturn P B g x = 2 * (2⁻¹ * fSumReturn P B g x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * M := mul_le_mul' le_rfl h2

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.9**, the direction `f`-regular for `P` ⇒ `f^{(m)}`-regular for `Pᵐ`: for an
aperiodic chain, `f ≥ 1`, an `f`-regular `C ∈ B⁺(X)` is `f^{(m)}`-regular for every
`m`-skeleton. -/
theorem IsFRegularSet.skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hC : IsFRegularSet P ψ f C)
    (hψC : 0 < ψ C) {m : ℕ} (hm : 1 ≤ m) :
    haveI := isMarkovKernel_pow P m
    IsFRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C := by
  have := isMarkovKernel_pow P m
  obtain ⟨hpet, b, hb, hdrift, hbdd⟩ := theorem_14_2_3_ii hψ hf hf1 hC hψC
  obtain ⟨M, hM, hVC⟩ := hbdd C hC
  obtain ⟨C', b', hC', hb', hdrift'⟩ := driftV3_skeleton hψ hap (measurable_gKernelFn hC.1 hf)
    hf hf1 hb hpet hdrift hm
  have hψm : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  obtain ⟨k, ν, hsm⟩ := hC'
  have hpet' : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsm⟩
  have hreg := theorem_14_2_3_i_fRegular hψm (measurable_gKernelFn hC.1 hf)
    (measurable_const.mul (measurable_fSkel P m hf)) hb' hpet' hdrift' hC.1 hM hVC
  exact hreg.of_half (measurable_fSkel P m hf)

/-- **Theorem 14.2.9**, the direction `f^{(m)}`-regular for `Pᵐ` ⇒ `f`-regular for `P`. -/
theorem IsFRegularSet.of_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) {C : Set X}
    (hC : haveI := isMarkovKernel_pow P m; IsFRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) :
    IsFRegularSet P ψ f C := by
  have := isMarkovKernel_pow P m
  refine ⟨hC.1, fun B hB hψB => ?_⟩
  obtain ⟨M, hM, h⟩ := hC.2 B hB hψB
  exact ⟨M, hM, fun x hx => (fSumReturn_le_skeleton hm hB hf x).trans (h x hx)⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.9** (MT p. 347): for an aperiodic `ψ`-irreducible chain and `f ≥ 1`, a set
`C ∈ B⁺(X)` is `f`-regular iff it is `f^{(m)}`-regular for one `m`-skeleton, iff it is for
every `m`-skeleton. -/
theorem theorem_14_2_9 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hψC : 0 < ψ C) :
    (IsFRegularSet P ψ f C ↔ ∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m;
        IsFRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) ∧
      (IsFRegularSet P ψ f C ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
        IsFRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) := by
  refine ⟨⟨fun hC => ⟨1, le_rfl, hC.skeleton hψ hap hf hf1 hψC le_rfl⟩,
    fun ⟨m, hm, hC⟩ => IsFRegularSet.of_skeleton hf hm hC⟩,
    ⟨fun hC m hm => hC.skeleton hψ hap hf hf1 hψC hm,
    fun h => IsFRegularSet.of_skeleton hf le_rfl (h 1 le_rfl)⟩⟩

/-- **Theorem 14.2.10**, the easy direction: if one `m`-skeleton is `f^{(m)}`-regular, the chain
is `f`-regular. -/
theorem isFRegularChain_of_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m)
    (h : haveI := isMarkovKernel_pow P m; IsFRegularChain (P ^ m : Kernel X X) ψ (fSkel P m f)) :
    IsFRegularChain P ψ f := by
  have := isMarkovKernel_pow P m
  obtain ⟨Cs, hCs, hcov⟩ := h
  exact ⟨Cs, fun n => IsFRegularSet.of_skeleton hf hm (hCs n), hcov⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.10** (MT p. 348): for an aperiodic `ψ`-irreducible chain and `f ≥ 1`, the chain
is `f`-regular iff each `m`-skeleton is `f^{(m)}`-regular. -/
theorem theorem_14_2_10 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) :
    IsFRegularChain P ψ f ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
      IsFRegularChain (P ^ m : Kernel X X) ψ (fSkel P m f) := by
  refine ⟨fun hreg m hm => ?_, fun h => isFRegularChain_of_skeleton hf le_rfl (h 1 le_rfl)⟩
  have := isMarkovKernel_pow P m
  obtain ⟨C, V, b, hC, hV, hb, hfin, hdrift⟩ := (theorem_14_2_6 hψ hf hf1).1 hreg
  obtain ⟨C', b', hC', hb', hdrift'⟩ := driftV3_skeleton hψ hap hV hf hf1 hb hC hdrift hm
  have hψm : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  obtain ⟨k, ν, hsm⟩ := hC'
  have hpet' : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsm⟩
  refine ⟨fun n => {x | V x ≤ n}, fun n => ?_, ?_⟩
  · exact (theorem_14_2_6_sublevel hψm hV (measurable_const.mul (measurable_fSkel P m hf)) hb'
      hpet' hdrift' (ENNReal.natCast_ne_top n)).of_half (measurable_fSkel P m hf)
  · ext x
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hfin x)
    exact ⟨n, hn.le⟩

/-! ### Lemma 14.3.2 -/

/-- **Lemma 14.3.2 (i)** (MT p. 349): for an invariant probability `π`, `m ≥ 1` and
`n = km + i` with `i < m`, `‖Pⁿ(x, ·) − π‖_f ≤ ‖P^{km}(x, ·) − π‖_{f^{(m)}}`. -/
theorem lemma_14_3_2_i {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {m i : ℕ} (hi : i < m) (k : ℕ)
    (f : X → ℝ≥0∞) (x : X) :
    fNorm f ((P ^ (k * m + i) : Kernel X X) x) π ≤
      fNorm (fSkel P m f) ((P ^ (k * m) : Kernel X X) x) π := by
  have := isMarkovKernel_pow P i
  have := isMarkovKernel_pow P (k * m)
  have h1 : (P ^ (k * m + i) : Kernel X X) x = (P ^ i : Kernel X X) ∘ₘ (P ^ (k * m)) x := by
    rw [add_comm, pow_add]; rfl
  have h2 : π = (P ^ i : Kernel X X) ∘ₘ π := (hπ.pow i).symm
  rw [h1]
  conv_lhs => rw [h2]
  exact (fNorm_comp_le (P ^ i) f _ π).trans
    (fNorm_mono (fun y => lintegral_pow_le_fSkel P hi f y) _ _)

/-- **Lemma 14.3.2 (ii)** (MT p. 349): if `‖P^{km}(x, ·) − π‖_{f^{(m)}} → 0` as `k → ∞` for some
`m ≥ 1`, then `‖Pᵏ(x, ·) − π‖_f → 0`. -/
theorem lemma_14_3_2_ii {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {m : ℕ} (hm : 1 ≤ m) (f : X → ℝ≥0∞) (x : X)
    (h : Tendsto (fun k => fNorm (fSkel P m f) (((P ^ m) ^ k : Kernel X X) x) π) atTop (𝓝 0)) :
    Tendsto (fun n => fNorm f ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n => n / m) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h.comp hdiv)
    (fun _ => zero_le) fun n => ?_
  simp only [Function.comp_apply, ← pow_mul]
  have hn : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  calc fNorm f ((P ^ n : Kernel X X) x) π
      = fNorm f ((P ^ (n / m * m + n % m) : Kernel X X) x) π := by rw [← hn]
    _ ≤ fNorm (fSkel P m f) ((P ^ (n / m * m) : Kernel X X) x) π :=
        lemma_14_3_2_i hπ (Nat.mod_lt n (by omega)) (n / m) f x
    _ = fNorm (fSkel P m f) ((P ^ (m * (n / m)) : Kernel X X) x) π := by rw [mul_comm]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Lemma 14.3.2 (iii)** (MT p. 349): if the `m`-skeleton is `f^{(m)}`-ergodic (and the chain
is `ψ`-irreducible with `f ≥ 1`), then the chain is `f`-ergodic. -/
theorem lemma_14_3_2_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {m : ℕ} (hm : 1 ≤ m) {π : Measure X}
    (h : haveI := isMarkovKernel_pow P m; IsFErgodic (P ^ m : Kernel X X) ψ (fSkel P m f) π) :
    IsFErgodic P ψ f π := by
  have := isMarkovKernel_pow P m
  obtain ⟨-, hph, hπp, hπ, hπf, hconv⟩ := h
  -- `πP` is invariant for `Pᵐ`, hence equals `π`
  have hπP : IsInvariant (P ^ m : Kernel X X) (P ∘ₘ π) := by
    change (P ^ m : Kernel X X) ∘ₘ (P ∘ₘ π) = P ∘ₘ π
    rw [Measure.comp_assoc, show (P ^ m : Kernel X X) ∘ₖ P = P ∘ₖ (P ^ m : Kernel X X) from
      (pow_succ P m).symm.trans (pow_succ' P m), ← Measure.comp_assoc, hπ]
  have hinv : IsInvariant P π := hph.2.invariant_prob_unique hπP hπ
  have hπf' : ∫⁻ y, f y ∂π ≠ ∞ := by
    refine ne_top_of_le_ne_top hπf (lintegral_mono fun y => le_fSkel P hm hf y)
  refine ⟨hf1, ⟨isHarris_of_skeleton hψ hm hph.1, hψ, π, hπp, hinv⟩, hπp, hinv, hπf',
    fun x => lemma_14_3_2_ii hinv hm f x ?_⟩
  exact hconv x

end MeynTweedie.FErgodicity
