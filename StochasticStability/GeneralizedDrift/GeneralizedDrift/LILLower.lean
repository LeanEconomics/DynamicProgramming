/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LILUpper
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.Real.Pi.Bounds


/-!
# The lower half of the Hartman–Wintner LIL

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/LILLower.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

For i.i.d. `Xⱼ` with mean `0` and variance `1` and `0 < ε ≤ 1`, almost surely
`Sₙ ≥ (1 − ε) √(2 n log log n)` for infinitely many `n` (`lil_lower_normalized`). With
`lil_upper` this gives the i.i.d. LIL (`IIDLIL`) used for MT Theorems 17.2.2 and 17.3.6.

The proof uses the central limit theorem (Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum`)
instead of Kolmogorov's lower exponential inequality, by a blocking argument in the spirit of
de Acosta (*Ann. Probab.* 11 (1983)). Along `n_k = mᵏ`, the block `[mᵏ, mᵏ⁺¹)` of
`N = mᵏ⁺¹ − mᵏ` summands is cut into `r ≈ 2γ² log log mᵏ⁺¹/A²` sub-blocks of length `ℓ = N/r`;
by the CLT each sub-block sum exceeds `(A + 2)√ℓ` with probability at least `e^{−κ}`,
`κ = (A + 3)²/2 + 2` (`gaussianReal_Ioi_ge`, `eventually_lt_measure_clt`), so the block sum
exceeds `(1 − ε/2) √(2 mᵏ⁺¹ log log mᵏ⁺¹)` with probability at least
`(e^{−κ}/2) (log mᵏ⁺¹)^{−p'}`, `p' = 2γ²κ/A² ≤ 1` (`block_lower_bound`,
`lil_lower_block_estimate`). These probabilities are not summable and the blocks are
independent (`iIndepFun_blockSum`, `iIndepSet_preimage`), so the second Borel–Cantelli lemma
applies; the start `S_{mᵏ}` of the block is controlled by the upper half.

* `gaussianReal_Ioi_ge`: `P(Z > b) ≥ e^{−(b+1)²/2}/√(2π)`; `two_mul_sqrt_two_pi_le_exp_two`.
* `sum_range_mul_eq`, `le_block_level`, `eventually_mul_sq_le_pow`, `exists_lil_lower_ratio`,
  `exists_lil_lower_level`: arithmetic of the blocks.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### A Gaussian tail bound -/

/-- `P(Z > b) ≥ e^{−(b+1)²/2}/√(2π)` for a standard normal `Z` and `b ≥ 0`. -/
theorem gaussianReal_Ioi_ge {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) ≤ (gaussianReal 0 1).real (Ioi b) := by
  set c := Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) with hc
  have hc0 : 0 ≤ c := by positivity
  have h1 : ENNReal.ofReal c ≤ gaussianReal 0 1 (Ioi b) := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc ENNReal.ofReal c = ∫⁻ _x in Ioo b (b + 1), ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one,
            mul_one]
      _ ≤ ∫⁻ x in Ioo b (b + 1), gaussianPDF 0 1 x :=
          setLIntegral_mono (measurable_gaussianPDF 0 1) fun x hx => by
            rw [gaussianPDF]
            apply ENNReal.ofReal_le_ofReal
            rw [gaussianPDFReal, hc]
            simp only [NNReal.coe_one, mul_one, sub_zero]
            rw [div_eq_inv_mul]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.2
            have hx1 : b < x := hx.1
            have hx2 : x < b + 1 := hx.2
            have : x ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
            linarith
      _ ≤ ∫⁻ x in Ioi b, gaussianPDF 0 1 x :=
          lintegral_mono_set Ioo_subset_Ioi_self
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  exact h2

/-- `2 √(2π) ≤ e²`. -/
theorem two_mul_sqrt_two_pi_le_exp_two : 2 * √(2 * Real.pi) ≤ Real.exp 2 := by
  have hpi := Real.pi_lt_d2
  have h1 : √(2 * Real.pi) ≤ 2.6 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have h2 := Real.exp_one_gt_d9
  have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  nlinarith

/-! ### The CLT on half lines -/

/-- From the CLT: for i.i.d. `Xⱼ` with mean `0` and variance `1`, every `b` and every
`q < P(Z > b)`, eventually `P(Σ_{j<ℓ} Xⱼ > b √ℓ) > q`. -/
theorem eventually_lt_measure_clt {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) (b : ℝ) {q : ℝ≥0∞}
    (hq : q < gaussianReal 0 1 (Ioi b)) :
    ∀ᶠ ℓ : ℕ in atTop, q < Q {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := by
  have h1' : Q[X 0 ^ 2] = 1 := by simpa [Pi.pow_apply] using h1
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (P' := gaussianReal 0 1) (Y := id)
    HasLaw.id h0 h1' hind hident
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hclt.tendsto
    (isOpen_Ioi (a := b))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hlim
  have hev := eventually_lt_of_lt_liminf (hq.trans_le hlim)
  filter_upwards [hev, eventually_ge_atTop 1] with ℓ hℓ hℓ1
  have hWm : Measurable fun ω => (√(ℓ : ℝ))⁻¹ * ∑ k ∈ Finset.range ℓ, X k ω :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => hm j)
  rw [Measure.map_apply hWm measurableSet_Ioi] at hℓ
  convert hℓ using 2
  ext ω
  have hs : 0 < √(ℓ : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hℓ1)
  simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
  rw [inv_mul_eq_div, lt_div_iff₀ hs]

/-! ### Independence of block sums -/

/-- Sums of independent variables over pairwise disjoint finite index sets are independent. -/
theorem iIndepFun_blockSum {Ω κ : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j)) {I : κ → Finset ℕ}
    (hI : Pairwise (Function.onFun Disjoint fun k => (I k : Set ℕ))) :
    iIndepFun (fun k ω => ∑ j ∈ I k, X j ω) Q := by
  have h1 : iIndep (fun j => MeasurableSpace.comap (X j) inferInstance) Q :=
    (iIndepFun_iff_iIndep _ _ _).1 hind
  have h2 := iIndep_iSup_blocks (fun j => (hm j).comap_le) h1 hI
  rw [iIndepFun_iff_iIndep]
  refine iIndep_of_iIndep_of_le h2 fun k => ?_
  apply Measurable.comap_le
  refine Finset.measurable_sum (I k) fun j hj => ?_
  exact Measurable.mono (comap_measurable (X j))
    (le_iSup₂ (f := fun j (_ : j ∈ (I k : Set ℕ)) => MeasurableSpace.comap (X j) inferInstance)
      j hj) le_rfl

/-- Preimages of measurable sets under independent variables are independent events. -/
theorem iIndepSet_preimage {Ω κ β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {Q : Measure Ω} {Z : κ → Ω → β} (h : iIndepFun Z Q) {A : κ → Set β}
    (hA : ∀ k, MeasurableSet (A k)) : iIndepSet (fun k => Z k ⁻¹' A k) Q := by
  rw [iIndepSet_iff_iIndep]
  refine iIndep_of_iIndep_of_le ((iIndepFun_iff_iIndep _ _ _).1 h) fun k => ?_
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  rw [mem_singleton_iff.1 ht]
  exact ⟨A k, hA k, rfl⟩

/-- `Σ_{j < r ℓ} f j = Σ_{i<r} Σ_{j<ℓ} f (i ℓ + j)`. -/
theorem sum_range_mul_eq (f : ℕ → ℝ) (r ℓ : ℕ) :
    ∑ j ∈ Finset.range (r * ℓ), f j =
      ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range ℓ, f (i * ℓ + j) := by
  induction r with
  | zero => simp
  | succ r ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-! ### The probability of a large block sum -/

/-- **A large block sum from many moderately large sub-blocks**: for i.i.d. centred `Xⱼ` with
`E[X₀²] = 1`, a block of `r ℓ + e` consecutive summands starting at `c` satisfies
`P(Σ ≥ (r b − 1) √ℓ) ≥ P(S_ℓ > b √ℓ)^r (1 − e/ℓ)`: all `r` sub-blocks of length `ℓ` exceed
`b √ℓ` (independently) and the remainder of `e` terms is at least `−√ℓ` (Kolmogorov). -/
theorem block_lower_bound {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1)
    (c r ℓ e : ℕ) (b : ℝ) (hℓ : 0 < ℓ) :
    Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r * (1 - e / ℓ) ≤
      Q.real {ω | (r * b - 1) * √(ℓ : ℝ) ≤ ∑ j ∈ Finset.range (r * ℓ + e), X (c + j) ω} := by
  classical
  set L : ℕ → ℕ := fun i => if i < r then ℓ else if i = r then e else 0 with hL
  set I : ℕ → Finset ℕ := fun i => Finset.Ico (c + i * ℓ) (c + i * ℓ + L i) with hI
  have hLle : ∀ i, i < r → L i = ℓ := fun i hi => by simp only [hL, hi, ite_true]
  have hLr : L r = e := by simp only [hL, lt_irrefl, ite_false, ite_true]
  have hLgt : ∀ i, r < i → L i = 0 := fun i hi => by
    simp only [hL, show ¬ i < r by omega, show i ≠ r by omega, ite_false]
  have hcase : ∀ i i', i < i' → L i' = 0 ∨ L i = ℓ := fun i i' h => by
    by_cases h1 : r < i'
    · exact Or.inl (hLgt i' h1)
    · exact Or.inr (hLle i (by omega))
  have hdisj1 : ∀ i i', i < i' → Disjoint (I i : Set ℕ) (I i') := fun i i' h => by
    simp only [Finset.coe_Ico, hI]
    rw [Set.Ico_disjoint_Ico]
    have hm1 : i * ℓ + ℓ ≤ i' * ℓ := by
      have := Nat.mul_le_mul_right ℓ h; rwa [Nat.succ_mul] at this
    generalize i * ℓ = u at hm1 ⊢
    generalize i' * ℓ = v at hm1 ⊢
    rcases hcase i i' h with h2 | h2 <;> rw [h2] <;> omega
  have hdisj : Pairwise (Function.onFun Disjoint fun i => (I i : Set ℕ)) := by
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact hdisj1 i i' h
    · exact (hdisj1 i' i h).symm
  -- the block sums
  set Z : ℕ → Ω → ℝ := fun i ω => ∑ j ∈ I i, X j ω with hZ
  have hZind : iIndepFun Z Q := iIndepFun_blockSum hind hm hdisj
  have hZeq : ∀ i ω, Z i ω = ∑ j ∈ Finset.range (L i), X (c + i * ℓ + j) ω := fun i ω => by
    simp only [hZ, hI]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  set A : ℕ → Set ℝ := fun i => if i < r then Ioi (b * √(ℓ : ℝ)) else Ici (-√(ℓ : ℝ)) with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    simp only [hA]; split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Ici
  set E := ⋂ i ∈ Finset.range (r + 1), Z i ⁻¹' A i with hE
  have hZm : ∀ i, Measurable (Z i) := fun i => Finset.measurable_sum _ fun j _ => hm j
  have hprod : Q.real E = ∏ i ∈ Finset.range (r + 1), Q.real (Z i ⁻¹' A i) := by
    have h := hZind.meas_biInter (S := Finset.range (r + 1))
      (s := fun i => Z i ⁻¹' A i) fun i _ => ⟨A i, hAm i, rfl⟩
    rw [measureReal_def, hE, h, ENNReal.toReal_prod]
    rfl
  -- the sub-blocks of length `ℓ`
  have hsub : ∀ i < r, Q.real (Z i ⁻¹' A i) =
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := fun i hi => by
    have hsh := identDistrib_shift_sum hind hident (c + i * ℓ) ℓ
    have e1 : Z i ⁻¹' A i =
        (fun ω => ∑ j ∈ Finset.range ℓ, X (c + i * ℓ + j) ω) ⁻¹' Ioi (b * √(ℓ : ℝ)) := by
      ext ω
      simp only [mem_preimage, hA, hi, ite_true, hZeq i ω, hLle i hi]
    rw [e1, measureReal_def, measureReal_def, hsh.measure_mem_eq measurableSet_Ioi]
    rfl
  -- the remainder
  have hrem : 1 - e / ℓ ≤ Q.real (Z r ⁻¹' A r) := by
    have hL2j : ∀ j, MemLp (X j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
    have h0j : ∀ j, ∫ ω, X j ω ∂Q = 0 := fun j => (hident j).integral_eq.trans h0
    have hσj : ∀ j, ∫ ω, X j ω ^ 2 ∂Q = 1 := fun j =>
      (((hident j).comp (measurable_id.pow_const 2)).integral_eq).trans h1
    have hk := kolmogorov_ineq_shift hind hm hL2j h0j (c + r * ℓ) e
      (t := √(ℓ : ℝ)) (Real.sqrt_pos.2 (by exact_mod_cast hℓ))
    simp_rw [hσj, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hk
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hk
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hbad : Q.real {ω | ∃ k ≤ e, √(ℓ : ℝ) ≤
        |∑ j ∈ Finset.range k, X (c + r * ℓ + j) ω|} ≤ e / ℓ := by
      rw [le_div_iff₀ hℓ', mul_comm]; exact hk
    have hsub2 : (Z r ⁻¹' A r)ᶜ ⊆ {ω | ∃ k ≤ e, √(ℓ : ℝ) ≤
        |∑ j ∈ Finset.range k, X (c + r * ℓ + j) ω|} := by
      intro ω hω
      simp only [mem_compl_iff, mem_preimage, hA, lt_irrefl, ite_false, mem_Ici, not_le,
        hZeq r ω, hLr] at hω
      refine ⟨e, le_rfl, ?_⟩
      rw [abs_of_neg (by linarith [Real.sqrt_nonneg (ℓ : ℝ)])]
      linarith
    have hmeas : MeasurableSet (Z r ⁻¹' A r) := (hZm r) (hAm r)
    have hc := measureReal_compl hmeas (μ := Q)
    rw [probReal_univ] at hc
    have := measureReal_mono hsub2 (μ := Q)
    linarith
  -- the event `E` forces a large sum
  have hEsub : E ⊆ {ω | (r * b - 1) * √(ℓ : ℝ) ≤
      ∑ j ∈ Finset.range (r * ℓ + e), X (c + j) ω} := by
    intro ω hω
    simp only [hE, mem_iInter, mem_preimage, Finset.mem_range] at hω
    simp only [mem_ofPred_eq]
    rw [Finset.sum_range_add, sum_range_mul_eq (fun j => X (c + j) ω)]
    have hi : ∀ i < r, b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X (c + (i * ℓ + j)) ω := by
      intro i hir
      have := hω i (by omega)
      simp only [hA, hir, ite_true, mem_Ioi, hZeq i ω, hLle i hir] at this
      simpa only [add_assoc] using this
    have hr : -√(ℓ : ℝ) ≤ ∑ j ∈ Finset.range e, X (c + (r * ℓ + j)) ω := by
      have := hω r (by omega)
      simp only [hA, lt_irrefl, ite_false, mem_Ici, hZeq r ω, hLr] at this
      simpa only [add_assoc] using this
    have hsum : ∑ i ∈ Finset.range r, b * √(ℓ : ℝ) ≤
        ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range ℓ, X (c + (i * ℓ + j)) ω :=
      Finset.sum_le_sum fun i hi' => (hi i (Finset.mem_range.1 hi')).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    nlinarith
  -- combine
  have hP0 : 0 ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := measureReal_nonneg
  calc Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r * (1 - e / ℓ)
      ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r *
          Q.real (Z r ⁻¹' A r) := mul_le_mul_of_nonneg_left hrem (pow_nonneg hP0 r)
    _ = Q.real E := by
        rw [hprod, Finset.prod_range_succ, Finset.prod_congr rfl fun i hi =>
          hsub i (Finset.mem_range.1 hi), Finset.prod_const, Finset.card_range]
    _ ≤ _ := measureReal_mono hEsub

/-! ### Choice of the constants -/

/-- The geometric ratio of the lower half: for `0 < ε ≤ 1` there is an integer `m ≥ 2` with
`(1 − ε/2)² m/(m − 1) < 1` and `2/√m ≤ ε/2`. -/
theorem exists_lil_lower_ratio {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ m : ℕ, 2 ≤ m ∧ (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) < 1 ∧
      2 / √(m : ℝ) ≤ ε / 2 := by
  refine ⟨⌈16 / ε ^ 2⌉₊ + 2, by omega, ?_, ?_⟩
  · set m : ℝ := ((⌈16 / ε ^ 2⌉₊ + 2 : ℕ) : ℝ) with hm
    have hm1 : 16 / ε ^ 2 ≤ m - 2 := by
      have := Nat.le_ceil (16 / ε ^ 2); rw [hm]; push_cast; linarith
    have hm2 : 16 ≤ m * ε ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hm1; nlinarith [sq_nonneg ε]
    have hm3 : (1 : ℝ) < m - 1 := by
      have : 0 < 16 / ε ^ 2 := by positivity
      linarith
    rw [mul_div_assoc', div_lt_one (by linarith)]
    have h4 : m * ε ^ 2 ≤ m * ε := by
      have : ε ^ 2 ≤ ε := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by linarith)
    nlinarith
  · set m : ℝ := ((⌈16 / ε ^ 2⌉₊ + 2 : ℕ) : ℝ) with hm
    have hm1 : 16 / ε ^ 2 ≤ m := by
      have := Nat.le_ceil (16 / ε ^ 2); rw [hm]; push_cast; linarith
    have hm0 : 0 < m := by positivity
    have hs : 0 < √m := Real.sqrt_pos.2 hm0
    rw [div_le_iff₀ hs]
    have h2 : 4 / ε ≤ √m := by
      rw [show 4 / ε = √((4 / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      rw [div_pow]; norm_num; exact hm1
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ε / 2 by positivity)
    have e : ε / 2 * (4 / ε) = 2 := by field_simp; norm_num
    linarith

/-- The sub-block level of the lower half: for `γ² < 1` there is an integer `A ≥ 1` with
`γ² ((A + 3)² + 4)/A² < 1`. -/
theorem exists_lil_lower_level {γ2 : ℝ} (hγ : γ2 < 1) :
    ∃ A : ℕ, 1 ≤ A ∧ γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 < 1 := by
  have ht : Tendsto (fun A : ℕ => γ2 * ((1 + 3 * (1 / (A : ℝ))) ^ 2 + 4 * (1 / (A : ℝ)) ^ 2))
      atTop (𝓝 (γ2 * ((1 + 3 * 0) ^ 2 + 4 * 0 ^ 2))) :=
    tendsto_const_nhds.mul (((tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul 3)).pow 2).add
      ((tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul 4))
  norm_num at ht
  obtain ⟨A, hA⟩ := ((ht.eventually (gt_mem_nhds hγ)).and (eventually_ge_atTop 1)).exists
  refine ⟨A, hA.2, ?_⟩
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA.2
  have e : γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 =
      γ2 * ((1 + 3 * (1 / (A : ℝ))) ^ 2 + 4 * (1 / (A : ℝ)) ^ 2) := by
    field_simp
  rw [e]
  have := hA.1
  simpa using this

/-- The deterministic block inequality: if `N = r ℓ + e` with `e < r`, `1 ≤ r`, `1 ≤ A ≤ ℓ` and
`T² ≤ A² N r` with `T ≥ 0`, then `T ≤ (r (A + 2) − 1) √ℓ`. -/
theorem le_block_level {T A : ℝ} (hT : 0 ≤ T) (hA : 1 ≤ A) {r ℓ e : ℕ} (her : e < r)
    (hr : 1 ≤ r) (hAℓ : A ≤ ℓ) (hTN : T ^ 2 ≤ A ^ 2 * ((r * ℓ + e : ℕ) : ℝ) * r) :
    T ≤ (r * (A + 2) - 1) * √(ℓ : ℝ) := by
  have hℓ : (1 : ℝ) ≤ ℓ := hA.trans hAℓ
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have her' : (e : ℝ) + 1 ≤ r := by exact_mod_cast her
  -- `N ≤ r (ℓ + 1) ≤ r ℓ (1 + 1/A)²`
  have hN : ((r * ℓ + e : ℕ) : ℝ) ≤ r * ℓ * (1 + 1 / A) ^ 2 := by
    push_cast
    have h1 : (ℓ : ℝ) + 1 ≤ ℓ * (1 + 1 / A) ^ 2 := by
      have h2 : (1 : ℝ) ≤ ℓ * (1 / A) := by
        rw [mul_one_div, le_div_iff₀ (by linarith)]; linarith
      have h3 : 0 ≤ (ℓ : ℝ) * (1 / A) ^ 2 := by positivity
      nlinarith
    nlinarith
  have hsq : T ^ 2 ≤ (r * (A + 1) * √(ℓ : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    have h4 : A ^ 2 * ((r * ℓ + e : ℕ) : ℝ) * r ≤ A ^ 2 * (r * ℓ * (1 + 1 / A) ^ 2) * r := by
      have := mul_le_mul_of_nonneg_left hN (sq_nonneg A)
      nlinarith
    have e1 : A ^ 2 * (r * ℓ * (1 + 1 / A) ^ 2) * r = r ^ 2 * (A + 1) ^ 2 * ℓ := by
      field_simp
    nlinarith
  have h5 : T ≤ r * (A + 1) * √(ℓ : ℝ) :=
    (pow_le_pow_iff_left₀ hT (by positivity) two_ne_zero).1 hsq
  have h6 : r * (A + 1) ≤ r * (A + 2) - 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg (ℓ : ℝ))
  linarith

/-- Exponential growth beats quadratic growth: for `m ≥ 2` and any `C`, eventually
`C (k + 1)² ≤ mᵏ`. -/
theorem eventually_mul_sq_le_pow {m : ℕ} (hm : 2 ≤ m) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * ((k : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ k := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hm1
  have hC : 0 < 4 * (|C| + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * (|C| + 1)) by positivity)),
    eventually_ge_atTop 1] with k hk hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpos : (0 : ℝ) < (m : ℝ) ^ k := by positivity
  rw [div_lt_div_iff₀ hpos hC, one_mul] at hk
  have h1 : C * ((k : ℝ) + 1) ^ 2 ≤ (|C| + 1) * (4 * (k : ℝ) ^ 2) := by
    have h2 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
    have h3 : C ≤ |C| + 1 := by have := le_abs_self C; linarith
    have h4 : 0 ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
    calc C * ((k : ℝ) + 1) ^ 2 ≤ (|C| + 1) * ((k : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right h3 h4
      _ ≤ (|C| + 1) * (4 * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-! ### The block estimate of the lower half -/

/-- **The block estimate of the lower half of the LIL**: for i.i.d. `Xⱼ` with mean `0` and
variance `1`, integers `m ≥ 2`, `A ≥ 1`, `b = A + 2`, `κ = (b + 1)²/2 + 2`, if
`P(S_ℓ > b √ℓ) ≥ e^{−κ}` for `ℓ ≥ ℓ₀`, then for every `k` with `log m^{k+1} ≥ 3` and
`C (k + 1)² ≤ mᵏ` (`C = (4m + 1)(ℓ₀ + A + 1 + 2(4m + 1))`) the block `[mᵏ, mᵏ⁺¹)` has
`P(Σ_{mᵏ ≤ j < mᵏ⁺¹} Xⱼ ≥ (1 − ε/2) √(2 M log log M)) ≥ (e^{−κ}/2) (log M)^{−p'}`, `M = mᵏ⁺¹`,
`p' = 2γ²κ/A²`, `γ² = (1 − ε/2)² m/(m − 1)`. -/
theorem lil_lower_block_estimate {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) {ε : ℝ}
    (hε1 : ε ≤ 1) {m A ℓ₀ : ℕ} (hm2 : 2 ≤ m) (hA1 : 1 ≤ A)
    (hγ : (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) ≤ 1)
    (hP1 : ∀ ℓ ≥ ℓ₀, Real.exp (-((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2)) ≤
      Q.real {ω | ((A : ℝ) + 2) * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω})
    {k : ℕ} (hk3 : 3 ≤ Real.log ((m : ℝ) ^ (k + 1)))
    (hkC : (4 * m + 1) * ((ℓ₀ + A + 1 : ℕ) + 2 * (4 * m + 1)) * ((k : ℝ) + 1) ^ 2 ≤
      (m : ℝ) ^ k) :
    Real.exp (-((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2)) / 2 *
      Real.exp (-(2 * ((1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1))) *
        ((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2) / (A : ℝ) ^ 2 *
        Real.log (Real.log ((m : ℝ) ^ (k + 1))))) ≤
      Q.real {ω | (1 - ε / 2) * lilScale (m ^ (k + 1)) ≤
        ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), X j ω} := by
  set γ2 := (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) with hγ2
  set b : ℝ := A + 2 with hb
  set κ : ℝ := (b + 1) ^ 2 / 2 + 2 with hκ
  set p' : ℝ := 2 * γ2 * κ / (A : ℝ) ^ 2 with hp'def
  set Lstar : ℕ := ℓ₀ + A + 1 with hLstar
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm2
  have hpow_le : m ^ k ≤ m ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  set N : ℕ := m ^ (k + 1) - m ^ k with hN
  set T : ℝ := (1 - ε / 2) * lilScale (m ^ (k + 1)) with hT
  set r : ℕ := ⌊T ^ 2 / ((A : ℝ) ^ 2 * N)⌋₊ + 1 with hr
  set ℓ : ℕ := N / r with hℓ
  set e : ℕ := N % r with he
  have hNcast : (N : ℝ) = (m : ℝ) ^ k * ((m : ℝ) - 1) := by
    rw [hN, Nat.cast_sub hpow_le]
    push_cast; ring
  have hNeq : r * ℓ + e = N := Nat.div_add_mod N r
  set M : ℕ := m ^ (k + 1) with hM
  have hMc : (M : ℝ) = (m : ℝ) ^ (k + 1) := by rw [hM]; push_cast; ring
  have hk3' : 3 ≤ Real.log (M : ℝ) := by rw [hMc]; exact hk3
  clear_value γ2 b κ p' Lstar N T r ℓ e M
  have hLL := one_le_loglog hk3'
  have hmk0 : (0 : ℝ) < (m : ℝ) ^ k := by positivity
  have hN0 : (0 : ℝ) < N := by rw [hNcast]; exact mul_pos hmk0 (by linarith)
  -- `T² /(A² N) = 2 γ² log log M`
  have hT2 : T ^ 2 = (1 - ε / 2) ^ 2 * (2 * M * Real.log (Real.log M)) := by
    rw [hT, mul_pow, lilScale_sq hk3']
  have hTN : T ^ 2 / ((A : ℝ) ^ 2 * N) = 2 * γ2 * Real.log (Real.log M) / (A : ℝ) ^ 2 := by
    rw [hT2, hNcast, hMc, hγ2]
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hTN0 : 0 ≤ T ^ 2 / ((A : ℝ) ^ 2 * N) := by positivity
  have hγ0 : 0 ≤ γ2 := by
    rw [hγ2]
    have : (0 : ℝ) < m - 1 := by linarith
    positivity
  -- `r ≤ (4m + 1)(k + 1)`
  have hlogM : Real.log (Real.log M) ≤ ((k : ℝ) + 1) * m := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log (M : ℝ) by linarith)
    have h2 : Real.log (M : ℝ) = ((k : ℝ) + 1) * Real.log m := by
      rw [hMc, Real.log_pow]; push_cast; ring
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith)
    have h4 : ((k : ℝ) + 1) * Real.log m ≤ ((k : ℝ) + 1) * m :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hrR : r ≤ (4 * m + 1) * (k + 1) := by
    have h1 : T ^ 2 / ((A : ℝ) ^ 2 * N) ≤ 4 * (((k : ℝ) + 1) * m) := by
      rw [hTN, div_le_iff₀ (by positivity)]
      have hL0 : 0 ≤ Real.log (Real.log M) := by linarith
      have hkm : 0 ≤ ((k : ℝ) + 1) * m := by positivity
      calc 2 * γ2 * Real.log (Real.log M) ≤ 2 * 1 * Real.log (Real.log M) :=
            mul_le_mul_of_nonneg_right (by linarith) hL0
        _ ≤ 2 * (((k : ℝ) + 1) * m) := by linarith
        _ ≤ 4 * (((k : ℝ) + 1) * m) * (A : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
            nlinarith
    have h2 : ⌊T ^ 2 / ((A : ℝ) ^ 2 * N)⌋₊ ≤ 4 * ((k + 1) * m) := by
      apply Nat.floor_le_of_le; push_cast; linarith
    have e1 : (4 * m + 1) * (k + 1) = 4 * ((k + 1) * m) + (k + 1) := by ring
    rw [hr, e1]
    omega
  have hr1 : 1 ≤ r := by rw [hr]; omega
  -- `ℓ ≥ L* + 2 (4m + 1)(k + 1)`
  have hNk : m ^ k ≤ N := by
    have hM' : M = m ^ k * m := by rw [hM, pow_succ]
    have : m ^ k * 2 ≤ m ^ k * m := Nat.mul_le_mul_left _ hm2
    omega
  have hbig : (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1))) ≤ m ^ k := by
    have hkC' : (4 * m + 1) * (Lstar + 2 * (4 * m + 1)) * (k + 1) ^ 2 ≤ m ^ k := by
      exact_mod_cast hkC
    have hLK : Lstar ≤ Lstar * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1)))
        ≤ (4 * m + 1) * (k + 1) * (Lstar * (k + 1) + 2 * ((4 * m + 1) * (k + 1))) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hLK _)
      _ = (4 * m + 1) * (Lstar + 2 * (4 * m + 1)) * (k + 1) ^ 2 := by ring
      _ ≤ m ^ k := hkC'
  have hℓbig : Lstar + 2 * ((4 * m + 1) * (k + 1)) ≤ ℓ := by
    calc Lstar + 2 * ((4 * m + 1) * (k + 1))
        ≤ N / ((4 * m + 1) * (k + 1)) := by
          rw [Nat.le_div_iff_mul_le (by positivity)]
          calc (Lstar + 2 * ((4 * m + 1) * (k + 1))) * ((4 * m + 1) * (k + 1))
              = (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1))) := by ring
            _ ≤ m ^ k := hbig
            _ ≤ N := hNk
      _ ≤ N / r := Nat.div_le_div_left hrR (by omega)
      _ = ℓ := hℓ.symm
  have hℓ₀ : ℓ₀ ≤ ℓ := by omega
  have hAℓ : (A : ℝ) ≤ ℓ := by exact_mod_cast (show A ≤ ℓ by omega)
  have h2r : 2 * r ≤ ℓ := by omega
  have hℓ0 : 0 < ℓ := by omega
  have her : e < r := by rw [he]; exact Nat.mod_lt _ (by omega)
  have hsubset : {ω | (r * b - 1) * √(ℓ : ℝ) ≤
      ∑ j ∈ Finset.range (r * ℓ + e), X (m ^ k + j) ω} ⊆
      {ω | T ≤ ∑ j ∈ Finset.Ico (m ^ k) M, X j ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Finset.sum_Ico_eq_sum_range, ← hN, ← hNeq]
    have hT0 : 0 ≤ T :=
      le_of_le_of_eq (mul_nonneg (by linarith only [hε1]) (lilScale_nonneg _)) hT.symm
    have hTle : T ≤ (r * ((A : ℝ) + 2) - 1) * √(ℓ : ℝ) := by
      refine le_block_level hT0 hA1' her hr1 hAℓ ?_
      have hfl : T ^ 2 / ((A : ℝ) ^ 2 * N) ≤ r := by
        rw [hr]; push_cast
        exact (Nat.lt_floor_add_one _).le
      rw [hNeq]
      rw [div_le_iff₀ (by positivity)] at hfl
      linarith only [hfl]
    rw [hb] at hω
    linarith only [hω, hTle]
  have hhalf : (1 : ℝ) / 2 ≤ 1 - e / ℓ := by
    have : (e : ℝ) / ℓ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hℓ0)]
      have h2e : (2 * e : ℝ) ≤ ℓ := by exact_mod_cast (show 2 * e ≤ ℓ by omega)
      linarith only [h2e]
    linarith only [this]
  have hr_le : (r : ℝ) ≤ T ^ 2 / ((A : ℝ) ^ 2 * N) + 1 := by
    rw [hr]; push_cast
    have := Nat.floor_le hTN0
    linarith only [this]
  have hexp_r : Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) ≤
      Real.exp (-κ * r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hκ0 : 0 ≤ κ := le_of_le_of_eq (by positivity) hκ.symm
    have h7 : κ * r ≤ κ * (T ^ 2 / ((A : ℝ) ^ 2 * N) + 1) :=
      mul_le_mul_of_nonneg_left hr_le hκ0
    rw [hTN] at h7
    have e2 : κ * (2 * γ2 * Real.log (Real.log M) / (A : ℝ) ^ 2 + 1) =
        p' * Real.log (Real.log M) + κ := by rw [hp'def]; ring
    linarith only [h7, e2]
  -- the block bound
  have hblk := block_lower_bound hind hm hident hL2 h0 h1 (m ^ k) r ℓ e b hℓ0
  have hP := hP1 ℓ hℓ₀
  have hpowr : Real.exp (-κ * r) ≤
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r := by
    rw [show -κ * r = r * (-κ) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hP _
  have hfin := (mul_le_mul hpowr hhalf (by norm_num) (pow_nonneg measureReal_nonneg _)).trans
    (hblk.trans (measureReal_mono hsubset))
  rw [← hMc]
  have hpos := Real.exp_pos (-κ * r)
  have e3 : Real.exp (-κ) / 2 * Real.exp (-(p' * Real.log (Real.log M))) =
      Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) * (1 / 2) := by ring
  rw [e3]
  calc Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) * (1 / 2)
      ≤ Real.exp (-κ * r) * (1 / 2) := mul_le_mul_of_nonneg_right hexp_r (by norm_num)
    _ ≤ _ := hfin

/-! ### The lower half of the LIL -/

/-- **The lower half of the Hartman–Wintner LIL**, normalised: for i.i.d. `Xⱼ` with mean `0`
and variance `1` and `0 < ε ≤ 1`, almost surely `Sₙ ≥ (1 − ε) √(2 n log log n)` for infinitely
many `n`. -/
theorem lil_lower_normalized {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ ω ∂Q, ∃ᶠ n in atTop, (1 - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, X j ω := by
  obtain ⟨m, hm2, hγ, hmε⟩ := exists_lil_lower_ratio hε hε1
  set γ2 := (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) with hγ2
  obtain ⟨A, hA1, hp'⟩ := exists_lil_lower_level hγ
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm2
  set b : ℝ := A + 2 with hb
  set κ : ℝ := (b + 1) ^ 2 / 2 + 2 with hκ
  set p' : ℝ := 2 * γ2 * κ / (A : ℝ) ^ 2 with hp'def
  have hp'1 : p' ≤ 1 := by
    have e : p' = γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 := by rw [hp'def, hκ, hb]; ring
    rw [e]; exact hp'.le
  -- the CLT for the sub-blocks
  have hb0 : 0 ≤ b := by positivity
  have hG := gaussianReal_Ioi_ge hb0
  set g := gaussianReal 0 1 (Ioi b) with hg
  have hc0 : 0 < Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) := by positivity
  have hgpos : g ≠ 0 := by
    intro h0'
    have : (gaussianReal 0 1).real (Ioi b) = 0 := by rw [measureReal_def, ← hg, h0']; rfl
    linarith
  have hq : g / 2 < g := ENNReal.half_lt_self hgpos (measure_ne_top _ _)
  obtain ⟨ℓ₀, hℓ₀⟩ := eventually_atTop.1 (eventually_lt_measure_clt hind hm hident h0 h1 b hq)
  have hP1 : ∀ ℓ ≥ ℓ₀, Real.exp (-κ) ≤
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := by
    intro ℓ hℓ
    have h2 : (g / 2).toReal ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hℓ₀ ℓ hℓ).le
    rw [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h2
    have h3 : Real.exp (-κ) ≤ Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) / 2 := by
      have e1 : Real.exp (-κ) = Real.exp (-((b + 1) ^ 2 / 2)) * Real.exp (-2) := by
        rw [← Real.exp_add, hκ]; ring_nf
      have h4 := two_mul_sqrt_two_pi_le_exp_two
      have h5 : Real.exp (-2) ≤ 1 / (2 * √(2 * Real.pi)) := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) h4
      rw [e1, div_div, mul_comm (√(2 * Real.pi)) 2]
      calc Real.exp (-((b + 1) ^ 2 / 2)) * Real.exp (-2)
          ≤ Real.exp (-((b + 1) ^ 2 / 2)) * (1 / (2 * √(2 * Real.pi))) :=
            mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = Real.exp (-((b + 1) ^ 2 / 2)) / (2 * √(2 * Real.pi)) := by rw [mul_one_div]
    have h6 : (gaussianReal 0 1).real (Ioi b) = g.toReal := rfl
    linarith
  -- the independent block events
  set Z : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), X j ω with hZ
  set T : ℕ → ℝ := fun k => (1 - ε / 2) * lilScale (m ^ (k + 1)) with hT
  set G : ℕ → Set Ω := fun k => Z k ⁻¹' Ici (T k) with hG
  have hpowmono : ∀ i j, i ≤ j → m ^ i ≤ m ^ j := fun i j h =>
    Nat.pow_le_pow_right (by omega) h
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k => ((Finset.Ico (m ^ k) (m ^ (k + 1)) : Finset ℕ) : Set ℕ)) := by
    have key : ∀ i i', i < i' → Disjoint ((Finset.Ico (m ^ i) (m ^ (i + 1)) : Finset ℕ) : Set ℕ)
        ((Finset.Ico (m ^ i') (m ^ (i' + 1)) : Finset ℕ) : Set ℕ) := fun i i' h => by
      simp only [Finset.coe_Ico]
      rw [Set.Ico_disjoint_Ico]
      have h1 := hpowmono (i + 1) i' h
      have h2 := hpowmono i' (i' + 1) (Nat.le_succ i')
      omega
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact key i i' h
    · exact (key i' i h).symm
  have hZm : ∀ k, Measurable (Z k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  have hGind : iIndepSet G Q :=
    iIndepSet_preimage (iIndepFun_blockSum hind hm hdisj) fun k => measurableSet_Ici
  have hGm : ∀ k, MeasurableSet (G k) := fun k => hZm k measurableSet_Ici
  -- the probabilities of the block events diverge
  set Cst : ℝ := (4 * m + 1) * ((ℓ₀ + A + 1 : ℕ) + 2 * (4 * m + 1)) with hCst
  have hlogt : Tendsto (fun k : ℕ => Real.log ((m : ℝ) ^ (k + 1))) atTop atTop := by
    have : (fun k : ℕ => Real.log ((m : ℝ) ^ (k + 1))) =
        fun k : ℕ => ((k : ℝ) + 1) * Real.log m := by
      ext k; rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
      (Real.log_pos hm1)
  have hprob : ∀ᶠ k in atTop, Real.exp (-κ) / 2 *
      Real.exp (-(p' * Real.log (Real.log ((m : ℝ) ^ (k + 1))))) ≤ Q.real (G k) := by
    filter_upwards [hlogt.eventually_ge_atTop 3, eventually_mul_sq_le_pow hm2 Cst] with k hk3 hkC
    exact lil_lower_block_estimate hind hm hident hL2 h0 h1 hε1 hm2 hA1 hγ.le hP1 hk3 hkC
  have hC0 : 0 < Real.exp (-κ) / 2 := by positivity
  have hdiv : ∑' k, Q (G k) = ∞ := by
    by_contra hne
    have hs : Summable fun k => Q.real (G k) := ENNReal.summable_toReal hne
    have hs2 : Summable fun k => Real.exp (-κ) / 2 *
        Real.exp (-(p' * Real.log (Real.log ((m : ℝ) ^ (k + 1))))) := by
      refine hs.of_norm_bounded_eventually_nat ?_
      filter_upwards [hprob] with k hk
      rwa [Real.norm_eq_abs, abs_of_pos (mul_pos hC0 (Real.exp_pos _))]
    exact not_summable_exp_neg_mul_loglog_pow hm2 hp'1 hC0 ((summable_nat_add_iff 1).1 hs2)
  have hlim := measure_limsup_eq_one hGm hGind hdiv
  have hae : ∀ᵐ ω ∂Q, ∃ᶠ k in atTop, ω ∈ G k := by
    have hm' : MeasurableSet (limsup G atTop) := MeasurableSet.measurableSet_limsup hGm
    have h2 : ∀ᵐ ω ∂Q, ω ∈ limsup G atTop := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hm').2 hlim
    filter_upwards [h2] with ω hω
    exact mem_limsup_iff_frequently_mem.1 hω
  -- the upper half for `−X` controls the start of the blocks
  have hneg := lil_upper (X := fun j ω => -X j ω)
    (hind.comp (fun _ x => -x) fun _ => measurable_neg) (fun j => (hm j).neg)
    (fun j => (hident j).comp measurable_neg) hL2.neg
    (by rw [integral_neg, h0, neg_zero]) one_pos
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = 1 := by
    simp_rw [neg_sq]; rw [h1, Real.sqrt_one]
  simp only [hsq] at hneg
  filter_upwards [hae, hneg] with ω hωG hωU
  rw [Filter.frequently_atTop]
  intro n₀
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hωU
  have hlogk : Tendsto (fun k : ℕ => Real.log ((m ^ k : ℕ) : ℝ)) atTop atTop := by
    have : (fun k : ℕ => Real.log ((m ^ k : ℕ) : ℝ)) = fun k : ℕ => (k : ℝ) * Real.log m := by
      ext k; push_cast; rw [Real.log_pow]
    rw [this]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos hm1)
  obtain ⟨k, hkG, hk⟩ := (hωG.and_eventually ((eventually_ge_atTop (n₀ + N1)).and
    (hlogk.eventually_ge_atTop 3))).exists
  have hk1 : n₀ + N1 ≤ k := hk.1
  have hk3 : 3 ≤ Real.log ((m ^ k : ℕ) : ℝ) := hk.2
  have hk3' : 3 ≤ Real.log ((m ^ (k + 1) : ℕ) : ℝ) :=
    three_le_log_of_le hk3 (hpowmono k (k + 1) (Nat.le_succ k))
  have hkm : k < m ^ k := Nat.lt_pow_self (by omega)
  refine ⟨m ^ (k + 1), ?_, ?_⟩
  · have := Nat.lt_pow_self (n := k + 1) (show 1 < m by omega)
    omega
  have hsplit : ∑ j ∈ Finset.range (m ^ (k + 1)), X j ω =
      ∑ j ∈ Finset.range (m ^ k), X j ω + Z k ω :=
    (Finset.sum_range_add_sum_Ico _ (hpowmono k (k + 1) (Nat.le_succ k))).symm
  have hU : ∑ j ∈ Finset.range (m ^ k), -X j ω ≤ (1 + 1) * lilScale (m ^ k) :=
    hN1 (m ^ k) (by omega)
  rw [Finset.sum_neg_distrib] at hU
  have hGk : T k ≤ Z k ω := hkG
  -- `√m lilScale mᵏ ≤ lilScale mᵏ⁺¹`
  have hlil : √(m : ℝ) * lilScale (m ^ k) ≤ lilScale (m ^ (k + 1)) := by
    have h1' := lilScale_sq hk3
    have h2' := lilScale_sq hk3'
    have hll : Real.log (Real.log ((m ^ k : ℕ) : ℝ)) ≤
        Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) := by
      have hp0 : (0 : ℝ) < ((m ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos (show 0 < m by omega) k
      exact Real.log_le_log (by linarith) (Real.log_le_log hp0
        (by exact_mod_cast hpowmono k (k + 1) (Nat.le_succ k)))
    have hsq2 : (√(m : ℝ) * lilScale (m ^ k)) ^ 2 ≤ lilScale (m ^ (k + 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), h1', h2']
      have e1 : ((m ^ (k + 1) : ℕ) : ℝ) = m * ((m ^ k : ℕ) : ℝ) := by push_cast; ring
      have hp1 : (0 : ℝ) ≤ 2 * (m * ((m ^ k : ℕ) : ℝ)) := by positivity
      calc (m : ℝ) * (2 * ((m ^ k : ℕ) : ℝ) * Real.log (Real.log ((m ^ k : ℕ) : ℝ)))
          = 2 * (m * ((m ^ k : ℕ) : ℝ)) * Real.log (Real.log ((m ^ k : ℕ) : ℝ)) := by ring
        _ ≤ 2 * (m * ((m ^ k : ℕ) : ℝ)) * Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hll hp1
        _ = 2 * ((m ^ (k + 1) : ℕ) : ℝ) * Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) := by
            rw [e1]
    exact (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) (lilScale_nonneg _))
      (lilScale_nonneg _) two_ne_zero).1 hsq2
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h2lil : 2 * lilScale (m ^ k) ≤ ε / 2 * lilScale (m ^ (k + 1)) := by
    have e2 : 2 * lilScale (m ^ k) = 2 / √(m : ℝ) * (√(m : ℝ) * lilScale (m ^ k)) := by
      field_simp
    rw [e2]
    calc 2 / √(m : ℝ) * (√(m : ℝ) * lilScale (m ^ k))
        ≤ 2 / √(m : ℝ) * lilScale (m ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hlil (by positivity)
      _ ≤ ε / 2 * lilScale (m ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hmε (lilScale_nonneg _)
  rw [hsplit]
  simp only [hT] at hGk
  linarith

end MeynTweedie.GeneralizedDrift
