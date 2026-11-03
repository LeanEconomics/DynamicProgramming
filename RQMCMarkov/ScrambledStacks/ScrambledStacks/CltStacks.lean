/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltVariance

/-!
# The CLT for two-state chains driven by scrambled van der Corput stacks (post #3)

Post #3, codes (ii) (one Sobol sequence per state, random digital shift) and (iii) (Owen
scrambling), two-state chain: "in the five-state chain normality cannot be rejected for the
per-state Sobol sequences ((ii) and (iii))", while "as in the i.i.d. case, the RQMC estimators
are typically not normally distributed".

**Reading.** We prove a central limit theorem along time sequences whose variance grows like
`log T`, for both randomisations at once (any `IsPathCoinModel`):

  if `T_k → ∞` and `Var(N₀(T_k) − T_k π₀) ≥ κ log₂ T_k` eventually, then
  `(N₀(T_k) − T_k π₀) / √Var ⇒ N(0,1)`.

The proof: the error is `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋))/q + O(log log T)` for every flip table
(`CltAnscombe`); the main term is a sum over binary levels of bounded functions of i.i.d. fair
path coins with geometrically decaying dependence (`CltPathBits`, `CltVariance`); the truncation
CLT (`CltMDependent`) gives its normality; Slutsky's theorem removes the `O(log log T)`.

The hypothesis is not vacuous: for `p₁₁ = p₂₂ = 2/3` and `T_k = 2 Σ_{a<k} 16^a` the variance is
`≥ k/12` (`CltVariance`), so `occErr_example_tendstoInDistribution` holds.

**Correction** (with `StackDyadic` and `StackPowerOfTwo`). (ii)/(iii) are not
asymptotically normal along all `T`: the CLT holds at the scale `√log T` along times with
`Var ≥ κ log T`; for non-dyadic chains the variance stays bounded along `T = 2^k`. And unlike the
i.i.d. case of post #2 (where the digital shift is not normal), for two-state Markov stacks the
digital shift and Owen's scramble give path coins with the same law (`map_owenPathCoins`),
hence main terms with the same law, and both are normal along such times.

**RMSE.** `E[(N₀(T) − T π₀)²] = O(log T)`, so the occupation frequency has RMSE
`O(√log T / T)` (`IsPathCoinModel.integral_sq_occErr_le`,
`IsPathCoinModel.isBigO_meanSq_occFreq`), against `O(1/√T)` for MC.

**Hypotheses added.** `p₀₁ > 0` and `p₁₁ > 0` (the thresholds `p₀₀`, `p₁₀` lie in `[0,1)`, where
their binary digits are defined; `p₀₁ > 0` also gives `q > 0`). The variance hypothesis is stated
along the given times (`∀ᶠ k`), as the CLT is about such subsequences.

## Main results

* `TendstoInDistribution.comp_measurePreserving`, `TendstoInDistribution.of_map_eq`:
  convergence in distribution only depends on laws.
* `tendstoInDistribution_coinSum`: the CLT for the coin sums on the fair-coin space.
* `tendstoInDistribution_of_abs_sub_le`: Slutsky's theorem for a bounded perturbation
  `b_k = o(σ_k)`; `anscBound_le_log`, `tendsto_anscBound_sq_div`: `anscBound(T)² = o(log T)`.
* `IsPathCoinModel.tendstoInDistribution_occErr` (**main theorem**), with
  `tendstoInDistribution_occErr_owen` (code (iii)) and `tendstoInDistribution_occErr_shift`
  (code (ii)).
* `chainSumErr`, `chainSumErr_eq` (`E_T(g) = (g 0 − g 1)(N₀(T) − T π₀)`) and
  `IsPathCoinModel.tendstoInDistribution_chainSumErr`: the CLT for every `g` with `g 0 ≠ g 1`.
* `occErr_example_tendstoInDistribution` (+ `_owen`, `_shift`): the CLT on the concrete
  sequence of `CltVariance` (the hypothesis holds: `IsPathCoinModel.eventually_variance_example`).
* `IsPathCoinModel.integral_sq_occErr_le`, `IsPathCoinModel.isBigO_meanSq_occFreq`: RMSE.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-- **Convergence in distribution depends only on laws**: it transfers through a
measure-preserving map. -/
theorem TendstoInDistribution.comp_measurePreserving {Ω Ω'' Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω''] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω''}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ψ : Ω → Ω''} (hΨ : MeasurePreserving Ψ μ ν) {G : ℕ → Ω'' → ℝ}
    {Z : Ω' → ℝ} (h : TendstoInDistribution G atTop Z (fun _ ↦ ν) P') :
    TendstoInDistribution (fun k ω ↦ G k (Ψ ω)) atTop Z (fun _ ↦ μ) P' where
  forall_aemeasurable k := by
    have h1 := h.forall_aemeasurable k
    rw [← hΨ.map_eq] at h1
    exact h1.comp_aemeasurable hΨ.aemeasurable
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    have e : ∀ k, μ.map (fun ω ↦ G k (Ψ ω)) = ν.map (G k) := fun k ↦ by
      have h1 := h.forall_aemeasurable k
      rw [← hΨ.map_eq] at h1 ⊢
      rw [AEMeasurable.map_map_of_aemeasurable h1 hΨ.aemeasurable]
      rfl
    exact Tendsto.congr (fun k ↦ Subtype.ext (e k).symm) h.tendsto

/-- **The CLT on the coin space.** For thresholds in `[0,1)`, indices `n k`, and `K k → ∞`
levels, if `Var(coin sum) ≥ κ K k` eventually, the normalised coin sums are asymptotically
`N(0,1)`. (`tendstoInDistribution_of_truncations` with `B = 2`, `C = 4`.) -/
theorem tendstoInDistribution_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1)
    {n : ℕ → Fin 2 → ℕ} {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * K k ≤ Var[coinSum c (n k) (K k); shiftMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k w ↦ coinSum c (n k) (K k) w /
      √Var[coinSum c (n k) (K k); shiftMeasure 2]) atTop Z (fun _ ↦ shiftMeasure 2) P' := by
  set Y : ℕ → ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k m w ↦
    ∑ i, coinTerm (c i) (n k i) m (stateCoins w i) with hY
  set Yt : ℕ → ℕ → ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k m L w ↦
    ∑ i, coinTermTrunc (c i) (n k i) m L (stateCoins w i) with hYt
  have h := tendstoInDistribution_of_truncations (fun _ : Fin 2 × ℕ ↦ fairCoin) Prod.snd hK
    (Y := Y) (Yt := Yt) (B := 2) (C := 4)
    (fun k m ↦ Finset.measurable_fun_sum _ fun i _ ↦ measurable_coinTerm (hc i).1 (hc i).2 _ _ i)
    (fun k m w ↦ ?_) (fun k m L w ↦ ?_) (fun k m L ↦ ?_) (fun k m L ↦ ?_) hκ hvar hZ
  · have e : (fun k w ↦ coinSum c (n k) (K k) w /
        √Var[coinSum c (n k) (K k); shiftMeasure 2]) =
        fun k w ↦ ((∑ m ∈ range (K k), Y k m w) -
          (shiftMeasure 2)[fun ω ↦ ∑ m ∈ range (K k), Y k m ω]) /
          √Var[fun ω ↦ ∑ m ∈ range (K k), Y k m ω; shiftMeasure 2] := by
      funext k w
      have h0 := integral_coinSum hc (n k) (K k)
      change coinSum c (n k) (K k) w / √Var[coinSum c (n k) (K k); shiftMeasure 2] =
        (coinSum c (n k) (K k) w - ∫ ω, coinSum c (n k) (K k) ω ∂(shiftMeasure 2)) /
          √Var[coinSum c (n k) (K k); shiftMeasure 2]
      rw [h0, sub_zero]
    rw [e]
    exact h
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Fin.sum_univ_two]
    linarith [abs_coinTerm_le (hc 0).1 (n k 0) m (stateCoins w 0),
      abs_coinTerm_le (hc 1).1 (n k 1) m (stateCoins w 1)]
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Fin.sum_univ_two]
    linarith [abs_coinTermTrunc_le (hc 0).1 (n k 0) m L (stateCoins w 0),
      abs_coinTermTrunc_le (hc 1).1 (n k 1) m L (stateCoins w 1)]
  · refine ⟨(univ : Finset (Fin 2)) ×ˢ Finset.Ico m (m + L), fun q hq ↦ ?_, ?_⟩
    · simp only [mem_product, mem_univ, Finset.mem_Ico, true_and] at hq
      exact hq
    · exact isLocal_sum _ fun i _ ↦ (isLocal_coinTermTrunc (c i) (n k i) m L i).mono
        (product_subset_product (subset_univ _) subset_rfl)
  · have h0 := integral_sq_coinTerm_sub_trunc_le (hc 0).1 (hc 0).2 (n k 0) m L 0
    have h1 := integral_sq_coinTerm_sub_trunc_le (hc 1).1 (hc 1).2 (n k 1) m L 1
    set d0 := fun w : Fin 2 × ℕ → Bool ↦
      coinTerm (c 0) (n k 0) m (stateCoins w 0) - coinTermTrunc (c 0) (n k 0) m L (stateCoins w 0)
    set d1 := fun w : Fin 2 × ℕ → Bool ↦
      coinTerm (c 1) (n k 1) m (stateCoins w 1) - coinTermTrunc (c 1) (n k 1) m L (stateCoins w 1)
    have hd0 : MemLp d0 2 (shiftMeasure 2) :=
      (memLp_coinTerm (hc 0).1 (hc 0).2 _ m 0).sub (memLp_coinTermTrunc (hc 0).1 _ m L 0)
    have hd1 : MemLp d1 2 (shiftMeasure 2) :=
      (memLp_coinTerm (hc 1).1 (hc 1).2 _ m 1).sub (memLp_coinTermTrunc (hc 1).1 _ m L 1)
    have hpt : ∀ w, (Y k m w - Yt k m L w) ^ 2 ≤ 2 * d0 w ^ 2 + 2 * d1 w ^ 2 := by
      intro w
      have e : Y k m w - Yt k m L w = d0 w + d1 w := by
        simp only [hY, hYt, Fin.sum_univ_two, d0, d1]
        ring
      rw [e]
      nlinarith [sq_nonneg (d0 w - d1 w)]
    have hint : Integrable (fun w ↦ (Y k m w - Yt k m L w) ^ 2) (shiftMeasure 2) := by
      have e : (fun w ↦ (Y k m w - Yt k m L w) ^ 2) = fun w ↦ (d0 w + d1 w) ^ 2 := by
        funext w
        simp only [hY, hYt, Fin.sum_univ_two, d0, d1]
        ring
      rw [e]
      exact (hd0.add hd1).integrable_sq
    calc ∫ w, (Y k m w - Yt k m L w) ^ 2 ∂(shiftMeasure 2)
        ≤ ∫ w, (2 * d0 w ^ 2 + 2 * d1 w ^ 2) ∂(shiftMeasure 2) :=
          integral_mono hint ((hd0.integrable_sq.const_mul 2).add (hd1.integrable_sq.const_mul 2))
            hpt
      _ = 2 * ∫ w, d0 w ^ 2 ∂(shiftMeasure 2) + 2 * ∫ w, d1 w ^ 2 ∂(shiftMeasure 2) := by
          rw [integral_add (hd0.integrable_sq.const_mul 2) (hd1.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 4 * (1 / 2) ^ L := by linarith

/-- **Slutsky for a bounded perturbation.** If `|E k − M k| ≤ b k` with `b k² = o(Var E k)`,
`M k` centred, and `M k / √Var(M k) ⇒ Z`, then `E k / √Var(E k) ⇒ Z`. -/
theorem tendstoInDistribution_of_abs_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (hE : ∀ k, MemLp (E k) 2 μ) (hM : ∀ k, MemLp (M k) 2 μ) (hM0 : ∀ k, μ[M k] = 0)
    (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k)
    (hb : Tendsto (fun k ↦ b k ^ 2 / Var[E k; μ]) atTop (𝓝 0))
    (hpos : ∀ᶠ k in atTop, 0 < Var[E k; μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hlim : TendstoInDistribution (fun k ω ↦ M k ω / √Var[M k; μ]) atTop Z (fun _ ↦ μ) P') :
    TendstoInDistribution (fun k ω ↦ E k ω / √Var[E k; μ]) atTop Z (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  -- the standard deviations are close
  have hσ : ∀ k, |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    intro k
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  -- eventually `b ≤ σ_E / 2`
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / Var[E k; μ] ≤ 1 / 4 :=
    hb.eventually (ge_mem_nhds (by norm_num))
  set D : ℕ → Ω → ℝ := fun k ω ↦ E k ω / √Var[E k; μ] - M k ω / √Var[M k; μ] with hD
  have hDm : ∀ k, MemLp (D k) 2 μ := fun k ↦ by
    simp_rw [hD, div_eq_mul_inv]
    exact ((hE k).mul_const _).sub ((hM k).mul_const _)
  have hbound : ∀ᶠ k in atTop, ∫ ω, D k ω ^ 2 ∂μ ≤ 4 * (b k ^ 2 / Var[E k; μ]) := by
    filter_upwards [hpos, hsmall] with k hk hs
    set sE := √Var[E k; μ] with hsE
    set sM := √Var[M k; μ] with hsM
    have hsE0 : 0 < sE := Real.sqrt_pos.2 hk
    have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt hk.le
    have hbE : b k ≤ sE / 2 := by
      rw [div_le_iff₀ hk, ← hsE2] at hs
      nlinarith [hb0 k]
    have hsM0 : 0 < sM := by
      have := (abs_le.1 (hσ k)).1
      linarith
    have hMvar : ∫ ω, M k ω ^ 2 ∂μ = sM ^ 2 := by
      rw [hsM, Real.sq_sqrt (variance_nonneg _ _),
        variance_of_integral_eq_zero (hM k).aestronglyMeasurable.aemeasurable (hM0 k)]
    have hpt : ∀ ω, D k ω ^ 2 ≤ 2 * ((E k ω - M k ω) / sE) ^ 2 +
        2 * ((sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2) := by
      intro ω
      have e : D k ω = (E k ω - M k ω) / sE + M k ω * (sE⁻¹ - sM⁻¹) := by
        simp only [hD]
        rw [← hsE, ← hsM]
        field_simp
        ring
      rw [e]
      nlinarith [sq_nonneg ((E k ω - M k ω) / sE - M k ω * (sE⁻¹ - sM⁻¹))]
    have hpt1 : ∀ ω, ((E k ω - M k ω) / sE) ^ 2 ≤ b k ^ 2 / sE ^ 2 := fun ω ↦ by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hclose k ω) 2) (by positivity)
    have hi1 : Integrable (fun ω ↦ ((E k ω - M k ω) / sE) ^ 2) μ := by
      simp_rw [div_eq_mul_inv]
      exact (((hE k).sub (hM k)).mul_const _).integrable_sq
    have hi2 : Integrable (fun ω ↦ (sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2) μ :=
      (hM k).integrable_sq.const_mul _
    calc ∫ ω, D k ω ^ 2 ∂μ
        ≤ ∫ ω, (2 * ((E k ω - M k ω) / sE) ^ 2 + 2 * ((sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2)) ∂μ :=
          integral_mono (hDm k).integrable_sq ((hi1.const_mul 2).add (hi2.const_mul 2)) hpt
      _ = 2 * ∫ ω, ((E k ω - M k ω) / sE) ^ 2 ∂μ + 2 * ((sE⁻¹ - sM⁻¹) ^ 2 * sM ^ 2) := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul, integral_const_mul, hMvar]
      _ ≤ 2 * (b k ^ 2 / sE ^ 2) + 2 * (b k ^ 2 / sE ^ 2) := by
          gcongr
          · have := integral_mono hi1 (integrable_const (b k ^ 2 / sE ^ 2)) hpt1
            rwa [integral_const, probReal_univ, one_smul] at this
          · have e : (sE⁻¹ - sM⁻¹) ^ 2 * sM ^ 2 = ((sM - sE) / sE) ^ 2 := by
              field_simp
            rw [e, div_pow]
            exact div_le_div_of_nonneg_right (by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hσ k) 2) (by positivity)
      _ = 4 * (b k ^ 2 / Var[E k; μ]) := by rw [hsE2]; ring
  have hlimD : Tendsto (fun k ↦ ∫ ω, D k ω ^ 2 ∂μ) atTop (𝓝 0) := by
    have h4 := hb.const_mul 4
    rw [mul_zero] at h4
    exact squeeze_zero' (Eventually.of_forall fun k ↦ integral_nonneg fun ω ↦ sq_nonneg _)
      hbound h4
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hlim ?_ fun k ↦
    ((hE k).aestronglyMeasurable.aemeasurable).div_const _
  exact tendstoInMeasure_of_integral_sq hDm hlimD

/-- The Anscombe bound is `O(log log T)`: `anscBound P T ≤ C (⌊log₂(⌊log₂ T⌋ + 1)⌋ + 1)`. -/
theorem anscBound_le_log {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) (T : ℕ) :
    anscBound P T ≤ (11 + 4 * (Nat.log 2 (anscConst P) : ℝ)) / (P 0 1 + P 1 0) *
      ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hA : 1 ≤ anscConst P := by rw [anscConst]; omega
  have hmul : Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) ≤
      Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    refine Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by positivity) ?_)
    have h1 := Nat.lt_pow_succ_log_self one_lt_two (anscConst P)
    have h2 := Nat.lt_pow_succ_log_self one_lt_two (Nat.log 2 T + 1)
    rw [Nat.succ_eq_add_one] at h1 h2 ⊢
    rw [show Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 + 1 =
      (Nat.log 2 (anscConst P) + 1) + (Nat.log 2 (Nat.log 2 T + 1) + 1) by ring, pow_add]
    exact Nat.mul_lt_mul'' h1 h2
  have hmul' : (Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by exact_mod_cast hmul
  rw [anscBound, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
  have h0 := (Nat.log 2 (anscConst P)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  nlinarith

/-- `anscBound(T_k)² / log₂ T_k → 0` along `T_k → ∞`. -/
theorem tendsto_anscBound_sq_div {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) {T : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) :
    Tendsto (fun k ↦ anscBound P (T k) ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0) := by
  set C := (11 + 4 * (Nat.log 2 (anscConst P) : ℝ)) / (P 0 1 + P 1 0) with hC
  have hC0 : 0 ≤ C := by positivity
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hx : Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlim := (tendsto_natLog_pow_six_div.comp hx).const_mul (2 * C ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hlim
  have hev : ∀ᶠ k in atTop, 2 ≤ Nat.log 2 (T k) + 1 := hx.eventually_ge_atTop 2
  filter_upwards [hev] with k hk
  have hb0 : 0 ≤ anscBound P (T k) := by
    rw [anscBound]
    positivity
  have hb := anscBound_le_log hq (T k)
  set y := (Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1 with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [(Nat.log 2 (Nat.log 2 (T k) + 1)).cast_nonneg (α := ℝ)]
  have hlog : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast (show 1 ≤ Nat.log 2 (T k) by omega)
  have hx2 : ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ 2 * Nat.log 2 (T k) := by push_cast; linarith
  have hy6 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have hb2 : anscBound P (T k) ^ 2 ≤ C ^ 2 * y ^ 6 := by
    have := pow_le_pow_left₀ hb0 hb 2
    rw [mul_pow] at this
    nlinarith
  simp only [Function.comp_apply]
  rw [div_le_iff₀ (by linarith), ← hy]
  have hpos : (0 : ℝ) < ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) := by positivity
  calc anscBound P (T k) ^ 2 ≤ C ^ 2 * y ^ 6 := hb2
    _ = 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) *
        (((Nat.log 2 (T k) + 1 : ℕ) : ℝ) / 2) := by field_simp
    _ ≤ 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) * Nat.log 2 (T k) := by
        gcongr
        linarith

/-- `n_i(T) < 2^{⌊log₂ T⌋ + 1}`. -/
theorem chainIdx_lt_two_pow {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P)
    (hq : 0 < P 0 1 + P 1 0) (T : ℕ) (i : Fin 2) : chainIdx P T i < 2 ^ (Nat.log 2 T + 1) :=
  lt_of_le_of_lt (chainIdx_le hP hq T i) (Nat.lt_pow_succ_log_self one_lt_two T)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- **The CLT for two-state scrambled-stack chains** (any path-coin model, in particular Owen's
scramble and the digital shift). Let `p₀₁, p₁₁ > 0` and `T_k → ∞` with
`Var(N₀(T_k) − T_k π₀) ≥ κ log₂ T_k` eventually. Then
`(N₀(T_k) − T_k π₀) / √Var(N₀(T_k) − T_k π₀) ⇒ N(0,1)`. -/
theorem IsPathCoinModel.tendstoInDistribution_occErr [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (F ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) atTop Z (fun _ ↦ μ) P' := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  set q := P 0 1 + P 1 0 with hqdef
  set K : ℕ → ℕ := fun k ↦ Nat.log 2 (T k) + 1 with hK
  have hTK : ∀ k i, chainIdx P (T k) i < 2 ^ K k := fun k i ↦ chainIdx_lt_two_pow hP hq (T k) i
  set X : ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k ↦
    coinSum (chainThresh P) (chainIdx P (T k)) (K k) with hX
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hKt : Tendsto K atTop atTop := tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlog1 : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (T k) := hlogT.eventually_ge_atTop 1
  have hb := tendsto_anscBound_sq_div hq hT
  -- `b² / Var E → 0`
  have hbE : Tendsto (fun k ↦ anscBound P (T k) ^ 2 /
      Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) atTop (𝓝 0) := by
    have h := hb.div_const κ
    rw [zero_div] at h
    refine squeeze_zero' (Eventually.of_forall fun k ↦ by
      have := variance_nonneg (fun ω ↦ occErr P x₀ (F ω) (T k)) μ
      positivity) ?_ h
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (0 : ℝ) < Nat.log 2 (T k) := by exact_mod_cast hl
    rw [div_div, mul_comm (Nat.log 2 (T k) : ℝ) κ]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk
  have hpos : ∀ᶠ k in atTop, 0 < Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    nlinarith
  refine tendstoInDistribution_of_abs_sub_le (b := fun k ↦ anscBound P (T k))
    (fun k ↦ hM.memLp_occErr hP hq x₀ (T k)) (fun k ↦ hM.memLp_mainTerm hP h01 h11 (hTK k))
    (fun k ↦ hM.integral_mainTerm hP h01 h11 (hTK k))
    (fun k ω ↦ abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) (T k)) hbE hpos ?_
  -- the main term is asymptotically normal
  have hvarX : ∀ᶠ k in atTop, q ^ 2 * κ / 8 * K k ≤ Var[X k; shiftMeasure 2] := by
    have hsmall : ∀ᶠ k in atTop, anscBound P (T k) ^ 2 /
        Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] ≤ 1 / 4 :=
      hbE.eventually (ge_mem_nhds (by norm_num))
    filter_upwards [hvar, hlog1, hsmall, hpos] with k hk hl hs hp
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    have hσ := hM.abs_sqrt_variance_occErr_sub_le hP h01 h11 x₀ (hTK k)
    set sE := √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] with hsE
    set sM := √Var[fun ω ↦ mainTerm P (F ω) (T k); μ] with hsM
    have hsE2 : sE ^ 2 = Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := Real.sq_sqrt hp.le
    have hb0 : 0 ≤ anscBound P (T k) := by rw [anscBound]; positivity
    have hbsE : anscBound P (T k) ≤ sE / 2 := by
      rw [div_le_iff₀ hp, ← hsE2] at hs
      have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
      by_contra hc
      push Not at hc
      nlinarith
    have hsMge : sE / 2 ≤ sM := by
      have := (abs_le.1 hσ).1
      linarith
    have hsE0 : 0 ≤ sE / 2 := by positivity
    have hVM : sE ^ 2 / 4 ≤ Var[fun ω ↦ mainTerm P (F ω) (T k); μ] := by
      have := pow_le_pow_left₀ hsE0 hsMge 2
      rw [hsM, Real.sq_sqrt (variance_nonneg _ _), div_pow] at this
      linarith
    have hVX := hM.variance_mainTerm hP h01 h11 (hTK k)
    rw [eq_div_iff (by positivity)] at hVX
    have hK2 : (K k : ℝ) ≤ 2 * Nat.log 2 (T k) := by
      change ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ _
      push_cast
      linarith
    change q ^ 2 * κ / 8 * K k ≤ Var[coinSum (chainThresh P) (chainIdx P (T k)) (K k);
      shiftMeasure 2]
    rw [← hVX]
    have hq2 : 0 < q ^ 2 := by positivity
    have h1 : κ * Nat.log 2 (T k) ≤ sE ^ 2 := by rw [hsE2]; exact hk
    calc q ^ 2 * κ / 8 * K k ≤ q ^ 2 * κ / 8 * (2 * Nat.log 2 (T k)) := by gcongr
      _ = q ^ 2 * (κ * Nat.log 2 (T k) / 4) := by ring
      _ ≤ q ^ 2 * (sE ^ 2 / 4) := by gcongr
      _ ≤ q ^ 2 * Var[fun ω ↦ mainTerm P (F ω) (T k); μ] := by gcongr
      _ = Var[fun ω ↦ mainTerm P (F ω) (T k); μ] * (P 0 1 + P 1 0) ^ 2 := by rw [hqdef]; ring
  have hcoin := tendstoInDistribution_coinSum (chainThresh_mem hP h01 h11)
    (n := fun k ↦ chainIdx P (T k)) hKt (by positivity : 0 < q ^ 2 * κ / 8) hvarX hZ
  have htr := TendstoInDistribution.comp_measurePreserving hM.measurePreserving hcoin
  have e : (fun k ω ↦ mainTerm P (F ω) (T k) / √Var[fun ω ↦ mainTerm P (F ω) (T k); μ]) =
      fun k ω ↦ X k (Ψ ω) / √Var[X k; shiftMeasure 2] := by
    funext k ω
    have h1 := congrFun (hM.mainTerm_eq hP h01 h11 (hTK k)) ω
    rw [h1, hM.variance_mainTerm hP h01 h11 (hTK k), Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hq.le, div_div_div_cancel_right₀ hq.ne']
  rw [e]
  exact htr

/-- **The CLT for Owen-scrambled stacks** (post #3, code (iii), two states). -/
theorem tendstoInDistribution_occErr_owen (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ}
    (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (owenTable ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2]) atTop Z
      (fun _ ↦ owenMeasure 2) P' :=
  (isPathCoinModel_owen P).tendstoInDistribution_occErr hP h01 h11 x₀ hT hκ hvar hZ

/-- **The CLT for digitally shifted stacks** (post #3, code (ii), two states). -/
theorem tendstoInDistribution_occErr_shift (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ}
    (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (shiftFlips ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2]) atTop Z
      (fun _ ↦ shiftMeasure 2) P' :=
  (isPathCoinModel_shift P).tendstoInDistribution_occErr hP h01 h11 x₀ hT hκ hvar hZ

/-- `T_k → ∞` for the example times. -/
theorem tendsto_exampleTime : Tendsto exampleTime atTop atTop := by
  refine tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
  have h : k ≤ patternN k := by
    rw [patternN]
    calc k = ∑ _a ∈ range k, 1 := by simp
      _ ≤ ∑ a ∈ range k, 16 ^ a := sum_le_sum fun a _ ↦ Nat.one_le_pow _ _ (by norm_num)
  change k ≤ 2 * patternN k
  omega

/-- The variance hypothesis holds along the example times. -/
theorem IsPathCoinModel.eventually_variance_example [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2) :
    ∀ᶠ k in atTop, (1 / 60 : ℝ) * Nat.log 2 (exampleTime k) ≤
      Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
  filter_upwards [hM.eventually_variance_occErr_example_ge x₀, eventually_ge_atTop 1] with k hk hk1
  have hT : Nat.log 2 (exampleTime k) ≤ 4 * k := by
    have h1 : exampleTime k < 2 ^ (4 * k + 1) := by
      rw [exampleTime, pow_succ]
      have := patternN_lt k
      omega
    rcases Nat.eq_zero_or_pos (exampleTime k) with h0 | hpos
    · rw [h0, Nat.log_zero_right]
      omega
    · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' h1)
  have hT' : (Nat.log 2 (exampleTime k) : ℝ) ≤ 4 * k := by exact_mod_cast hT
  linarith

/-- **The CLT on the concrete sequence** (non-vacuity): for `p₁₁ = p₂₂ = 2/3` and
`T_k = 2 Σ_{a<k} 16^a`, the normalised occupation error of Owen-scrambled (and of digitally
shifted) stacks is asymptotically `N(0,1)`. -/
theorem occErr_example_tendstoInDistribution [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ]) atTop Z
      (fun _ ↦ μ) P' :=
  hM.tendstoInDistribution_occErr isStochastic_exampleChain (by rw [exampleChain_01]; norm_num)
    (by rw [exampleChain_11]; norm_num) x₀ tendsto_exampleTime (by norm_num)
    (hM.eventually_variance_example x₀) hZ

/-- The concrete CLT for Owen's scramble. -/
theorem occErr_example_tendstoInDistribution_owen (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (owenTable ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (owenTable ω) (exampleTime k); owenMeasure 2]) atTop
      Z (fun _ ↦ owenMeasure 2) P' :=
  occErr_example_tendstoInDistribution (isPathCoinModel_owen exampleChain) x₀ hZ

/-- The concrete CLT for the digital shift. -/
theorem occErr_example_tendstoInDistribution_shift (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (shiftFlips ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (shiftFlips ω) (exampleTime k); shiftMeasure 2]) atTop
      Z (fun _ ↦ shiftMeasure 2) P' :=
  occErr_example_tendstoInDistribution (isPathCoinModel_shift exampleChain) x₀ hZ

/-- **Mean-square error** (every two-state chain, every path-coin model, every `T`):
`E[(N₀(T) − T π₀)²] ≤ 10 (⌊log₂ T⌋ + 1)/q² + 2 anscBound(T)²`. -/
theorem IsPathCoinModel.integral_sq_occErr_le [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) (T : ℕ) :
    ∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ ≤
      10 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 + 2 * anscBound P T ^ 2 := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have hTK : ∀ i, chainIdx P T i < 2 ^ (Nat.log 2 T + 1) := chainIdx_lt_two_pow hP hq T
  have hE := hM.memLp_occErr hP hq x₀ T
  have hMm := hM.memLp_mainTerm hP h01 h11 hTK
  have hpt : ∀ ω, occErr P x₀ (F ω) T ^ 2 ≤
      2 * mainTerm P (F ω) T ^ 2 + 2 * anscBound P T ^ 2 := by
    intro ω
    have h := abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) T
    have h2 : (occErr P x₀ (F ω) T - mainTerm P (F ω) T) ^ 2 ≤ anscBound P T ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [sq_nonneg (occErr P x₀ (F ω) T - 2 * mainTerm P (F ω) T)]
  have hvarM : ∫ ω, mainTerm P (F ω) T ^ 2 ∂μ ≤ 5 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 := by
    rw [← variance_of_integral_eq_zero hMm.aestronglyMeasurable.aemeasurable
      (hM.integral_mainTerm hP h01 h11 hTK), hM.variance_mainTerm hP h01 h11 hTK]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := variance_coinSum_le (chainThresh_mem hP h01 h11) (chainIdx P T) (Nat.log 2 T + 1)
    push_cast at this
    exact this
  calc ∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ
      ≤ ∫ ω, (2 * mainTerm P (F ω) T ^ 2 + 2 * anscBound P T ^ 2) ∂μ :=
        integral_mono hE.integrable_sq ((hMm.integrable_sq.const_mul 2).add (integrable_const _))
          hpt
    _ = 2 * ∫ ω, mainTerm P (F ω) T ^ 2 ∂μ + 2 * anscBound P T ^ 2 := by
        rw [integral_add (hMm.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 10 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 + 2 * anscBound P T ^ 2 := by
        have := hvarM
        rw [div_eq_mul_inv] at this ⊢
        nlinarith

/-- **RMSE of the occupation frequency is `O(√log T / T)`**: `E[(N₀(T)/T − π₀)²] = O(log T / T²)`
(against `1/T` for i.i.d. MC driving). -/
theorem IsPathCoinModel.isBigO_meanSq_occFreq [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) :
    (fun T : ℕ ↦ ∫ ω, (occErr P x₀ (F ω) T / T) ^ 2 ∂μ) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have hb := tendsto_anscBound_sq_div hq (T := id) tendsto_id
  have hev : ∀ᶠ T : ℕ in atTop, anscBound P T ^ 2 / Nat.log 2 T ≤ 1 :=
    hb.eventually (ge_mem_nhds one_pos)
  have hlog : ∀ᶠ T : ℕ in atTop, 1 ≤ Nat.log 2 T :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      tendsto_id).eventually_ge_atTop 1
  refine Asymptotics.IsBigO.of_bound (20 / (P 0 1 + P 1 0) ^ 2 + 2) ?_
  filter_upwards [hev, hlog, eventually_ge_atTop 1] with T h1 h2 h3
  have hT0 : (0 : ℝ) < T := by exact_mod_cast h3
  have hl : (1 : ℝ) ≤ Nat.log 2 T := by exact_mod_cast h2
  have hbT : anscBound P T ^ 2 ≤ Nat.log 2 T := by
    rw [div_le_one (by linarith)] at h1
    exact h1
  have hsq := hM.integral_sq_occErr_le hP h01 h11 x₀ T
  have e : ∫ ω, (occErr P x₀ (F ω) T / T) ^ 2 ∂μ = (∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ) / T ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (div_nonneg
    (integral_nonneg fun ω ↦ sq_nonneg _) (by positivity)), abs_of_nonneg (by positivity),
    mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have hq2 : 0 < (P 0 1 + P 1 0) ^ 2 := by positivity
  have h10 : 10 * ((Nat.log 2 T : ℝ) + 1) / (P 0 1 + P 1 0) ^ 2 ≤
      20 / (P 0 1 + P 1 0) ^ 2 * Nat.log 2 T := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq2]
    linarith
  nlinarith

/-! ### General functions of the state -/

/-- The error `E_T(g) = Σ_{t<T} g(x_t) − T π(g)` of the time average of `g`. -/
noncomputable def chainSumErr (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool)
    (g : Fin 2 → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, g (stackPath P x₀ (scrambledStack f) t) - T * (piZero P * g 0 + piOne P * g 1)

/-- For two states, `E_T(g) = (g 0 − g 1) (N₀(T) − T π₀)`. -/
theorem chainSumErr_eq {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (g : Fin 2 → ℝ) (T : ℕ) :
    chainSumErr P x₀ f g T = (g 0 - g 1) * occErr P x₀ f T := by
  classical
  set x := stackPath P x₀ (scrambledStack f) with hx
  have hfib : ∑ t ∈ range T, g (x t) = ∑ i, (occCount x i T : ℝ) * g i := by
    rw [← sum_fiberwise_of_maps_to (s := range T) (t := univ) (g := x) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_congr rfl fun t ht ↦ by rw [(mem_filter.1 ht).2], sum_const, nsmul_eq_mul]
    rfl
  have hsum : (occCount x 0 T : ℝ) + occCount x 1 T = T := by
    have := sum_occCount x T
    rw [Fin.sum_univ_two] at this
    exact_mod_cast this
  have h1 := piZero_add_piOne hq
  rw [chainSumErr, ← hx, hfib, Fin.sum_univ_two, occErr, ← hx]
  have e1 : piOne P = 1 - piZero P := by linarith
  rw [e1, ← hsum]
  ring

/-- Convergence in distribution only depends on the law of the limit. -/
theorem TendstoInDistribution.of_map_eq {Ω'' Ω' : Type*} [MeasurableSpace Ω'']
    [MeasurableSpace Ω'] {ν : Measure Ω''} [IsProbabilityMeasure ν] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : ℕ → Ω'' → ℝ} {Z Z' : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z' (fun _ ↦ ν) P') (hZ : AEMeasurable Z P')
    (hmap : P'.map Z' = P'.map Z) : TendstoInDistribution X atTop Z (fun _ ↦ ν) P' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ
  tendsto := by
    have e : (⟨P'.map Z', inferInstance⟩ : ProbabilityMeasure ℝ) = ⟨P'.map Z, inferInstance⟩ :=
      Subtype.ext hmap
    rw [← e]
    exact h.tendsto

/-- **The CLT for any function of the state** (two states, any path-coin model). If
`g 0 ≠ g 1`, `T_k → ∞` and `Var(E_{T_k}(g)) ≥ κ log₂ T_k` eventually, then
`E_{T_k}(g) / √Var(E_{T_k}(g)) ⇒ N(0,1)`. -/
theorem IsPathCoinModel.tendstoInDistribution_chainSumErr [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {g : Fin 2 → ℝ} (hg : g 0 ≠ g 1) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
      √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) atTop Z (fun _ ↦ μ) P' := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  set c := g 0 - g 1 with hc
  have hc0 : c ≠ 0 := sub_ne_zero.2 hg
  have hc2 : 0 < c ^ 2 := by positivity
  have hE : ∀ k, (fun ω ↦ chainSumErr P x₀ (F ω) g (T k)) =
      fun ω ↦ c * occErr P x₀ (F ω) (T k) := fun k ↦ funext fun ω ↦ chainSumErr_eq hq x₀ _ g _
  have hV : ∀ k, Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ] =
      c ^ 2 * Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := fun k ↦ by
    rw [hE k, variance_const_mul]
  have hvar' : ∀ᶠ k in atTop,
      κ / c ^ 2 * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
    filter_upwards [hvar] with k hk
    rw [hV k] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hc2]
    linarith
  have hclt := hM.tendstoInDistribution_occErr hP h01 h11 x₀ hT (by positivity) hvar' hZ
  have hval : ∀ k ω, chainSumErr P x₀ (F ω) g (T k) /
      √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ] =
      c / |c| * (occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) := by
    intro k ω
    rw [hV k, chainSumErr_eq hq x₀ _ g _, Real.sqrt_mul hc2.le, Real.sqrt_sq_eq_abs,
      mul_div_mul_comm]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hcc : c / |c| = -1 := by rw [abs_of_neg hneg, div_neg, div_self hc0]
    have e : (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
        √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) = fun k ↦ (fun x : ℝ ↦ -1 * x) ∘
          fun ω ↦ occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
      funext k ω
      rw [hval k ω, hcc]
      rfl
    rw [e]
    have hneg' := hclt.continuous_comp (g := fun x : ℝ ↦ -1 * x) (by fun_prop)
    refine TendstoInDistribution.of_map_eq hneg' hZ.aemeasurable ?_
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable, hZ.map_eq]
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    simp only [neg_zero] at this
    rw [← this]
    congr 1
    funext x
    ring
  · have hcc : c / |c| = 1 := by rw [abs_of_pos hpos, div_self hc0]
    have e : (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
        √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) = fun k ω ↦
          occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
      funext k ω
      rw [hval k ω, hcc, one_mul]
    rw [e]
    exact hclt

end RQMCMarkov.ScrambledStacks
