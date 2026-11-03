/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNCoins

/-!
# Variance of level sums of fair coins (for post #3, n states)

The CLT of `CltNCoins` normalises by the standard deviation and needs `Var ≥ κ log T`. This
module gives the matching upper bound `Var = O(K)` for every coin layout, and a lower-bound
criterion for level sums along sparse ("pattern") indices, which is used for the non-vacuity
examples (`CltNExample`) under both randomisations.

Two level terms at levels `m < m'` are almost uncorrelated: the level-`m` term, truncated at
depth `m' − m`, depends only on coordinates of levels `[m, m')`, which are independent of the
level-`m'` term; the truncation costs `2^{-(m'-m)}` in `L¹`. No independence between cut points of
the same row is needed (they share coordinates for the digital shift and, along common binary
prefixes, for Owen's scramble).

## Main results

* `abs_covariance_le_of_bound`: `|cov[R, Y]| ≤ 2B E|R|` for `|Y| ≤ B`.
* `abs_covariance_le_of_local`: if `X` is `L¹`-close to a function of coordinates `S`, and `Y` is
  an `L¹`-limit of functions of coordinates disjoint from `S`, then `|cov[X, Y]| ≤ 2B E|X − X_S|`.
* `abs_covariance_levelYN_le`, `variance_levelSumN_le` (**upper bound**):
  `Var(levelSumN) ≤ 5 (nW)² K` for `K` levels, every coin layout.
* `variance_ge_of_int` (**integer variance bound**): an integer-valued `X` has
  `Var X ≥ φ(1 − φ)`, `φ` the fractional part of `E X`.
* `variance_rowTerm_ge_of_int`: a row term with integer weights at a level of a set bit has
  variance at least `φ(1−φ)` for `φ = {Σ_j w_j {2^m c_{ij}}}`, under ANY coin layout.
* `patternR r k = Σ_{a<k} 2^{ra}`, `testBit_patternR`.
* `covariance_rowTerm_eq_zero` (different rows, disjoint coordinates), `abs_covariance_rowTerm_le`.
* `variance_levelSumN_pattern_ge` (**lower-bound criterion**): at indices `patternR r k` in every
  row, rows on disjoint coordinates, and row-term variances `≥ a₀`:
  `Var ≥ n k (a₀ − 4 W² ρ/(1 − ρ))`, `ρ = 2^{-r}`.
* Mean-square tools: `natLog_add_one_sq_le`, `integral_sq_le_of_close`,
  `integral_sq_levelSumN_le`, `isBigO_meanSq_div_of_le`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Covariance tools -/

/-- **Covariance with a bounded variable**: `|cov[R, Y]| ≤ 2B E|R|` when `|Y| ≤ B`. -/
theorem abs_covariance_le_of_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {R Y : Ω → ℝ} (hR : MemLp R 2 μ) (hYm : Measurable Y) {B : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ B) : |cov[R, Y; μ]| ≤ 2 * B * ∫ ω, |R ω| ∂μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hYb (Classical.arbitrary Ω))
  have hI0 : 0 ≤ ∫ ω, |R ω| ∂μ := integral_nonneg fun ω ↦ abs_nonneg _
  rcases hB0.lt_or_eq with hB | hB
  · have e : Y = fun ω ↦ (2 * B) * (Y ω / (2 * B)) := funext fun ω ↦ by field_simp
    rw [e, covariance_const_mul_right, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * B)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine abs_covariance_le_integral_abs hR (hYm.div_const _) (a := -1 / 2) fun ω ↦ ?_
    have h := abs_le.1 (hYb ω)
    constructor
    · rw [le_div_iff₀ (by positivity)]
      linarith
    · rw [div_le_iff₀ (by positivity)]
      linarith
  · have e : Y = fun ω ↦ 0 * Y ω := funext fun ω ↦ by
      have := hYb ω
      rw [← hB] at this
      rw [zero_mul]
      exact abs_nonpos_iff.1 this
    rw [e, covariance_const_mul_right, zero_mul, abs_zero]
    positivity

variable {ι : Type*} {n : ℕ}

/-- **Covariance across disjoint coordinates.** On fair coins, let `|X|, |Y|, |X_S|, |Y_L| ≤ B`,
`X_S` depend only on the coordinates in `S`, each `Y_L` only on coordinates disjoint from `S`,
and `E|Y − Y_L| → 0`. Then `|cov[X, Y]| ≤ 2B E|X − X_S|`. -/
theorem abs_covariance_le_of_local {X Y Xt : (ι → Bool) → ℝ} {Yt : ℕ → (ι → Bool) → ℝ}
    {S : Finset ι} {S' : ℕ → Finset ι} {B : ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    (hXb : ∀ ω, |X ω| ≤ B) (hYb : ∀ ω, |Y ω| ≤ B) (hXtb : ∀ ω, |Xt ω| ≤ B)
    (hYtb : ∀ L ω, |Yt L ω| ≤ B) (hXt : IsLocal Xt S) (hYt : ∀ L, IsLocal (Yt L) (S' L))
    (hdisj : ∀ L, Disjoint S (S' L))
    (hYe : Tendsto (fun L ↦ ∫ ω, |Y ω - Yt L ω| ∂(coinMeasure ι)) atTop (𝓝 0)) :
    |cov[X, Y; coinMeasure ι]| ≤ 2 * B * ∫ ω, |X ω - Xt ω| ∂(coinMeasure ι) := by
  have hX2 : MemLp X 2 (coinMeasure ι) := MemLp.of_bound hXm.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hXb ω)
  have hY2 : MemLp Y 2 (coinMeasure ι) := MemLp.of_bound hYm.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYb ω)
  have hXt2 : MemLp Xt 2 (coinMeasure ι) := MemLp.of_bound hXt.measurable.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hXtb ω)
  have hYt2 : ∀ L, MemLp (Yt L) 2 (coinMeasure ι) := fun L ↦
    MemLp.of_bound (hYt L).measurable.aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYtb L ω)
  have hYvar : Tendsto (fun L ↦ Var[Y - Yt L; coinMeasure ι]) atTop (𝓝 0) := by
    have hlim := hYe.const_mul (2 * B)
    rw [mul_zero] at hlim
    refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_) hlim
    refine (variance_le_expectation_sq (hY2.sub (hYt2 L)).aestronglyMeasurable).trans ?_
    have hd : ∀ ω, |(Y - Yt L) ω| ≤ 2 * B := fun ω ↦ by
      have := abs_sub (Y ω) (Yt L ω)
      simp only [Pi.sub_apply]
      linarith [hYb ω, hYtb L ω]
    have hm : Measurable (Y - Yt L) := hYm.sub (hYt L).measurable
    have hi1 : Integrable ((Y - Yt L) ^ 2) (coinMeasure ι) :=
      (hY2.sub (hYt2 L)).integrable_sq
    have hi2 : Integrable (fun ω ↦ 2 * B * |Y ω - Yt L ω|) (coinMeasure ι) :=
      (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable (2 * B)
        (Eventually.of_forall fun ω ↦ by
          change ‖|(Y - Yt L) ω|‖ ≤ 2 * B
          rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul _
    refine (integral_mono hi1 hi2 fun ω ↦ ?_).trans (le_of_eq (integral_const_mul _ _))
    have h1 := hd ω
    simp only [Pi.pow_apply, Pi.sub_apply] at h1 ⊢
    rw [← sq_abs]
    nlinarith [abs_nonneg (Y ω - Yt L ω)]
  have h0 : cov[Xt, Y; coinMeasure ι] = 0 := by
    refine covariance_eq_zero_of_approx hXt2 hY2 (Xa := fun _ ↦ Xt) (fun _ ↦ hXt2) hYt2
      (fun L ↦ IsLocal.indepFun (fun _ ↦ fairCoin) hXt (hYt L) (hdisj L)) ?_ hYvar
    simp only [sub_self, variance_zero, tendsto_const_nhds]
  have e : cov[X, Y; coinMeasure ι] = cov[X - Xt, Y; coinMeasure ι] := by
    rw [covariance_sub_left hX2 hXt2 hY2, h0, sub_zero]
  rw [e]
  exact abs_covariance_le_of_bound (hX2.sub hXt2) hYm hYb

/-! ### The upper bound -/

variable {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ}

/-- Coordinates of disjoint level ranges are disjoint. -/
theorem disjoint_levelCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {m m' L L' : ℕ} (h : m + L ≤ m') :
    Disjoint (levelCoords n γ m L) (levelCoords n γ m' L') := by
  refine Finset.disjoint_left.2 fun q hq hq' ↦ ?_
  have h1 := lev_mem_of_mem_levelCoords hlev hq
  have h2 := lev_mem_of_mem_levelCoords hlev hq'
  omega

/-- **Level terms decorrelate geometrically**: for `m < m'`,
`|cov[Y_m, Y'_{m'}]| ≤ 2 (nW)² 2^{-(m'-m)}` (any index vectors `N`, `N'`). -/
theorem abs_covariance_levelYN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N N' : Fin n → ℕ)
    {m m' : ℕ} (hmm' : m < m') :
    |cov[fun ω ↦ levelYN w cp N m (coinsOf γ ω), fun ω ↦ levelYN w cp N' m' (coinsOf γ ω);
      coinMeasure ι]| ≤ 2 * (n * absWeightSum n w) ^ 2 * (1 / 2) ^ (m' - m) := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  have h := abs_covariance_le_of_local (B := B)
    (Xt := fun ω ↦ levelYNTrunc w cp N m (m' - m) (coinsOf γ ω))
    (Yt := fun L ω ↦ levelYNTrunc w cp N' m' L (coinsOf γ ω))
    (S := levelCoords n γ m (m' - m)) (S' := fun L ↦ levelCoords n γ m' L)
    (measurable_levelYN_coins hcp N m γ) (measurable_levelYN_coins hcp N' m' γ)
    (fun ω ↦ abs_levelYN_le hcp N m _) (fun ω ↦ abs_levelYN_le hcp N' m' _)
    (fun ω ↦ abs_levelYNTrunc_le hcp N m _ _) (fun L ω ↦ abs_levelYNTrunc_le hcp N' m' L _)
    (isLocal_levelYNTrunc_coins N m (m' - m) γ) (fun L ↦ isLocal_levelYNTrunc_coins N' m' L γ)
    (fun L ↦ disjoint_levelCoords hlev (by omega)) ?_
  · refine h.trans ?_
    have := integral_abs_levelYN_sub_trunc_le (w := w) hcp N m (m' - m) hγ
    calc 2 * B * ∫ ω, |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m (m' - m)
          (coinsOf γ ω)| ∂(coinMeasure ι) ≤ 2 * B * (B * (1 / 2) ^ (m' - m)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * B ^ 2 * (1 / 2) ^ (m' - m) := by ring
  · have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul B
    rw [mul_zero] at hlim
    exact squeeze_zero (fun L ↦ integral_nonneg fun ω ↦ abs_nonneg _)
      (fun L ↦ integral_abs_levelYN_sub_trunc_le (w := w) hcp N' m' L hγ) hlim

/-- **Variance upper bound**: `Var(levelSumN) ≤ 5 (nW)² K` for every coin layout. -/
theorem variance_levelSumN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ) :
    Var[fun ω ↦ levelSumN w cp N K (coinsOf γ ω); coinMeasure ι] ≤
      K * (5 * (n * absWeightSum n w) ^ 2) := by
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  set Z : ℕ → (ι → Bool) → ℝ := fun m ω ↦ levelYN w cp N m (coinsOf γ ω) with hZ
  have hZ2 : ∀ m ∈ range K, MemLp (Z m) 2 (coinMeasure ι) := fun m _ ↦
    MemLp.of_bound (measurable_levelYN_coins hcp N m γ).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_levelYN_le hcp N m _)
  have e : (fun ω ↦ levelSumN w cp N K (coinsOf γ ω)) = fun ω ↦ ∑ m ∈ range K, Z m ω := rfl
  rw [e]
  have h := variance_sum_le_of_cov (μ := coinMeasure ι) (range K) hZ2 (A := B ^ 2)
    (β := 4 * B ^ 2) (fun m _ ↦ ?_) (fun m _ ↦ ?_)
  · rw [card_range] at h
    refine h.trans (le_of_eq ?_)
    ring
  · refine (variance_le_sq_of_bounded (a := -B) (b := B) (Eventually.of_forall fun ω ↦
      abs_le.1 (abs_levelYN_le hcp N m _))
      (measurable_levelYN_coins hcp N m γ).aemeasurable).trans (le_of_eq ?_)
    ring
  · have hcov : ∀ m' ∈ (range K).erase m, |cov[Z m, Z m'; coinMeasure ι]| ≤
        2 * B ^ 2 * (1 / 2) ^ (m - m' + (m' - m)) := by
      intro m' hm'
      have hne := ne_of_mem_erase hm'
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := abs_covariance_levelYN_le lev hlev hcp (w := w) N N hlt
        rw [covariance_comm, show m - m' + (m' - m) = m - m' by omega]
        exact this
      · have := abs_covariance_levelYN_le lev hlev hcp (w := w) N N hlt
        rw [show m - m' + (m' - m) = m' - m by omega]
        exact this
    have hgeo := sum_erase_pow_dist_le (r := 1 / 2) (by norm_num) (by norm_num) m K
    calc ∑ m' ∈ (range K).erase m, |cov[Z m, Z m'; coinMeasure ι]|
        ≤ ∑ m' ∈ (range K).erase m, 2 * B ^ 2 * (1 / 2) ^ (m - m' + (m' - m)) :=
          sum_le_sum hcov
      _ = 2 * B ^ 2 * ∑ m' ∈ (range K).erase m, (1 / 2 : ℝ) ^ (m - m' + (m' - m)) := by
          rw [mul_sum]
      _ ≤ 2 * B ^ 2 * (2 * ((1 / 2) / (1 - 1 / 2))) :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = 4 * B ^ 2 := by norm_num; ring

/-! ### The integer variance bound -/

/-- **Integer-valued variables are spread out**: if `X` takes integer values, then
`Var X ≥ φ (1 − φ)` with `φ = {E X}` (the minimum is attained by the two-point law on
`⌊E X⌋, ⌈E X⌉`). -/
theorem variance_ge_of_int {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (hint : ∀ ω, ∃ z : ℤ, X ω = z) :
    Int.fract (μ[X]) * (1 - Int.fract (μ[X])) ≤ Var[X; μ] := by
  set a : ℝ := (⌊μ[X]⌋ : ℝ) with ha
  have hpt : ∀ ω, 0 ≤ (X ω - a) * (X ω - a - 1) := by
    intro ω
    obtain ⟨z, hz⟩ := hint ω
    rw [hz, ha]
    rcases le_or_gt z ⌊μ[X]⌋ with h | h
    · have h1 : (z : ℝ) - ⌊μ[X]⌋ ≤ 0 := by
        have : (z : ℝ) ≤ ⌊μ[X]⌋ := by exact_mod_cast h
        linarith
      nlinarith
    · have h1 : (⌊μ[X]⌋ : ℝ) + 1 ≤ z := by exact_mod_cast h
      nlinarith
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := hX.integrable_sq
  have hexp : ∫ ω, (X ω - a) * (X ω - a - 1) ∂μ =
      ∫ ω, X ω ^ 2 ∂μ - (2 * a + 1) * μ[X] + a * (a + 1) := by
    have e : (fun ω ↦ (X ω - a) * (X ω - a - 1)) =
        fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω + a * (a + 1) := funext fun ω ↦ by ring
    have h1 : Integrable (fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω) μ := hX2.sub (hXi.const_mul _)
    rw [e, integral_add (f := fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω) (g := fun _ ↦ a * (a + 1)) h1
      (integrable_const _), integral_sub (f := fun ω ↦ X ω ^ 2)
      (g := fun ω ↦ (2 * a + 1) * X ω) hX2 (hXi.const_mul _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have hnn : 0 ≤ ∫ ω, (X ω - a) * (X ω - a - 1) ∂μ := integral_nonneg hpt
  have hvar : Var[X; μ] = ∫ ω, X ω ^ 2 ∂μ - μ[X] ^ 2 := variance_eq_sub hX
  have hfr : Int.fract (μ[X]) = μ[X] - a := by rw [ha, Int.fract]
  rw [hvar, hfr]
  rw [hexp] at hnn
  nlinarith

/-- The fractional parts of `w_j {2^m c_{ij}}` summed over the cut points `c_{ij} < 1`. -/
noncomputable def rowFrac (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (m : ℕ) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * (if cp i j < 1 then fracPow (cp i j) m else 0)

/-- **Row terms with integer weights are spread out** (any coin layout): at a level `m` where
bit `m` of `N_i` is set, `Var(rowTerm) ≥ φ (1 − φ)` with `φ = {Σ_j w_j {2^m c_{ij}}}`. -/
theorem variance_rowTerm_ge_of_int {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j)) (hcp : ∀ i j, 0 ≤ cp i j)
    (hw : ∀ j ∈ range (n - 1), ∃ z : ℤ, w j = z) (N : Fin n → ℕ) (m : ℕ) (i : Fin n)
    (hbit : (N i).testBit m = true) :
    Int.fract (rowFrac w cp m i) * (1 - Int.fract (rowFrac w cp m i)) ≤
      Var[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i; coinMeasure ι] := by
  classical
  set I : (ι → Bool) → ℝ := fun ω ↦ ∑ j ∈ range (n - 1),
    w j * (if cp i j < 1 then levelVal (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) else 0)
    with hI
  have hrow : (fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) = fun ω ↦ I ω - rowFrac w cp m i := by
    funext ω
    rw [rowTerm, rowFrac, hI, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    unfold cutTerm coinTerm levelTerm
    by_cases hc : cp i j < 1
    · simp only [hc, hbit, ite_true, fracPow]
      ring
    · simp only [hc, ite_false]
      ring
  have hIm : Measurable I := Finset.measurable_fun_sum _ fun j _ ↦ by
    by_cases hc : cp i j < 1
    · simp only [hc, ite_true]
      exact (measurable_levelVal_coins (hcp i j) hc (N i) m (γ i j)).const_mul _
    · simp only [hc, ite_false]
      exact measurable_const
  have hIb : ∀ ω, |I ω| ≤ absWeightSum n w := fun ω ↦ by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs
    · rcases levelVal_mem (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) with h | h <;>
        rw [h] <;> simp
    · simp
  have hI2 : MemLp I 2 (coinMeasure ι) := MemLp.of_bound hIm.aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hIb ω)
  have hIint : ∀ ω, ∃ z : ℤ, I ω = z := by
    intro ω
    have : ∀ j ∈ range (n - 1), ∃ z : ℤ, w j * (if cp i j < 1 then
        levelVal (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) else 0) = z := by
      intro j hj
      obtain ⟨z, hz⟩ := hw j hj
      by_cases hc : cp i j < 1
      · simp only [hc, ite_true]
        rcases levelVal_mem (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) with h | h
        · exact ⟨0, by rw [h]; simp⟩
        · exact ⟨z, by rw [h, hz, mul_one]⟩
      · exact ⟨0, by simp [hc]⟩
    choose! zf hzf using this
    exact ⟨∑ j ∈ range (n - 1), zf j, by
      rw [hI]; push_cast; exact sum_congr rfl fun j hj ↦ hzf j hj⟩
  have hmean : (coinMeasure ι)[I] = rowFrac w cp m i := by
    have h0 := integral_rowTerm_coins (w := w) hcp N m hγ i
    rw [hrow, integral_sub (hI2.integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul] at h0
    linarith
  rw [hrow, variance_sub_const hIm.aestronglyMeasurable, ← hmean]
  exact variance_ge_of_int hI2 hIint

/-! ### Sparse indices and the lower-bound criterion -/

/-- The index `Σ_{a<k} 2^{ra}`: bits exactly at the levels `ra`, `a < k`. -/
def patternR (r k : ℕ) : ℕ := ∑ a ∈ range k, 2 ^ (r * a)

/-- `patternR r k < 2^{rk}` for `r ≥ 1`. -/
theorem patternR_lt {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : patternR r k < 2 ^ (r * k) := by
  induction k with
  | zero => simp [patternR]
  | succ k ih =>
      rw [patternR, sum_range_succ, ← patternR, show r * (k + 1) = r * k + r by ring, pow_add]
      have h2 : 2 ≤ 2 ^ r := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
      have : 0 < 2 ^ (r * k) := Nat.two_pow_pos _
      nlinarith

/-- **The bits of `patternR r k`** are exactly the levels `ra`, `a < k`. -/
theorem testBit_patternR {r : ℕ} (hr : 1 ≤ r) (k m : ℕ) :
    (patternR r k).testBit m = true ↔ m % r = 0 ∧ m / r < k := by
  induction k generalizing m with
  | zero => simp [patternR]
  | succ k ih =>
      have e : patternR r (k + 1) = 2 ^ (r * k) * 1 + patternR r k := by
        rw [patternR, sum_range_succ, ← patternR]
        ring
      rw [e, Nat.testBit_two_pow_mul_add _ (patternR_lt hr k)]
      by_cases hm : m < r * k
      · simp only [hm, ite_true]
        rw [ih]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [mul_comm]; exact hm)
      · simp only [hm, ite_false, Nat.testBit_one_eq_true_iff_self_eq_zero]
        have hdiv : m / r ≥ k := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
        constructor
        · intro h
          have hm' : m = r * k := by omega
          subst hm'
          rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega)]
          exact ⟨rfl, Nat.lt_succ_self k⟩
        · rintro ⟨h1, h2⟩
          have hmk : m / r = k := by omega
          have := Nat.div_add_mod m r
          rw [hmk, h1] at this
          omega

/-- The row coordinates of levels `[m, m + L)`. -/
def rowCoords [DecidableEq ι] (n : ℕ) (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) (m L : ℕ) :
    Finset ι :=
  (range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)

/-- A coordinate of a row has a level in the range and comes from that row. -/
theorem mem_rowCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {i : Fin n} {m L : ℕ} {q : ι}
    (hq : q ∈ rowCoords n γ i m L) :
    (m ≤ lev q ∧ lev q < m + L) ∧ ∃ j d, q = γ i j d := by
  simp only [rowCoords, mem_biUnion, mem_image, Finset.mem_Ico] at hq
  obtain ⟨j, _, d, hd, rfl⟩ := hq
  rw [hlev]
  exact ⟨hd, j, d, rfl⟩

/-- The truncated row term is `L¹`-close: `E|row − row_L| → 0`, and its variance too. -/
theorem tendsto_variance_rowTerm_sub_trunc (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    Tendsto (fun L ↦ Var[(fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i); coinMeasure ι]) atTop (𝓝 0) := by
  set W := absWeightSum n w with hW
  have hW0 : 0 ≤ W := absWeightSum_nonneg n w
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (W * W)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_) hlim
  have hm : Measurable ((fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)) :=
    (measurable_rowTerm_coins hcp N m γ i).sub (measurable_rowTermTrunc_coins N m L γ i)
  refine (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_
  have hd : ∀ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
      ≤ W := fun ω ↦ abs_rowTerm_sub_trunc_le N m L _ i
  have hi1 : Integrable (((fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)) ^ 2) (coinMeasure ι) := by
    refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (W ^ 2)
      (Eventually.of_forall fun ω ↦ ?_)
    simp only [Pi.pow_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd ω) 2
  have hi2 : Integrable (fun ω ↦ W * |rowTerm w cp N m (coinsOf γ ω) i -
      rowTermTrunc w cp N m L (coinsOf γ ω) i|) (coinMeasure ι) :=
    (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable W
      (Eventually.of_forall fun ω ↦ by
        change ‖|rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|‖ ≤ W
        rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul W
  refine (integral_mono hi1 hi2 fun ω ↦ ?_).trans ?_
  · simp only [Pi.pow_apply, Pi.sub_apply]
    rw [← sq_abs]
    nlinarith [abs_nonneg (rowTerm w cp N m (coinsOf γ ω) i -
      rowTermTrunc w cp N m L (coinsOf γ ω) i), hd ω]
  · rw [integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_abs_rowTerm_sub_trunc_le hcp N m L hγ i) hW0

/-- **Different rows on disjoint coordinates are uncorrelated.** -/
theorem covariance_rowTerm_eq_zero {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j))
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hcp : ∀ i j, 0 ≤ cp i j)
    (N N' : Fin n → ℕ) (m m' : ℕ) {i i' : Fin n} (hii' : i ≠ i') :
    cov[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i, fun ω ↦ rowTerm w cp N' m' (coinsOf γ ω) i';
      coinMeasure ι] = 0 := by
  classical
  have hmem : ∀ N m i, MemLp (fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) 2 (coinMeasure ι) :=
    fun N m i ↦ MemLp.of_bound (measurable_rowTerm_coins hcp N m γ i).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N m _ i)
  have hmemt : ∀ N m L i, MemLp (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i) 2
      (coinMeasure ι) := fun N m L i ↦
    MemLp.of_bound (measurable_rowTermTrunc_coins N m L γ i).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_rowTermTrunc_le hcp N m L _ i)
  refine covariance_eq_zero_of_approx (hmem N m i) (hmem N' m' i') (fun L ↦ hmemt N m L i)
    (fun L ↦ hmemt N' m' L i') (fun L ↦ ?_) (tendsto_variance_rowTerm_sub_trunc hcp N m hγ i)
    (tendsto_variance_rowTerm_sub_trunc hcp N' m' hγ i')
  refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_rowTermTrunc_coins N m L γ i)
    (isLocal_rowTermTrunc_coins N' m' L γ i') (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
  simp only [mem_biUnion, mem_image] at hq hq'
  obtain ⟨j, _, d, _, rfl⟩ := hq
  obtain ⟨j', _, d', _, h⟩ := hq'
  exact hrows i i' j j' d d' hii' h.symm

/-- **Same row: covariance decays geometrically**, `|cov| ≤ 2 W² 2^{-(m'-m)}` for `m < m'`. -/
theorem abs_covariance_rowTerm_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N N' : Fin n → ℕ)
    (i : Fin n) {m m' : ℕ} (hmm' : m < m') :
    |cov[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i, fun ω ↦ rowTerm w cp N' m' (coinsOf γ ω) i;
      coinMeasure ι]| ≤ 2 * absWeightSum n w ^ 2 * (1 / 2) ^ (m' - m) := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set W := absWeightSum n w with hW
  have hW0 : 0 ≤ W := absWeightSum_nonneg n w
  have h := abs_covariance_le_of_local (B := W)
    (Xt := fun ω ↦ rowTermTrunc w cp N m (m' - m) (coinsOf γ ω) i)
    (Yt := fun L ω ↦ rowTermTrunc w cp N' m' L (coinsOf γ ω) i)
    (S := rowCoords n γ i m (m' - m)) (S' := fun L ↦ rowCoords n γ i m' L)
    (measurable_rowTerm_coins hcp N m γ i) (measurable_rowTerm_coins hcp N' m' γ i)
    (fun ω ↦ abs_rowTerm_le hcp N m _ i) (fun ω ↦ abs_rowTerm_le hcp N' m' _ i)
    (fun ω ↦ abs_rowTermTrunc_le hcp N m _ _ i) (fun L ω ↦ abs_rowTermTrunc_le hcp N' m' L _ i)
    (isLocal_rowTermTrunc_coins N m (m' - m) γ i) (fun L ↦ isLocal_rowTermTrunc_coins N' m' L γ i)
    (fun L ↦ Finset.disjoint_left.2 fun q hq hq' ↦ by
      have h1 := (mem_rowCoords hlev hq).1
      have h2 := (mem_rowCoords hlev hq').1
      omega) ?_
  · refine h.trans ?_
    have := integral_abs_rowTerm_sub_trunc_le (w := w) hcp N m (m' - m) hγ i
    calc 2 * W * ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i -
          rowTermTrunc w cp N m (m' - m) (coinsOf γ ω) i| ∂(coinMeasure ι)
        ≤ 2 * W * (W * (1 / 2) ^ (m' - m)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * W ^ 2 * (1 / 2) ^ (m' - m) := by ring
  · have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul W
    rw [mul_zero] at hlim
    exact squeeze_zero (fun L ↦ integral_nonneg fun ω ↦ abs_nonneg _)
      (fun L ↦ integral_abs_rowTerm_sub_trunc_le (w := w) hcp N' m' L hγ i) hlim

/-- At a level whose bit is not set the row term vanishes. -/
theorem rowTerm_eq_zero_of_testBit {N : Fin n → ℕ} {m : ℕ} {i : Fin n}
    (hbit : (N i).testBit m = false) (e : Fin n → ℕ → ℕ → Bool) : rowTerm w cp N m e i = 0 := by
  refine sum_eq_zero fun j _ ↦ ?_
  unfold cutTerm coinTerm
  simp [hbit]

/-- **Level sums along pattern indices** are sums of the row terms at the levels `ra`. -/
theorem levelSumN_pattern_eq {r k K : ℕ} (hr : 1 ≤ r) (hK : ∀ a < k, r * a < K) {N : Fin n → ℕ}
    (hN : ∀ i, N i = patternR r k) (e : Fin n → ℕ → ℕ → Bool) :
    levelSumN w cp N K e =
      ∑ p ∈ (univ : Finset (Fin n)) ×ˢ range k, rowTerm w cp N (r * p.2) e p.1 := by
  classical
  rw [levelSumN, sum_product, sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  have hsub : (range k).image (fun a ↦ r * a) ⊆ range K := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hm
    exact mem_range.2 (hK a (mem_range.1 ha))
  rw [← sum_subset hsub fun m _ hm ↦ ?_, sum_image fun a _ b _ h ↦ by
    simpa [Nat.mul_left_cancel_iff (show 0 < r by omega)] using h]
  refine rowTerm_eq_zero_of_testBit ?_ e
  rw [hN i]
  by_contra h
  have h' := (testBit_patternR hr k m).1 (by simpa using h)
  refine hm (mem_image.2 ⟨m / r, mem_range.2 h'.2, ?_⟩)
  have := Nat.div_add_mod m r
  rw [h'.1, add_zero] at this
  exact this

/-- **Lower-bound criterion.** Let every row have index `patternR r k`, the rows use disjoint
coordinates, and every row term at the levels `ra`, `a < k`, have variance `≥ a₀`. Then
`Var(levelSumN) ≥ n k (a₀ − 4 W² ρ/(1 − ρ))` with `ρ = 2^{-r}`. -/
theorem variance_levelSumN_pattern_ge (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d)
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hcp : ∀ i j, 0 ≤ cp i j)
    {r k K : ℕ} (hr : 1 ≤ r) (hK : ∀ a < k, r * a < K) {N : Fin n → ℕ}
    (hN : ∀ i, N i = patternR r k)
    {a₀ : ℝ} (hdiag : ∀ i, ∀ a < k,
      a₀ ≤ Var[fun ω ↦ rowTerm w cp N (r * a) (coinsOf γ ω) i; coinMeasure ι]) :
    n * k * (a₀ - 4 * absWeightSum n w ^ 2 * ((1 / 2) ^ r / (1 - (1 / 2) ^ r))) ≤
      Var[fun ω ↦ levelSumN w cp N K (coinsOf γ ω); coinMeasure ι] := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set W := absWeightSum n w with hW
  set ρ : ℝ := (1 / 2) ^ r with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  set s := (univ : Finset (Fin n)) ×ˢ range k with hs
  set Z : Fin n × ℕ → (ι → Bool) → ℝ := fun p ω ↦ rowTerm w cp N (r * p.2) (coinsOf γ ω) p.1
    with hZ
  have e : (fun ω ↦ levelSumN w cp N K (coinsOf γ ω)) = fun ω ↦ ∑ p ∈ s, Z p ω :=
    funext fun ω ↦ levelSumN_pattern_eq hr hK hN _
  rw [e]
  have hZ2 : ∀ p ∈ s, MemLp (Z p) 2 (coinMeasure ι) := fun p _ ↦
    MemLp.of_bound (measurable_rowTerm_coins hcp N _ γ p.1).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N _ _ _)
  have h := variance_sum_ge_of_cov s hZ2 (a := a₀)
    (β := 4 * W ^ 2 * (ρ / (1 - ρ))) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · rw [hs, card_product, card_univ, Fintype.card_fin, card_range] at h
    push_cast at h
    exact h
  · simp only [hs, mem_product, mem_univ, mem_range, true_and] at hp
    exact hdiag p.1 p.2 hp
  · -- the off-diagonal covariances
    obtain ⟨i, a⟩ := p
    have hcov : ∀ p' ∈ s.erase (i, a), |cov[Z (i, a), Z p'; coinMeasure ι]| ≤
        if p'.1 = i then 2 * W ^ 2 * ρ ^ (a - p'.2 + (p'.2 - a)) else 0 := by
      rintro ⟨i', b⟩ hp'
      have hne := ne_of_mem_erase hp'
      by_cases hii : i' = i
      · subst hii
        have hab : a ≠ b := fun h ↦ hne (by rw [h])
        simp only [ite_true]
        have hpow : ∀ d : ℕ, (1 / 2 : ℝ) ^ (r * d) = ρ ^ d := fun d ↦ by rw [hρ, pow_mul]
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · have hmm : r * a < r * b := Nat.mul_lt_mul_of_pos_left hlt (by omega)
          have := abs_covariance_rowTerm_le lev hlev hcp (w := w) N N i' hmm
          rw [show r * b - r * a = r * (b - a) by rw [Nat.mul_sub], hpow] at this
          rwa [show a - b + (b - a) = b - a by omega]
        · have hmm : r * b < r * a := Nat.mul_lt_mul_of_pos_left hlt (by omega)
          have := abs_covariance_rowTerm_le lev hlev hcp (w := w) N N i' hmm
          rw [show r * a - r * b = r * (a - b) by rw [Nat.mul_sub], hpow] at this
          rw [covariance_comm, show a - b + (b - a) = a - b by omega]
          exact this
      · simp only [hii, ite_false]
        rw [covariance_rowTerm_eq_zero hγ hrows hcp N N _ _ (Ne.symm hii), abs_zero]
    refine (sum_le_sum hcov).trans ?_
    rw [← sum_filter]
    have hfil : (s.erase (i, a)).filter (fun p' ↦ p'.1 = i) =
        ((range k).erase a).image (fun b ↦ (i, b)) := by
      ext ⟨i', b⟩
      simp only [hs, mem_filter, mem_erase, mem_product, mem_univ, mem_range, true_and,
        mem_image, ne_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hne, hb⟩, rfl⟩
        exact ⟨b, ⟨fun h ↦ hne ⟨rfl, h⟩, hb⟩, rfl, rfl⟩
      · rintro ⟨b', ⟨hb', hb⟩, rfl, rfl⟩
        exact ⟨⟨fun h ↦ hb' h.2, hb⟩, rfl⟩
    rw [hfil, sum_image fun b _ b' _ h ↦ by simpa using h]
    have hgeo := sum_erase_pow_dist_le hρ0 hρ1 a k
    calc ∑ b ∈ (range k).erase a, 2 * W ^ 2 * ρ ^ (a - b + (b - a))
        = 2 * W ^ 2 * ∑ b ∈ (range k).erase a, ρ ^ (a - b + (b - a)) := by rw [mul_sum]
      _ ≤ 2 * W ^ 2 * (2 * (ρ / (1 - ρ))) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = 4 * W ^ 2 * (ρ / (1 - ρ)) := by ring

/-! ### Mean-square tools -/

/-- `(⌊log₂ y⌋ + 1)² ≤ 4 y` for `y ≥ 1`. -/
theorem natLog_add_one_sq_le {y : ℕ} (hy : 1 ≤ y) : ((Nat.log 2 y : ℝ) + 1) ^ 2 ≤ 4 * y := by
  set ℓ := Nat.log 2 y with hℓ
  have hpow : 2 ^ ℓ ≤ y := Nat.pow_log_le_self 2 (by omega)
  have hnat : (ℓ + 1) ^ 2 ≤ 4 * 2 ^ ℓ := by
    clear hpow hℓ
    induction ℓ with
    | zero => norm_num
    | succ ℓ ih =>
        have h1 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
        have h2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
        rw [h2]
        nlinarith
  have h1 : ((ℓ + 1) ^ 2 : ℕ) ≤ 4 * y := hnat.trans (by omega)
  exact_mod_cast h1

/-- **Mean square of a perturbed centred term**: if `|E − M| ≤ b` and `E[M²] ≤ V`, then
`E[E²] ≤ 2V + 2b²`. -/
theorem integral_sq_le_of_close {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : Ω → ℝ} (hE : MemLp E 2 μ) (hM : MemLp M 2 μ) {b V : ℝ}
    (hclose : ∀ ω, |E ω - M ω| ≤ b) (hV : ∫ ω, M ω ^ 2 ∂μ ≤ V) :
    ∫ ω, E ω ^ 2 ∂μ ≤ 2 * V + 2 * b ^ 2 := by
  have hpt : ∀ ω, E ω ^ 2 ≤ 2 * M ω ^ 2 + 2 * b ^ 2 := by
    intro ω
    have h2 : (E ω - M ω) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hclose ω) 2
    nlinarith [sq_nonneg (E ω - 2 * M ω)]
  calc ∫ ω, E ω ^ 2 ∂μ ≤ ∫ ω, (2 * M ω ^ 2 + 2 * b ^ 2) ∂μ :=
        integral_mono hE.integrable_sq ((hM.integrable_sq.const_mul 2).add (integrable_const _))
          hpt
    _ = 2 * ∫ ω, M ω ^ 2 ∂μ + 2 * b ^ 2 := by
        rw [integral_add (hM.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 2 * V + 2 * b ^ 2 := by linarith

/-- **Mean square of a level sum**: `E[levelSumN²] = Var ≤ 5 (nW)² K`. -/
theorem integral_sq_levelSumN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ) :
    ∫ ω, levelSumN w cp N K (coinsOf γ ω) ^ 2 ∂(coinMeasure ι) ≤
      K * (5 * (n * absWeightSum n w) ^ 2) := by
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  have h0 := integral_levelSumN_coins (w := w) hcp N K hγ
  have hv := variance_levelSumN_le lev hlev hcp (w := w) N K
  rw [variance_of_integral_eq_zero
    (memLp_levelSumN_coins hcp N K γ).aestronglyMeasurable.aemeasurable h0] at hv
  exact hv

/-- **Rate of the mean square of the frequency**: if `E[E_T²] ≤ C (⌊log₂ T⌋ + 1)` for all `T`,
then `E[(E_T/T)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_div_of_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : ℕ → Ω → ℝ} {C : ℝ} (hC : ∀ T, ∫ ω, E T ω ^ 2 ∂μ ≤ C * ((Nat.log 2 T : ℝ) + 1)) :
    (fun T : ℕ ↦ ∫ ω, (E T ω / T) ^ 2 ∂μ) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by
  have hlog : ∀ᶠ T : ℕ in atTop, 1 ≤ Nat.log 2 T :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      tendsto_id).eventually_ge_atTop 1
  refine Asymptotics.IsBigO.of_bound (2 * |C|) ?_
  filter_upwards [hlog, eventually_ge_atTop 1] with T h2 h3
  have hT0 : (0 : ℝ) < T := by exact_mod_cast h3
  have hl : (1 : ℝ) ≤ Nat.log 2 T := by exact_mod_cast h2
  have e : ∫ ω, (E T ω / T) ^ 2 ∂μ = (∫ ω, E T ω ^ 2 ∂μ) / T ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
  have hnn : 0 ≤ ∫ ω, E T ω ^ 2 ∂μ := integral_nonneg fun ω ↦ sq_nonneg _
  have hq : (0 : ℝ) ≤ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (div_nonneg hnn (by positivity)),
    abs_of_nonneg hq, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have h1 := hC T
  have h4 : C * ((Nat.log 2 T : ℝ) + 1) ≤ |C| * ((Nat.log 2 T : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  nlinarith [abs_nonneg C]

end RQMCMarkov.ScrambledStacks
