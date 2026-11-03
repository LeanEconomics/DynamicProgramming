/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltPathBits
import ScrambledStacks.CltAnscombe
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Variance of the error of two-state scrambled-stack chains (post #3)

Post #3 finds that "normality cannot be rejected" for the per-state Sobol stacks in some runs.
The CLT of `CltStacks` normalises by the standard deviation and needs the variance to grow like
`log T`; this module shows that the hypothesis is not vacuous and that `log T` is the right
order.

By `CltPathBits`, for either randomisation the main term of the two-state chain is
`q · mainTerm = Σ_i Σ_{m : bit m of n_i} (1{LevelInd_{i,m}} − θ_{i,m})`, a function of i.i.d.
fair path coins (`coinSum`), where `θ_{i,m} = {2^m c_i}`. Each term is a centred Bernoulli
(`integral_levelVal`: `P(LevelInd) = {2^m c}`, as the digits beyond depth `m` form a uniform
number), terms of different states are uncorrelated, and two terms of the same state at levels
`m < m'` have covariance at most `2^{-(m'-m)}` (the tie cascade from `m` must survive to `m'`).

## Main results

* `covariance_eq_zero_of_approx`: two variables approximated in `L²` by independent ones are
  uncorrelated.
* `variance_sum_ge_of_cov`, `variance_sum_le_of_cov`: diagonal-dominance bounds.
* `integral_levelVal`, `variance_coinTerm`, `abs_covariance_coinTerm_le`,
  `covariance_coinTerm_eq_zero`: moments of the level terms on the coin space.
* `variance_coinSum_le`: `Var ≤ 5 K` for `K` levels (upper bound, every two-state chain).
* `variance_coinSum_pattern_ge` (**variance lower bound**): for `n₀ = n₁ = Σ_{i<k} 16^i` and
  thresholds whose fractional parts `{2^m c}` stay in `[1/3, 2/3]`, `Var ≥ 8k/45`.
* `IsPathCoinModel` (`isPathCoinModel_owen`, `isPathCoinModel_shift`): randomisations whose
  path coins are i.i.d. fair; `IsPathCoinModel.mainTerm_eq`, `.variance_mainTerm`,
  `.integral_mainTerm`: the main term is the coin sum of the path coins, centred, with variance
  `Var(coin sum)/q²` — the same for Owen and the digital shift.
* `IsPathCoinModel.abs_sqrt_variance_occErr_sub_le`: the standard deviations of the occupation
  error and of the main term differ by at most `anscBound = O(log log T)`.
* `exampleChain` (`p₁₁ = p₂₂ = 2/3`), `exampleTime k = 2 Σ_{i<k} 16^i`,
  `IsPathCoinModel.variance_mainTerm_example_ge` (`Var(main term) ≥ 2k/5`, every `k`) and
  `IsPathCoinModel.eventually_variance_occErr_example_ge`: for Owen-scrambled AND digitally
  shifted stacks, `Var(N₀(T_k) − T_k/2) ≥ k/12` eventually, while `log₂ T_k ≤ 4k + 1` — the
  variance does grow like `log T` (the REQUIRED non-vacuity of the CLT hypothesis).

Numerically (coin-space simulation, 2·10⁵ replications) the per-block variance at this pattern
is `≈ 0.209`, close to the diagonal value `2/9`; the bound `8k/45` uses `2/9 − 2/15`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Model-free covariance tools -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Uncorrelated by approximation.** If `X` and `Y` are `L²`-limits (in variance) of
independent pairs `(X_L, Y_L)`, then `cov[X, Y] = 0`. -/
theorem covariance_eq_zero_of_approx [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {Xa Ya : ℕ → Ω → ℝ} (hXa : ∀ L, MemLp (Xa L) 2 μ)
    (hYa : ∀ L, MemLp (Ya L) 2 μ) (hind : ∀ L, IndepFun (Xa L) (Ya L) μ)
    (hXe : Tendsto (fun L ↦ Var[X - Xa L; μ]) atTop (𝓝 0))
    (hYe : Tendsto (fun L ↦ Var[Y - Ya L; μ]) atTop (𝓝 0)) : cov[X, Y; μ] = 0 := by
  have hbound : ∀ L, |cov[X, Y; μ]| ≤ √Var[X - Xa L; μ] * √Var[Y; μ] +
      (√Var[X; μ] + √Var[X - Xa L; μ]) * √Var[Y - Ya L; μ] := by
    intro L
    have e : cov[X, Y; μ] = cov[X - Xa L, Y; μ] + cov[Xa L, Y - Ya L; μ] := by
      rw [covariance_sub_left hX (hXa L) hY, covariance_sub_right (hXa L) hY (hYa L),
        (hind L).covariance_eq_zero (hXa L) (hYa L)]
      ring
    have h1 := abs_covariance_le_sqrt (hX.sub (hXa L)) hY
    have h2 := abs_covariance_le_sqrt (hXa L) (hY.sub (hYa L))
    have h3 : √Var[Xa L; μ] ≤ √Var[X; μ] + √Var[X - Xa L; μ] := by
      have := abs_sqrt_variance_sub_le (μ := μ) hX (hXa L)
      have e' : (fun ω ↦ X ω - Xa L ω) = X - Xa L := rfl
      rw [e'] at this
      linarith [le_abs_self (√Var[Xa L; μ] - √Var[X; μ])]
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add h1 (h2.trans ?_))
    exact mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  have hlim : Tendsto (fun L ↦ √Var[X - Xa L; μ] * √Var[Y; μ] +
      (√Var[X; μ] + √Var[X - Xa L; μ]) * √Var[Y - Ya L; μ]) atTop (𝓝 0) := by
    have hs1 := (Real.continuous_sqrt.tendsto 0).comp hXe
    have hs2 := (Real.continuous_sqrt.tendsto 0).comp hYe
    rw [Real.sqrt_zero] at hs1 hs2
    have := (hs1.mul_const (√Var[Y; μ])).add
      (((tendsto_const_nhds (x := √Var[X; μ])).add hs1).mul hs2)
    rw [zero_mul, add_zero, mul_zero, add_zero] at this
    exact this
  have h0 : |cov[X, Y; μ]| ≤ 0 := ge_of_tendsto' hlim hbound
  exact abs_nonpos_iff.1 h0

/-- **Covariance with a small perturbation.** If `Z` takes values in an interval of length one,
then `|cov[R, Z]| ≤ E|R|`. -/
theorem abs_covariance_le_integral_abs [IsProbabilityMeasure μ] {R Z : Ω → ℝ}
    (hR : MemLp R 2 μ) (hZm : Measurable Z) {a : ℝ} (hZ : ∀ ω, Z ω ∈ Set.Icc a (a + 1)) :
    |cov[R, Z; μ]| ≤ ∫ ω, |R ω| ∂μ := by
  have hZi : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable (|a| + 1)
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_le]
      have := hZ ω
      constructor <;> linarith [abs_nonneg a, neg_abs_le a, le_abs_self a, this.1, this.2])
  have hRi : Integrable R μ := hR.integrable one_le_two
  have hEZ : μ[Z] ∈ Set.Icc a (a + 1) := by
    constructor
    · have := integral_mono (integrable_const a) hZi fun ω ↦ (hZ ω).1
      rwa [integral_const, probReal_univ, one_smul] at this
    · have := integral_mono hZi (integrable_const (a + 1)) fun ω ↦ (hZ ω).2
      rwa [integral_const, probReal_univ, one_smul] at this
  have hdev : ∀ ω, |Z ω - μ[Z]| ≤ 1 := fun ω ↦ by
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hZ ω
    obtain ⟨h3, h4⟩ := hEZ
    constructor <;> linarith
  have hint : Integrable (fun ω ↦ R ω * (Z ω - μ[Z])) μ := by
    refine Integrable.mono' hRi.abs ((hRi.aestronglyMeasurable).mul
      (hZm.sub measurable_const).aestronglyMeasurable) (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hdev ω)
  have e : cov[R, Z; μ] = ∫ ω, R ω * (Z ω - μ[Z]) ∂μ := by
    rw [covariance]
    have h1 : (fun ω ↦ (R ω - μ[R]) * (Z ω - μ[Z])) =
        fun ω ↦ R ω * (Z ω - μ[Z]) - μ[R] * (Z ω - μ[Z]) := funext fun ω ↦ by ring
    have hc : Integrable (fun ω ↦ μ[R] * (Z ω - μ[Z])) μ :=
      (hZi.sub (integrable_const (μ[Z]))).const_mul (μ[R])
    rw [h1, integral_sub hint hc, integral_const_mul, integral_sub hZi (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero]
  rw [e]
  refine (abs_integral_le_integral_abs).trans (integral_mono hint.abs hRi.abs fun ω ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hdev ω)

/-- **Diagonal dominance, lower bound.** If each variance is at least `a` and, for each index,
the absolute covariances with the others sum to at most `β`, then
`Var (Σ_{p∈s} Z p) ≥ |s| (a − β)`. -/
theorem variance_sum_ge_of_cov [IsFiniteMeasure μ] {κ : Type*} [DecidableEq κ] (s : Finset κ)
    {Z : κ → Ω → ℝ} (hZ : ∀ p ∈ s, MemLp (Z p) 2 μ) {a β : ℝ}
    (hdiag : ∀ p ∈ s, a ≤ Var[Z p; μ])
    (hrow : ∀ p ∈ s, ∑ p' ∈ s.erase p, |cov[Z p, Z p'; μ]| ≤ β) :
    s.card * (a - β) ≤ Var[fun ω ↦ ∑ p ∈ s, Z p ω; μ] := by
  rw [variance_fun_sum' hZ]
  have hp : ∀ p ∈ s, a - β ≤ ∑ p' ∈ s, cov[Z p, Z p'; μ] := by
    intro p hp
    rw [← add_sum_erase s _ hp, covariance_self (hZ p hp).aemeasurable]
    have h1 := hdiag p hp
    have h2 : -β ≤ ∑ p' ∈ s.erase p, cov[Z p, Z p'; μ] := by
      have := (abs_sum_le_sum_abs (fun p' ↦ cov[Z p, Z p'; μ]) (s.erase p)).trans (hrow p hp)
      linarith [neg_abs_le (∑ p' ∈ s.erase p, cov[Z p, Z p'; μ])]
    linarith
  calc (s.card : ℝ) * (a - β) = ∑ _p ∈ s, (a - β) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum hp

/-- **Diagonal dominance, upper bound.** -/
theorem variance_sum_le_of_cov [IsFiniteMeasure μ] {κ : Type*} [DecidableEq κ] (s : Finset κ)
    {Z : κ → Ω → ℝ} (hZ : ∀ p ∈ s, MemLp (Z p) 2 μ) {A β : ℝ}
    (hdiag : ∀ p ∈ s, Var[Z p; μ] ≤ A)
    (hrow : ∀ p ∈ s, ∑ p' ∈ s.erase p, |cov[Z p, Z p'; μ]| ≤ β) :
    Var[fun ω ↦ ∑ p ∈ s, Z p ω; μ] ≤ s.card * (A + β) := by
  rw [variance_fun_sum' hZ]
  have hp : ∀ p ∈ s, ∑ p' ∈ s, cov[Z p, Z p'; μ] ≤ A + β := by
    intro p hp
    rw [← add_sum_erase s _ hp, covariance_self (hZ p hp).aemeasurable]
    have h1 := hdiag p hp
    have h2 : ∑ p' ∈ s.erase p, cov[Z p, Z p'; μ] ≤ β :=
      (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (hrow p hp))
    linarith
  calc ∑ p ∈ s, ∑ p' ∈ s, cov[Z p, Z p'; μ] ≤ ∑ _p ∈ s, (A + β) := sum_le_sum hp
    _ = s.card * (A + β) := by rw [sum_const, nsmul_eq_mul]

/-! ### Level terms on the coin space -/

/-- The coins of state `i`. -/
def stateCoins (w : Fin 2 × ℕ → Bool) (i : Fin 2) : ℕ → Bool := fun j ↦ w (i, j)

/-- The fractional part `{2^m c}`. -/
noncomputable def fracPow (c : ℝ) (m : ℕ) : ℝ := 2 ^ m * c - ⌊2 ^ m * c⌋₊

/-- The level-`m` term of a stack with threshold `c` at index `N` (zero unless bit `m` of `N`
is set). -/
noncomputable def coinTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if N.testBit m then levelTerm c N m e else 0

/-- The level-`m` term truncated at depth `L`. -/
noncomputable def coinTermTrunc (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if N.testBit m then levelValTrunc (threshDigit c) N m L e - fracPow c m else 0

/-- **The coin sum** of a two-state chain with thresholds `c i` at indices `n i`, over the
levels `m < K`. -/
noncomputable def coinSum (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (K : ℕ) (w : Fin 2 × ℕ → Bool) : ℝ :=
  ∑ m ∈ range K, ∑ i, coinTerm (c i) (n i) m (stateCoins w i)

theorem fracPow_mem_Ico {c : ℝ} (hc0 : 0 ≤ c) (m : ℕ) : fracPow c m ∈ Set.Ico (0 : ℝ) 1 := by
  rw [fracPow]
  have h1 : (⌊2 ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
  have h2 := Nat.lt_floor_add_one (2 ^ m * c)
  constructor <;> linarith

theorem levelVal_mem (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) :
    levelVal cb N m e = 0 ∨ levelVal cb N m e = 1 := by
  unfold levelVal
  split_ifs <;> simp

theorem levelValTrunc_mem (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) :
    levelValTrunc cb N m L e = 0 ∨ levelValTrunc cb N m L e = 1 := by
  unfold levelValTrunc
  split_ifs <;> simp

/-- The level term lies in `[-θ, 1 - θ]`, an interval of length one. -/
theorem coinTerm_mem {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    coinTerm c N m e ∈ Set.Icc (-(if N.testBit m then fracPow c m else 0))
      (-(if N.testBit m then fracPow c m else 0) + 1) := by
  have hf := fracPow_mem_Ico hc0 m
  unfold coinTerm levelTerm
  split_ifs
  · rcases levelVal_mem (threshDigit c) N m e with h | h <;>
      · rw [h]; constructor <;> simp only [fracPow] at hf ⊢ <;> linarith [hf.1, hf.2]
  · constructor <;> norm_num

/-- `|coinTerm| ≤ 1`. -/
theorem abs_coinTerm_le {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    |coinTerm c N m e| ≤ 1 := by
  have h := coinTerm_mem hc0 N m e
  have hf := fracPow_mem_Ico hc0 m
  rw [abs_le]
  split_ifs at h
  · constructor <;> linarith [h.1, h.2, hf.1, hf.2]
  · constructor <;> linarith [h.1, h.2]

/-- `|coinTermTrunc| ≤ 1`. -/
theorem abs_coinTermTrunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (e : ℕ → Bool) :
    |coinTermTrunc c N m L e| ≤ 1 := by
  have hf := fracPow_mem_Ico hc0 m
  unfold coinTermTrunc
  split_ifs
  · rw [abs_le]
    rcases levelValTrunc_mem (threshDigit c) N m L e with h | h <;> rw [h] <;>
      constructor <;> linarith [hf.1, hf.2]
  · simp

open Classical in
/-- The difference of the full and truncated level terms is at most the tie indicator. -/
theorem abs_coinTerm_sub_trunc_le (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) :
    |coinTerm c N m e - coinTermTrunc c N m L e| ≤
      (if LevelTie (threshDigit c) N m L e then 1 else 0) := by
  unfold coinTerm coinTermTrunc levelTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    have e1 : levelVal (threshDigit c) N m e - (2 ^ m * c - ⌊2 ^ m * c⌋₊) -
        (levelValTrunc (threshDigit c) N m L e - fracPow c m) =
        levelVal (threshDigit c) N m e - levelValTrunc (threshDigit c) N m L e := by
      rw [fracPow]
      ring
    rw [e1]
    by_cases ht : LevelTie (threshDigit c) N m L e
    · simp only [ht, ite_true]
      rcases levelVal_mem (threshDigit c) N m e with h | h <;>
        rcases levelValTrunc_mem (threshDigit c) N m L e with h' | h' <;> rw [h, h'] <;> norm_num
    · simp only [ht, ite_false]
      rw [(levelVal_eq_trunc_of_not_tie le_rfl ht).1, sub_self, abs_zero]
  · simp only [hb, Bool.false_eq_true, ite_false, sub_self, abs_zero]
    split_ifs <;> norm_num

/-- The truncated coin term of state `i` depends only on the coins `(i, j)`, `j ∈ [m, m+L)`. -/
theorem isLocal_coinTermTrunc (c : ℝ) (N m L : ℕ) (i : Fin 2) :
    IsLocal (fun w ↦ coinTermTrunc c N m L (stateCoins w i))
      ((({i} : Finset (Fin 2)) ×ˢ Finset.Ico m (m + L))) := by
  intro w w' h
  change coinTermTrunc c N m L (stateCoins w i) = coinTermTrunc c N m L (stateCoins w' i)
  unfold coinTermTrunc
  rw [levelValTrunc_congr (threshDigit c) N m L (e := stateCoins w i) (e' := stateCoins w' i)
    fun j hm hj ↦ h (i, j) (by simp [hm, hj])]

/-- The level indicator as a binary comparison of coins. -/
theorem levelInd_stateCoins_iff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (w : Fin 2 × ℕ → Bool) (i : Fin 2) :
    LevelInd (threshDigit c) N m (stateCoins w i) ↔
      binaryVal (fun j ↦ xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) ≤ fracPow c m :=
  levelInd_iff_binaryVal_le hc0 hc1 N m (stateCoins w i)

theorem measurableSet_levelInd {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    MeasurableSet {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} := by
  have e : {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} =
      (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (w ((fun j ↦ (i, j + m)) j))) ⁻¹'
          Set.Iic (fracPow c m) := by
    ext w
    exact levelInd_stateCoins_iff hc0 hc1 N m w i
  rw [e]
  exact (measurable_binaryVal.comp (measurable_xor_digits _ _)) measurableSet_Iic

theorem measurable_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    Measurable fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i) := by
  classical
  unfold coinTerm levelTerm levelVal
  split_ifs
  · exact (Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const
      measurable_const).sub measurable_const
  · exact measurable_const

/-- `P(LevelInd) = {2^m c}` under fair coins: the digits beyond depth `m` form a uniform
number. -/
theorem measureReal_levelInd {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    (shiftMeasure 2).real {w | LevelInd (threshDigit c) N m (stateCoins w i)} = fracPow c m := by
  have hg : Function.Injective fun j : ℕ ↦ ((i, j + m) : Fin 2 × ℕ) :=
    fun j j' h ↦ by simpa using congrArg Prod.snd h
  have hmap := map_binaryVal_xor_eq_uniformIco hg fun j ↦ (levelBase N m).testBit (j + m)
  have e : {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} =
      (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) ⁻¹' Set.Iic (fracPow c m) := by
    ext w
    exact levelInd_stateCoins_iff hc0 hc1 N m w i
  have hXm : Measurable (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
      xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) :=
    measurable_binaryVal.comp (measurable_xor_digits (fun j ↦ ((i, j + m) : Fin 2 × ℕ)) _)
  have hf := fracPow_mem_Ico hc0 m
  rw [e, measureReal_def, ← Measure.map_apply hXm measurableSet_Iic, hmap,
    Measure.restrict_apply measurableSet_Iic]
  have hI : Set.Iic (fracPow c m) ∩ Set.Ico 0 1 = Set.Icc 0 (fracPow c m) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, lt_of_le_of_lt h2 hf.2⟩
  rw [hI, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hf.1]

/-- The level indicator has mean `{2^m c}`. -/
theorem integral_levelVal {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    ∫ w, levelVal (threshDigit c) N m (stateCoins w i) ∂(shiftMeasure 2) = fracPow c m := by
  classical
  have e : (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) =
      Set.indicator {w | LevelInd (threshDigit c) N m (stateCoins w i)} 1 := by
    funext w
    unfold levelVal
    by_cases h : LevelInd (threshDigit c) N m (stateCoins w i)
    · simp only [h, ite_true, Set.indicator_of_mem (show w ∈ {w |
        LevelInd (threshDigit c) N m (stateCoins w i)} from h), Pi.one_apply]
    · simp only [h, ite_false, Set.indicator_of_notMem (show w ∉ {w |
        LevelInd (threshDigit c) N m (stateCoins w i)} from h)]
  rw [e, integral_indicator_one (measurableSet_levelInd hc0 hc1 N m i),
    measureReal_levelInd hc0 hc1 N m i]

/-- The tie event as a cylinder of `L` coins. -/
theorem setOf_levelTie_eq (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    {w : Fin 2 × ℕ → Bool | LevelTie cb N m L (stateCoins w i)} =
      {w | ∀ j < L, xor ((levelBase N m).testBit (m + j)) (w ((fun j ↦ (i, m + j)) j)) =
        cb (m + j)} := by
  ext w
  simp only [Set.mem_ofPred_eq, LevelTie, levelDigits, stateCoins]
  constructor
  · intro h j hj
    exact h (m + j) (by omega) (by omega)
  · intro h j hm hj
    have := h (j - m) (by omega)
    rwa [show m + (j - m) = j by omega] at this

theorem measurableSet_levelTie (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    MeasurableSet {w : Fin 2 × ℕ → Bool | LevelTie cb N m L (stateCoins w i)} := by
  rw [setOf_levelTie_eq]
  exact measurableSet_xor_cylinder _ _ _ L

/-- **The tie cascade survives `L` levels with probability `2^{-L}`.** -/
theorem measureReal_levelTie (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    (shiftMeasure 2).real {w | LevelTie cb N m L (stateCoins w i)} = (1 / 2) ^ L := by
  have hg : Function.Injective fun j : ℕ ↦ ((i, m + j) : Fin 2 × ℕ) :=
    fun j j' h ↦ by simpa using congrArg Prod.snd h
  rw [setOf_levelTie_eq, measureReal_def, infinitePi_xor_cylinder hg, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- Level terms of the coin space are in `L²`. -/
theorem memLp_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    MemLp (fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i)) 2 (shiftMeasure 2) :=
  MemLp.of_bound (measurable_coinTerm hc0 hc1 N m i).aestronglyMeasurable 1
    (Eventually.of_forall fun w ↦ by rw [Real.norm_eq_abs]; exact abs_coinTerm_le hc0 N m _)

theorem memLp_coinTermTrunc {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (i : Fin 2) :
    MemLp (fun w : Fin 2 × ℕ → Bool ↦ coinTermTrunc c N m L (stateCoins w i)) 2
      (shiftMeasure 2) :=
  MemLp.of_bound (isLocal_coinTermTrunc c N m L i).measurable.aestronglyMeasurable 1
    (Eventually.of_forall fun w ↦ by rw [Real.norm_eq_abs]; exact abs_coinTermTrunc_le hc0 N m L _)

/-- **Truncation error in `L²`**: `E[(Y − Y_L)²] ≤ 2^{-L}`. -/
theorem integral_sq_coinTerm_sub_trunc_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m L : ℕ)
    (i : Fin 2) :
    ∫ w, (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2
      ∂(shiftMeasure 2) ≤ (1 / 2) ^ L := by
  classical
  set S := {w : Fin 2 × ℕ → Bool | LevelTie (threshDigit c) N m L (stateCoins w i)} with hS
  have hSm : MeasurableSet S := measurableSet_levelTie _ N m L i
  have hpt : ∀ w, (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2
      ≤ S.indicator 1 w := by
    intro w
    have h1 := abs_coinTerm_sub_trunc_le c N m L (stateCoins w i)
    have h2 : |coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)| ≤ 1 :=
      h1.trans (by split_ifs <;> norm_num)
    have h3 : (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2 ≤
        |coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (coinTerm c N m (stateCoins w i) -
        coinTermTrunc c N m L (stateCoins w i))]
    refine h3.trans (h1.trans (le_of_eq ?_))
    by_cases ht : LevelTie (threshDigit c) N m L (stateCoins w i)
    · simp only [ht, ite_true, Set.indicator_of_mem (show w ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show w ∉ S from ht)]
  have hint : Integrable (fun w ↦ (coinTerm c N m (stateCoins w i) -
      coinTermTrunc c N m L (stateCoins w i)) ^ 2) (shiftMeasure 2) :=
    ((memLp_coinTerm hc0 hc1 N m i).sub (memLp_coinTermTrunc hc0 N m L i)).integrable_sq
  have hind : Integrable (S.indicator (1 : (Fin 2 × ℕ → Bool) → ℝ)) (shiftMeasure 2) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono hint hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie]

/-- The variance of `Y - Y_L` tends to zero. -/
theorem tendsto_variance_coinTerm_sub_trunc {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (i : Fin 2) :
    Tendsto (fun L ↦ Var[(fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i)) -
      (fun w ↦ coinTermTrunc c N m L (stateCoins w i)); shiftMeasure 2]) atTop (𝓝 0) := by
  refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine (variance_le_expectation_sq ((memLp_coinTerm hc0 hc1 N m i).sub
    (memLp_coinTermTrunc hc0 N m L i)).aestronglyMeasurable).trans ?_
  exact le_of_eq_of_le rfl (integral_sq_coinTerm_sub_trunc_le hc0 hc1 N m L i)

/-- **Variance of a level term**: `θ(1 − θ)` with `θ = {2^m c}` if bit `m` of `N` is set. -/
theorem variance_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    Var[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i); shiftMeasure 2] =
      if N.testBit m then fracPow c m * (1 - fracPow c m) else 0 := by
  classical
  unfold coinTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    unfold levelTerm
    have hm : Measurable fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i) :=
      Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const measurable_const
    rw [variance_sub_const hm.aestronglyMeasurable]
    have hL2 : MemLp (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) 2
        (shiftMeasure 2) :=
      MemLp.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun w ↦ by
        rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> simp)
    rw [variance_eq_sub hL2]
    have hsq : (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) ^ 2 =
        fun w ↦ levelVal (threshDigit c) N m (stateCoins w i) := by
      funext w
      simp only [Pi.pow_apply]
      rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> norm_num
    rw [hsq, integral_levelVal hc0 hc1 N m i]
    ring
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact variance_zero _

/-! ### Covariances of level terms -/

/-- **Different states are uncorrelated.** -/
theorem covariance_coinTerm_eq_zero {c c' : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hc0' : 0 ≤ c')
    (hc1' : c' < 1) (N N' m m' : ℕ) {i i' : Fin 2} (hii' : i ≠ i') :
    cov[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i),
      fun w ↦ coinTerm c' N' m' (stateCoins w i'); shiftMeasure 2] = 0 := by
  refine covariance_eq_zero_of_approx (memLp_coinTerm hc0 hc1 N m i)
    (memLp_coinTerm hc0' hc1' N' m' i') (fun L ↦ memLp_coinTermTrunc hc0 N m L i)
    (fun L ↦ memLp_coinTermTrunc hc0' N' m' L i') (fun L ↦ ?_)
    (tendsto_variance_coinTerm_sub_trunc hc0 hc1 N m i)
    (tendsto_variance_coinTerm_sub_trunc hc0' hc1' N' m' i')
  refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_coinTermTrunc c N m L i)
    (isLocal_coinTermTrunc c' N' m' L i') (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
  simp only [mem_product, mem_singleton] at hq hq'
  exact hii' (hq.1.symm.trans hq'.1)

/-- **Same state: covariance decays geometrically.** For `m < m'` the cascade from level `m`
must tie on `[m, m')` to reach level `m'`, so `|cov| ≤ 2^{-(m'-m)}`. -/
theorem abs_covariance_coinTerm_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N N' m m' : ℕ)
    (i : Fin 2) (hmm' : m < m') :
    |cov[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i),
      fun w ↦ coinTerm c N' m' (stateCoins w i); shiftMeasure 2]| ≤ (1 / 2) ^ (m' - m) := by
  classical
  set Y := fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i) with hY
  set Y' := fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N' m' (stateCoins w i) with hY'
  set Yh := fun w : Fin 2 × ℕ → Bool ↦ coinTermTrunc c N m (m' - m) (stateCoins w i) with hYh
  have hY2 := memLp_coinTerm hc0 hc1 N m i
  have hY'2 := memLp_coinTerm hc0 hc1 N' m' i
  have hYh2 := memLp_coinTermTrunc hc0 N m (m' - m) i
  -- the truncated part is uncorrelated with the higher level
  have h0 : cov[Yh, Y'; shiftMeasure 2] = 0 := by
    refine covariance_eq_zero_of_approx hYh2 hY'2 (Xa := fun _ ↦ Yh) (fun _ ↦ hYh2)
      (fun L ↦ memLp_coinTermTrunc hc0 N' m' L i) (fun L ↦ ?_) ?_
      (tendsto_variance_coinTerm_sub_trunc hc0 hc1 N' m' i)
    · refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_coinTermTrunc c N m (m' - m) i)
        (isLocal_coinTermTrunc c N' m' L i) (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
      simp only [mem_product, mem_singleton, Finset.mem_Ico] at hq hq'
      omega
    · simp only [sub_self, variance_zero, tendsto_const_nhds]
  -- the remainder
  have e : cov[Y, Y'; shiftMeasure 2] = cov[Y - Yh, Y'; shiftMeasure 2] := by
    rw [covariance_sub_left hY2 hYh2 hY'2, h0, sub_zero]
  rw [e]
  have hY'm : Measurable Y' := measurable_coinTerm hc0 hc1 N' m' i
  refine (abs_covariance_le_integral_abs (hY2.sub hYh2) hY'm
    (fun w ↦ coinTerm_mem hc0 N' m' (stateCoins w i))).trans ?_
  set S := {w : Fin 2 × ℕ → Bool | LevelTie (threshDigit c) N m (m' - m) (stateCoins w i)}
    with hS
  have hSm : MeasurableSet S := measurableSet_levelTie _ N m _ i
  have hpt : ∀ w, |(Y - Yh) w| ≤ S.indicator 1 w := by
    intro w
    have h1 := abs_coinTerm_sub_trunc_le c N m (m' - m) (stateCoins w i)
    refine h1.trans (le_of_eq ?_)
    by_cases ht : LevelTie (threshDigit c) N m (m' - m) (stateCoins w i)
    · simp only [ht, ite_true, Set.indicator_of_mem (show w ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show w ∉ S from ht)]
  have hind : Integrable (S.indicator (1 : (Fin 2 × ℕ → Bool) → ℝ)) (shiftMeasure 2) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono ((hY2.sub hYh2).integrable one_le_two).abs hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie]

/-- **Geometric row sums.** `Σ_{m' ≠ m, m' < K} r^{|m - m'|} ≤ 2 r/(1 - r)`. -/
theorem sum_erase_pow_dist_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m K : ℕ) :
    ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)) ≤ 2 * (r / (1 - r)) := by
  classical
  rw [← sum_filter_add_sum_filter_not ((range K).erase m) (fun m' ↦ m' < m)]
  have hA : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ m' < m), r ^ (m - m' + (m' - m)) ≤
      r / (1 - r) := by
    have e : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ m' < m), r ^ (m - m' + (m' - m)) =
        ∑ d ∈ (((range K).erase m).filter (fun m' ↦ m' < m)).image (fun m' ↦ m - m'), r ^ d := by
      rw [sum_image]
      · refine sum_congr rfl fun m' hm' ↦ ?_
        have := (mem_filter.1 hm').2
        rw [show m' - m = 0 by omega, add_zero]
      · intro a ha b hb h
        have := (mem_filter.1 ha).2
        have := (mem_filter.1 hb).2
        simp only at h
        omega
    rw [e]
    refine (sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 1 (m + 1)) ?_
      fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
    · intro d hd
      obtain ⟨m', hm', rfl⟩ := mem_image.1 hd
      have := (mem_filter.1 hm').2
      exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
    · have := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) hr0 hr1
      rwa [pow_one] at this
  have hB : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ ¬ m' < m), r ^ (m - m' + (m' - m)) ≤
      r / (1 - r) := by
    have e : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ ¬ m' < m), r ^ (m - m' + (m' - m)) =
        ∑ d ∈ (((range K).erase m).filter (fun m' ↦ ¬ m' < m)).image (fun m' ↦ m' - m),
          r ^ d := by
      rw [sum_image]
      · refine sum_congr rfl fun m' hm' ↦ ?_
        have := (mem_filter.1 hm').2
        rw [show m - m' = 0 by omega, zero_add]
      · intro a ha b hb h
        have h1 := (mem_filter.1 ha).2
        have h2 := (mem_filter.1 hb).2
        simp only at h
        omega
    rw [e]
    refine (sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 1 (K + 1)) ?_
      fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
    · intro d hd
      obtain ⟨m', hm', rfl⟩ := mem_image.1 hd
      have h1 := (mem_filter.1 hm').2
      have h2 := (mem_filter.1 hm').1
      rw [mem_erase, mem_range] at h2
      exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
    · have := geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) hr0 hr1
      rwa [pow_one] at this
  linarith

/-! ### Variance of the coin sum -/

/-- The level term at coordinate `p = (state, level)`. -/
noncomputable def coinZ (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (p : Fin 2 × ℕ) (w : Fin 2 × ℕ → Bool) :
    ℝ :=
  coinTerm (c p.1) (n p.1) p.2 (stateCoins w p.1)

theorem coinSum_eq_sum_coinZ (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (K : ℕ) (w : Fin 2 × ℕ → Bool) :
    coinSum c n K w = ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w := by
  rw [coinSum, sum_product, sum_comm]
  rfl

/-- The covariance bound between two coordinates. -/
noncomputable def covBound (r : ℝ) (p p' : Fin 2 × ℕ) : ℝ :=
  if p.1 = p'.1 ∧ p.2 ≠ p'.2 then r ^ (p.2 - p'.2 + (p'.2 - p.2)) else 0

theorem abs_covariance_coinZ_le {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    {p p' : Fin 2 × ℕ} (hpp' : p ≠ p') :
    |cov[coinZ c n p, coinZ c n p'; shiftMeasure 2]| ≤ covBound (1 / 2) p p' := by
  obtain ⟨i, m⟩ := p
  obtain ⟨i', m'⟩ := p'
  unfold covBound
  by_cases hi : i = i'
  · subst hi
    have hm : m ≠ m' := fun h ↦ hpp' (by rw [h])
    simp only [hm, ne_eq, not_false_eq_true, and_self, ite_true]
    rcases lt_or_gt_of_ne hm with h | h
    · have := abs_covariance_coinTerm_le (hc i).1 (hc i).2 (n i) (n i) m m' i h
      rw [show m - m' + (m' - m) = m' - m by omega]
      exact this
    · have := abs_covariance_coinTerm_le (hc i).1 (hc i).2 (n i) (n i) m' m i h
      rw [covariance_comm] at this
      rw [show m - m' + (m' - m) = m - m' by omega]
      exact this
  · simp only [hi, false_and, ite_false]
    rw [show coinZ c n (i, m) = fun w ↦ coinTerm (c i) (n i) m (stateCoins w i) from rfl,
      show coinZ c n (i', m') = fun w ↦ coinTerm (c i') (n i') m' (stateCoins w i') from rfl,
      covariance_coinTerm_eq_zero (hc i).1 (hc i).2 (hc i').1 (hc i').2 _ _ _ _ hi, abs_zero]

/-- Row sums of `covBound` over `Fin 2 × range K`. -/
theorem sum_erase_covBound_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) (p : Fin 2 × ℕ) :
    ∑ p' ∈ ((univ : Finset (Fin 2)) ×ˢ range K).erase p, covBound r p p' ≤ 2 * (r / (1 - r)) := by
  classical
  obtain ⟨i, m⟩ := p
  rw [sum_erase _ (by simp [covBound]), sum_product]
  have h : ∀ i' : Fin 2, ∑ m' ∈ range K, covBound r (i, m) (i', m') =
      if i = i' then ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)) else 0 := by
    intro i'
    by_cases hi : i = i'
    · subst hi
      simp only [covBound, true_and, ite_true]
      rw [← sum_filter, filter_ne]
    · simp [covBound, hi]
  simp only [h]
  rw [sum_ite_eq univ i (fun _ ↦ ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)))]
  simp only [mem_univ, ite_true]
  exact sum_erase_pow_dist_le hr0 hr1 m K

theorem memLp_coinZ {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    (p : Fin 2 × ℕ) : MemLp (coinZ c n p) 2 (shiftMeasure 2) :=
  memLp_coinTerm (hc p.1).1 (hc p.1).2 (n p.1) p.2 p.1

theorem memLp_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) (K : ℕ) :
    MemLp (coinSum c n K) 2 (shiftMeasure 2) := by
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e]
  exact memLp_finsetSum _ fun p _ ↦ memLp_coinZ hc n p

/-- **Variance upper bound** for every two-state chain: `Var(coin sum over K levels) ≤ 5K`. -/
theorem variance_coinSum_le {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    (K : ℕ) : Var[coinSum c n K; shiftMeasure 2] ≤ 5 * K := by
  classical
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e]
  have h := variance_sum_le_of_cov (μ := shiftMeasure 2) ((univ : Finset (Fin 2)) ×ˢ range K)
    (Z := coinZ c n) (fun p _ ↦ memLp_coinZ hc n p) (A := 1 / 4) (β := 2)
    (fun p _ ↦ ?_) (fun p _ ↦ ?_)
  · refine h.trans ?_
    rw [card_product, card_univ, Fintype.card_fin, card_range]
    push_cast
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  · rw [show coinZ c n p = fun w ↦ coinTerm (c p.1) (n p.1) p.2 (stateCoins w p.1) from rfl,
      variance_coinTerm (hc p.1).1 (hc p.1).2]
    split_ifs
    · nlinarith [sq_nonneg (fracPow (c p.1) p.2 - 1 / 2)]
    · norm_num
  · refine (sum_le_sum fun p' hp' ↦ abs_covariance_coinZ_le hc n (ne_of_mem_erase hp').symm).trans
      ?_
    have := sum_erase_covBound_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) K p
    refine this.trans (le_of_eq ?_)
    norm_num

/-! ### A concrete lower bound -/

/-- The index `N_k = Σ_{a<k} 16^a`, binary digits `0001` repeated `k` times. -/
def patternN (k : ℕ) : ℕ := ∑ a ∈ range k, 16 ^ a

theorem patternN_lt (k : ℕ) : patternN k < 2 ^ (4 * k) := by
  induction k with
  | zero => simp [patternN]
  | succ k ih =>
      rw [patternN, sum_range_succ, ← patternN, show 4 * (k + 1) = 4 * k + 4 by ring, pow_add,
        show (16 : ℕ) ^ k = 2 ^ (4 * k) by rw [pow_mul]; norm_num]
      have : 0 < 2 ^ (4 * k) := Nat.two_pow_pos _
      omega

/-- The bits of `N_k` are exactly the levels `4a`, `a < k`. -/
theorem testBit_patternN (k m : ℕ) :
    (patternN k).testBit m = true ↔ m % 4 = 0 ∧ m / 4 < k := by
  induction k generalizing m with
  | zero => simp [patternN]
  | succ k ih =>
      have e : patternN (k + 1) = 2 ^ (4 * k) * 1 + patternN k := by
        rw [patternN, sum_range_succ, ← patternN, show (16 : ℕ) ^ k = 2 ^ (4 * k) by
          rw [pow_mul]; norm_num]
        ring
      rw [e, Nat.testBit_two_pow_mul_add _ (patternN_lt k)]
      by_cases hm : m < 4 * k
      · simp only [hm, ite_true]
        rw [ih]
        omega
      · simp only [hm, ite_false, Nat.testBit_one_eq_true_iff_self_eq_zero]
        omega

/-- A fraction `M/3` with `3 ∤ M` has fractional part `1/3` or `2/3`. -/
theorem frac_div_three_mem {M : ℕ} (hM : ¬ 3 ∣ M) :
    (M : ℝ) / 3 - ⌊(M : ℝ) / 3⌋₊ ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h1 : ⌊(M : ℝ) / 3⌋₊ = M / 3 := by
    have := Nat.floor_div_eq_div (K := ℝ) M 3
    rwa [Nat.cast_ofNat] at this
  rw [h1]
  have h2 : (M : ℝ) = 3 * ((M / 3 : ℕ) : ℝ) + ((M % 3 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod M 3).symm
  have h3 : M % 3 = 1 ∨ M % 3 = 2 := by omega
  rw [h2]
  rcases h3 with h | h <;> rw [h] <;> constructor <;> norm_num <;> ring_nf <;> norm_num

theorem not_three_dvd_two_pow (k : ℕ) : ¬ 3 ∣ 2 ^ k := fun h ↦ by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- `{2^m · 2/3} ∈ {1/3, 2/3}`. -/
theorem fracPow_two_thirds_mem (m : ℕ) : fracPow (2 / 3) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h := frac_div_three_mem (not_three_dvd_two_pow (m + 1))
  have e : (2 : ℝ) ^ m * (2 / 3) = ((2 ^ (m + 1) : ℕ) : ℝ) / 3 := by
    push_cast
    ring
  rw [fracPow, e]
  exact h

/-- `{2^m · 1/3} ∈ {1/3, 2/3}`. -/
theorem fracPow_one_third_mem (m : ℕ) : fracPow (1 / 3) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h := frac_div_three_mem (not_three_dvd_two_pow m)
  have e : (2 : ℝ) ^ m * (1 / 3) = ((2 ^ m : ℕ) : ℝ) / 3 := by
    push_cast
    ring
  rw [fracPow, e]
  exact h

/-- The coin sum at `N_k` only has the levels `4a`, `a < k`. -/
theorem coinSum_patternN (c : Fin 2 → ℝ) (k : ℕ) (w : Fin 2 × ℕ → Bool) :
    coinSum c (fun _ ↦ patternN k) (4 * k) w =
      ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range k, coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2) w := by
  classical
  rw [sum_product, sum_comm, coinSum]
  have himg : (range k).image (fun a ↦ 4 * a) ⊆ range (4 * k) := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hm
    rw [mem_range] at ha ⊢
    omega
  rw [← sum_subset himg, sum_image (fun a _ b _ h ↦ by omega)]
  · rfl
  · intro m _ hm
    refine sum_eq_zero fun i _ ↦ ?_
    have hb : (patternN k).testBit m = false := by
      by_contra hc
      rw [Bool.not_eq_false, testBit_patternN] at hc
      exact hm (mem_image.2 ⟨m / 4, mem_range.2 hc.2, by omega⟩)
    simp [coinTerm, hb]

/-- **Variance lower bound on the coin space.** If all the fractional parts `{2^m c_i}` lie in
`[1/3, 2/3]`, then at `n₀ = n₁ = N_k = Σ_{a<k} 16^a` the coin sum has variance `≥ 8k/45`. -/
theorem variance_coinSum_pattern_ge {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1)
    (hfrac : ∀ i m, fracPow (c i) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)) (k : ℕ) :
    8 * k / 45 ≤ Var[coinSum c (fun _ ↦ patternN k) (4 * k); shiftMeasure 2] := by
  classical
  have e : coinSum c (fun _ ↦ patternN k) (4 * k) = fun w ↦
      ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range k, coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2) w :=
    funext (coinSum_patternN c k)
  rw [e]
  have h := variance_sum_ge_of_cov (μ := shiftMeasure 2) ((univ : Finset (Fin 2)) ×ˢ range k)
    (Z := fun p ↦ coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2))
    (fun p _ ↦ memLp_coinZ hc _ _) (a := 2 / 9) (β := 2 / 15) (fun p hp ↦ ?_) (fun p _ ↦ ?_)
  · refine le_of_eq_of_le ?_ h
    rw [card_product, card_univ, Fintype.card_fin, card_range]
    push_cast
    ring
  · have hb : (patternN k).testBit (4 * p.2) = true := by
      rw [testBit_patternN]
      simp only [mem_product, mem_univ, mem_range, true_and] at hp
      omega
    change 2 / 9 ≤ Var[fun w ↦ coinTerm (c p.1) (patternN k) (4 * p.2) (stateCoins w p.1);
      shiftMeasure 2]
    rw [variance_coinTerm (hc p.1).1 (hc p.1).2]
    simp only [hb, ↓reduceIte]
    have := hfrac p.1 (4 * p.2)
    nlinarith [this.1, this.2]
  · have hrow : ∀ p' ∈ ((univ : Finset (Fin 2)) ×ˢ range k).erase p,
        |cov[coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2),
          coinZ c (fun _ ↦ patternN k) (p'.1, 4 * p'.2); shiftMeasure 2]| ≤
          covBound (1 / 16) p p' := by
      intro p' hp'
      have hne : p' ≠ p := ne_of_mem_erase hp'
      have hne' : (p.1, 4 * p.2) ≠ (p'.1, 4 * p'.2) := fun h ↦ hne (by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext h1.symm (by omega))
      refine (abs_covariance_coinZ_le hc _ hne').trans (le_of_eq ?_)
      unfold covBound
      have hiff : (p.1 = p'.1 ∧ 4 * p.2 ≠ 4 * p'.2) ↔ (p.1 = p'.1 ∧ p.2 ≠ p'.2) :=
        and_congr_right fun _ ↦ by omega
      simp only [hiff]
      split_ifs
      · rw [show 4 * p.2 - 4 * p'.2 + (4 * p'.2 - 4 * p.2) = 4 * (p.2 - p'.2 + (p'.2 - p.2)) by
          omega, pow_mul]
        norm_num
      · rfl
    refine (sum_le_sum hrow).trans ?_
    have := sum_erase_covBound_le (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num) k p
    refine this.trans (le_of_eq ?_)
    norm_num

/-- The mean of a level term is zero. -/
theorem integral_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    ∫ w, coinTerm c N m (stateCoins w i) ∂(shiftMeasure 2) = 0 := by
  classical
  unfold coinTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    unfold levelTerm
    have hm : Measurable fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i) :=
      Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const measurable_const
    have hi : Integrable (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i))
        (shiftMeasure 2) :=
      Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun w ↦ by
        rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> simp)
    rw [integral_sub hi (integrable_const _), integral_levelVal hc0 hc1, integral_const,
      probReal_univ, one_smul, fracPow, sub_self]
  · simp only [hb, Bool.false_eq_true, ite_false, integral_zero]

/-- The coin sum has mean zero. -/
theorem integral_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) (K : ℕ) :
    ∫ w, coinSum c n K w ∂(shiftMeasure 2) = 0 := by
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e, integral_finsetSum _ fun p _ ↦ (memLp_coinZ hc n p).integrable one_le_two]
  exact sum_eq_zero fun p _ ↦ integral_coinTerm (hc p.1).1 (hc p.1).2 _ _ _

/-! ### Connection with the chain -/

/-- The thresholds `c_i = p_{i0}` of a two-state chain. -/
def chainThresh (P : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦ P i 0

/-- The deterministic indices `n₀ = ⌊T π₀⌋`, `n₁ = ⌊T π₁⌋`. -/
noncomputable def chainIdx (P : Fin 2 → Fin 2 → ℝ) (T : ℕ) : Fin 2 → ℕ :=
  fun i ↦ if i = 0 then ⌊T * piZero P⌋₊ else ⌊T * piOne P⌋₊

/-- The threshold digits of the two rows. -/
noncomputable def chainDigits (P : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℕ → Bool :=
  fun i ↦ threshDigit (P i 0)

/-- **The level decomposition of both stacks** (every flip table). -/
theorem sum_segErr_eq_coinSum (f : Fin 2 → ℕ → ℕ → Bool) {c : Fin 2 → ℝ}
    (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) {K : ℕ} (hn : ∀ i, n i < 2 ^ K) :
    ∑ i, segErr (scrambledVdc (f i)) (c i) 0 (n i) =
      coinSum c n K (fun p ↦ pathCoin (f p.1) (threshDigit (c p.1)) p.2) := by
  rw [coinSum, sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [segErr_scrambledVdc_eq_sum_level (f i) (hc i).1 (hc i).2 (hn i), sum_filter]
  rfl

/-- `n_i ≤ T`. -/
theorem chainIdx_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0)
    (T : ℕ) (i : Fin 2) : chainIdx P T i ≤ T := by
  have hz : piZero P ≤ 1 := by
    rw [piZero, div_le_one hq]
    linarith [hP.nonneg 0 1]
  have ho : piOne P ≤ 1 := by
    rw [piOne, div_le_one hq]
    linarith [hP.nonneg 1 0]
  have h : ∀ x : ℝ, x ≤ 1 → ⌊(T : ℝ) * x⌋₊ ≤ T := fun x hx ↦ by
    refine Nat.floor_le_of_le ?_
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  unfold chainIdx
  split_ifs
  · exact h _ hz
  · exact h _ ho

/-- The thresholds `p_{00}, p_{10}` are in `[0,1)` when `p_{01}, p_{11} > 0`. -/
theorem chainThresh_mem {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (i : Fin 2) : 0 ≤ chainThresh P i ∧ chainThresh P i < 1 := by
  refine ⟨hP.nonneg i 0, ?_⟩
  have h := hP.sum_eq_one i
  rw [Fin.sum_univ_two] at h
  have hi1 : 0 < P i 1 := by
    fin_cases i
    exacts [h01, h11]
  change P i 0 < 1
  linarith

/-- **The main term as a coin sum** (every flip table). -/
theorem mul_mainTerm_eq_coinSum {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (f : Fin 2 → ℕ → ℕ → Bool) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    (P 0 1 + P 1 0) * mainTerm P f T = coinSum (chainThresh P) (chainIdx P T) K
      (fun p ↦ pathCoin (f p.1) (threshDigit (P p.1 0)) p.2) := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have h := sum_segErr_eq_coinSum f (chainThresh_mem hP h01 h11) (chainIdx P T) hT
  rw [show (fun p : Fin 2 × ℕ ↦ pathCoin (f p.1) (threshDigit (P p.1 0)) p.2) =
    (fun p ↦ pathCoin (f p.1) (threshDigit (chainThresh P p.1)) p.2) from rfl, ← h,
    Fin.sum_univ_two, mainTerm, mul_div_cancel₀ _ hq.ne']
  rfl

/-- For Owen's scramble the path-coin map is `owenPathCoins`. -/
theorem owenPathCoins_chainDigits (P : Fin 2 → Fin 2 → ℝ) (ω : Fin 2 × ℕ × ℕ → Bool) :
    owenPathCoins (chainDigits P) ω =
      fun p ↦ pathCoin (owenTable ω p.1) (threshDigit (P p.1 0)) p.2 := rfl

/-- For the digital shift the path coins are the flips. -/
theorem shiftPathCoins_eq (P : Fin 2 → Fin 2 → ℝ) (ω : Fin 2 × ℕ → Bool) :
    (fun p : Fin 2 × ℕ ↦ pathCoin (shiftFlips ω p.1) (threshDigit (P p.1 0)) p.2) = ω := rfl

/-! ### Randomisations through the path coins -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Fin 2 → Fin 2 → ℝ) (μ : Measure Ω)
  (F : Ω → Fin 2 → ℕ → ℕ → Bool) (Ψ : Ω → Fin 2 × ℕ → Bool) in
/-- A randomisation of the two flip tables (`F ω`) whose path coins along the two thresholds
are a measure-preserving map `Ψ` to the fair coins `shiftMeasure 2`. Owen's scramble and the
digital shift are both of this kind (`isPathCoinModel_owen`, `isPathCoinModel_shift`). -/
structure IsPathCoinModel : Prop where
  /-- The path coins are i.i.d. fair. -/
  measurePreserving : MeasurePreserving Ψ μ (shiftMeasure 2)
  /-- The path coins of the flip tables. -/
  pathCoin_eq : ∀ ω p, pathCoin (F ω p.1) (threshDigit (P p.1 0)) p.2 = Ψ ω p
  /-- The stack points are measurable. -/
  measurable_stack : ∀ i k, Measurable fun ω ↦ scrambledStack (F ω) i k

/-- **Owen's scramble is a path-coin model** (`map_owenPathCoins`). -/
theorem isPathCoinModel_owen (P : Fin 2 → Fin 2 → ℝ) :
    IsPathCoinModel P (owenMeasure 2) owenTable (owenPathCoins (chainDigits P)) where
  measurePreserving := ⟨measurable_owenPathCoins _, map_owenPathCoins _⟩
  pathCoin_eq _ _ := rfl
  measurable_stack := measurable_scrambledStack_owen

/-- **The digital shift is a path-coin model**: the path coins are the flips. -/
theorem isPathCoinModel_shift (P : Fin 2 → Fin 2 → ℝ) :
    IsPathCoinModel P (shiftMeasure 2) shiftFlips id where
  measurePreserving := MeasurePreserving.id _
  pathCoin_eq _ _ := rfl
  measurable_stack := measurable_scrambledStack_shift

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- In a path-coin model the main term is the coin sum of the path coins over `q`. -/
theorem IsPathCoinModel.mainTerm_eq (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    (fun ω ↦ mainTerm P (F ω) T) =
      fun ω ↦ coinSum (chainThresh P) (chainIdx P T) K (Ψ ω) / (P 0 1 + P 1 0) := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  funext ω
  rw [eq_div_iff hq.ne', mul_comm, mul_mainTerm_eq_coinSum hP h01 h11 (F ω) hT]
  congr 1
  funext p
  exact hM.pathCoin_eq ω p

/-- Variance of the main term in a path-coin model. -/
theorem IsPathCoinModel.variance_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    Var[fun ω ↦ mainTerm P (F ω) T; μ] =
      Var[coinSum (chainThresh P) (chainIdx P T) K; shiftMeasure 2] / (P 0 1 + P 1 0) ^ 2 := by
  rw [hM.mainTerm_eq hP h01 h11 hT]
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, hM.measurePreserving.variance_fun_comp
    (memLp_coinSum (chainThresh_mem hP h01 h11) _ K).aestronglyMeasurable.aemeasurable, inv_pow]

/-- The main term has mean zero in a path-coin model. -/
theorem IsPathCoinModel.integral_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    ∫ ω, mainTerm P (F ω) T ∂μ = 0 := by
  have h := congrFun (hM.mainTerm_eq hP h01 h11 hT)
  simp_rw [h]
  rw [integral_div, ← integral_map hM.measurePreserving.aemeasurable, hM.measurePreserving.map_eq,
    integral_coinSum (chainThresh_mem hP h01 h11), zero_div]
  rw [hM.measurePreserving.map_eq]
  exact (memLp_coinSum (chainThresh_mem hP h01 h11) _ K).aestronglyMeasurable

/-- The main term is in `L²` in a path-coin model. -/
theorem IsPathCoinModel.memLp_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    MemLp (fun ω ↦ mainTerm P (F ω) T) 2 μ := by
  rw [hM.mainTerm_eq hP h01 h11 hT]
  simp_rw [div_eq_mul_inv]
  exact ((memLp_coinSum (chainThresh_mem hP h01 h11) _ K).comp_measurePreserving
    hM.measurePreserving).mul_const _

/-- The occupation error is measurable and bounded, hence in `L²`. -/
theorem IsPathCoinModel.memLp_occErr (hM : IsPathCoinModel P μ F Ψ) [IsFiniteMeasure μ]
    (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2) (T : ℕ) :
    MemLp (fun ω ↦ occErr P x₀ (F ω) T) 2 μ := by
  have hm : Measurable fun ω ↦ occErr P x₀ (F ω) T := by
    unfold occErr
    exact ((measurable_from_nat (f := fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_occCount_of (V := fun ω ↦ scrambledStack (F ω)) hM.measurable_stack P x₀ 0
        T)).sub measurable_const
  refine MemLp.of_bound hm.aestronglyMeasurable (2 * T) (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, occErr]
  have h1 : (occCount (stackPath P x₀ (scrambledStack (F ω))) 0 T : ℝ) ≤ T := by
    exact_mod_cast occCount_le (stackPath P x₀ (scrambledStack (F ω))) 0 T
  have hz0 : 0 ≤ piZero P := div_nonneg (hP.nonneg 1 0) hq.le
  have hz1 : piZero P ≤ 1 := by
    rw [piZero, div_le_one hq]
    linarith [hP.nonneg 0 1]
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  rw [abs_le]
  constructor <;> nlinarith [(Nat.cast_nonneg (occCount (stackPath P x₀ (scrambledStack (F ω))) 0
    T) : (0 : ℝ) ≤ _)]

/-- **Variance of the occupation error vs the main term.** -/
theorem IsPathCoinModel.abs_sqrt_variance_occErr_sub_le (hM : IsPathCoinModel P μ F Ψ)
    [IsProbabilityMeasure μ] (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    |√Var[fun ω ↦ mainTerm P (F ω) T; μ] - √Var[fun ω ↦ occErr P x₀ (F ω) T; μ]| ≤
      anscBound P T := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  refine (abs_sqrt_variance_sub_le (hM.memLp_occErr hP hq x₀ T)
    (hM.memLp_mainTerm hP h01 h11 hT)).trans ?_
  have hb : 0 ≤ anscBound P T := (abs_nonneg _).trans
    (abs_occErr_sub_mainTerm_le hP hq x₀ (F (Classical.arbitrary Ω)) T)
  refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -anscBound P T) (b := anscBound P T)
    (Eventually.of_forall fun ω ↦ abs_le.1 (abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) T))
    ((hM.memLp_occErr hP hq x₀ T).sub
      (hM.memLp_mainTerm hP h01 h11 hT)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
  rw [show (anscBound P T - -anscBound P T) / 2 = anscBound P T by ring, Real.sqrt_sq hb]

/-! ### The example `p₁₁ = p₂₂ = 2/3` along `T_k = 2 Σ_{a<k} 16^a` -/

/-- The symmetric two-state chain with stay probability `2/3`. -/
noncomputable def exampleChain : Fin 2 → Fin 2 → ℝ := fun i j ↦ if i = j then 2 / 3 else 1 / 3

theorem isStochastic_exampleChain : IsStochastic exampleChain where
  nonneg i j := by unfold exampleChain; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [exampleChain] <;> norm_num

theorem exampleChain_01 : exampleChain 0 1 = 1 / 3 := by simp [exampleChain]
theorem exampleChain_10 : exampleChain 1 0 = 1 / 3 := by simp [exampleChain]
theorem exampleChain_11 : exampleChain 1 1 = 2 / 3 := by simp [exampleChain]
theorem exampleChain_00 : exampleChain 0 0 = 2 / 3 := by simp [exampleChain]

/-- The times `T_k = 2 Σ_{a<k} 16^a` (so that `T_k/2` has binary digits `0001` repeated). -/
def exampleTime (k : ℕ) : ℕ := 2 * patternN k

theorem chainIdx_exampleTime (k : ℕ) :
    chainIdx exampleChain (exampleTime k) = fun _ ↦ patternN k := by
  have hz : piZero exampleChain = 1 / 2 := by
    rw [piZero, exampleChain_01, exampleChain_10]
    norm_num
  have ho : piOne exampleChain = 1 / 2 := by
    rw [piOne, exampleChain_01, exampleChain_10]
    norm_num
  have h : ⌊((exampleTime k : ℕ) : ℝ) * (1 / 2)⌋₊ = patternN k := by
    rw [exampleTime]
    push_cast
    rw [show (2 : ℝ) * patternN k * (1 / 2) = patternN k by ring, Nat.floor_natCast]
  funext i
  unfold chainIdx
  split_ifs
  · rw [hz, h]
  · rw [ho, h]

theorem fracPow_exampleChain_mem (i : Fin 2) (m : ℕ) :
    fracPow (chainThresh exampleChain i) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  fin_cases i
  · change fracPow (exampleChain 0 0) m ∈ _
    rw [exampleChain_00]
    exact fracPow_two_thirds_mem m
  · change fracPow (exampleChain 1 0) m ∈ _
    rw [exampleChain_10]
    exact fracPow_one_third_mem m

/-- **The main term's variance grows linearly in `k`** for the example chain, for every
path-coin model (Owen's scramble and the digital shift): `Var ≥ 2k/5`. -/
theorem IsPathCoinModel.variance_mainTerm_example_ge (hM : IsPathCoinModel exampleChain μ F Ψ)
    (k : ℕ) : 2 * k / 5 ≤ Var[fun ω ↦ mainTerm exampleChain (F ω) (exampleTime k); μ] := by
  have hT : ∀ i, chainIdx exampleChain (exampleTime k) i < 2 ^ (4 * k) := fun i ↦ by
    rw [chainIdx_exampleTime]
    exact patternN_lt k
  rw [hM.variance_mainTerm isStochastic_exampleChain (by rw [exampleChain_01]; norm_num)
    (by rw [exampleChain_11]; norm_num) hT, chainIdx_exampleTime, exampleChain_01,
    exampleChain_10]
  have h := variance_coinSum_pattern_ge (chainThresh_mem isStochastic_exampleChain
    (by rw [exampleChain_01]; norm_num) (by rw [exampleChain_11]; norm_num))
    fracPow_exampleChain_mem k
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- The Anscombe bound along `T_k` is `O(log k)`. -/
theorem anscBound_exampleTime_le {k : ℕ} (hk : 1 ≤ k) :
    anscBound exampleChain (exampleTime k) ≤ 41 * ((Nat.log 2 k : ℝ) + 1) := by
  have hA : anscConst exampleChain ≤ 6 := by
    rw [anscConst, exampleChain_01, exampleChain_10]
    have : ⌈(3 : ℝ) / (1 / 3 + 1 / 3)⌉₊ ≤ 5 := Nat.ceil_le.2 (by norm_num)
    omega
  have hT : Nat.log 2 (exampleTime k) ≤ 4 * k := by
    have h1 : exampleTime k < 2 ^ (4 * k + 1) := by
      rw [exampleTime, pow_succ]
      have := patternN_lt k
      omega
    rcases Nat.eq_zero_or_pos (exampleTime k) with h0 | hpos
    · rw [h0, Nat.log_zero_right]
      omega
    · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' h1)
  have hprod : anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1) ≤ 2 ^ 5 * k := by
    have := Nat.mul_le_mul hA (Nat.add_le_add_right hT 1)
    omega
  have hlog : Nat.log 2 (anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1)) ≤
      Nat.log 2 k + 5 := by
    refine (Nat.log_mono_right hprod).trans (Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow
      (by positivity) ?_))
    have := Nat.lt_pow_succ_log_self one_lt_two k
    rw [Nat.succ_eq_add_one] at this ⊢
    rw [show Nat.log 2 k + 5 + 1 = 5 + (Nat.log 2 k + 1) by ring, pow_add]
    exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
  have hlog' : (Nat.log 2 (anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1)) : ℝ) ≤
      Nat.log 2 k + 5 := by exact_mod_cast hlog
  rw [anscBound, exampleChain_01, exampleChain_10, div_le_iff₀ (by norm_num)]
  have := (Nat.log 2 k).cast_nonneg (α := ℝ)
  nlinarith

/-- **The variance of the occupation error grows like `log T`** (example chain, every
path-coin model, so Owen-scrambled and digitally shifted stacks):
eventually `Var(N₀(T_k) − T_k/2) ≥ k/12`, and `log₂ T_k ≤ 4k + 1`. -/
theorem IsPathCoinModel.eventually_variance_occErr_example_ge [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2) :
    ∀ᶠ k : ℕ in atTop,
      (k : ℝ) / 12 ≤ Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
  have hlim := tendsto_natLog_pow_six_div
  have hev : ∀ᶠ k : ℕ in atTop, ((Nat.log 2 k : ℝ) + 1) ^ 6 / k ≤ 1 / (16 * 41 ^ 2) :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hT : ∀ i, chainIdx exampleChain (exampleTime k) i < 2 ^ (4 * k) := fun i ↦ by
    rw [chainIdx_exampleTime]
    exact patternN_lt k
  have hd := hM.abs_sqrt_variance_occErr_sub_le isStochastic_exampleChain
    (by rw [exampleChain_01]; norm_num) (by rw [exampleChain_11]; norm_num) x₀ hT
  have hmain := hM.variance_mainTerm_example_ge k
  have hb := anscBound_exampleTime_le hk1
  set b := anscBound exampleChain (exampleTime k) with hbdef
  set L := (Nat.log 2 k : ℝ) + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [(Nat.log 2 k).cast_nonneg (α := ℝ)]
  -- `b ≤ √k / 4`
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hd.trans le_rfl) |>.trans le_rfl
  have hL6 : L ^ 6 ≤ k / (16 * 41 ^ 2) := by
    rw [div_le_iff₀ hk0] at hk
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hL2 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hbk : b ^ 2 ≤ k / 16 := by
    have h1 : b ^ 2 ≤ (41 * L) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    nlinarith
  have hsk := Real.sq_sqrt hk0.le
  have hbs : b ≤ √k / 4 := by
    rw [← Real.sqrt_sq hb0, show √(k : ℝ) / 4 = √(k / 16) by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hbk
  -- `√Var(main) ≥ 3√k/5`
  have hsm : 3 * √k / 5 ≤ √Var[fun ω ↦ mainTerm exampleChain (F ω) (exampleTime k); μ] := by
    have : 3 * √(k : ℝ) / 5 = √(9 * k / 25) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 25), Real.sqrt_mul (by norm_num),
        show (9 : ℝ) = 3 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hso : 7 * √k / 20 ≤ √Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
    have := (abs_le.1 hd).2
    linarith
  have hs0 : 0 ≤ 7 * √(k : ℝ) / 20 := by positivity
  have := pow_le_pow_left₀ hs0 hso 2
  rw [Real.sq_sqrt (variance_nonneg _ _), div_pow, mul_pow, hsk] at this
  linarith

end RQMCMarkov.ScrambledStacks
