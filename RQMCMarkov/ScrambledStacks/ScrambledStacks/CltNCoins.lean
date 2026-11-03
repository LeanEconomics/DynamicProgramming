/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNDecomp
import ScrambledStacks.CltStacks

/-!
# Level sums of fair coins: moments and the CLT (for post #3, n states)

The main term of an n-state scrambled-stack chain is a level sum `levelSumN` (`CltNDecomp`):
over levels `m`, rows `i` and cut points `j`, bounded level terms of coin sequences
`e i j = (ω (γ i j d))_d`. This module works on an arbitrary product of fair coins
`coinMeasure ι = ⊗_{q : ι} fairCoin`, with a **coin layout** `γ : Fin n → ℕ → ℕ → ι` whose
coordinate `γ i j d` has level `lev (γ i j d) = d`. Different cut points may share coordinates
(for the digital shift all cut points of a row share them, `CltNShift`; for Owen's scramble two
cut points share the nodes of their common binary prefix, `CltNOwen`): no independence between
cut points is assumed. The two randomisations are then treated by two instantiations.

## Main results

* `coinMeasure`, `coinsOf`, `absWeightSum`.
* One cut point (any injective `g : ℕ → ι`): `measureReal_levelInd_coins` (`{2^m c}`),
  `integral_cutTerm_coins` (`0`), `measureReal_levelTie_coins` (`2^{-L}`),
  `integral_abs_cutTerm_sub_trunc_le`, `isLocal_cutTermTrunc_coins`.
* Rows: `abs_rowTerm_le`, `integral_rowTerm_coins`, `integral_abs_rowTerm_sub_trunc_le`,
  `isLocal_rowTermTrunc_coins`; levels: `levelYN`, `abs_levelYN_le`, `integral_levelSumN_coins`.
* `tendstoInDistribution_levelSumN` (**CLT for level sums**): if `K_k → ∞` and
  `Var(levelSumN) ≥ κ K_k` eventually, the normalised level sums are asymptotically `N(0,1)`
  (`tendstoInDistribution_of_truncations`, with `B = nW`, `C = (nW)²`).
* `tendstoInDistribution_of_close_main` (**Slutsky assembly**): an error within `b_k` of a
  centred main term, `b_k² = o(log T_k)`, `Var ≥ κ log T_k`, inherits the main term's CLT.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {ι : Type*} {n : ℕ}

/-- The product of fair coins on the coordinates `ι`. -/
noncomputable abbrev coinMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι ↦ fairCoin

/-- The coin sequences `e i j = (ω (γ i j d))_d` of a coin layout `γ`. -/
def coinsOf (γ : Fin n → ℕ → ℕ → ι) (ω : ι → Bool) : Fin n → ℕ → ℕ → Bool :=
  fun i j d ↦ ω (γ i j d)

/-- The total absolute weight `Σ_{j<n−1} |w_j|`. -/
noncomputable def absWeightSum (n : ℕ) (w : ℕ → ℝ) : ℝ := ∑ j ∈ range (n - 1), |w j|

/-- `0 ≤ absWeightSum n w`. -/
theorem absWeightSum_nonneg (n : ℕ) (w : ℕ → ℝ) : 0 ≤ absWeightSum n w :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-! ### One cut point -/

/-- The level indicator of a coin sequence as a binary comparison. -/
theorem measurableSet_levelInd_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (g : ℕ → ι) :
    MeasurableSet {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} := by
  have e : {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} =
      (fun ω : ι → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (ω ((fun j ↦ g (j + m)) j))) ⁻¹'
          Set.Iic (fracPow c m) := by
    ext ω
    exact levelInd_iff_binaryVal_le hc0 hc1 N m _
  rw [e]
  exact (measurable_binaryVal.comp (measurable_xor_digits _ _)) measurableSet_Iic

/-- `P(LevelInd) = {2^m c}` for an injective coin sequence. -/
theorem measureReal_levelInd_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    (coinMeasure ι).real {ω | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} = fracPow c m := by
  have hg' : Function.Injective fun j : ℕ ↦ g (j + m) :=
    fun j j' h ↦ by simpa using hg h
  have hmap := map_binaryVal_xor_eq_uniformIco hg' fun j ↦ (levelBase N m).testBit (j + m)
  have e : {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} =
      (fun ω : ι → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (ω (g (j + m)))) ⁻¹' Set.Iic (fracPow c m) := by
    ext ω
    exact levelInd_iff_binaryVal_le hc0 hc1 N m _
  have hXm : Measurable (fun ω : ι → Bool ↦ binaryVal fun j ↦
      xor ((levelBase N m).testBit (j + m)) (ω (g (j + m)))) :=
    measurable_binaryVal.comp (measurable_xor_digits (fun j ↦ g (j + m)) _)
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

/-- The level indicator of a coin sequence is measurable. -/
theorem measurable_levelVal_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d)) := by
  classical
  unfold levelVal
  exact Measurable.ite (measurableSet_levelInd_coins hc0 hc1 N m g) measurable_const
    measurable_const

/-- The level indicator has mean `{2^m c}`. -/
theorem integral_levelVal_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, levelVal (threshDigit c) N m (fun d ↦ ω (g d)) ∂(coinMeasure ι) = fracPow c m := by
  classical
  have e : (fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d))) =
      Set.indicator {ω | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} 1 := by
    funext ω
    unfold levelVal
    by_cases h : LevelInd (threshDigit c) N m (fun d ↦ ω (g d))
    · simp only [h, ite_true, Set.indicator_of_mem (show ω ∈ {ω : ι → Bool |
        LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} from h), Pi.one_apply]
    · simp only [h, ite_false, Set.indicator_of_notMem (show ω ∉ {ω : ι → Bool |
        LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} from h)]
  rw [e, integral_indicator_one (measurableSet_levelInd_coins hc0 hc1 N m g),
    measureReal_levelInd_coins hc0 hc1 N m hg]

/-- The level term of a coin sequence is measurable. -/
theorem measurable_cutTerm_coins {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ cutTerm c N m (fun d ↦ ω (g d)) := by
  unfold cutTerm
  by_cases hc1 : c < 1
  · simp only [hc1, ite_true]
    unfold coinTerm levelTerm
    by_cases hb : N.testBit m = true
    · simp only [hb, ite_true]
      exact (measurable_levelVal_coins hc0 hc1 N m g).sub measurable_const
    · simp only [hb, Bool.false_eq_true, ite_false]
      exact measurable_const
  · simp only [hc1, ite_false]
    exact measurable_const

/-- `|cutTerm| ≤ 1`. -/
theorem abs_cutTerm_le {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    |cutTerm c N m e| ≤ 1 := by
  unfold cutTerm
  split_ifs
  · exact abs_coinTerm_le hc0 N m e
  · simp

/-- `|cutTermTrunc| ≤ 1`. -/
theorem abs_cutTermTrunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (e : ℕ → Bool) :
    |cutTermTrunc c N m L e| ≤ 1 := by
  unfold cutTermTrunc
  split_ifs
  · exact abs_coinTermTrunc_le hc0 N m L e
  · simp

open Classical in
/-- The truncation error of a level term is at most the tie indicator. -/
theorem abs_cutTerm_sub_trunc_le (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) :
    |cutTerm c N m e - cutTermTrunc c N m L e| ≤
      (if LevelTie (threshDigit c) N m L e then 1 else 0) := by
  unfold cutTerm cutTermTrunc
  by_cases hc : c < 1
  · simp only [hc, ite_true]
    exact abs_coinTerm_sub_trunc_le c N m L e
  · simp only [hc, ite_false, sub_self, abs_zero]
    split_ifs <;> norm_num

/-- The tie event of a coin sequence as a cylinder. -/
theorem setOf_levelTie_coins_eq (cb : ℕ → Bool) (N m L : ℕ) (g : ℕ → ι) :
    {ω : ι → Bool | LevelTie cb N m L (fun d ↦ ω (g d))} =
      {ω | ∀ j < L, xor ((levelBase N m).testBit (m + j)) (ω ((fun j ↦ g (m + j)) j)) =
        cb (m + j)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, LevelTie, levelDigits]
  constructor
  · intro h j hj
    exact h (m + j) (by omega) (by omega)
  · intro h j hm hj
    have := h (j - m) (by omega)
    rwa [show m + (j - m) = j by omega] at this

/-- The tie event is measurable. -/
theorem measurableSet_levelTie_coins (cb : ℕ → Bool) (N m L : ℕ) (g : ℕ → ι) :
    MeasurableSet {ω : ι → Bool | LevelTie cb N m L (fun d ↦ ω (g d))} := by
  rw [setOf_levelTie_coins_eq]
  exact measurableSet_xor_cylinder _ _ _ L

/-- **The tie cascade survives `L` levels with probability `2^{-L}`.** -/
theorem measureReal_levelTie_coins (cb : ℕ → Bool) (N m L : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    (coinMeasure ι).real {ω | LevelTie cb N m L (fun d ↦ ω (g d))} = (1 / 2) ^ L := by
  have hg' : Function.Injective fun j : ℕ ↦ g (m + j) :=
    fun j j' h ↦ by simpa using hg h
  rw [setOf_levelTie_coins_eq, measureReal_def, infinitePi_xor_cylinder hg', ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- The truncated level term depends only on the coins of depths `[m, m + L)`. -/
theorem isLocal_cutTermTrunc_coins [DecidableEq ι] (c : ℝ) (N m L : ℕ) (g : ℕ → ι) :
    IsLocal (fun ω : ι → Bool ↦ cutTermTrunc c N m L (fun d ↦ ω (g d)))
      ((Finset.Ico m (m + L)).image g) := by
  intro ω ω' h
  change cutTermTrunc c N m L (fun d ↦ ω (g d)) = cutTermTrunc c N m L (fun d ↦ ω' (g d))
  unfold cutTermTrunc coinTermTrunc
  rw [levelValTrunc_congr (threshDigit c) N m L (e := fun d ↦ ω (g d)) (e' := fun d ↦ ω' (g d))
    fun j hm hj ↦ h (g j) (mem_image_of_mem g (Finset.mem_Ico.2 ⟨hm, hj⟩))]

/-- The truncated level term is measurable. -/
theorem measurable_cutTermTrunc_coins (c : ℝ) (N m L : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ cutTermTrunc c N m L (fun d ↦ ω (g d)) := by
  classical
  exact (isLocal_cutTermTrunc_coins c N m L g).measurable

/-- **Truncation error in `L¹`**: `E|Y − Y_L| ≤ 2^{-L}`. -/
theorem integral_abs_cutTerm_sub_trunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))|
      ∂(coinMeasure ι) ≤ (1 / 2) ^ L := by
  classical
  set S := {ω : ι → Bool | LevelTie (threshDigit c) N m L (fun d ↦ ω (g d))} with hS
  have hSm : MeasurableSet S := measurableSet_levelTie_coins _ N m L g
  have hpt : ∀ ω, |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))| ≤
      S.indicator 1 ω := by
    intro ω
    refine (abs_cutTerm_sub_trunc_le c N m L _).trans (le_of_eq ?_)
    by_cases ht : LevelTie (threshDigit c) N m L (fun d ↦ ω (g d))
    · simp only [ht, ite_true, Set.indicator_of_mem (show ω ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show ω ∉ S from ht)]
  have hm : Measurable fun ω : ι → Bool ↦
      |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))| :=
    continuous_abs.measurable.comp
      ((measurable_cutTerm_coins hc0 N m g).sub (measurable_cutTermTrunc_coins c N m L g))
  have hint : Integrable (fun ω : ι → Bool ↦
      |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 2 (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_cutTerm_le hc0 N m (fun d ↦ ω (g d))
    have h2 := abs_cutTermTrunc_le hc0 N m L (fun d ↦ ω (g d))
    have := abs_sub (cutTerm c N m (fun d ↦ ω (g d))) (cutTermTrunc c N m L (fun d ↦ ω (g d)))
    linarith
  have hind : Integrable (S.indicator (1 : (ι → Bool) → ℝ)) (coinMeasure ι) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono hint hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie_coins _ N m L hg]

/-- **Level terms are centred.** -/
theorem integral_cutTerm_coins {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, cutTerm c N m (fun d ↦ ω (g d)) ∂(coinMeasure ι) = 0 := by
  unfold cutTerm
  by_cases hc1 : c < 1
  · simp only [hc1, ite_true]
    unfold coinTerm levelTerm
    by_cases hb : N.testBit m = true
    · simp only [hb, ite_true]
      have hi : Integrable (fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d)))
          (coinMeasure ι) := by
        refine Integrable.of_bound (measurable_levelVal_coins hc0 hc1 N m g).aestronglyMeasurable
          1 (Eventually.of_forall fun ω ↦ ?_)
        rcases levelVal_mem (threshDigit c) N m (fun d ↦ ω (g d)) with h | h <;> rw [h] <;> simp
      rw [integral_sub hi (integrable_const _), integral_levelVal_coins hc0 hc1 N m hg,
        integral_const, probReal_univ, one_smul, fracPow, sub_self]
    · simp only [hb, Bool.false_eq_true, ite_false, integral_zero]
  · simp only [hc1, ite_false, integral_zero]

/-! ### Rows and levels -/

variable {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ}

/-- `|rowTerm| ≤ W = Σ_j |w_j|`. -/
theorem abs_rowTerm_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : |rowTerm w cp N m e i| ≤ absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutTerm_le (hcp i j) _ m _)

/-- `|rowTermTrunc| ≤ W`. -/
theorem abs_rowTermTrunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) :
    |rowTermTrunc w cp N m L e i| ≤ absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutTermTrunc_le (hcp i j) _ m L _)

/-- `|rowTerm − rowTermTrunc| ≤ W`. -/
theorem abs_rowTerm_sub_trunc_le (N : Fin n → ℕ) (m L : ℕ) (e : Fin n → ℕ → ℕ → Bool)
    (i : Fin n) : |rowTerm w cp N m e i - rowTermTrunc w cp N m L e i| ≤ absWeightSum n w := by
  classical
  rw [rowTerm, rowTermTrunc, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [← mul_sub, abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ((abs_cutTerm_sub_trunc_le _ _ m L _).trans ?_)
  split_ifs <;> norm_num

/-- The row term of a coin layout is measurable. -/
theorem measurable_rowTerm_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) :
    Measurable fun ω : ι → Bool ↦ rowTerm w cp N m (coinsOf γ ω) i :=
  Finset.measurable_fun_sum _ fun j _ ↦
    (measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).const_mul (w j)

/-- The truncated row term depends only on coordinates `γ i j d`, `d ∈ [m, m + L)`. -/
theorem isLocal_rowTermTrunc_coins [DecidableEq ι] (N : Fin n → ℕ) (m L : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) :
    IsLocal (fun ω : ι → Bool ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)
      ((range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)) :=
  isLocal_sum _ fun j hj ↦ ((isLocal_cutTermTrunc_coins (cp i j) (N i) m L (γ i j)).comp
    (fun x ↦ w j * x)).mono
      (subset_biUnion_of_mem (fun j ↦ (Finset.Ico m (m + L)).image (γ i j)) hj)

/-- The truncated row term is measurable. -/
theorem measurable_rowTermTrunc_coins (N : Fin n → ℕ) (m L : ℕ) (γ : Fin n → ℕ → ℕ → ι)
    (i : Fin n) : Measurable fun ω : ι → Bool ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i := by
  classical
  exact (isLocal_rowTermTrunc_coins N m L γ i).measurable

/-- **Row truncation error in `L¹`**: `E|row − row_L| ≤ W 2^{-L}`. -/
theorem integral_abs_rowTerm_sub_trunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
      ∂(coinMeasure ι) ≤ absWeightSum n w * (1 / 2) ^ L := by
  have hint : ∀ j, Integrable (fun ω : ι → Bool ↦ |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
      cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)|) (coinMeasure ι) := by
    intro j
    refine Integrable.of_bound (continuous_abs.measurable.comp
      ((measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).sub
      (measurable_cutTermTrunc_coins (cp i j) (N i) m L (γ i j)))).aestronglyMeasurable 2
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_cutTerm_le (hcp i j) (N i) m (coinsOf γ ω i j)
    have h2 := abs_cutTermTrunc_le (hcp i j) (N i) m L (coinsOf γ ω i j)
    have := abs_sub (cutTerm (cp i j) (N i) m (coinsOf γ ω i j))
      (cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j))
    linarith
  have hpt : ∀ ω : ι → Bool,
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i| ≤
      ∑ j ∈ range (n - 1), |w j| * |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
        cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)| := by
    intro ω
    rw [rowTerm, rowTermTrunc, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ ↦ ?_))
    rw [← mul_sub, abs_mul]
  have hm : Measurable fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i| :=
    continuous_abs.measurable.comp
      ((measurable_rowTerm_coins hcp N m γ i).sub (measurable_rowTermTrunc_coins N m L γ i))
  have hi1 : Integrable (fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (absWeightSum n w)
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_rowTerm_sub_trunc_le N m L _ i
  have hi2 : Integrable (fun ω : ι → Bool ↦ ∑ j ∈ range (n - 1),
      |w j| * |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
        cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)|) (coinMeasure ι) :=
    integrable_finsetSum _ fun j _ ↦ (hint j).const_mul _
  refine (integral_mono hi1 hi2 hpt).trans ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint j).const_mul _, absWeightSum, sum_mul]
  refine sum_le_sum fun j _ ↦ ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_abs_cutTerm_sub_trunc_le (hcp i j) (N i) m L (hγ i j)) (abs_nonneg _)

/-- **Row terms are centred.** -/
theorem integral_rowTerm_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    ∫ ω, rowTerm w cp N m (coinsOf γ ω) i ∂(coinMeasure ι) = 0 := by
  have hint : ∀ j, Integrable (fun ω : ι → Bool ↦ w j * cutTerm (cp i j) (N i) m
      (coinsOf γ ω i j)) (coinMeasure ι) := fun j ↦
    (Integrable.of_bound (measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_cutTerm_le (hcp i j) _ m _)).const_mul _
  unfold rowTerm
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  refine sum_eq_zero fun j _ ↦ ?_
  rw [integral_const_mul]
  change w j * ∫ ω, cutTerm (cp i j) (N i) m (fun d ↦ ω (γ i j d)) ∂(coinMeasure ι) = 0
  rw [integral_cutTerm_coins (hcp i j) (N i) m (hγ i j), mul_zero]

/-- The level-`m` term `Σ_i rowTerm … m … i`. -/
noncomputable def levelYN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ i, rowTerm w cp N m e i

/-- The truncated level term. -/
noncomputable def levelYNTrunc (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ i, rowTermTrunc w cp N m L e i

/-- `levelSumN = Σ_{m<K} levelYN`. -/
theorem levelSumN_eq_sum_levelYN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) :
    levelSumN w cp N K e = ∑ m ∈ range K, levelYN w cp N m e := rfl

/-- `|levelYN| ≤ n W`. -/
theorem abs_levelYN_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelYN w cp N m e| ≤ n * absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |rowTerm w cp N m e i| ≤ ∑ _i : Fin n, absWeightSum n w :=
        sum_le_sum fun i _ ↦ abs_rowTerm_le hcp N m e i
    _ = n * absWeightSum n w := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|levelYNTrunc| ≤ n W`. -/
theorem abs_levelYNTrunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelYNTrunc w cp N m L e| ≤ n * absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |rowTermTrunc w cp N m L e i| ≤ ∑ _i : Fin n, absWeightSum n w :=
        sum_le_sum fun i _ ↦ abs_rowTermTrunc_le hcp N m L e i
    _ = n * absWeightSum n w := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|levelYN − levelYNTrunc| ≤ Σ_i |row_i − row_{i,L}|`. -/
theorem abs_levelYN_sub_trunc_le (N : Fin n → ℕ) (m L : ℕ) (e : Fin n → ℕ → ℕ → Bool) :
    |levelYN w cp N m e - levelYNTrunc w cp N m L e| ≤
      ∑ i, |rowTerm w cp N m e i - rowTermTrunc w cp N m L e i| := by
  rw [levelYN, levelYNTrunc, ← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-- The level term of a coin layout is measurable. -/
theorem measurable_levelYN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) : Measurable fun ω : ι → Bool ↦ levelYN w cp N m (coinsOf γ ω) :=
  Finset.measurable_fun_sum _ fun i _ ↦ measurable_rowTerm_coins hcp N m γ i

/-- The coordinates of levels `[m, m + L)` used by the truncated level term. -/
def levelCoords [DecidableEq ι] (n : ℕ) (γ : Fin n → ℕ → ℕ → ι) (m L : ℕ) : Finset ι :=
  univ.biUnion fun i ↦ (range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)

/-- The coordinates of `levelCoords` have levels in `[m, m + L)`. -/
theorem lev_mem_of_mem_levelCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {m L : ℕ} {q : ι} (hq : q ∈ levelCoords n γ m L) :
    m ≤ lev q ∧ lev q < m + L := by
  simp only [levelCoords, mem_biUnion, mem_univ, true_and, mem_image, Finset.mem_Ico] at hq
  obtain ⟨i, j, _, d, hd, rfl⟩ := hq
  rw [hlev]
  exact hd

/-- The truncated level term is local on `levelCoords`. -/
theorem isLocal_levelYNTrunc_coins [DecidableEq ι] (N : Fin n → ℕ) (m L : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    IsLocal (fun ω : ι → Bool ↦ levelYNTrunc w cp N m L (coinsOf γ ω)) (levelCoords n γ m L) :=
  isLocal_sum _ fun i _ ↦ (isLocal_rowTermTrunc_coins N m L γ i).mono
    (subset_biUnion_of_mem (fun i ↦ (range (n - 1)).biUnion fun j ↦
      (Finset.Ico m (m + L)).image (γ i j)) (mem_univ i))

/-- **Level truncation error in `L¹`**: `E|Y − Y_L| ≤ n W 2^{-L}`. -/
theorem integral_abs_levelYN_sub_trunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) :
    ∫ ω, |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)|
      ∂(coinMeasure ι) ≤ n * absWeightSum n w * (1 / 2) ^ L := by
  classical
  have hi : ∀ i, Integrable (fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|)
      (coinMeasure ι) := fun i ↦
    Integrable.of_bound (continuous_abs.measurable.comp ((measurable_rowTerm_coins hcp N m γ i).sub
      (measurable_rowTermTrunc_coins N m L γ i))).aestronglyMeasurable (absWeightSum n w)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]; exact abs_rowTerm_sub_trunc_le N m L _ i)
  have hm : Measurable fun ω : ι → Bool ↦
      |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)| :=
    continuous_abs.measurable.comp ((measurable_levelYN_coins hcp N m γ).sub
      (isLocal_levelYNTrunc_coins N m L γ).measurable)
  have hi1 : Integrable (fun ω : ι → Bool ↦
      |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (2 * (n * absWeightSum n w))
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_levelYN_le (w := w) hcp N m (coinsOf γ ω)
    have h2 := abs_levelYNTrunc_le (w := w) hcp N m L (coinsOf γ ω)
    have := abs_sub (levelYN w cp N m (coinsOf γ ω)) (levelYNTrunc w cp N m L (coinsOf γ ω))
    linarith
  refine (integral_mono hi1 (integrable_finsetSum _ fun i _ ↦ hi i)
    fun ω ↦ abs_levelYN_sub_trunc_le N m L _).trans ?_
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  calc ∑ i, ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
        ∂(coinMeasure ι) ≤ ∑ _i : Fin n, absWeightSum n w * (1 / 2) ^ L :=
        sum_le_sum fun i _ ↦ integral_abs_rowTerm_sub_trunc_le hcp N m L hγ i
    _ = n * absWeightSum n w * (1 / 2) ^ L := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Level sums are centred.** -/
theorem integral_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) :
    ∫ ω, levelSumN w cp N K (coinsOf γ ω) ∂(coinMeasure ι) = 0 := by
  have hint : ∀ m i, Integrable (fun ω : ι → Bool ↦ rowTerm w cp N m (coinsOf γ ω) i)
      (coinMeasure ι) := fun m i ↦
    Integrable.of_bound (measurable_rowTerm_coins hcp N m γ i).aestronglyMeasurable
      (absWeightSum n w) (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N m _ i)
  unfold levelSumN
  rw [integral_finsetSum _ fun m _ ↦ integrable_finsetSum _ fun i _ ↦ hint m i]
  refine sum_eq_zero fun m _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ hint m i]
  exact sum_eq_zero fun i _ ↦ integral_rowTerm_coins hcp N m hγ i

/-- Level sums of a coin layout are measurable. -/
theorem measurable_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ levelSumN w cp N K (coinsOf γ ω) :=
  Finset.measurable_fun_sum _ fun m _ ↦ measurable_levelYN_coins hcp N m γ

/-- Level sums are bounded by `K n W`. -/
theorem abs_levelSumN_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelSumN w cp N K e| ≤ K * (n * absWeightSum n w) := by
  rw [levelSumN_eq_sum_levelYN]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ range K, |levelYN w cp N m e| ≤ ∑ _m ∈ range K, (n * absWeightSum n w) :=
        sum_le_sum fun m _ ↦ abs_levelYN_le hcp N m e
    _ = K * (n * absWeightSum n w) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Level sums of a coin layout are in `L²`. -/
theorem memLp_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    MemLp (fun ω : ι → Bool ↦ levelSumN w cp N K (coinsOf γ ω)) 2 (coinMeasure ι) :=
  MemLp.of_bound (measurable_levelSumN_coins hcp N K γ).aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_levelSumN_le hcp N K _)

/-! ### The CLT for level sums -/

/-- **The CLT for level sums of a coin layout.** Let `lev (γ i j d) = d`, the cut points be
nonnegative, `K_k → ∞` and `Var(levelSumN) ≥ κ K_k` eventually. Then the normalised level sums
are asymptotically `N(0,1)`. -/
theorem tendstoInDistribution_levelSumN (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) {N : ℕ → Fin n → ℕ}
    {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * K k ≤ Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω) /
      √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]) atTop Z
      (fun _ ↦ coinMeasure ι) P' := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  set Y : ℕ → ℕ → (ι → Bool) → ℝ := fun k m ω ↦ levelYN w cp (N k) m (coinsOf γ ω) with hY
  set Yt : ℕ → ℕ → ℕ → (ι → Bool) → ℝ := fun k m L ω ↦
    levelYNTrunc w cp (N k) m L (coinsOf γ ω) with hYt
  have h := tendstoInDistribution_of_truncations (fun _ : ι ↦ fairCoin) lev hK
    (Y := Y) (Yt := Yt) (B := B) (C := B ^ 2)
    (fun k m ↦ measurable_levelYN_coins hcp (N k) m γ)
    (fun k m ω ↦ abs_levelYN_le hcp (N k) m _) (fun k m L ω ↦ abs_levelYNTrunc_le hcp (N k) m L _)
    (fun k m L ↦ ⟨levelCoords n γ m L, fun q hq ↦ lev_mem_of_mem_levelCoords hlev hq,
      isLocal_levelYNTrunc_coins (N k) m L γ⟩) (fun k m L ↦ ?_) hκ hvar hZ
  · have e : (fun k ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω) /
        √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]) =
        fun k ω ↦ ((∑ m ∈ range (K k), Y k m ω) -
          (coinMeasure ι)[fun ω ↦ ∑ m ∈ range (K k), Y k m ω]) /
          √Var[fun ω ↦ ∑ m ∈ range (K k), Y k m ω; coinMeasure ι] := by
      funext k ω
      have h0 := integral_levelSumN_coins (w := w) hcp (N k) (K k) hγ
      change levelSumN w cp (N k) (K k) (coinsOf γ ω) /
          √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι] =
        (levelSumN w cp (N k) (K k) (coinsOf γ ω) -
          ∫ ω, levelSumN w cp (N k) (K k) (coinsOf γ ω) ∂(coinMeasure ι)) /
          √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]
      rw [h0, sub_zero]
    rw [e]
    exact h
  · -- the `L²` truncation error
    have hd : ∀ ω, |Y k m ω - Yt k m L ω| ≤ 2 * B := fun ω ↦ by
      have h1 := abs_levelYN_le (w := w) hcp (N k) m (coinsOf γ ω)
      have h2 := abs_levelYNTrunc_le (w := w) hcp (N k) m L (coinsOf γ ω)
      have := abs_sub (Y k m ω) (Yt k m L ω)
      simp only [hY, hYt] at this ⊢
      linarith
    have hpt : ∀ ω, (Y k m ω - Yt k m L ω) ^ 2 ≤ B * |Y k m ω - Yt k m L ω| := by
      intro ω
      have h1 : |Y k m ω - Yt k m L ω| ≤ B := by
        refine (abs_levelYN_sub_trunc_le (N k) m L _).trans ?_
        calc ∑ i, |rowTerm w cp (N k) m (coinsOf γ ω) i -
              rowTermTrunc w cp (N k) m L (coinsOf γ ω) i|
            ≤ ∑ _i : Fin n, absWeightSum n w :=
              sum_le_sum fun i _ ↦ abs_rowTerm_sub_trunc_le (N k) m L _ i
          _ = B := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← sq_abs]
      nlinarith [abs_nonneg (Y k m ω - Yt k m L ω)]
    have hm : Measurable fun ω ↦ Y k m ω - Yt k m L ω :=
      (measurable_levelYN_coins hcp (N k) m γ).sub
        (isLocal_levelYNTrunc_coins (N k) m L γ).measurable
    have hi1 : Integrable (fun ω ↦ (Y k m ω - Yt k m L ω) ^ 2) (coinMeasure ι) := by
      refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
        (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd ω) 2
    have hi2 : Integrable (fun ω ↦ B * |Y k m ω - Yt k m L ω|) (coinMeasure ι) :=
      (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable (2 * B)
        (Eventually.of_forall fun ω ↦ by
          change ‖|Y k m ω - Yt k m L ω|‖ ≤ 2 * B
          rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul B
    refine (integral_mono hi1 hi2 hpt).trans ?_
    rw [integral_const_mul]
    have := integral_abs_levelYN_sub_trunc_le (w := w) hcp (N k) m L hγ
    calc B * ∫ ω, |Y k m ω - Yt k m L ω| ∂(coinMeasure ι) ≤ B * (B * (1 / 2) ^ L) :=
          mul_le_mul_of_nonneg_left this hB0
      _ = B ^ 2 * (1 / 2) ^ L := by ring

/-! ### Slutsky assembly -/

/-- **Slutsky assembly.** Let `E_k` be within `b_k` of a centred `M_k`, with
`b_k² / log₂ T_k → 0` and `Var E_k ≥ κ log₂ T_k` eventually. If `M_k` satisfies the CLT whenever
`Var M_k ≥ κ' (⌊log₂ T_k⌋ + 1)` eventually, then `E_k / √Var E_k ⇒ Z`. -/
theorem tendstoInDistribution_of_close_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {T : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    {b : ℕ → ℝ} (hb : Tendsto (fun k ↦ b k ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0))
    (hE : ∀ k, MemLp (E k) 2 μ) (hM : ∀ k, MemLp (M k) 2 μ) (hM0 : ∀ k, μ[M k] = 0)
    (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * Nat.log 2 (T k) ≤ Var[E k; μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hclt : ∀ κ' : ℝ, 0 < κ' →
      (∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[M k; μ]) →
        TendstoInDistribution (fun k ω ↦ M k ω / √Var[M k; μ]) atTop Z (fun _ ↦ μ) P') :
    TendstoInDistribution (fun k ω ↦ E k ω / √Var[E k; μ]) atTop Z (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hlog1 : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (T k) := hlogT.eventually_ge_atTop 1
  have hbE : Tendsto (fun k ↦ b k ^ 2 / Var[E k; μ]) atTop (𝓝 0) := by
    have h := hb.div_const κ
    rw [zero_div] at h
    refine squeeze_zero' (Eventually.of_forall fun k ↦ by
      have := variance_nonneg (E k) μ
      have := hb0 k
      positivity) ?_ h
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (0 : ℝ) < Nat.log 2 (T k) := by exact_mod_cast hl
    rw [div_div, mul_comm (Nat.log 2 (T k) : ℝ) κ]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk
  have hpos : ∀ᶠ k in atTop, 0 < Var[E k; μ] := by
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    nlinarith
  refine tendstoInDistribution_of_abs_sub_le hE hM hM0 hclose hbE hpos ?_
  refine hclt (κ / 8) (by positivity) ?_
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / Var[E k; μ] ≤ 1 / 4 :=
    hbE.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hvar, hlog1, hsmall, hpos] with k hk hl hs hp
  have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
  have hσ : |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  set sE := √Var[E k; μ] with hsE
  set sM := √Var[M k; μ] with hsM
  have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt hp.le
  have hbsE : b k ≤ sE / 2 := by
    rw [div_le_iff₀ hp, ← hsE2] at hs
    have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
    by_contra hc
    push Not at hc
    nlinarith [hb0 k]
  have hsMge : sE / 2 ≤ sM := by
    have := (abs_le.1 hσ).1
    linarith
  have hsE0 : 0 ≤ sE / 2 := by positivity
  have hVM : sE ^ 2 / 4 ≤ Var[M k; μ] := by
    have := pow_le_pow_left₀ hsE0 hsMge 2
    rw [hsM, Real.sq_sqrt (variance_nonneg _ _), div_pow] at this
    linarith
  have hK2 : ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ 2 * Nat.log 2 (T k) := by
    push_cast
    linarith
  calc κ / 8 * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ κ / 8 * (2 * Nat.log 2 (T k)) := by gcongr
    _ = κ * Nat.log 2 (T k) / 4 := by ring
    _ ≤ sE ^ 2 / 4 := by rw [hsE2]; linarith
    _ ≤ Var[M k; μ] := hVM

end RQMCMarkov.ScrambledStacks
