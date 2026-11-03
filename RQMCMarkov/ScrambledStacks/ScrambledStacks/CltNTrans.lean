/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNOwen

/-!
# The stacks CLT for transition counts, n states (post #3, codes (ii) and (iii))

Post #3 reports "the error in the number of each transition" of the per-state Sobol stacks.
The transition-count error `N_ij(T) − p_ij N_i(T)` is EXACTLY the departure discrepancy of row
`i` for the indicator `1_{j}` (`transCount_sub_eq_departureDiscrepancy`); by Abel summation it is
`segErr(v_i, c_{i,j+1}, 0, N_i(T)) − segErr(v_i, c_{i,j}, 0, N_i(T))`: integer weights `±1` at the
cut points `c_{i,j}`, `c_{i,j+1}` (`transErrN_eq`).

**Reading.** As for the occupation error: along times `T_k → ∞` with
`Var(N_ij(T_k) − p_ij N_i(T_k)) ≥ κ log₂ T_k`, the normalised transition-count error is
asymptotically `N(0,1)`, for the digital shift (`tendstoInDistribution_transErrN_shift`) and,
by a separate proof, for Owen's scramble (`tendstoInDistribution_transErrN_owen`).

**Proof.** Only row `i` is in play: we give the other rows the inert cut point `1` (`rowCut`),
whose level terms vanish, so the main term `Σ_{j'} w_{j'} segErr(v_i, c_{ij'}, 0, ⌊T π_i⌋)` is a
level sum (`transMainN_eq_levelSumN`); the Anscombe step uses only `|N_i(T) − T π_i| = O(log T)`
(`abs_transErrN_sub_transMainN_le`, `O(log log T)`). Then `CltNCoins` (shift layout) or the Owen
relabelling of `CltNOwenTree` (Owen layout of the row cut points), and Slutsky.

**Hypotheses added.** `IsPoissonFamily P H π` (for `|N_i(T) − T π_i| = O(log T)`); the variance
hypothesis along the given times. Non-vacuity is not proved here (the uniform chains of
`CltNExample` treat the occupation error).

## Main results

* `transErrN`, `indicatorFn`, `transErrN_eq`, `transMainN`, `abs_transErrN_sub_transMainN_le`,
  `transBound`, `transBound_le_log`.
* `rowCut`, `transMainN_eq_levelSumN`, `owenLayoutOf`.
* `tendstoInDistribution_transErrN_shift`, `tendstoInDistribution_transErrN_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The transition-count error `N_ij(T) − p_ij N_i(T)` of the chain driven by the stacks of
`f`. -/
noncomputable def transErrN (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : ℝ :=
  (transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
    P i j * occCount (stackPath P x₀ (scrambledStack f)) i T

/-- The indicator `1_{j}` of a state. -/
noncomputable def indicatorFn (j : Fin n) : Fin n → ℝ := fun k ↦ if k = j then 1 else 0

/-- **The transition-count error is a weighted sum of local discrepancies of row `i`.** -/
theorem transErrN_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    transErrN P x₀ f i j T = ∑ j' ∈ range (n - 1), cutWeight (indicatorFn j) j' *
      segErr (scrambledVdc (f i)) (cutPoint P i j') 0
        (occCount (stackPath P x₀ (scrambledStack f)) i T) := by
  rw [transErrN, transCount_sub_eq_departureDiscrepancy P _ i j T]
  refine (departureDiscrepancy_stackDrive P (indicatorFn j) (step P) x₀ (scrambledStack f) i
    T).trans ?_
  exact sum_step_sub_eq_sum_segErr hP (indicatorFn j) i (fun k ↦ (scrambledVdc_mem_Icc (f i) k).2) _

/-- The main term of the transition-count error at the deterministic index `⌊T π_i⌋`. -/
noncomputable def transMainN (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : ℝ :=
  ∑ j' ∈ range (n - 1), cutWeight (indicatorFn j) j' *
    segErr (scrambledVdc (f i)) (cutPoint P i j') 0 (chainIdxN pi T i)

/-- The Anscombe bound `W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)` for transitions. -/
noncomputable def transBound (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) : ℝ :=
  cutWeightSum (indicatorFn j) * (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3)

/-- **Deterministic Anscombe theorem for transition counts** (every flip table). -/
theorem abs_transErrN_sub_transMainN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |transErrN P x₀ f i j T - transMainN P pi f i j T| ≤ transBound H j T := by
  rw [transErrN_eq hP x₀ f i j T, transMainN, ← sum_sub_distrib, transBound, cutWeightSum,
    sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j' _ ↦ ?_)
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hc := cutPoint_mem_Icc hP i j'
  refine (abs_segErr_sub_segErr_le (f i) hc.1 hc.2 _ _).trans ?_
  have hpi := hH.mem_Icc hP i
  have hfl : |T * pi i - (chainIdxN pi T i : ℝ)| < 1 := by
    have hy : 0 ≤ (T : ℝ) * pi i := mul_nonneg (Nat.cast_nonneg T) hpi.1
    rw [chainIdxN, abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
    linarith [Nat.lt_floor_add_one ((T : ℝ) * pi i)]
  have hd := natLog_dist_le (abs_occCount_sub_pi_le hP hH x₀ f i T) hfl
  have hd' : (Nat.log 2 (occCount (stackPath P x₀ (scrambledStack f)) i T - chainIdxN pi T i +
      (chainIdxN pi T i - occCount (stackPath P x₀ (scrambledStack f)) i T)) : ℝ) ≤
      Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) := by exact_mod_cast hd
  linarith

/-- `0 ≤ transBound`. -/
theorem transBound_nonneg (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) : 0 ≤ transBound H j T := by
  have := cutWeightSum_nonneg (indicatorFn j)
  rw [transBound]
  positivity

/-- **The transition Anscombe bound is `O(log log T)`.** -/
theorem transBound_le_log (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) :
    transBound H j T ≤ cutWeightSum (indicatorFn j) * (2 * Nat.log 2 (anscConstN H) + 5) *
      ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hmul : (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConstN H) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    exact_mod_cast natLog_mul_le _ _
  have hW := cutWeightSum_nonneg (indicatorFn j)
  have h0 := (Nat.log 2 (anscConstN H)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  rw [transBound, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hW
  nlinarith

/-- Row-restricted cut points: those of row `i`, and the inert cut point `1` in other rows. -/
noncomputable def rowCut (P : Fin n → Fin n → ℝ) (i : Fin n) : Fin n → ℕ → ℝ :=
  fun i' j' ↦ if i' = i then cutPoint P i' j' else 1

/-- Row-restricted cut points are nonnegative. -/
theorem rowCut_nonneg {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i i' : Fin n) (j' : ℕ) :
    0 ≤ rowCut P i i' j' := by
  unfold rowCut
  split_ifs
  · exact (cutPoint_mem_Icc hP i' j').1
  · norm_num

/-- **Level decomposition of the transition main term** (every flip table). -/
theorem transMainN_eq_levelSumN {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (pi : Fin n → ℝ)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) {K : ℕ}
    (hK : ∀ i', chainIdxN pi T i' < 2 ^ K) :
    transMainN P pi f i j T = levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) K
      (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) := by
  have hrow : ∀ m, ∑ i', rowTerm (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) m
      (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) i' =
      rowTerm (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) m
        (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) i := by
    intro m
    refine sum_eq_single i (fun i' _ hne ↦ sum_eq_zero fun j' _ ↦ ?_)
      (fun h ↦ absurd (mem_univ i) h)
    simp only [cutTerm, rowCut, hne, ite_false, lt_irrefl, mul_zero]
  rw [levelSumN, sum_congr rfl fun m _ ↦ hrow m, transMainN]
  simp only [rowTerm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc := cutPoint_mem_Icc hP i j'
  rw [segErr_scrambledVdc_eq_sum_cutTerm (f i) hc.1 hc.2 (hK i), mul_sum]
  simp only [rowCut, ite_true]

/-- The transition main term under the digital shift. -/
noncomputable def shiftTransMain (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (i j : Fin n) (T : ℕ)
    (ω : Fin n × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (shiftLayout n) ω)

/-- The transition-count error is bounded: `|N_ij − p_ij N_i| ≤ T + |p_ij| T`. -/
theorem abs_transErrN_le (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : |transErrN P x₀ f i j T| ≤ T + |P i j| * T := by
  rw [transErrN]
  refine (abs_sub _ _).trans ?_
  rw [Nat.abs_cast, abs_mul, Nat.abs_cast]
  have h1 : (transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) ≤ T := by
    exact_mod_cast (transCount_le_occCount _ i j T).trans (occCount_le _ i T)
  have h2 : (occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) ≤ T := by
    exact_mod_cast occCount_le _ i T
  nlinarith [abs_nonneg (P i j)]

/-- **The transition-count CLT, digital shift** (post #3, code (ii), n states): along `T_k → ∞`
with `Var(N_ij(T_k) − p_ij N_i(T_k)) ≥ κ log₂ T_k`, the normalised error is asymptotically
`N(0,1)`. -/
theorem tendstoInDistribution_transErrN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ i j : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k); shiftMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k) /
      √Var[fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k); shiftMeasure n]) atTop Z
      (fun _ ↦ shiftMeasure n) P' := by
  have hcp := rowCut_nonneg hP i
  have hγ : ∀ i j, Function.Injective (shiftLayout n i j) := fun i j d d' h ↦
    congrArg Prod.snd h
  have hE : ∀ k, MemLp (fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k)) 2 (shiftMeasure n) := by
    intro k
    have hm : Measurable fun ω : Fin n × ℕ → Bool ↦ transErrN P x₀ (shiftFlips ω) i j (T k) :=
      ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_transCount_of
        (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ i j (T k))).sub
        (((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
        (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ i (T k))).const_mul _)
    exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_transErrN_le P x₀ _ i j (T k))
  have hclose : ∀ k ω, |transErrN P x₀ (shiftFlips ω) i j (T k) -
      shiftTransMain P pi i j (T k) ω| ≤ transBound H j (T k) := by
    intro k ω
    have e : shiftTransMain P pi i j (T k) ω = transMainN P pi (shiftFlips ω) i j (T k) :=
      (transMainN_eq_levelSumN hP pi (shiftFlips ω) i j (T k)
        (chainIdxN_lt_two_pow hP hH (T k))).symm
    rw [e]
    exact abs_transErrN_sub_transMainN_le hP hH x₀ (shiftFlips ω) i j (T k)
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k))
    (M := fun k ω ↦ shiftTransMain P pi i j (T k) ω) hT (b := fun k ↦ transBound H j (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ transBound_nonneg H j (T k))
      (fun k ↦ transBound_le_log H j (T k))) hE
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ↦ integral_levelSumN_coins hcp _ _ hγ) hclose hκ hvar ?_
  intro κ' hκ' hv
  exact tendstoInDistribution_levelSumN Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv hZ

/-- The Owen coin layout of arbitrary cut points `cp`. -/
noncomputable def owenLayoutOf (cp : Fin n → ℕ → ℝ) : Fin n → ℕ → ℕ → Fin n × ℕ × ℕ :=
  fun i j d ↦ (i, d, ⌊2 ^ d * cp i j⌋₊)

/-- The transition main term under Owen's scramble, at relabelled flips `ω'`. -/
noncomputable def owenTransMain (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (i j : Fin n) (T : ℕ)
    (ω' : Fin n × ℕ × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (owenLayoutOf (rowCut P i)) ω')

/-- **The transition-count CLT, Owen's scramble** (post #3, code (iii), n states), a separate
proof through the relabelling by the scrambled tree. -/
theorem tendstoInDistribution_transErrN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ i j : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k); owenMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ transErrN P x₀ (owenTable ω) i j (T k) /
      √Var[fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k); owenMeasure n]) atTop Z
      (fun _ ↦ owenMeasure n) P' := by
  have hcp := rowCut_nonneg hP i
  have hγ : ∀ i' j', Function.Injective (owenLayoutOf (rowCut P i) i' j') := fun i' j' d d' h ↦
    congrArg (fun q : Fin n × ℕ × ℕ ↦ q.2.1) h
  have hMP := measurePreserving_owenRelabel (n := n)
  set G : ℕ → (Fin n × ℕ × ℕ → Bool) → ℝ := fun k ω' ↦ owenTransMain P pi i j (T k) ω' with hG
  have hGm : ∀ k, Measurable (G k) := fun k ↦
    measurable_levelSumN_coins (w := cutWeight (indicatorFn j)) hcp _ _ _
  have hvarG : ∀ k, Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n] =
      Var[G k; owenMeasure n] := fun k ↦ hMP.variance_fun_comp (hGm k).aemeasurable
  have hE : ∀ k, MemLp (fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k)) 2 (owenMeasure n) := by
    intro k
    have hm : Measurable fun ω : Fin n × ℕ × ℕ → Bool ↦ transErrN P x₀ (owenTable ω) i j (T k) :=
      ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_transCount_of
        (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ i j (T k))).sub
        (((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
        (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ i (T k))).const_mul _)
    exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_transErrN_le P x₀ _ i j (T k))
  have hclose : ∀ k ω, |transErrN P x₀ (owenTable ω) i j (T k) - G k (owenRelabel ω)| ≤
      transBound H j (T k) := by
    intro k ω
    have e : G k (owenRelabel ω) = transMainN P pi (owenTable ω) i j (T k) := by
      rw [transMainN_eq_levelSumN hP pi (owenTable ω) i j (T k)
        (chainIdxN_lt_two_pow hP hH (T k))]
      refine levelSumN_congr _ _ fun i' j' hc ↦ ?_
      exact (funext fun d ↦ pathCoin_owenTable_eq_relabel ω i' hc d).symm
    rw [e]
    exact abs_transErrN_sub_transMainN_le hP hH x₀ (owenTable ω) i j (T k)
  have hM0 : ∀ k, ∫ ω, G k (owenRelabel ω) ∂(owenMeasure n) = 0 := by
    intro k
    rw [← integral_map measurable_owenRelabel.aemeasurable (hGm k).aestronglyMeasurable,
      hMP.map_eq]
    exact integral_levelSumN_coins hcp _ _ hγ
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ transErrN P x₀ (owenTable ω) i j (T k))
    (M := fun k ω ↦ G k (owenRelabel ω)) hT (b := fun k ↦ transBound H j (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ transBound_nonneg H j (T k))
      (fun k ↦ transBound_le_log H j (T k))) hE
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ _).comp_measurePreserving hMP) hM0 hclose hκ hvar ?_
  intro κ' hκ' hv
  have hv' : ∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[G k; owenMeasure n] := by
    filter_upwards [hv] with k hk
    rwa [← hvarG k]
  have hclt := tendstoInDistribution_levelSumN (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
    (γ := owenLayoutOf (rowCut P i)) (fun i j d ↦ rfl) hcp (w := cutWeight (indicatorFn j))
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv' hZ
  have htr := TendstoInDistribution.comp_measurePreserving hMP hclt
  have e : (fun k ω ↦ G k (owenRelabel ω) / √Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n]) =
      fun k ω ↦ G k (owenRelabel ω) / √Var[G k; owenMeasure n] := by
    funext k ω
    rw [hvarG k]
  rw [e]
  exact htr

end RQMCMarkov.ScrambledStacks
