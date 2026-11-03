/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNOwenTree
import ScrambledStacks.CltNShift

/-!
# The stacks CLT for n states: Owen's nested scramble (post #3, code (iii))

Post #3, code (iii): one Sobol (base-2 van der Corput) sequence per state with Owen's nested
scramble; "in the five-state chain normality cannot be rejected for the per-state Sobol
sequences ((ii) and (iii))".

**Reading.** As for the digital shift (`CltNShift`): for any number `n` of states, any
stochastic `P` with Poisson data for every target and any target `s`, along times `T_k → ∞`
with `Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` under Owen's measure, the normalised occupation
error is asymptotically `N(0,1)`; its variance is `O(log T)` and the RMSE of the occupation
frequency `O(√log T / T)`. The variance hypothesis is for Owen's own variance, which differs
from the shift's in general (`CltNExample` shows both satisfy it on the uniform chains; their
values are not claimed equal).

**Proof (separate from the shift).** By `CltThreeState` the path laws of (ii) and (iii) differ
for `n ≥ 3`, so nothing is transferred from the shift. Instead the flips are relabelled by the
scrambled tree (`CltNOwenTree`): the path coin of cut point `c_{ij}` at depth `d` is the
relabelled flip at `(i, d, ⌊2^d c_{ij}⌋)` (`pathCoins_owenTable_eq`), so the main term is the level
sum of the coin layout `owenLayout P` on `Fin n × ℕ × ℕ` with level `q ↦ q.2.1`
(`mainTermN_owenTable_eq`), evaluated at the relabelled flips. Two cut points of a row share
the coordinates of their common binary prefix (the level-sum CLT of `CltNCoins` allows this).
The relabelling preserves Owen's measure (`measurePreserving_owenRelabel`), so the CLT for level
sums transfers (`TendstoInDistribution.comp_measurePreserving`); the Anscombe theorem and
Slutsky finish as for the shift.

**Hypotheses added.** As in `CltNShift`: `IsPoissonFamily P H π`, and the variance hypothesis
along the given times.

## Main results

* `owenLayout`, `pathCoins_owenTable_eq`, `levelSumN_congr`, `mainTermN_owenTable_eq`,
  `owenMainTerm`, `abs_occErrN_owen_sub_le`, `memLp_occErrN_owen`.
* `tendstoInDistribution_occErrN_owen` (**main theorem, code (iii)**).
* `integral_sq_occErrN_owen_le`, `variance_occErrN_owen_le`, `isBigO_meanSq_occFreqN_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The Owen coin layout: cut point `j` of row `i` at depth `d` uses the relabelled flip at the
scrambled node `⌊2^d c_{ij}⌋`. -/
noncomputable def owenLayout (P : Fin n → Fin n → ℝ) : Fin n → ℕ → ℕ → Fin n × ℕ × ℕ :=
  fun i j d ↦ (i, d, ⌊2 ^ d * cutPoint P i j⌋₊)

/-- The level of the Owen coordinate `(i, d, p)` is the depth `d`. -/
theorem owenLayout_lev (P : Fin n → Fin n → ℝ) (i : Fin n) (j d : ℕ) :
    (owenLayout P i j d).2.1 = d := rfl

/-- Different rows use different Owen flips. -/
theorem owenLayout_rows (P : Fin n → Fin n → ℝ) (i i' : Fin n) (j j' d d' : ℕ) (hii' : i ≠ i') :
    owenLayout P i j d ≠ owenLayout P i' j' d' := fun h ↦ hii' (congrArg Prod.fst h)

/-- **Owen path coins are relabelled flips**: for a cut point `c_{ij} < 1`, its path coins are
the relabelled flips of the Owen layout. -/
theorem pathCoins_owenTable_eq (P : Fin n → Fin n → ℝ) (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n)
    (j : ℕ) (hc : cutPoint P i j < 1) :
    pathCoin (owenTable ω i) (threshDigit (cutPoint P i j)) =
      coinsOf (owenLayout P) (owenRelabel ω) i j :=
  funext fun d ↦ pathCoin_owenTable_eq_relabel ω i hc d

/-- Level sums only see the coins of cut points `< 1`. -/
theorem levelSumN_congr {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ} (N : Fin n → ℕ) (K : ℕ)
    {e e' : Fin n → ℕ → ℕ → Bool} (h : ∀ i j, cp i j < 1 → e i j = e' i j) :
    levelSumN w cp N K e = levelSumN w cp N K e' := by
  refine sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  unfold cutTerm
  by_cases hc : cp i j < 1
  · simp only [hc, ite_true]
    rw [h i j hc]
  · simp only [hc, ite_false]

/-- The main term of the Owen-scrambled chain as a level sum of relabelled flips `ω'`, with
`⌊log₂ T⌋ + 1` levels. -/
noncomputable def owenMainTerm (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) (ω' : Fin n × ℕ × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (H s)) (cutPoint P) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (owenLayout P) ω')

/-- The main term of the Owen-scrambled chain is the level sum at the relabelled flips. -/
theorem mainTermN_owenTable_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (s : Fin n) (T : ℕ)
    (ω : Fin n × ℕ × ℕ → Bool) :
    mainTermN P (H s) pi (owenTable ω) T = owenMainTerm P H pi s T (owenRelabel ω) := by
  rw [mainTermN_eq_levelSumN hP (H s) pi (owenTable ω) T (chainIdxN_lt_two_pow hP hH T),
    owenMainTerm]
  exact levelSumN_congr _ _ fun i j hc ↦ pathCoins_owenTable_eq P ω i j hc

/-- The occupation error of the Owen-scrambled chain is within `ansBoundN` of the level sum. -/
theorem abs_occErrN_owen_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) (ω : Fin n × ℕ × ℕ → Bool) :
    |occErrN P pi x₀ (owenTable ω) s T - owenMainTerm P H pi s T (owenRelabel ω)| ≤
      ansBoundN H s T := by
  rw [← mainTermN_owenTable_eq hP hH s T ω]
  exact abs_occErrN_sub_mainTermN_le hP hH x₀ (owenTable ω) s T

/-- The occupation error of the Owen-scrambled chain is in `L²`. -/
theorem memLp_occErrN_owen (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ s : Fin n) (T : ℕ) :
    MemLp (fun ω ↦ occErrN P pi x₀ (owenTable ω) s T) 2 (owenMeasure n) := by
  have hm : Measurable fun ω : Fin n × ℕ × ℕ → Bool ↦ occErrN P pi x₀ (owenTable ω) s T :=
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
      (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ s T)).sub measurable_const
  exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact abs_occErrN_le P pi x₀ _ s T)

/-- The relabelled main term has the moments of the level sum: it is centred. -/
theorem integral_owenMainTerm_relabel {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (H : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) :
    ∫ ω, owenMainTerm P H pi s T (owenRelabel ω) ∂(owenMeasure n) = 0 := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hγ : ∀ i j, Function.Injective (owenLayout P i j) := fun i j d d' h ↦
    congrArg (fun q : Fin n × ℕ × ℕ ↦ q.2.1) h
  have hGm := measurable_levelSumN_coins (w := cutWeight (H s)) hcp (chainIdxN pi T)
    (Nat.log 2 T + 1) (owenLayout P)
  unfold owenMainTerm
  rw [← integral_map measurable_owenRelabel.aemeasurable hGm.aestronglyMeasurable,
    measurePreserving_owenRelabel.map_eq]
  exact integral_levelSumN_coins hcp _ _ hγ

/-- **The stacks CLT for n states, Owen's scramble** (post #3, code (iii)). For a stochastic `P`
on `Fin n` with Poisson data `H`, `π` for every target, a target `s`, and `T_k → ∞` with
`Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` eventually (Owen's variance),
`(N_s(T_k) − T_k π_s) / √Var(N_s(T_k) − T_k π_s) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_occErrN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s (T k); owenMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErrN P pi x₀ (owenTable ω) s (T k) /
      √Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s (T k); owenMeasure n]) atTop Z
      (fun _ ↦ owenMeasure n) P' := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  set G : ℕ → (Fin n × ℕ × ℕ → Bool) → ℝ := fun k ω' ↦ owenMainTerm P H pi s (T k) ω' with hG
  have hGm : ∀ k, Measurable (G k) := fun k ↦
    measurable_levelSumN_coins (w := cutWeight (H s)) hcp _ _ (owenLayout P)
  have hvarG : ∀ k, Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n] =
      Var[G k; owenMeasure n] := fun k ↦ hMP.variance_fun_comp (hGm k).aemeasurable
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ occErrN P pi x₀ (owenTable ω) s (T k))
    (M := fun k ω ↦ G k (owenRelabel ω)) hT (b := fun k ↦ ansBoundN H s (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ ansBoundN_nonneg H s (T k))
      (fun k ↦ ansBoundN_le_log H s (T k)))
    (fun k ↦ memLp_occErrN_owen P pi x₀ s (T k))
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ (owenLayout P)).comp_measurePreserving hMP)
    (fun k ↦ integral_owenMainTerm_relabel hP H pi s (T k))
    (fun k ω ↦ abs_occErrN_owen_sub_le hP hH x₀ s (T k) ω) hκ hvar ?_
  intro κ' hκ' hv
  have hv' : ∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[G k; owenMeasure n] := by
    filter_upwards [hv] with k hk
    rwa [← hvarG k]
  have hclt := tendstoInDistribution_levelSumN (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
    (γ := owenLayout P) (fun i j d ↦ rfl) hcp (w := cutWeight (H s))
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv' hZ
  have htr := TendstoInDistribution.comp_measurePreserving hMP hclt
  have e : (fun k ω ↦ G k (owenRelabel ω) / √Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n]) =
      fun k ω ↦ G k (owenRelabel ω) / √Var[G k; owenMeasure n] := by
    funext k ω
    rw [hvarG k]
  rw [e]
  exact htr

/-- **Mean-square bound** (Owen): `E[(N_s(T) − T π_s)²] ≤ C (⌊log₂ T⌋ + 1)`. -/
theorem integral_sq_occErrN_owen_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    ∫ ω, occErrN P pi x₀ (owenTable ω) s T ^ 2 ∂(owenMeasure n) ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  have hGm := measurable_levelSumN_coins (w := cutWeight (H s)) hcp (chainIdxN pi T)
    (Nat.log 2 T + 1) (owenLayout P)
  have hV0 := integral_sq_levelSumN_le (fun q : Fin n × ℕ × ℕ ↦ q.2.1) (γ := owenLayout P)
    (fun i j d ↦ rfl) hcp (w := cutWeight (H s)) (chainIdxN pi T) (Nat.log 2 T + 1)
  have hV : ∫ ω, owenMainTerm P H pi s T (owenRelabel ω) ^ 2 ∂(owenMeasure n) ≤
      ((Nat.log 2 T + 1 : ℕ) : ℝ) * (5 * (n * absWeightSum n (cutWeight (H s))) ^ 2) := by
    rw [← integral_map (f := fun ω' ↦ owenMainTerm P H pi s T ω' ^ 2)
      measurable_owenRelabel.aemeasurable (hGm.pow_const 2).aestronglyMeasurable, hMP.map_eq]
    exact hV0
  have h := integral_sq_le_of_close (memLp_occErrN_owen P pi x₀ s T)
    ((memLp_levelSumN_coins hcp _ _ (owenLayout P)).comp_measurePreserving hMP)
    (abs_occErrN_owen_sub_le hP hH x₀ s T) hV
  have hb := two_mul_ansBoundN_sq_le H s T
  refine h.trans ?_
  rw [varConstN]
  push_cast
  change 2 * (((Nat.log 2 T : ℝ) + 1) * (5 * (n * cutWeightSum (H s)) ^ 2)) +
    2 * ansBoundN H s T ^ 2 ≤ _
  nlinarith

/-- **Variance bound** (Owen): `Var(N_s(T) − T π_s) ≤ C (⌊log₂ T⌋ + 1) = O(log T)`. -/
theorem variance_occErrN_owen_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s T; owenMeasure n] ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) :=
  (variance_le_expectation_sq (memLp_occErrN_owen P pi x₀ s T).aestronglyMeasurable).trans
    (integral_sq_occErrN_owen_le hP hH x₀ s T)

/-- **RMSE of the occupation frequency is `O(√log T / T)`** (Owen, n states):
`E[(N_s(T)/T − π_s)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_occFreqN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n) :
    (fun T : ℕ ↦ ∫ ω, (occErrN P pi x₀ (owenTable ω) s T / T) ^ 2 ∂(owenMeasure n)) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 :=
  isBigO_meanSq_div_of_le (E := fun T ω ↦ occErrN P pi x₀ (owenTable ω) s T)
    (integral_sq_occErrN_owen_le hP hH x₀ s)

end RQMCMarkov.ScrambledStacks
