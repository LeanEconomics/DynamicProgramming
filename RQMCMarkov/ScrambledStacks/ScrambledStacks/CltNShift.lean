/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNVariance

/-!
# The stacks CLT for n states: the random digital shift (post #3, code (ii))

Post #3, code (ii): one Sobol (base-2 van der Corput) sequence per state with a random digital
shift; "in the five-state chain normality cannot be rejected for the per-state Sobol sequences".

**Reading.** As for two states (`CltStacks`): for ANY number `n` of states, any stochastic `P`
with Poisson data for every target (`IsPoissonFamily`) and any target `s`, along times `T_k → ∞`
with `Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k`, the normalised occupation error is asymptotically
`N(0,1)`. The variance is always `O(log T)`, so the RMSE of the occupation frequency is
`O(√log T / T)`.

**Proof.** Under the digital shift the path coins of EVERY cut point of row `i` are the same
flips `ω (i, d)` (`pathCoin_shiftTable`): the main term is the level sum of the coin layout
`shiftLayout` on `Fin n × ℕ` with level `Prod.snd` (`mainTermN_shiftFlips_eq`). The CLT for level
sums (`CltNCoins`) and the deterministic Anscombe theorem (`CltNDecomp`, `O(log log T)`) with
Slutsky give the result. This proof uses no law of Owen's scramble (the laws differ for `n ≥ 3`,
`CltThreeState`); the Owen case is the separate `CltNOwen`.

**Hypotheses added.** `IsPoissonFamily P H π` (Poisson data for every target; satisfiable, e.g.
`CltNExample`); the variance hypothesis is stated along the given times (`∀ᶠ k`), as the CLT is
about such subsequences (along `T = 2^k` the variance stays bounded for non-dyadic chains,
`StackPowerOfTwo`). No positivity of `P` and no condition on the cut points is needed (cut points
equal to `1` contribute nothing).

## Main results

* `shiftLayout`, `pathCoins_shiftFlips_eq`, `mainTermN_shiftFlips_eq`, `shiftMainTerm`.
* `abs_occErrN_shift_sub_le`, `memLp_occErrN_shift`.
* `tendstoInDistribution_occErrN_shift` (**main theorem, code (ii)**).
* `integral_sq_occErrN_shift_le`, `variance_occErrN_shift_le`: `E[E_T²], Var(E_T) ≤ C (log₂ T + 1)`.
* `isBigO_meanSq_occFreqN_shift`: `E[(N_s(T)/T − π_s)²] = O(log T / T²)` (RMSE `O(√log T / T)`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The digital-shift coin layout: every cut point `j` of row `i` uses the flips `(i, d)`. -/
def shiftLayout (n : ℕ) : Fin n → ℕ → ℕ → Fin n × ℕ := fun i _ d ↦ (i, d)

/-- The level of the shift coordinate `(i, d)` is `d`. -/
theorem shiftLayout_lev (i : Fin n) (j d : ℕ) : (shiftLayout n i j d).2 = d := rfl

/-- Different rows use different shift flips. -/
theorem shiftLayout_rows (i i' : Fin n) (j j' d d' : ℕ) (hii' : i ≠ i') :
    shiftLayout n i j d ≠ shiftLayout n i' j' d' := fun h ↦ hii' (congrArg Prod.fst h)

/-- **Shift path coins.** Under the digital shift the path coins of every cut point of row `i`
are the flips `ω (i, ·)`. -/
theorem pathCoins_shiftFlips_eq (P : Fin n → Fin n → ℝ) (ω : Fin n × ℕ → Bool) :
    (fun i j ↦ pathCoin (shiftFlips ω i) (threshDigit (cutPoint P i j))) =
      coinsOf (shiftLayout n) ω := rfl

/-- The main term of the shifted chain as a level sum of the flips, with `⌊log₂ T⌋ + 1` levels. -/
noncomputable def shiftMainTerm (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) (ω : Fin n × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (H s)) (cutPoint P) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (shiftLayout n) ω)

/-- The main term of the shifted chain is the level sum of the flips. -/
theorem mainTermN_shiftFlips_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (s : Fin n) (T : ℕ)
    (ω : Fin n × ℕ → Bool) :
    mainTermN P (H s) pi (shiftFlips ω) T = shiftMainTerm P H pi s T ω :=
  mainTermN_eq_levelSumN hP (H s) pi (shiftFlips ω) T (chainIdxN_lt_two_pow hP hH T)

/-- The occupation error of the shifted chain is within `ansBoundN` of the level sum. -/
theorem abs_occErrN_shift_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) (ω : Fin n × ℕ → Bool) :
    |occErrN P pi x₀ (shiftFlips ω) s T - shiftMainTerm P H pi s T ω| ≤ ansBoundN H s T := by
  rw [← mainTermN_shiftFlips_eq hP hH s T ω]
  exact abs_occErrN_sub_mainTermN_le hP hH x₀ (shiftFlips ω) s T

/-- The occupation error is bounded: `|N_s(T) − T π_s| ≤ T + T |π_s|`. -/
theorem abs_occErrN_le (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) :
    |occErrN P pi x₀ f s T| ≤ T + T * |pi s| := by
  rw [occErrN]
  refine (abs_sub _ _).trans ?_
  rw [Nat.abs_cast, abs_mul, Nat.abs_cast]
  have : (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) ≤ T := by
    exact_mod_cast occCount_le _ s T
  linarith

/-- The occupation error of the shifted chain is in `L²`. -/
theorem memLp_occErrN_shift (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ s : Fin n) (T : ℕ) :
    MemLp (fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s T) 2 (shiftMeasure n) := by
  have hm : Measurable fun ω : Fin n × ℕ → Bool ↦ occErrN P pi x₀ (shiftFlips ω) s T :=
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
      (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ s T)).sub measurable_const
  exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact abs_occErrN_le P pi x₀ _ s T)

/-- `⌊log₂ T_k⌋ + 1 → ∞` along `T_k → ∞`. -/
theorem tendsto_natLog_add_one {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ Nat.le_succ _)
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun _ ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      hT)

/-- **The stacks CLT for n states, random digital shift** (post #3, code (ii)). For a stochastic
`P` on `Fin n` with Poisson data `H`, `π` for every target, a target `s`, and `T_k → ∞` with
`Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` eventually,
`(N_s(T_k) − T_k π_s) / √Var(N_s(T_k) − T_k π_s) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_occErrN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k); shiftMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k) /
      √Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k); shiftMeasure n]) atTop Z
      (fun _ ↦ shiftMeasure n) P' := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hγ : ∀ i j, Function.Injective (shiftLayout n i j) := fun i j d d' h ↦
    congrArg Prod.snd h
  refine tendstoInDistribution_of_close_main (E := fun k ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k))
    (M := fun k ω ↦ shiftMainTerm P H pi s (T k) ω) hT (b := fun k ↦ ansBoundN H s (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ ansBoundN_nonneg H s (T k))
      (fun k ↦ ansBoundN_le_log H s (T k)))
    (fun k ↦ memLp_occErrN_shift P pi x₀ s (T k))
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ↦ integral_levelSumN_coins hcp _ _ hγ)
    (fun k ω ↦ abs_occErrN_shift_sub_le hP hH x₀ s (T k) ω) hκ hvar ?_
  intro κ' hκ' hv
  exact tendstoInDistribution_levelSumN Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv hZ

/-- The constant `10 (nW)² + 8 C²` of the mean-square bound. -/
noncomputable def varConstN (H : Fin n → Fin n → ℝ) (s : Fin n) : ℝ :=
  10 * (n * cutWeightSum (H s)) ^ 2 + 8 * ansConstN H s ^ 2

/-- `2 ansBoundN² ≤ 8 C² (⌊log₂ T⌋ + 1)`: the Anscombe error is `o(√log T)` in mean square. -/
theorem two_mul_ansBoundN_sq_le (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) :
    2 * ansBoundN H s T ^ 2 ≤ 8 * ansConstN H s ^ 2 * ((Nat.log 2 T : ℝ) + 1) := by
  have h1 := ansBoundN_le_log H s T
  have h0 := ansBoundN_nonneg H s T
  have hy := natLog_add_one_sq_le (y := Nat.log 2 T + 1) (by omega)
  push_cast at hy
  have h2 : ansBoundN H s T ^ 2 ≤
      ansConstN H s ^ 2 * ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [mul_pow] at this
  nlinarith [sq_nonneg (ansConstN H s)]

/-- **Mean-square bound** (digital shift): `E[(N_s(T) − T π_s)²] ≤ C (⌊log₂ T⌋ + 1)`. -/
theorem integral_sq_occErrN_shift_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    ∫ ω, occErrN P pi x₀ (shiftFlips ω) s T ^ 2 ∂(shiftMeasure n) ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hV := integral_sq_levelSumN_le Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (w := cutWeight (H s)) (chainIdxN pi T) (Nat.log 2 T + 1)
  have h := integral_sq_le_of_close (memLp_occErrN_shift P pi x₀ s T)
    (memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (abs_occErrN_shift_sub_le hP hH x₀ s T) hV
  have hb := two_mul_ansBoundN_sq_le H s T
  refine h.trans ?_
  rw [varConstN]
  push_cast
  change 2 * (((Nat.log 2 T : ℝ) + 1) * (5 * (n * cutWeightSum (H s)) ^ 2)) +
    2 * ansBoundN H s T ^ 2 ≤ _
  nlinarith

/-- **Variance bound** (digital shift): `Var(N_s(T) − T π_s) ≤ C (⌊log₂ T⌋ + 1) = O(log T)`. -/
theorem variance_occErrN_shift_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s T; shiftMeasure n] ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) :=
  (variance_le_expectation_sq (memLp_occErrN_shift P pi x₀ s T).aestronglyMeasurable).trans
    (integral_sq_occErrN_shift_le hP hH x₀ s T)

/-- **RMSE of the occupation frequency is `O(√log T / T)`** (digital shift, n states):
`E[(N_s(T)/T − π_s)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_occFreqN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n) :
    (fun T : ℕ ↦ ∫ ω, (occErrN P pi x₀ (shiftFlips ω) s T / T) ^ 2 ∂(shiftMeasure n)) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 :=
  isBigO_meanSq_div_of_le (E := fun T ω ↦ occErrN P pi x₀ (shiftFlips ω) s T)
    (integral_sq_occErrN_shift_le hP hH x₀ s)

end RQMCMarkov.ScrambledStacks
