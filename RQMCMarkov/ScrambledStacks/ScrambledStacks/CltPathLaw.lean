/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltStacks
import Mathlib.Probability.IdentDistrib

/-!
# Two states: Owen's scramble and the digital shift give the same path law (post #3)

Post #3 treats codes (ii) (one Sobol sequence per state with a random digital shift) and (iii)
(Owen scrambling) side by side. `CltPathBits` showed that, for one threshold per row, the path
coins of Owen's scramble have the law of the digital-shift flips (`map_owenPathCoins`), so the
main term of the occupation error has the same law under both. Here the whole stack path is
shown to have the same law.

**Every decision is read off the path coins.** For every flip table `f`, every index `k` and
every threshold `c ∈ [0,1)`, `x_k ≤ c` iff the digits `bit_j(k) xor e_j` (the bits of `k`
flipped by the path coins `e_j = pathCoin f (threshDigit c) j`) are lexicographically `≤` the
digits of `c` (`scrambledVdc_le_iff_lexLeFrom_pathCoin`): while point `k` ties with `c` it sits
on the path of `c`, so its next digit is flipped by the next path coin, and after the first
disagreement nothing matters. So the comparison under `f` is the comparison under the digital
shift by the path coins (`scrambledVdc_le_iff_shiftTable`), for every real `c` (for `c < 0` and
`c ≥ 1` both sides are constant). There is no exceptional set: a point equal to `c`, and a
point whose digits are the second expansion of a dyadic `c` (`threshDigit` picks the terminating
one), are decided correctly by the lexicographic rule (`binaryVal_le_iff_lexLeFrom`).

For two states the update `step P i u` only compares `u` with `p_{i0}` and `p_{i0} + p_{i1} = 1`
(`step_congr_of_le_iff`), and a stack path only depends on the updates of its stack points
(`stackDrive_congr_of_forall`). Hence, for every flip table `f`, the path is the path of the
digitally shifted stacks with flips the path coins of `f` (`stackPath_eq_pathShift`). For any
path-coin model, in particular Owen's scramble and the digital shift, the path is
`coinPath P x₀` of the path coins (`IsPathCoinModel.stackPath_eq_coinPath`,
`stackPath_owen_eq_coinPath`), a measurable function (`measurable_coinPath`) of i.i.d. fair
coins. So the path laws on `ℕ → Fin 2` (product σ-algebra) coincide.

## Main results

* `scrambledVdc_le_iff_lexLeFrom_pathCoin`, `scrambledVdc_le_iff_shiftTable`,
  `scrambledVdc_le_congr_pathCoin`: the comparison with a threshold is a function of the path
  coins, for every flip table.
* `stackPath_eq_pathShift`: every pair of flip tables acts on a two-state chain as the digital
  shift by its path coins (every stochastic `P`, every flip table).
* `IsPathCoinModel.map_stackPath`, `map_stackPath_owen_eq_shift` (**law of the path**):
  `(owenMeasure 2).map (owen path) = (shiftMeasure 2).map (shift path)`;
  `identDistrib_stackPath_owen_shift`; `owenMeasure_stackPath_cylinder` (all cylinder
  probabilities agree).
* `identDistrib_comp_stackPath_owen_shift`: every measurable path functional has the same law;
  `measurable_occCount_path`, `measurable_transCount_path`; `identDistrib_occCount_owen_shift`,
  `identDistrib_transCount_owen_shift`.
* `identDistrib_occErr_owen_shift`, `variance_occErr_owen_eq_shift`: the occupation error has
  the same law, hence the same variance, for every `T`.
* `tendstoInDistribution_congr_identDistrib`, `tendstoInDistribution_occErr_owen_iff_shift`,
  `tendstoInDistribution_normalised_occErr_owen_iff_shift`: every limit theorem in distribution
  for the occupation error holds for Owen's scramble iff it holds for the digital shift; in
  particular the CLTs `tendstoInDistribution_occErr_owen` and `tendstoInDistribution_occErr_shift`
  are equivalent statements, with equivalent variance hypotheses.

**Hypotheses.** Only `IsStochastic P` (the positivity conditions `0 < p₀₁`, `0 < p₁₁` of
`CltStacks` are not needed here: thresholds `0` or `1` are handled directly).

**Correction** (of the "law equivalence" convention in `CltPathBits`, `CltVariance` and
`CltStacks`, which stated the same law of the main term only). For two-state chains the claim
is upgraded from "the main term has the same law under Owen's scramble and the digital shift"
to "the whole stack path has the same law", and with it the occupation error `occErr`, the
counts `occCount`, `transCount` and every measurable path functional, for every `T`. For three
states the path laws differ (`owen_ne_shift_stayThenMove`, `CltThreeState`): with two
thresholds in a row the two jump paths share digital-shift flips but use independent Owen flips
after they split.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Comparisons with a threshold through the path coins -/

/-- **Every comparison is decided along the path of the threshold** (every flip table). For
`c ∈ [0,1)`, point `k` is `≤ c` iff the bits of `k` flipped by the path coins of `c` are
lexicographically `≤` the digits of `c`. -/
theorem scrambledVdc_le_iff_lexLeFrom_pathCoin (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (k : ℕ) :
    scrambledVdc f k ≤ c ↔
      LexLeFrom (fun j ↦ xor (k.testBit j) (pathCoin f (threshDigit c) j)) (threshDigit c) 0 := by
  rw [scrambledVdc, binaryVal_le_iff_lexLeFrom hc0 hc1 (m := 0)
    fun i hi ↦ absurd hi (Nat.not_lt_zero i)]
  refine lexLeFrom_congr fun j _ hj ↦ ?_
  have hall : ∀ i < j, scrambledDigit f k i = threshDigit c i :=
    fun i hi ↦ hj i (Nat.zero_le i) hi
  have hkj := (tie_iff_mod_eq_pathPrefix f (threshDigit c) k j).1 hall
  rw [scrambledDigit, hkj]
  rfl

/-- **A flip table acts on one threshold as the digital shift by its path coins** (every flip
table, every real threshold). -/
theorem scrambledVdc_le_iff_shiftTable (f : ℕ → ℕ → Bool) (c : ℝ) (k : ℕ) :
    scrambledVdc f k ≤ c ↔ scrambledVdc (shiftTable (pathCoin f (threshDigit c))) k ≤ c := by
  have h1 := scrambledVdc_mem_Icc f k
  have h2 := scrambledVdc_mem_Icc (shiftTable (pathCoin f (threshDigit c))) k
  rcases lt_or_ge c 0 with hc | hc0
  · constructor <;> intro h
    · linarith [h1.1]
    · linarith [h2.1]
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [scrambledVdc_le_iff_lexLeFrom_pathCoin f hc0 hc1,
      scrambledVdc_le_iff_lexLeFrom_pathCoin _ hc0 hc1, pathCoin_shiftTable]
  · exact ⟨fun _ ↦ h2.2.trans hc1, fun _ ↦ h1.2.trans hc1⟩

/-- The comparison with a threshold is a function of the path coins: two flip tables with the
same path coins give the same comparisons, at every index. -/
theorem scrambledVdc_le_congr_pathCoin {f f' : ℕ → ℕ → Bool} (c : ℝ)
    (h : pathCoin f (threshDigit c) = pathCoin f' (threshDigit c)) (k : ℕ) :
    scrambledVdc f k ≤ c ↔ scrambledVdc f' k ≤ c := by
  rw [scrambledVdc_le_iff_shiftTable f, scrambledVdc_le_iff_shiftTable f', h]

/-! ### Stack paths through their decisions -/

/-- The inverse-CDF update only sees the comparisons of `u` with the cumulative sums. -/
theorem step_congr_of_le_iff {n : ℕ} (P : Fin n → Fin n → ℝ) (i : Fin n) {u u' : ℝ}
    (h : ∀ j : Fin n, u ≤ cumProb P i ((j : ℕ) + 1) ↔ u' ≤ cumProb P i ((j : ℕ) + 1)) :
    step P i u = step P i u' := by
  have e : (univ.filter fun j : Fin n ↦ u ≤ cumProb P i ((j : ℕ) + 1)) =
      univ.filter fun j : Fin n ↦ u' ≤ cumProb P i ((j : ℕ) + 1) :=
    Finset.filter_congr fun j _ ↦ h j
  unfold step
  simp only [e]

/-- A stack-driven path only depends on the updates of the stack entries. -/
theorem stackDrive_congr_of_forall {S α : Type*} [DecidableEq S] (G : S → α → S) (x₀ : S)
    {v v' : S → ℕ → α} (h : ∀ i k, G i (v i k) = G i (v' i k)) :
    stackDrive G x₀ v = stackDrive G x₀ v' := by
  have key : ∀ T, ∀ t ≤ T, stackDrive G x₀ v t = stackDrive G x₀ v' t := by
    intro T
    induction T with
    | zero =>
        intro t ht
        rw [Nat.le_zero.1 ht]
        rfl
    | succ T ih =>
        intro t ht
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with hlt | heq
        · exact ih t (Nat.lt_succ_iff.1 hlt)
        · rw [heq, stackDrive_succ, stackDrive_succ, h,
            departureIndex_congr (fun t' ht' ↦ ih t' ht'), ih T le_rfl]
  funext t
  exact key t t le_rfl

/-- `cumProb P i 1 = p_{i0}`. -/
theorem cumProb_one_eq_two_state (P : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : cumProb P i 1 = P i 0 := by
  have h := cumProb_succ P i 0
  rw [Fin.val_zero, zero_add, cumProb_zero, zero_add] at h
  exact h

/-- `cumProb P i 2 = 1` for a stochastic two-state `P`. -/
theorem cumProb_two_eq_two_state {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (i : Fin 2) :
    cumProb P i 2 = 1 := by
  have h := cumProb_succ P i 1
  change cumProb P i 2 = cumProb P i 1 + P i 1 at h
  rw [h, cumProb_one_eq_two_state, ← Fin.sum_univ_two (fun j ↦ P i j), hP.sum_eq_one i]

/-- The digital-shift tables given by the path coins of `f` along the thresholds `p₀₀`, `p₁₀`. -/
noncomputable def pathShift (P : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → ℕ → ℕ → Bool) :
    Fin 2 → ℕ → ℕ → Bool :=
  fun i ↦ shiftTable (pathCoin (f i) (threshDigit (P i 0)))

/-- **Every flip table acts on a two-state chain as a digital shift** (every stochastic `P`,
every flip table): the stack path is the path of the digitally shifted stacks whose flips are
the path coins of `f`. -/
theorem stackPath_eq_pathShift {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) :
    stackPath P x₀ (scrambledStack f) = stackPath P x₀ (scrambledStack (pathShift P f)) := by
  refine stackDrive_congr_of_forall _ _ fun i k ↦ step_congr_of_le_iff P i
    (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change scrambledVdc (f i) k ≤ cumProb P i 1 ↔ scrambledVdc (pathShift P f i) k ≤ cumProb P i 1
    rw [cumProb_one_eq_two_state]
    exact scrambledVdc_le_iff_shiftTable (f i) (P i 0) k
  · change scrambledVdc (f i) k ≤ cumProb P i 2 ↔ scrambledVdc (pathShift P f i) k ≤ cumProb P i 2
    rw [cumProb_two_eq_two_state hP]
    exact ⟨fun _ ↦ (scrambledVdc_mem_Icc _ k).2, fun _ ↦ (scrambledVdc_mem_Icc _ k).2⟩

/-! ### The path as a function of the path coins -/

/-- The stack path of the digitally shifted stacks with flips `w`: the two-state path as a
function of the path coins. -/
noncomputable def coinPath (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (w : Fin 2 × ℕ → Bool) :
    ℕ → Fin 2 :=
  stackPath P x₀ (scrambledStack (shiftFlips w))

/-- `coinPath` is measurable (product σ-algebra on paths). -/
theorem measurable_coinPath (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) :
    Measurable (coinPath P x₀) :=
  measurable_pi_iff.2 fun t ↦
    measurable_stackPath_of (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ t

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- In a path-coin model the shift tables of the path coins are the digital shift by `Ψ ω`. -/
theorem IsPathCoinModel.pathShift_eq (hM : IsPathCoinModel P μ F Ψ) (ω : Ω) :
    pathShift P (F ω) = shiftFlips (Ψ ω) := by
  funext i
  change shiftTable (pathCoin (F ω i) (threshDigit (P i 0))) = shiftTable fun j ↦ Ψ ω (i, j)
  congr 1
  funext j
  exact hM.pathCoin_eq ω (i, j)

/-- **The path is a function of the path coins** in every path-coin model. -/
theorem IsPathCoinModel.stackPath_eq_coinPath (hM : IsPathCoinModel P μ F Ψ)
    (hP : IsStochastic P) (x₀ : Fin 2) (ω : Ω) :
    stackPath P x₀ (scrambledStack (F ω)) = coinPath P x₀ (Ψ ω) := by
  rw [stackPath_eq_pathShift hP, hM.pathShift_eq]
  rfl

/-- The stack path is measurable in every path-coin model. -/
theorem IsPathCoinModel.measurable_stackPath (hM : IsPathCoinModel P μ F Ψ) (x₀ : Fin 2) :
    Measurable fun ω ↦ stackPath P x₀ (scrambledStack (F ω)) :=
  measurable_pi_iff.2 fun t ↦ measurable_stackPath_of hM.measurable_stack P x₀ t

/-- **The law of the path in a path-coin model** is the image of the fair coins under
`coinPath`. -/
theorem IsPathCoinModel.map_stackPath (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (x₀ : Fin 2) :
    μ.map (fun ω ↦ stackPath P x₀ (scrambledStack (F ω))) =
      (shiftMeasure 2).map (coinPath P x₀) := by
  have e : (fun ω ↦ stackPath P x₀ (scrambledStack (F ω))) = coinPath P x₀ ∘ Ψ :=
    funext fun ω ↦ hM.stackPath_eq_coinPath hP x₀ ω
  rw [e, ← Measure.map_map (measurable_coinPath P x₀) hM.measurePreserving.measurable,
    hM.measurePreserving.map_eq]

/-- Any two path-coin models give identically distributed paths. -/
theorem IsPathCoinModel.identDistrib_stackPath {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} {F' : Ω' → Fin 2 → ℕ → ℕ → Bool} {Ψ' : Ω' → Fin 2 × ℕ → Bool}
    (hM : IsPathCoinModel P μ F Ψ) (hM' : IsPathCoinModel P μ' F' Ψ') (hP : IsStochastic P)
    (x₀ : Fin 2) :
    IdentDistrib (fun ω ↦ stackPath P x₀ (scrambledStack (F ω)))
      (fun ω ↦ stackPath P x₀ (scrambledStack (F' ω))) μ μ' where
  aemeasurable_fst := (hM.measurable_stackPath x₀).aemeasurable
  aemeasurable_snd := (hM'.measurable_stackPath x₀).aemeasurable
  map_eq := by rw [hM.map_stackPath hP, hM'.map_stackPath hP]

/-! ### Owen's scramble and the digital shift -/

/-- **Owen's path is the digital-shift path of the Owen path coins**, for every `ω`. -/
theorem stackPath_owen_eq_coinPath (hP : IsStochastic P) (x₀ : Fin 2)
    (ω : Fin 2 × ℕ × ℕ → Bool) :
    stackPath P x₀ (scrambledStack (owenTable ω)) =
      coinPath P x₀ (owenPathCoins (chainDigits P) ω) :=
  (isPathCoinModel_owen P).stackPath_eq_coinPath hP x₀ ω

/-- The digital-shift path is `coinPath` of the flips. -/
theorem stackPath_shift_eq_coinPath (x₀ : Fin 2) (ω : Fin 2 × ℕ → Bool) :
    stackPath P x₀ (scrambledStack (shiftFlips ω)) = coinPath P x₀ ω := rfl

/-- **Law equivalence of the paths** (post #3, codes (ii) and (iii), two states): the stack path
driven by Owen-scrambled stacks and the one driven by digitally shifted stacks have the same
law on `ℕ → Fin 2`. -/
theorem map_stackPath_owen_eq_shift (hP : IsStochastic P) (x₀ : Fin 2) :
    (owenMeasure 2).map (fun ω ↦ stackPath P x₀ (scrambledStack (owenTable ω))) =
      (shiftMeasure 2).map (fun ω ↦ stackPath P x₀ (scrambledStack (shiftFlips ω))) := by
  rw [(isPathCoinModel_owen P).map_stackPath hP, (isPathCoinModel_shift P).map_stackPath hP]

/-- The Owen and digital-shift paths are identically distributed. -/
theorem identDistrib_stackPath_owen_shift (hP : IsStochastic P) (x₀ : Fin 2) :
    IdentDistrib (fun ω ↦ stackPath P x₀ (scrambledStack (owenTable ω)))
      (fun ω ↦ stackPath P x₀ (scrambledStack (shiftFlips ω))) (owenMeasure 2)
      (shiftMeasure 2) :=
  (isPathCoinModel_owen P).identDistrib_stackPath (isPathCoinModel_shift P) hP x₀

/-- **Cylinder probabilities agree**: for every horizon `T` and every finite path `s`,
`P(x_t = s_t, t ≤ T)` is the same under Owen's scramble and under the digital shift. -/
theorem owenMeasure_stackPath_cylinder (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ)
    (s : ℕ → Fin 2) :
    owenMeasure 2 {ω | ∀ t ≤ T, stackPath P x₀ (scrambledStack (owenTable ω)) t = s t} =
      shiftMeasure 2 {ω | ∀ t ≤ T, stackPath P x₀ (scrambledStack (shiftFlips ω)) t = s t} := by
  have hs : MeasurableSet {p : ℕ → Fin 2 | ∀ t ≤ T, p t = s t} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun t ↦ ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun _ ↦ ?_
    change MeasurableSet ((fun p : ℕ → Fin 2 ↦ p t) ⁻¹' {s t})
    exact (measurableSet_singleton (s t)).preimage (measurable_pi_apply t)
  exact (identDistrib_stackPath_owen_shift hP x₀).measure_mem_eq hs

/-- **Every measurable path functional has the same law** under Owen's scramble and the
digital shift. -/
theorem identDistrib_comp_stackPath_owen_shift {β : Type*} [MeasurableSpace β]
    (hP : IsStochastic P) (x₀ : Fin 2) {G : (ℕ → Fin 2) → β} (hG : Measurable G) :
    IdentDistrib (fun ω ↦ G (stackPath P x₀ (scrambledStack (owenTable ω))))
      (fun ω ↦ G (stackPath P x₀ (scrambledStack (shiftFlips ω)))) (owenMeasure 2)
      (shiftMeasure 2) :=
  (identDistrib_stackPath_owen_shift hP x₀).comp hG

/-! ### Counts and the occupation error -/

/-- The occupation count is a measurable path functional. -/
theorem measurable_occCount_path (i : Fin 2) (T : ℕ) :
    Measurable fun p : ℕ → Fin 2 ↦ occCount p i T := by
  have hloc : IsLocal (fun p : ℕ → Fin 2 ↦ occCount p i T) (range T) :=
    fun p q h ↦ occCount_congr (fun t ht ↦ h t (mem_range.2 ht)) i
  exact hloc.measurable

/-- The transition count is a measurable path functional. -/
theorem measurable_transCount_path (i j : Fin 2) (T : ℕ) :
    Measurable fun p : ℕ → Fin 2 ↦ transCount p i j T := by
  have hloc : IsLocal (fun p : ℕ → Fin 2 ↦ transCount p i j T) (range (T + 1)) :=
    fun p q h ↦ transCount_congr (fun t ht ↦ h t (mem_range.2 (Nat.lt_succ_of_le ht))) i j
  exact hloc.measurable

/-- The occupation counts have the same law under Owen's scramble and the digital shift. -/
theorem identDistrib_occCount_owen_shift (hP : IsStochastic P) (x₀ i : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ occCount (stackPath P x₀ (scrambledStack (owenTable ω))) i T)
      (fun ω ↦ occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i T) (owenMeasure 2)
      (shiftMeasure 2) :=
  identDistrib_comp_stackPath_owen_shift hP x₀ (measurable_occCount_path i T)

/-- The transition counts have the same law under Owen's scramble and the digital shift. -/
theorem identDistrib_transCount_owen_shift (hP : IsStochastic P) (x₀ i j : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ transCount (stackPath P x₀ (scrambledStack (owenTable ω))) i j T)
      (fun ω ↦ transCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i j T)
      (owenMeasure 2) (shiftMeasure 2) :=
  identDistrib_comp_stackPath_owen_shift hP x₀ (measurable_transCount_path i j T)

/-- **The occupation error has the same law** under Owen's scramble and the digital shift, for
every `T`. -/
theorem identDistrib_occErr_owen_shift (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ occErr P x₀ (owenTable ω) T) (fun ω ↦ occErr P x₀ (shiftFlips ω) T)
      (owenMeasure 2) (shiftMeasure 2) := by
  have hG : Measurable fun p : ℕ → Fin 2 ↦ (occCount p 0 T : ℝ) - T * piZero P :=
    ((measurable_from_nat (f := fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_occCount_path 0 T)).sub measurable_const
  exact identDistrib_comp_stackPath_owen_shift hP x₀ hG

/-- **Equal variances** of the occupation error under Owen's scramble and the digital shift. -/
theorem variance_occErr_owen_eq_shift (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ) :
    Var[fun ω ↦ occErr P x₀ (owenTable ω) T; owenMeasure 2] =
      Var[fun ω ↦ occErr P x₀ (shiftFlips ω) T; shiftMeasure 2] :=
  (identDistrib_occErr_owen_shift hP x₀ T).variance_eq

/-! ### Limit theorems transfer -/

/-- Convergence in distribution only depends on the laws of the terms. -/
theorem tendstoInDistribution_congr_identDistrib {Ω₁ Ω₂ Ω' : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω'] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {l : Filter ℕ} {X : ℕ → Ω₁ → ℝ} {Y : ℕ → Ω₂ → ℝ} {Z : Ω' → ℝ}
    (h : ∀ k, IdentDistrib (X k) (Y k) μ₁ μ₂) :
    TendstoInDistribution X l Z (fun _ ↦ μ₁) P' ↔ TendstoInDistribution Y l Z (fun _ ↦ μ₂) P' := by
  constructor
  · intro hX
    exact ⟨fun k ↦ (h k).aemeasurable_snd, hX.aemeasurable_limit,
      Tendsto.congr (fun k ↦ Subtype.ext (h k).map_eq) hX.tendsto⟩
  · intro hY
    exact ⟨fun k ↦ (h k).aemeasurable_fst, hY.aemeasurable_limit,
      Tendsto.congr (fun k ↦ Subtype.ext (h k).map_eq.symm) hY.tendsto⟩

/-- **Limit laws of the occupation error transfer** between Owen's scramble and the digital
shift: for every time sequence `T_k`, every sequence of measurable maps `u_k` (e.g.
normalisations) and every limit `Z`, `u_k(N₀(T_k) − T_k π₀)` converges in distribution to `Z`
under Owen's scramble iff it does under the digital shift. -/
theorem tendstoInDistribution_occErr_owen_iff_shift (hP : IsStochastic P) (x₀ : Fin 2)
    (T : ℕ → ℕ) {u : ℕ → ℝ → ℝ} (hu : ∀ k, Measurable (u k)) {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ} :
    TendstoInDistribution (fun k ω ↦ u k (occErr P x₀ (owenTable ω) (T k))) atTop Z
        (fun _ ↦ owenMeasure 2) P' ↔
      TendstoInDistribution (fun k ω ↦ u k (occErr P x₀ (shiftFlips ω) (T k))) atTop Z
        (fun _ ↦ shiftMeasure 2) P' :=
  tendstoInDistribution_congr_identDistrib fun k ↦
    (identDistrib_occErr_owen_shift hP x₀ (T k)).comp (hu k)

/-- **The two CLTs are the same statement**: the occupation error normalised by its own
standard deviation converges in distribution to `Z` under Owen's scramble iff it does under the
digital shift (and the variances, hence the variance hypotheses of
`tendstoInDistribution_occErr_owen` and `tendstoInDistribution_occErr_shift`, agree:
`variance_occErr_owen_eq_shift`). -/
theorem tendstoInDistribution_normalised_occErr_owen_iff_shift (hP : IsStochastic P)
    (x₀ : Fin 2) (T : ℕ → ℕ) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (owenTable ω) (T k) /
        √Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2]) atTop Z
        (fun _ ↦ owenMeasure 2) P' ↔
      TendstoInDistribution (fun k ω ↦ occErr P x₀ (shiftFlips ω) (T k) /
        √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2]) atTop Z
        (fun _ ↦ shiftMeasure 2) P' := by
  have hv : ∀ k, Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2] =
      Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2] :=
    fun k ↦ variance_occErr_owen_eq_shift hP x₀ (T k)
  simp only [hv]
  exact tendstoInDistribution_occErr_owen_iff_shift hP x₀ T
    (u := fun k x ↦ x / √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2])
    fun k ↦ measurable_id.div_const _

end RQMCMarkov.ScrambledStacks
