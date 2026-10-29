/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.CUDDefs
import MarkovDriving.Driving

/-! # Chentsov's theorem: CUD driving gives consistent occupation frequencies

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". We prove this for a finite chain simulated by the inverse-CDF update
`step P` (`MarkovDriving.Driving`), under a **coupling-region** hypothesis, following the
coupling argument of Chentsov (1967) as presented by Owen–Tribble (2005) and Chen–Dick–Owen
(2011, Definition 6, where `d = 1`).

**Definitions.**
* `windowMap P m i w`: the state reached from `i` after `m` inverse-CDF steps driven by the
  uniforms `w 0, …, w (m-1)`; `drivenPath P x₀ u (t + m) = windowMap P m (x_t) (window u m t)`
  (`drive_add_eq_windowMap`).
* `multiStep P m i j`: the `m`-step transition probability (`multiStep_eq_pow`: it is `(Pᵐ) i j`).
* `HasCouplingBox P d`: there is a box `B ⊆ [0,1)^d` of positive volume (sides open, closed or
  half-open) and a state `j₀` such that `windowMap P d i w = j₀` for **every** start `i` whenever
  `w ∈ B`: `d` steps driven by uniforms in `B` forget the starting state.

**Results.**
* `isStepFn_windowMap`: `w ↦ 1{windowMap P m i w = j}` is a step function on `[0,1)^m` (a finite
  union of boxes, one per path `i → ⋯ → j`) with integral `multiStep P m i j`.
* `tendsto_occFreq_of_isCUD`: **Chentsov's theorem (coupling form).** If `u` is CUD, `P` is
  stochastic and has a coupling box, and `π` is a stationary distribution, then for every start
  `x₀` and state `j`, `N_j(T)/T → π_j` (`N_j(T) = occCount`, visits before `T`).
* `tendsto_timeAvg_of_isCUD`: time averages `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`.
* `hasCouplingBox_of_common_interval`, `hasCouplingBox_of_col_pos`, `hasCouplingBox_of_pos`: a
  one-step coupling box exists when the intervals of some state `j₀` in all rows share a
  subinterval; in particular when the column of the first state is bounded below by `c > 0` (a
  Doeblin condition realised by a common interval of uniforms), e.g. when all entries are
  positive.
* `tendsto_occFreq_of_isCUD_of_col_pos`: the theorem under that condition.
* `not_tendsto_occFreq_identity`: counterexample for a reducible chain (see **Correction**).
* `multiStep_fourState_two`, `not_hasCouplingBox_fourState`: a perfectly mixing chain
  (`P² = (1/4)·𝟙`) without any coupling box (see **Correction**).

**The proof.** With `m = d k`, `x_{t+m} = windowMap P m (x_t) (window u m t)`. If none of the `k`
aligned blocks of the window lies in the coupling box (`noCouple`, a step function with
integral `(1-δ)^k`, `δ = vol B`), the window may remember `x_t`; otherwise `x_{t+m}` equals
`windowMap P m r (window u m t)` for any fixed `r`. CUD gives the frequencies of both events, so
`N_j(T)/T` is eventually within `2(1-δ)^k + ε` of `π_j`; the bound `|Pᵐ(r,j) - π_j| ≤ (1-δ)^k`
(`abs_multiStep_sub_le`) comes from the same coupling read through the CUD frequencies.

**Correction (post #3).** The claim is stated without conditions on the chain. Some condition is
needed: for a reducible chain the frequencies depend on the start whatever the driving sequence,
e.g. the identity matrix on two states, where every driven path is constant
(`not_tendsto_occFreq_identity`: the frequency of state `0` from state `0` is `1`, while the
uniform vector is stationary). We prove the theorem under the coupling-box hypothesis. This is
**not** implied by irreducibility and aperiodicity, nor by a Doeblin minorisation of `P` alone:
`fourState` is a doubly stochastic chain with `P² = (1/4)·𝟙` (perfect mixing in two steps) whose
inverse-CDF grand coupling never coalesces (`not_hasCouplingBox_fourState`), because each update
sends the blocks `{0,2}` and `{1,3}` to different blocks. The coupling hypothesis is only a
convenience of this proof: `ChentsovGeneral` proves the theorem for **every** finite chain with a
unique stationary distribution (`tendsto_occFreq_of_isCUD_general`, by an entropy argument,
`ChentsovEntropy`), so `fourState` is consistent too (`tendsto_occFreq_fourState_of_isCUD`). The
corrected claim of post #3 is: *with the inverse-CDF update, driving a finite chain by a CUD
sequence gives occupation frequencies and time averages converging to `π` whenever the stationary
distribution `π` is unique* (e.g. irreducible `P`; aperiodicity is not needed). Periodic chains do
not refute the claim: the deterministic two-cycle is consistent for every driving sequence.
CUD sequences exist (`CUDExistence.exists_isCUD`: i.i.d. uniforms are CUD almost surely).
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

variable {n : ℕ}

/-- The state reached from `i` after `m` inverse-CDF steps driven by `w 0, …, w (m-1)`. -/
noncomputable def windowMap (P : Fin n → Fin n → ℝ) : (m : ℕ) → Fin n → (Fin m → ℝ) → Fin n
  | 0, i, _ => i
  | m + 1, i, w => step P (windowMap P m i fun k => w (Fin.castSucc k)) (w (Fin.last m))

/-- One step of `windowMap`. -/
theorem windowMap_succ (P : Fin n → Fin n → ℝ) (m : ℕ) (i : Fin n) (w : Fin (m + 1) → ℝ) :
    windowMap P (m + 1) i w =
      step P (windowMap P m i fun k => w (Fin.castSucc k)) (w (Fin.last m)) :=
  rfl

/-- **Composition.** Driving `m + m'` steps is driving `m` steps and then `m'` steps. -/
theorem windowMap_add (P : Fin n → Fin n → ℝ) (m m' : ℕ) (i : Fin n) (w : Fin (m + m') → ℝ) :
    windowMap P (m + m') i w = windowMap P m' (windowMap P m i fun k => w (Fin.castAdd m' k))
      (fun k => w (Fin.natAdd m k)) := by
  induction m' generalizing i with
  | zero => rfl
  | succ m' ih =>
    change step P (windowMap P (m + m') i fun k => w (Fin.castSucc k)) (w (Fin.last (m + m'))) =
      step P (windowMap P m' (windowMap P m i fun k => w (Fin.castAdd (m' + 1) k))
        fun k => w (Fin.natAdd m (Fin.castSucc k))) (w (Fin.natAdd m (Fin.last m')))
    rw [ih]
    rfl

/-- The driven path after `m` more steps is `windowMap` of the window of uniforms. -/
theorem drive_add_eq_windowMap (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) (t m : ℕ) :
    drivenPath P x₀ u (t + m) = windowMap P m (drivenPath P x₀ u t) (window u m t) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change step P (drivenPath P x₀ u (t + m)) (u (t + m)) = _
    rw [ih]
    rfl

/-- The `m`-step transition probabilities, by the Chapman–Kolmogorov recursion
`Pᵐ⁺¹(i,j) = ∑ₖ Pᵐ(i,k) P(k,j)`. -/
noncomputable def multiStep (P : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0, i, j => if i = j then 1 else 0
  | m + 1, i, j => ∑ k, multiStep P m i k * P k j

/-- `multiStep P m` is the matrix power `Pᵐ`. -/
theorem multiStep_eq_pow (P : Fin n → Fin n → ℝ) (m : ℕ) (i j : Fin n) :
    multiStep P m i j = (Matrix.of P ^ m) i j := by
  induction m generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    rfl
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [ih, Matrix.of_apply]

/-- A stationary vector is stationary for every `Pᵐ`. -/
theorem sum_mul_multiStep {P : Fin n → Fin n → ℝ} {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (m : ℕ) (j : Fin n) :
    ∑ i, π i * multiStep P m i j = π j := by
  induction m generalizing j with
  | zero =>
    change ∑ i, π i * (if i = j then 1 else 0) = π j
    rw [Finset.sum_eq_single j (fun i _ hij => by simp only [hij, ↓reduceIte, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp only [↓reduceIte, mul_one]
  | succ m ih =>
    change ∑ i, π i * ∑ k, multiStep P m i k * P k j = π j
    calc ∑ i, π i * ∑ k, multiStep P m i k * P k j
        = ∑ k, (∑ i, π i * multiStep P m i k) * P k j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      _ = π j := by
          rw [← hπ j]
          exact Finset.sum_congr rfl fun k _ => by rw [ih k]

/-- At `u = 0` the inverse-CDF update goes to the first state. -/
theorem val_step_zero (P : Fin n → Fin n → ℝ) (hP : IsStochastic P) (i : Fin n) :
    ((step P i 0 : Fin n) : ℕ) = 0 := by
  have h0 : (⟨0, by have := i.isLt; omega⟩ : Fin n) ∈
      insert (lastState i) (univ.filter fun j : Fin n ↦ (0 : ℝ) ≤ cumProb P i (j + 1)) :=
    Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (cumProb_mem_Icc hP i _).1⟩)
  have hle := Finset.min'_le _ _ h0
  have : step P i 0 ≤ (⟨0, by have := i.isLt; omega⟩ : Fin n) := hle
  rw [Fin.le_def] at this
  exact Nat.le_zero.1 this

/-- The set `{u : step P i u = j}` is a side between `cs_{i,j}` and `cs_{i,j+1}`. -/
theorem isSide_step {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    IsSide {u | step P i u = j} (cumProb P i j) (cumProb P i (j + 1)) := by
  refine ⟨(cumProb_mem_Icc hP i _).1, cumProb_mono hP.nonneg i (Nat.le_succ _),
    (cumProb_mem_Icc hP i _).2, fun u hu => ?_, fun u hu => ?_⟩
  · have hu' : u ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (cumProb_mem_Icc hP i j).1 hu.1, hu.2.le.trans (cumProb_mem_Icc hP i _).2⟩
    exact (step_eq_iff hP i j hu').2 ⟨hu.1, hu.2.le⟩
  · rcases hu with ⟨hstep, hu0, hu1⟩
    rcases hu0.lt_or_eq with hpos | hzero
    · have h := (step_eq_iff hP i j ⟨hpos, hu1.le⟩).1 hstep
      exact ⟨h.1.le, h.2⟩
    · subst hzero
      have hj : (j : ℕ) = 0 := by
        rw [← hstep]
        exact val_step_zero P hP i
      refine ⟨?_, (cumProb_mem_Icc hP i _).1⟩
      rw [hj, cumProb_zero]

/-- One step: `v ↦ 1{step P i (v 0) = j}` is a step function on `[0,1)` with integral `P i j`. -/
theorem isStepFn_step {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    IsStepFn 1 (fun v => if step P i (v 0) = j then 1 else 0) (P i j) := by
  refine ((isStepFn_boxInd (S := fun _ => {u | step P i u = j})
    (a := fun _ => cumProb P i j) (b := fun _ => cumProb P i (j + 1))
    fun _ => isSide_step hP i j).congr fun v _ => ?_).of_eq ?_
  · classical
    rw [boxInd_eq_ite]
    by_cases h : step P i (v 0) = j
    · have h' : ∀ k : Fin 1, v k ∈ {u | step P i u = j} := fun k => by
        rw [Fin.fin_one_eq_zero k]; exact h
      simp only [h, h', ↓reduceIte, implies_true]
    · have h' : ¬ ∀ k : Fin 1, v k ∈ {u | step P i u = j} := fun hk => h (hk 0)
      simp only [h, h', ↓reduceIte]
  · rw [Fin.prod_univ_one, cumProb_succ, add_sub_cancel_left]

/-- **The `m`-step event is a finite union of boxes.** `w ↦ 1{windowMap P m i w = j}` is a step
function on `[0,1)^m` with integral `Pᵐ(i,j)`. -/
theorem isStepFn_windowMap {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (m : ℕ)
    (i j : Fin n) :
    IsStepFn m (fun w => if windowMap P m i w = j then 1 else 0) (multiStep P m i j) := by
  induction m generalizing j with
  | zero => exact isStepFn_const 0 (if i = j then 1 else 0)
  | succ m ih =>
    have hsum := isStepFn_finset_sum (Finset.univ : Finset (Fin n))
      (fun k _ => (ih k).append (isStepFn_step hP k j))
    refine (hsum.congr fun w _ => ?_).of_eq rfl
    change ∑ k, (if windowMap P m i (fun r => w (Fin.castSucc r)) = k then (1 : ℝ) else 0) *
        (if step P k (w (Fin.last m)) = j then 1 else 0) =
      if step P (windowMap P m i fun r => w (Fin.castSucc r)) (w (Fin.last m)) = j then 1 else 0
    rw [Finset.sum_eq_single (windowMap P m i fun r => w (Fin.castSucc r))
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]

/-- **Coupling box** (Owen–Tribble 2005; Chen–Dick–Owen 2011, Definition 6, for `d = 1`): a box
`B = ∏ₖ Sₖ ⊆ [0,1)^d` of positive volume and a state `j₀` such that `d` inverse-CDF steps driven
by any `w ∈ B` end in `j₀` from every starting state. -/
def HasCouplingBox (P : Fin n → Fin n → ℝ) (d : ℕ) : Prop :=
  ∃ (S : Fin d → Set ℝ) (a b : Fin d → ℝ) (j₀ : Fin n),
    (∀ k, IsSide (S k) (a k) (b k)) ∧ 0 < ∏ k, (b k - a k) ∧
    ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀

/-- The indicator that none of the `k` aligned blocks of length `d` of `w` lies in the box
`∏ S`. -/
noncomputable def noCouple {d : ℕ} (S : Fin d → Set ℝ) : (k : ℕ) → (Fin (d * k) → ℝ) → ℝ
  | 0, _ => 1
  | k + 1, w => noCouple S k (fun r => w (Fin.castAdd d r)) *
      (1 - boxInd S fun r => w (Fin.natAdd (d * k) r))

/-- `noCouple` is a step function with integral `(1 - vol B)^k`. -/
theorem isStepFn_noCouple {d : ℕ} {S : Fin d → Set ℝ} {a b : Fin d → ℝ}
    (hS : ∀ k, IsSide (S k) (a k) (b k)) (k : ℕ) :
    IsStepFn (d * k) (noCouple S k) ((1 - ∏ r, (b r - a r)) ^ k) := by
  induction k with
  | zero => exact (isStepFn_const 0 1).of_eq (pow_zero _).symm
  | succ k ih =>
    exact (ih.append ((isStepFn_const d 1).sub (isStepFn_boxInd hS))).of_eq (pow_succ _ _).symm

/-- `noCouple` takes the values `0` and `1`. -/
theorem noCouple_eq_zero_or_one {d : ℕ} (S : Fin d → Set ℝ) (k : ℕ) (w : Fin (d * k) → ℝ) :
    noCouple S k w = 0 ∨ noCouple S k w = 1 := by
  induction k with
  | zero => exact Or.inr rfl
  | succ k ih =>
    have hdef : noCouple S (k + 1) w = noCouple S k (fun r => w (Fin.castAdd d r)) *
        (1 - boxInd S fun r => w (Fin.natAdd (d * k) r)) := rfl
    rw [hdef]
    classical
    rw [boxInd_eq_ite]
    rcases ih (fun r => w (Fin.castAdd d r)) with h | h <;> rw [h] <;> split_ifs <;> norm_num

/-- If some aligned block of `w` lies in the coupling box (`noCouple = 0`), then `d k` steps
driven by `w` end in the same state from every start. -/
theorem windowMap_eq_of_noCouple_eq_zero {P : Fin n → Fin n → ℝ} {d : ℕ} {S : Fin d → Set ℝ}
    {j₀ : Fin n} (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (w : Fin (d * k) → ℝ) (hw : InUnitCube w) (h0 : noCouple S k w = 0) (i i' : Fin n) :
    windowMap P (d * k) i w = windowMap P (d * k) i' w := by
  induction k with
  | zero => exact absurd h0 one_ne_zero
  | succ k ih =>
    change windowMap P (d * k + d) i w = windowMap P (d * k + d) i' w
    rw [windowMap_add, windowMap_add]
    change noCouple S k (fun r => w (Fin.castAdd d r)) *
      (1 - boxInd S fun r => w (Fin.natAdd (d * k) r)) = 0 at h0
    rcases mul_eq_zero.1 h0 with h | h
    · rw [ih (fun r => w (Fin.castAdd d r)) (fun r => hw _) h]
    · have hbox := (boxInd_eq_one_iff S _).1 (sub_eq_zero.1 h).symm
      rw [hC _ (fun r => hw _) hbox, hC _ (fun r => hw _) hbox]

/-- The two event indicators differ by at most `noCouple`. -/
theorem abs_ind_sub_le_noCouple {P : Fin n → Fin n → ℝ} {d : ℕ} {S : Fin d → Set ℝ}
    {j₀ : Fin n} (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (w : Fin (d * k) → ℝ) (hw : InUnitCube w) (i i' j : Fin n) :
    |(if windowMap P (d * k) i w = j then (1 : ℝ) else 0) -
      (if windowMap P (d * k) i' w = j then 1 else 0)| ≤ noCouple S k w := by
  rcases noCouple_eq_zero_or_one S k w with h | h
  · rw [windowMap_eq_of_noCouple_eq_zero hC k w hw h i i', sub_self, abs_zero, h]
  · rw [h]
    split_ifs <;> norm_num

/-- **Coupling bound for `Pᵐ`.** Read through the frequencies of a CUD sequence, the coupling
gives `|Pᵈᵏ(i,j) - Pᵈᵏ(i',j)| ≤ (1 - vol B)^k`. -/
theorem abs_multiStep_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} {S : Fin d → Set ℝ} {a b : Fin d → ℝ} {j₀ : Fin n}
    (hS : ∀ k, IsSide (S k) (a k) (b k))
    (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (i i' j : Fin n) :
    |multiStep P (d * k) i j - multiStep P (d * k) i' j| ≤ (1 - ∏ r, (b r - a r)) ^ k := by
  have hW := hu.isUD_window (d * k)
  have h1 := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP (d * k) i j)
  have h2 := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP (d * k) i' j)
  have h3 := tendsto_empAvg_of_isStepFn hW (isStepFn_noCouple hS k)
  refine le_of_tendsto_of_tendsto' (h1.sub h2).abs h3 fun N => ?_
  unfold empAvg
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ => ?_)) (Nat.cast_nonneg N)
  exact abs_ind_sub_le_noCouple hC k _ (hW.1 t) i i' j

/-- The occupation count as a sum of indicators. -/
theorem occCount_eq_sum (path : ℕ → Fin n) (j : Fin n) (T : ℕ) :
    (occCount path j T : ℝ) = ∑ t ∈ range T, if path t = j then (1 : ℝ) else 0 := by
  unfold occCount
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ => by
    split_ifs
    · exact Nat.cast_one
    · exact Nat.cast_zero

/-- Shifting a `[0,1]`-valued sum by `m` changes it by at most `m`. -/
theorem abs_sum_shift_sub_le (g : ℕ → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (N m : ℕ) :
    |∑ t ∈ range N, g (t + m) - ∑ t ∈ range N, g t| ≤ m := by
  have h1 := Finset.sum_range_add g m N
  have h2 := Finset.sum_range_add g N m
  rw [add_comm m N] at h1
  have heq : ∑ t ∈ range N, g (t + m) = ∑ t ∈ range N, g (m + t) :=
    Finset.sum_congr rfl fun t _ => by rw [add_comm]
  have hA : 0 ≤ ∑ t ∈ range m, g (N + t) := Finset.sum_nonneg fun t _ => hg0 _
  have hB : 0 ≤ ∑ t ∈ range m, g t := Finset.sum_nonneg fun t _ => hg0 _
  have hA' : ∑ t ∈ range m, g (N + t) ≤ m := by
    have := Finset.sum_le_sum fun t (_ : t ∈ range m) => hg1 (N + t)
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  have hB' : ∑ t ∈ range m, g t ≤ m := by
    have := Finset.sum_le_sum fun t (_ : t ∈ range m) => hg1 t
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  rw [heq, abs_le]
  constructor <;> linarith

/-- **Chentsov's theorem, coupling form** (post #3; Chentsov 1967; Owen–Tribble 2005). Let `P`
be a stochastic matrix on `Fin n` with a coupling box for the inverse-CDF update, `π` a
stationary distribution, and `u` a CUD sequence. Then the path driven by `u` from any start
`x₀` has occupation frequencies `N_j(T)/T → π_j`. -/
theorem tendsto_occFreq_of_isCUD {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} (hC : HasCouplingBox P d) {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  obtain ⟨S, a, b, j₀, hS, hδ, hcpl⟩ := hC
  set δ := ∏ r, (b r - a r) with hδdef
  have hδ1 : δ ≤ 1 := Finset.prod_le_one₀ (fun r _ => sub_nonneg.2 (hS r).2.1)
    fun r _ => by linarith [(hS r).1, (hS r).2.2.1]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 8 by positivity)
    (show 1 - δ < 1 by linarith)
  set m := d * k with hm
  have hW := hu.isUD_window m
  -- the comparison chain started at `x₀` and the no-coupling indicator
  have hf := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP m x₀ j)
  have hc := tendsto_empAvg_of_isStepFn hW (isStepFn_noCouple hS k)
  rw [← hδdef] at hc
  -- `|Pᵐ(x₀, j) - π j| ≤ (1 - δ)^k`
  have hstat : |multiStep P m x₀ j - π j| ≤ (1 - δ) ^ k := by
    have hsum : multiStep P m x₀ j - π j =
        ∑ i, π i * (multiStep P m x₀ j - multiStep P m i j) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul, sum_mul_multiStep hπ]
    rw [hsum]
    calc |∑ i, π i * (multiStep P m x₀ j - multiStep P m i j)|
        ≤ ∑ i, π i * (1 - δ) ^ k := (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hπ0 i)]
            exact mul_le_mul_of_nonneg_left
              (abs_multiStep_sub_le hP hu hS hcpl k x₀ i j) (hπ0 i))
      _ = (1 - δ) ^ k := by rw [← Finset.sum_mul, hπ1, one_mul]
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hf (ε / 8) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hc (ε / 8) (by positivity)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (8 * m / ε)
  refine ⟨max (max N₁ N₂) (N₃ + 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 N₃) hN3
    linarith
  have hmN : (m : ℝ) / N < ε / 8 := by
    have hN3' : 8 * (m : ℝ) / ε < N := by
      have : (N₃ : ℝ) + 1 ≤ N := by exact_mod_cast hN3
      linarith
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hN3'
    linarith
  have e1 := hN₁ N hN1
  have e2 := hN₂ N hN2
  rw [Real.dist_eq] at e1 e2 ⊢
  -- the three comparisons
  set x := drivenPath P x₀ u with hx
  set ind : ℕ → ℝ := fun t => if x t = j then 1 else 0 with hind
  have hshift := abs_sum_shift_sub_le ind
    (fun t => by rw [hind]; dsimp only; split_ifs <;> norm_num)
    (fun t => by rw [hind]; dsimp only; split_ifs <;> norm_num) N m
  have hcoup : |∑ t ∈ range N, ind (t + m) -
      ∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)| ≤
      ∑ t ∈ range N, noCouple S k (window u m t) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hind]
    dsimp only
    rw [hx, drive_add_eq_windowMap]
    exact abs_ind_sub_le_noCouple hcpl k _ (hW.1 t) _ x₀ j
  have hocc : (occCount x j N : ℝ) = ∑ t ∈ range N, ind t := occCount_eq_sum x j N
  have hfavg : empAvg (fun w => if windowMap P m x₀ w = j then 1 else 0) (window u m) N =
      (∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)) / N := rfl
  have hcavg : empAvg (noCouple S k) (window u m) N =
      (∑ t ∈ range N, noCouple S k (window u m t)) / N := rfl
  rw [hfavg] at e1
  rw [hcavg] at e2
  rw [hocc]
  set A := ∑ t ∈ range N, ind t
  set B := ∑ t ∈ range N, ind (t + m)
  set F := ∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)
  set C := ∑ t ∈ range N, noCouple S k (window u m t)
  have hAB : |A / N - B / N| ≤ m / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact hshift) hNpos.le
  have hBF : |B / N - F / N| ≤ C / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hcoup hNpos.le
  have hC2 : C / N < (1 - δ) ^ k + ε / 8 := by
    have := (abs_lt.1 e2).2
    linarith
  calc |A / N - π j|
      ≤ |A / N - B / N| + |B / N - F / N| + |F / N - multiStep P m x₀ j| +
          |multiStep P m x₀ j - π j| := by
        have := abs_sub_le (A / N) (B / N) (π j)
        have := abs_sub_le (B / N) (F / N) (π j)
        have := abs_sub_le (F / N) (multiStep P m x₀ j) (π j)
        linarith
    _ < ε / 8 + ((1 - δ) ^ k + ε / 8) + ε / 8 + (1 - δ) ^ k := by
        have := hAB.trans_lt hmN
        have := hBF.trans_lt hC2
        linarith
    _ < ε := by linarith

/-- **Time averages** (post #3): under the hypotheses of `tendsto_occFreq_of_isCUD`,
`(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)` for every function `g` of the state. -/
theorem tendsto_timeAvg_of_isCUD {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} (hC : HasCouplingBox P d) {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (x₀ : Fin n) (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
    (tendsto_occFreq_of_isCUD hP hu hC hπ hπ0 hπ1 x₀ j).mul_const (g j)
  refine h.congr fun T => ?_
  have hfib : ∀ t, g (drivenPath P x₀ u t) =
      ∑ j, (if drivenPath P x₀ u t = j then (1 : ℝ) else 0) * g j := fun t => by
    rw [Finset.sum_eq_single (drivenPath P x₀ u t)
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]
  rw [Finset.sum_congr rfl fun t _ => hfib t, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [occCount_eq_sum, ← Finset.sum_mul, div_mul_eq_mul_div]

/-- **One-step coupling from a common interval.** If the inverse-CDF intervals
`(cs_{i,j₀}, cs_{i,j₀+1}]` of a state `j₀` in all rows contain a common interval `(α, β)` with
`α < β`, then `(α, β)` is a coupling box of length `1`. -/
theorem hasCouplingBox_of_common_interval {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (j₀ : Fin n) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ 1)
    (hrow : ∀ i, cumProb P i j₀ ≤ α ∧ β ≤ cumProb P i (j₀ + 1)) : HasCouplingBox P 1 := by
  refine ⟨fun _ => Set.Ioo α β, fun _ => α, fun _ => β, j₀,
    fun _ => ⟨hα, hαβ.le, hβ, subset_rfl, fun v hv => ⟨hv.1.1.le, hv.1.2.le⟩⟩, ?_, ?_⟩
  · rw [Fin.prod_univ_one]
    linarith
  · intro w _ hw i
    have hv := hw 0
    change step P i (w (Fin.last 0)) = j₀
    have hlast : w (Fin.last 0) = w 0 := rfl
    rw [hlast]
    exact (step_eq_iff hP i j₀ ⟨by linarith [hv.1], by linarith [hv.2]⟩).2
      ⟨lt_of_le_of_lt (hrow i).1 hv.1, le_trans hv.2.le (hrow i).2⟩

/-- **Doeblin condition by a common interval.** If the column of the first state `j₀`
(`(j₀ : ℕ) = 0`) is bounded below by `c > 0`, then `(0, c)` is a coupling box of length `1`.
This covers every `P` with all entries positive. -/
theorem hasCouplingBox_of_col_pos {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (j₀ : Fin n)
    (hj₀ : (j₀ : ℕ) = 0) {c : ℝ} (hc : 0 < c) (hcol : ∀ i, c ≤ P i j₀) :
    HasCouplingBox P 1 := by
  have hc1 : c ≤ 1 := by
    have h := hP.sum_eq_one j₀
    have hle : P j₀ j₀ ≤ ∑ j, P j₀ j :=
      Finset.single_le_sum (fun j _ => hP.nonneg j₀ j) (Finset.mem_univ j₀)
    linarith [hcol j₀]
  refine hasCouplingBox_of_common_interval hP j₀ (le_refl 0) hc hc1 fun i => ⟨?_, ?_⟩
  · rw [hj₀, cumProb_zero]
  · rw [cumProb_succ, hj₀, cumProb_zero, zero_add]
    exact hcol i

/-- **All entries positive** (the classical ergodic case): then `(0, minᵢ P i 0)` is a coupling
box of length `1`. -/
theorem hasCouplingBox_of_pos {P : Fin (n + 1) → Fin (n + 1) → ℝ} (hP : IsStochastic P)
    (hpos : ∀ i j, 0 < P i j) : HasCouplingBox P 1 :=
  hasCouplingBox_of_col_pos hP 0 rfl (c := Finset.univ.inf' Finset.univ_nonempty fun i => P i 0)
    ((Finset.lt_inf'_iff _).2 fun i _ => hpos i 0) fun i => Finset.inf'_le _ (Finset.mem_univ i)

/-- **Chentsov's theorem under a Doeblin condition** (in particular for every `P` with all
entries positive): if the column of the first state is bounded below by `c > 0` and `u` is CUD,
the occupation frequencies converge to the stationary distribution. -/
theorem tendsto_occFreq_of_isCUD_of_col_pos {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) (j₀ : Fin n) (hj₀ : (j₀ : ℕ) = 0) {c : ℝ} (hc : 0 < c)
    (hcol : ∀ i, c ≤ P i j₀) {π : Fin n → ℝ} (hπ : ∀ j, ∑ i, π i * P i j = π j)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1) (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) :=
  tendsto_occFreq_of_isCUD hP hu (hasCouplingBox_of_col_pos hP j₀ hj₀ hc hcol) hπ hπ0 hπ1 x₀ j

/-- The identity matrix on two states: a reducible chain in which every state is absorbing. -/
noncomputable def identityTwo : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0

/-- The identity matrix is stochastic. -/
theorem isStochastic_identityTwo : IsStochastic identityTwo := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold identityTwo
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num [identityTwo]

/-- The uniform vector `(1/2, 1/2)` is stationary for the identity matrix. -/
theorem identityTwo_stationary (j : Fin 2) : ∑ i, (1 / 2 : ℝ) * identityTwo i j = 1 / 2 := by
  rw [Fin.sum_univ_two]
  fin_cases j <;> norm_num [identityTwo]

/-- Under the identity matrix, every uniform in `[0,1)` keeps the chain in state `0`. -/
theorem step_identityTwo_zero {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    step identityTwo 0 u = 0 := by
  rcases hu.1.lt_or_eq with hpos | hzero
  · refine (step_eq_iff isStochastic_identityTwo 0 0 ⟨hpos, hu.2.le⟩).2 ⟨?_, ?_⟩
    · rw [Fin.val_zero, cumProb_zero]
      exact hpos
    · rw [cumProb_succ, Fin.val_zero, cumProb_zero, zero_add]
      unfold identityTwo
      norm_num
      exact hu.2.le
  · subst hzero
    exact Fin.ext (val_step_zero _ isStochastic_identityTwo 0)

/-- The path of the identity chain from state `0` is constant, whatever the driving sequence
in `[0,1)`. -/
theorem drivenPath_identityTwo {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Ico (0 : ℝ) 1) (t : ℕ) :
    drivenPath identityTwo 0 u t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step identityTwo (drivenPath identityTwo 0 u t) (u t) = 0
    rw [ih]
    exact step_identityTwo_zero (hu t)

/-- **Counterexample (post #3, consistency needs a condition on the chain).** For the identity
chain on two states, driven from state `0` by any sequence in `[0,1)` — in particular by every
CUD sequence — the frequency of state `0` tends to `1`, not to the value `1/2` of the
stationary distribution `(1/2, 1/2)` (`identityTwo_stationary`). -/
theorem not_tendsto_occFreq_identity {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Ico (0 : ℝ) 1) :
    ¬ Tendsto (fun T => (occCount (drivenPath identityTwo 0 u) 0 T : ℝ) / T) atTop
      (𝓝 (1 / 2)) := by
  intro h
  have h1 : Tendsto (fun T => (occCount (drivenPath identityTwo 0 u) 0 T : ℝ) / T) atTop
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hocc : occCount (drivenPath identityTwo 0 u) 0 T = T := by
      unfold occCount
      rw [Finset.filter_true_of_mem fun t _ => drivenPath_identityTwo hu t, Finset.card_range]
    rw [hocc, div_self (by exact_mod_cast hT.ne')]
  have := tendsto_nhds_unique h h1
  norm_num at this

/-- The four-state chain with rows `(1/2, 0, 0, 1/2)` (states `0`, `2`) and `(0, 1/2, 1/2, 0)`
(states `1`, `3`): irreducible, aperiodic and doubly stochastic, with `P² = (1/4)·𝟙`. -/
noncomputable def fourState : Fin 4 → Fin 4 → ℝ := fun i j =>
  if (i : ℕ) % 2 = 0 then (if (j : ℕ) = 0 ∨ (j : ℕ) = 3 then 1 / 2 else 0)
  else (if (j : ℕ) = 1 ∨ (j : ℕ) = 2 then 1 / 2 else 0)

/-- `fourState` is stochastic. -/
theorem isStochastic_fourState : IsStochastic fourState := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold fourState
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_four]
    fin_cases i <;> norm_num [fourState]

/-- **Perfect mixing in two steps:** `P²(i,j) = 1/4` for all `i, j`, so `P²` is the matrix of the
uniform stationary distribution (the strongest Doeblin minorisation). -/
theorem multiStep_fourState_two (i j : Fin 4) : multiStep fourState 2 i j = 1 / 4 := by
  change ∑ k, (∑ l, (if i = l then (1 : ℝ) else 0) * fourState l k) * fourState k j = 1 / 4
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num [fourState]

/-- The uniform distribution is stationary for `fourState`. -/
theorem fourState_stationary (j : Fin 4) : ∑ i, (1 / 4 : ℝ) * fourState i j = 1 / 4 := by
  rw [Fin.sum_univ_four]
  fin_cases j <;> norm_num [fourState]

/-- For a uniform in `(0,1)`, the `fourState` update keeps the block (`{0,2}` or `{1,3}`, the
parity of the state) when `u ≤ 1/2` and switches it when `u > 1/2`. -/
theorem step_fourState_parity (i : Fin 4) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    ((step fourState i u : ℕ) % 2 = (i : ℕ) % 2) ↔ u ≤ 1 / 2 := by
  have hP := isStochastic_fourState
  have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
  by_cases h2 : u ≤ 1 / 2
  · rw [iff_true_intro h2, iff_true]
    fin_cases i
    · have h : step fourState 0 u = 0 := (step_eq_iff hP 0 0 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 0 u : ℕ) % 2 = (((0 : Fin 4) : ℕ) % 2)
      rw [h]
    · have h : step fourState 1 u = 1 := (step_eq_iff hP 1 1 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 1 u : ℕ) % 2 = (((1 : Fin 4) : ℕ) % 2)
      rw [h]
    · have h : step fourState 2 u = 0 := (step_eq_iff hP 2 0 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 2 u : ℕ) % 2 = (((2 : Fin 4) : ℕ) % 2)
      rw [h]
      rfl
    · have h : step fourState 3 u = 1 := (step_eq_iff hP 3 1 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 3 u : ℕ) % 2 = (((3 : Fin 4) : ℕ) % 2)
      rw [h]
      rfl
  · rw [iff_false_intro h2, iff_false]
    have h2' : 1 / 2 < u := lt_of_not_ge h2
    fin_cases i
    · have h : step fourState 0 u = 3 := (step_eq_iff hP 0 3 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 0 u : ℕ) % 2 = (((0 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 1 u = 2 := (step_eq_iff hP 1 2 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 1 u : ℕ) % 2 = (((1 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 2 u = 3 := (step_eq_iff hP 2 3 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 2 u : ℕ) % 2 = (((2 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 3 u = 2 := (step_eq_iff hP 3 2 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 3 u : ℕ) % 2 = (((3 : Fin 4) : ℕ) % 2))
      rw [h]
      decide

/-- Paths of `fourState` started in different blocks, driven by the same uniforms in `(0,1)`,
stay in different blocks forever: the inverse-CDF grand coupling never coalesces. -/
theorem windowMap_fourState_parity_ne (m : ℕ) (w : Fin m → ℝ)
    (hw : ∀ k, w k ∈ Set.Ioo (0 : ℝ) 1) {i i' : Fin 4} (hii' : (i : ℕ) % 2 ≠ (i' : ℕ) % 2) :
    (windowMap fourState m i w : ℕ) % 2 ≠ (windowMap fourState m i' w : ℕ) % 2 := by
  induction m with
  | zero => exact hii'
  | succ m ih =>
    rw [windowMap_succ, windowMap_succ]
    have hih := ih (fun k => w (Fin.castSucc k)) fun k => hw _
    have hA := step_fourState_parity (windowMap fourState m i fun k => w (Fin.castSucc k))
      (hw (Fin.last m))
    have hB := step_fourState_parity (windowMap fourState m i' fun k => w (Fin.castSucc k))
      (hw (Fin.last m))
    have hpl : (windowMap fourState m i fun k => w (Fin.castSucc k) : ℕ) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    have hql : (windowMap fourState m i' fun k => w (Fin.castSucc k) : ℕ) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    generalize (windowMap fourState m i fun k => w (Fin.castSucc k) : ℕ) % 2 = p at hA hih hpl
    generalize (windowMap fourState m i' fun k => w (Fin.castSucc k) : ℕ) % 2 = q at hB hih hql
    have hp : ((step fourState (windowMap fourState m i fun k => w (Fin.castSucc k))
      (w (Fin.last m)) : ℕ) % 2) < 2 := Nat.mod_lt _ (by norm_num)
    have hq : ((step fourState (windowMap fourState m i' fun k => w (Fin.castSucc k))
      (w (Fin.last m)) : ℕ) % 2) < 2 := Nat.mod_lt _ (by norm_num)
    by_cases h : w (Fin.last m) ≤ 1 / 2
    · rw [hA.2 h, hB.2 h]
      exact hih
    · have h1 := mt hA.1 h
      have h2 := mt hB.1 h
      omega

/-- **The coupling hypothesis is not implied by irreducibility + aperiodicity + Doeblin.**
`fourState` (which has `P² = (1/4)·𝟙`, `multiStep_fourState_two`) has no coupling box of any
length `d`: every box of positive volume contains a window in `(0,1)^d`, and along it the paths
from `0` and from `1` never meet. -/
theorem not_hasCouplingBox_fourState (d : ℕ) : ¬ HasCouplingBox fourState d := by
  rintro ⟨S, a, b, j₀, hS, hvol, hC⟩
  have hab : ∀ k, a k < b k := by
    intro k
    rcases (hS k).2.1.lt_or_eq with h | h
    · exact h
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [h, sub_self])) hvol.ne'
  set w : Fin d → ℝ := fun k => (a k + b k) / 2 with hw
  have hwI : ∀ k, w k ∈ Set.Ioo (a k) (b k) := fun k => by
    rw [hw]
    constructor <;> linarith [hab k]
  have hw01 : ∀ k, w k ∈ Set.Ioo (0 : ℝ) 1 := fun k =>
    ⟨lt_of_le_of_lt (hS k).1 (hwI k).1, lt_of_lt_of_le (hwI k).2 (hS k).2.2.1⟩
  have hcube : InUnitCube w := fun k => ⟨(hw01 k).1.le, (hw01 k).2⟩
  have hmem : ∀ k, w k ∈ S k := fun k => (hS k).2.2.2.1 (hwI k)
  have h0 := hC w hcube hmem 0
  have h1 := hC w hcube hmem 1
  exact windowMap_fourState_parity_ne d w hw01 (i := 0) (i' := 1) (by decide)
    (by rw [h0, h1])

end RQMCMarkov.MarkovDriving
