/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.DrivingMC

/-!
# Spell lengths: geometric under MC, and stratified sampling of them (post #3, approach (vii))

Post #3: "a path can also be seen as a sequence of spells … Under the Markov chain spell lengths in
state `i` are geometric with stay probability `p_ii`", and approach (vii) draws "the spell lengths
in each state by stratified sampling from the geometric distribution (one draw in each of `K`
equal intervals, where `K` is the number of spells in that state) rather than at random,
adjusting them slightly so they add up to the total time spent in that state".

**Readings.** (1) "Geometric": for MC from `x₀`, after any history `s_0, …, s_t` with `s_t = i`,
the event "exactly `k − 1` further periods in `i`, then an exit" has probability
`P(history) · p_ii^{k−1}(1 − p_ii)`, so conditionally on the past at the start of a stay in `i`
the length of the stay is geometric on `{1, 2, …}`; in particular the first spell of a chain
started in `i` (`runLength` from time `0`) has this law. (2) "Stratified sampling from the
geometric distribution": `L_k = G((k + V_k)/K)`, `k < K`, with `V_k` i.i.d. `U[0,1)` and `G` the
geometric inverse CDF `geomQuantile p` (`G(u)` = least `k ≥ 1` with `u < 1 − p^k`; using `<`
rather than post #3's `≤` changes `G` only on a null set). "Better than at random" is read as:
unbiased for the mean spell length, with variance at most that of `K` i.i.d. draws.

## Main results

* `iidUniform_spell_after_history`, `iidUniform_firstSpell`, `iidUniform_runLength_eq`: MC spell
  lengths are geometric with stay probability `p_ii` (`pathProb_extend_stay`,
  `uniformIco_step_ne` are the steps).
* `geomQuantile`, `geomQuantile_eq_succ_iff`, `geomQuantile_eq_zero_iff`,
  `measurable_geomQuantile`, `geomQuantile_preimage_inter_Ico`; `uniformIco_geomQuantile_eq_succ`
  (`P(G(U) = k + 1) = p^k (1 − p)`) and `uniformIco_geomQuantile_eq_firstSpell` (the law of
  `G(U)` is the MC spell-length law).
* `lintegral_geomQuantile`, `integral_geomQuantile`, `memLp_geomQuantile`;
  `integral_geomQuantile_id` (`E[L] = 1/(1 − p)`, e.g. `8` for post #3's `p = 7/8`),
  `integral_geomQuantile_sq`, `variance_geomQuantile` (`Var(L) = p/(1 − p)²`).
* `variance_stratified_le_div`: generic — stratified inverse-CDF sampling of any `f ∈ L²` has
  variance at most `Var(f(U))/K`.
* `integral_stratifiedSpell`: the stratified spell lengths are unbiased for `1/(1 − p)`;
  `variance_stratifiedSpell_le_iid`: their mean has variance at most that of `K` i.i.d. spell
  lengths; `variance_stratifiedSpell_le`: explicitly `≤ p/((1 − p)² K)`.

**Not formalised.** The "adjusting them slightly so they add up to the total time spent in that
state" step is a heuristic (it changes the joint law in an unspecified way) and is not
formalised; neither is the random ordering of the spells, nor the "three to four times more
accurate" simulation finding.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {n : ℕ}

/-- Extending a history `s` (up to time `t`, with `s t = i`) by staying in `i` multiplies its
path probability by `P i i` per period. -/
theorem pathProb_extend_stay (P : Fin n → Fin n → ℝ) (x₀ i : Fin n) (s : ℕ → Fin n) {t : ℕ}
    (hst : s t = i) (j : ℕ) :
    pathProb P x₀ (fun m ↦ if m ≤ t then s m else i) (t + j) = pathProb P x₀ s t * P i i ^ j := by
  induction j with
  | zero =>
    rw [add_zero, pow_zero, mul_one]
    unfold pathProb
    simp only [Nat.zero_le, ↓reduceIte]
    congr 1
    refine Finset.prod_congr rfl fun m hm ↦ ?_
    have hm' := Finset.mem_range.1 hm
    simp only [hm'.le, show m + 1 ≤ t by omega, ↓reduceIte]
  | succ j ih =>
    rw [← add_assoc, pathProb_succ, ih, pow_succ, mul_assoc]
    have e1 : (if t + j ≤ t then s (t + j) else i) = i := by
      split_ifs with hj
      · rw [show t + j = t by omega, hst]
      · rfl
    have e2 : (if t + j + 1 ≤ t then s (t + j + 1) else i) = i := by
      split_ifs with hj
      · omega
      · rfl
    rw [e1, e2]

/-- `uniformIco {r : step P i r ≠ i} = 1 − P i i`. -/
theorem uniformIco_step_ne {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) :
    uniformIco {r | step P i r ≠ i} = ENNReal.ofReal (1 - P i i) := by
  have := isProbabilityMeasure_uniformIco
  have hc : {r | step P i r ≠ i} = {r | step P i r = i}ᶜ := rfl
  rw [hc, prob_compl_eq_one_sub (measurableSet_step_eq P i i), uniformIco_step_eq hP,
    ENNReal.ofReal_sub _ (hP.nonneg i i), ENNReal.ofReal_one]

/-- **Spell lengths are geometric, after any history** (post #3: "under the Markov chain spell
lengths in state `i` are geometric with stay probability `p_ii`"): for MC from `x₀`, any history
`s_0, …, s_t` ending in `s_t = i`, and `k ≥ 1`, the probability of that history followed by
exactly `k − 1` further periods in `i` and then an exit is
`P(history) · p_ii^{k−1} (1 − p_ii)`. So, conditional on the past up to the start of a stay in `i`
(e.g. a spell start), the remaining length of the stay is geometric. -/
theorem iidUniform_spell_after_history {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i : Fin n) (s : ℕ → Fin n) {t k : ℕ} (hst : s t = i) (hk : 1 ≤ k) :
    iidUniform ℕ {u | (∀ m ≤ t, drivenPath P x₀ u m = s m) ∧
        (∀ m < k, drivenPath P x₀ u (t + m) = i) ∧ drivenPath P x₀ u (t + k) ≠ i} =
      ENNReal.ofReal (pathProb P x₀ s t * (P i i ^ (k - 1) * (1 - P i i))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set s' : ℕ → Fin n := fun m ↦ if m ≤ t then s m else i with hs'
  set B : ℕ → Set ℝ := fun m ↦
    if m < t + j then {r | step P (s' m) r = s' (m + 1)} else {r | step P i r ≠ i} with hB
  have hs'i : ∀ m, t ≤ m → s' m = i := fun m hm ↦ by
    by_cases hmt : m ≤ t
    · simp only [hs', hmt, ↓reduceIte]
      rw [show m = t by omega, hst]
    · simp only [hs', hmt, ↓reduceIte]
  have hset : {u | (∀ m ≤ t, drivenPath P x₀ u m = s m) ∧
      (∀ m < j + 1, drivenPath P x₀ u (t + m) = i) ∧ drivenPath P x₀ u (t + (j + 1)) ≠ i} =
      {u | s' 0 = x₀ ∧ ∀ m < t + j + 1, u (id m) ∈ B m} := by
    ext u
    simp only [Set.mem_ofPred_eq, id, drivenPath]
    constructor
    · rintro ⟨hA, hBu, hC⟩
      have hD : ∀ m ≤ t + j, drive (step P) x₀ u m = s' m := fun m hm ↦ by
        by_cases hmt : m ≤ t
        · simp only [hs', hmt, ↓reduceIte]
          exact hA m hmt
        · have := hBu (m - t) (by omega)
          rw [show t + (m - t) = m by omega] at this
          rw [this, hs'i m (by omega)]
      obtain ⟨h0, hstep⟩ := (drive_eq_iff (step P) x₀ u s' (t + j)).1 hD
      refine ⟨h0, fun m hm ↦ ?_⟩
      by_cases hmj : m < t + j
      · simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq]
        exact hstep m hmj
      · simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq]
        rw [show m = t + j by omega]
        have h1 : drive (step P) x₀ u (t + (j + 1)) =
            step P (drive (step P) x₀ u (t + j)) (u (t + j)) := rfl
        rw [h1, hBu j (Nat.lt_succ_self j)] at hC
        exact hC
    · rintro ⟨h0, hm⟩
      have hstep : ∀ m < t + j, step P (s' m) (u m) = s' (m + 1) := fun m hmj ↦ by
        have := hm m (by omega)
        simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq] at this
        exact this
      have hD := (drive_eq_iff (step P) x₀ u s' (t + j)).2 ⟨h0, hstep⟩
      have hend : drive (step P) x₀ u (t + j) = i := by
        rw [hD (t + j) le_rfl, hs'i (t + j) (by omega)]
      refine ⟨fun m hm' ↦ ?_, fun m hm' ↦ ?_, ?_⟩
      · rw [hD m (by omega)]
        simp only [hs', hm', ↓reduceIte]
      · rw [hD (t + m) (by omega), hs'i (t + m) (by omega)]
      · have h1 : drive (step P) x₀ u (t + (j + 1)) =
            step P (drive (step P) x₀ u (t + j)) (u (t + j)) := rfl
        have := hm (t + j) (by omega)
        simp only [hB, lt_irrefl, ↓reduceIte, Set.mem_ofPred_eq] at this
        rw [h1, hend]
        exact this
  have hBm : ∀ m, MeasurableSet (B m) := fun m ↦ by
    simp only [hB]
    split_ifs
    · exact measurableSet_step_eq P _ _
    · exact (measurableSet_step_eq P i i).compl
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [hset]
  have hs0 : s' 0 = s 0 := by simp only [hs', Nat.zero_le, ↓reduceIte]
  by_cases h0 : s' 0 = x₀
  · simp only [h0, true_and]
    rw [infinitePi_setOf_forall_mem uniformIco Function.injective_id hBm, Finset.prod_range_succ]
    have hpre : ∏ m ∈ range (t + j), uniformIco (B m) =
        ∏ m ∈ range (t + j), uniformIco {r | step P (s' m) r = s' (m + 1)} :=
      Finset.prod_congr rfl fun m hm ↦ by
        simp only [hB, Finset.mem_range.1 hm, ↓reduceIte]
    have hlast : B (t + j) = {r | step P i r ≠ i} := by
      simp only [hB, lt_irrefl, ↓reduceIte]
    rw [hpre, hlast, prod_uniformIco_step_eq hP s' (t + j), uniformIco_step_ne hP,
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun m _ ↦ hP.nonneg _ _)]
    congr 1
    have hext : pathProb P x₀ s' (t + j) = pathProb P x₀ s t * P i i ^ j :=
      pathProb_extend_stay P x₀ i s hst j
    have hprod : ∏ m ∈ range (t + j), P (s' m) (s' (m + 1)) = pathProb P x₀ s' (t + j) := by
      unfold pathProb
      exact (ite_eq_left_of_eq_true _ _ (eq_true h0)).symm
    rw [hprod, hext, mul_assoc]
  · simp only [h0, false_and, Set.ofPred_false, measure_empty]
    unfold pathProb
    rw [← hs0]
    simp only [h0, ↓reduceIte, zero_mul, ENNReal.ofReal_zero]

/-- **The first spell is geometric** (post #3): for MC started in `i` and `k ≥ 1`,
`P(x_1 = … = x_{k−1} = i, x_k ≠ i) = p_ii^{k−1} (1 − p_ii)`. -/
theorem iidUniform_firstSpell {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) {k : ℕ}
    (hk : 1 ≤ k) :
    iidUniform ℕ {u | (∀ m < k, drivenPath P i u m = i) ∧ drivenPath P i u k ≠ i} =
      ENNReal.ofReal (P i i ^ (k - 1) * (1 - P i i)) := by
  have h := iidUniform_spell_after_history hP i i (fun _ ↦ i) (t := 0) rfl hk
  have hp : pathProb P i (fun _ ↦ i) 0 = 1 := by
    unfold pathProb
    simp only [↓reduceIte, Finset.range_zero, Finset.prod_empty]
  rw [hp, one_mul] at h
  rw [← h]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq, zero_add]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun m hm ↦ ?_, h1, h2⟩
    rw [Nat.le_zero.1 hm]
    rfl
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

/-- **The first spell length, as `runLength`** (post #3): for MC started in `i`, `1 ≤ k < T`,
`P(runLength = k) = p_ii^{k−1} (1 − p_ii)`, the geometric law with stay probability `p_ii`. -/
theorem iidUniform_runLength_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {k T : ℕ} (hk : 1 ≤ k) (hkT : k < T) :
    iidUniform ℕ {u | runLength (drivenPath P i u) 0 T = k} =
      ENNReal.ofReal (P i i ^ (k - 1) * (1 - P i i)) := by
  rw [← iidUniform_firstSpell hP i hk]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  rw [runLength_eq_iff (by omega)]
  simp only [zero_add]
  rfl

/-! ### The geometric inverse CDF and stratified spell lengths -/

/-- **The geometric inverse CDF** with stay probability `p`: `geomQuantile p u` is the smallest
`k ≥ 1` with `u < 1 − p^k` (`P(L ≤ k) = 1 − p^k` for a spell length `L`), and `0` if there is
none (only for `u ≥ 1`, or `p ≥ 1`). -/
noncomputable def geomQuantile (p u : ℝ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, u < 1 - p ^ (k + 1) then Nat.find h + 1 else 0

/-- The fibres of `geomQuantile` above `k + 1`. -/
theorem geomQuantile_eq_succ_iff (p u : ℝ) (k : ℕ) :
    geomQuantile p u = k + 1 ↔ u < 1 - p ^ (k + 1) ∧ ∀ m < k, 1 - p ^ (m + 1) ≤ u := by
  classical
  unfold geomQuantile
  split_ifs with h
  · rw [Nat.add_right_cancel_iff, Nat.find_eq_iff]
    simp only [not_lt]
  · constructor
    · intro h'
      exact h'.elim
    · rintro ⟨h1, -⟩
      exact absurd ⟨k, h1⟩ h

/-- The fibre of `geomQuantile` above `0`. -/
theorem geomQuantile_eq_zero_iff (p u : ℝ) :
    geomQuantile p u = 0 ↔ ∀ k : ℕ, 1 - p ^ (k + 1) ≤ u := by
  classical
  unfold geomQuantile
  split_ifs with h
  · constructor
    · intro h'
      exact h'.elim
    · intro h'
      obtain ⟨k, hk⟩ := h
      exact absurd (h' k) (not_le.2 hk)
  · push Not at h
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- `geomQuantile p` is measurable. -/
theorem measurable_geomQuantile (p : ℝ) : Measurable (geomQuantile p) := by
  refine measurable_to_countable' fun k ↦ ?_
  rcases k with _ | k
  · have : geomQuantile p ⁻¹' {0} = ⋂ k : ℕ, Set.Ici (1 - p ^ (k + 1)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_Ici]
      exact geomQuantile_eq_zero_iff p u
    rw [this]
    exact MeasurableSet.iInter fun _ ↦ measurableSet_Ici
  · have : geomQuantile p ⁻¹' {k + 1} =
        Set.Iio (1 - p ^ (k + 1)) ∩ ⋂ (m : ℕ) (_ : m < k), Set.Ici (1 - p ^ (m + 1)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Iio,
        Set.mem_iInter, Set.mem_Ici]
      exact geomQuantile_eq_succ_iff p u k
    rw [this]
    exact measurableSet_Iio.inter (MeasurableSet.iInter fun _ ↦ .iInter fun _ ↦ measurableSet_Ici)

variable {p : ℝ}

/-- On `[0,1)`, the fibre of `geomQuantile p` above `k + 1` is `[1 − p^k, 1 − p^{k+1})`. -/
theorem geomQuantile_preimage_inter_Ico (hp0 : 0 ≤ p) (hp1 : p < 1) (k : ℕ) :
    {u | geomQuantile p u = k + 1} ∩ Set.Ico 0 1 = Set.Ico (1 - p ^ k) (1 - p ^ (k + 1)) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, geomQuantile_eq_succ_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hu0, -⟩
    refine ⟨?_, h1⟩
    rcases k with _ | k
    · rw [pow_zero, sub_self]
      exact hu0
    · exact h2 k (Nat.lt_succ_self k)
  · rintro ⟨h1, h2⟩
    have hpk : p ^ k ≤ 1 := pow_le_one₀ hp0 hp1.le
    have hpk1 : 0 ≤ p ^ (k + 1) := pow_nonneg hp0 _
    refine ⟨⟨h2, fun m hm ↦ le_trans ?_ h1⟩, by linarith, by linarith⟩
    have := pow_le_pow_of_le_one hp0 hp1.le (show m + 1 ≤ k by omega)
    linarith

/-- **The stratification target is the spell-length law**: under `U[0,1)`,
`P(geomQuantile p U = k + 1) = p^k (1 − p)`, the geometric law of the MC spell lengths
(`iidUniform_firstSpell`). -/
theorem uniformIco_geomQuantile_eq_succ (hp0 : 0 ≤ p) (hp1 : p < 1) (k : ℕ) :
    uniformIco {u | geomQuantile p u = k + 1} = ENNReal.ofReal (p ^ k * (1 - p)) := by
  rw [Measure.restrict_apply' measurableSet_Ico, geomQuantile_preimage_inter_Ico hp0 hp1,
    Real.volume_Ico]
  congr 1
  ring

/-- `geomQuantile p U ≥ 1` almost surely. -/
theorem uniformIco_geomQuantile_eq_zero (hp0 : 0 ≤ p) (hp1 : p < 1) :
    uniformIco {u | geomQuantile p u = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ico]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, geomQuantile_eq_zero_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hall _ hu1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - u by linarith) hp1
  have := hall N
  have := pow_le_pow_of_le_one hp0 hp1.le (show N ≤ N + 1 by omega)
  linarith

/-- **The stratified draws have the MC spell-length law**: for `k ≥ 1` and `p = P i i < 1`,
`P(geomQuantile p U = k)` equals the MC probability that the first spell in `i` lasts `k`. -/
theorem uniformIco_geomQuantile_eq_firstSpell {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (i : Fin n) (hp1 : P i i < 1) {k : ℕ} (hk : 1 ≤ k) :
    uniformIco {u | geomQuantile (P i i) u = k} =
      iidUniform ℕ {u | (∀ m < k, drivenPath P i u m = i) ∧ drivenPath P i u k ≠ i} := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [iidUniform_firstSpell hP i hk, Nat.add_sub_cancel,
    uniformIco_geomQuantile_eq_succ (hP.nonneg i i) hp1]

/-- Lebesgue integrals of functions of the geometric draw:
`∫⁻ g (geomQuantile p u) du = Σ_m g (m + 1) p^m (1 − p)`. -/
theorem lintegral_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) (g : ℕ → ℝ≥0∞) :
    ∫⁻ u, g (geomQuantile p u) ∂uniformIco =
      ∑' m : ℕ, g (m + 1) * ENNReal.ofReal (p ^ m * (1 - p)) := by
  rw [← lintegral_map measurable_from_nat (measurable_geomQuantile p), lintegral_countable',
    tsum_eq_zero_add' ENNReal.summable]
  have hmap : ∀ k, uniformIco.map (geomQuantile p) {k} = uniformIco {u | geomQuantile p u = k} :=
    fun k ↦ Measure.map_apply (measurable_geomQuantile p) (measurableSet_singleton k)
  rw [hmap, uniformIco_geomQuantile_eq_zero hp0 hp1, mul_zero, zero_add]
  exact tsum_congr fun m ↦ by rw [hmap, uniformIco_geomQuantile_eq_succ hp0 hp1]

/-- Summability of `(m + 1)^2 p^m (1 − p)`. -/
theorem summable_succ_sq_mul_geometric (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p)) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hpn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hpn
  have h0 := summable_geometric_of_lt_one hp0 hp1
  refine (((h2.add (h1.mul_left 2)).add h0).mul_right (1 - p)).congr fun m ↦ ?_
  ring

/-- Summability of `(m + 1) p^m (1 − p)`. -/
theorem summable_succ_mul_geometric (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) * (p ^ m * (1 - p)) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hpn
  have h0 := summable_geometric_of_lt_one hp0 hp1
  refine ((h1.add h0).mul_right (1 - p)).congr fun m ↦ ?_
  ring

/-- `∫ g ∘ geomQuantile = Σ_m g (m + 1) p^m (1 − p)` for nonnegative real `g`. -/
theorem integral_geomQuantile {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hs : Summable fun m : ℕ ↦ g (m + 1) * (p ^ m * (1 - p))) :
    ∫ u, g (geomQuantile p u) ∂uniformIco = ∑' m : ℕ, g (m + 1) * (p ^ m * (1 - p)) := by
  have hnn : ∀ m : ℕ, 0 ≤ g (m + 1) * (p ^ m * (1 - p)) := fun m ↦
    mul_nonneg (hg _) (mul_nonneg (pow_nonneg hp0 _) (by linarith))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u ↦ hg _)
    (measurable_from_nat.comp (measurable_geomQuantile p)).aestronglyMeasurable,
    lintegral_geomQuantile hp0 hp1 (fun k ↦ ENNReal.ofReal (g k))]
  have : ∀ m : ℕ, ENNReal.ofReal (g (m + 1)) * ENNReal.ofReal (p ^ m * (1 - p)) =
      ENNReal.ofReal (g (m + 1) * (p ^ m * (1 - p))) := fun m ↦
    (ENNReal.ofReal_mul (hg _)).symm
  rw [tsum_congr this, ← ENNReal.ofReal_tsum_of_nonneg hnn hs,
    ENNReal.toReal_ofReal (tsum_nonneg hnn)]

/-- The geometric draw has a finite second moment. -/
theorem memLp_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) :
    MemLp (fun u ↦ (geomQuantile p u : ℝ)) 2 uniformIco := by
  have hm : AEStronglyMeasurable (fun u ↦ (geomQuantile p u : ℝ)) uniformIco :=
    (measurable_from_nat.comp (measurable_geomQuantile p)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine ⟨hm.pow 2, ?_⟩
  change ∫⁻ u, ‖(geomQuantile p u : ℝ) ^ 2‖ₑ ∂uniformIco < ∞
  have he : ∀ u, ‖(geomQuantile p u : ℝ) ^ 2‖ₑ =
      ENNReal.ofReal (((geomQuantile p u : ℕ) : ℝ) ^ 2) := fun u ↦
    Real.enorm_eq_ofReal (sq_nonneg _)
  have hnn : ∀ m : ℕ, 0 ≤ ((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p)) := fun m ↦
    mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hp0 _) (by linarith))
  rw [lintegral_congr fun u ↦ he u,
    lintegral_geomQuantile hp0 hp1 (fun k : ℕ ↦ ENNReal.ofReal ((k : ℝ) ^ 2))]
  have : ∀ m : ℕ, ENNReal.ofReal (((m + 1 : ℕ) : ℝ) ^ 2) * ENNReal.ofReal (p ^ m * (1 - p)) =
      ENNReal.ofReal (((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p))) := fun m ↦ by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), Nat.cast_succ]
  rw [tsum_congr this, ← ENNReal.ofReal_tsum_of_nonneg hnn
    (summable_succ_sq_mul_geometric hp0 hp1)]
  exact ENNReal.ofReal_lt_top

/-- **Mean spell length** `E[L] = 1/(1 − p)` (post #3's two-state chain: `p = 7/8`, mean `8`). -/
theorem integral_geomQuantile_id (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ u, (geomQuantile p u : ℝ) ∂uniformIco = 1 / (1 - p) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have hs := summable_succ_mul_geometric hp0 hp1
  have h := integral_geomQuantile (g := fun k ↦ (k : ℝ)) (fun k ↦ Nat.cast_nonneg k) hp0 hp1
    (by
      refine hs.congr fun m ↦ ?_
      rw [Nat.cast_succ])
  rw [h]
  have h1 : Summable fun m : ℕ ↦ (m : ℝ) * p ^ m :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hpn).congr fun m ↦ by rw [pow_one]
  have h0 := summable_geometric_of_lt_one hp0 hp1
  have hsplit : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) * (p ^ m * (1 - p)) =
      ((m : ℝ) * p ^ m + p ^ m) * (1 - p) := fun m ↦ by
    rw [Nat.cast_succ]
    ring
  rw [tsum_congr hsplit, tsum_mul_right, h1.tsum_add h0, tsum_coe_mul_geometric_of_norm_lt_one hpn,
    tsum_geometric_of_lt_one hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

/-- `E[L²] = (1 + p)/(1 − p)²`. -/
theorem integral_geomQuantile_sq (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ u, (geomQuantile p u : ℝ) ^ 2 ∂uniformIco = (1 + p) / (1 - p) ^ 2 := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h := integral_geomQuantile (g := fun k ↦ (k : ℝ) ^ 2) (fun k ↦ sq_nonneg _) hp0 hp1
    ((summable_succ_sq_mul_geometric hp0 hp1).congr fun m ↦ by rw [Nat.cast_succ])
  rw [h]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hpn
  have h1 : Summable fun m : ℕ ↦ (m : ℝ) * p ^ m :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hpn).congr fun m ↦ by rw [pow_one]
  have h0 := summable_geometric_of_lt_one hp0 hp1
  have hsplit : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ)) ^ 2 * (p ^ m * (1 - p)) =
      ((m : ℝ) ^ 2 * p ^ m + 2 * ((m : ℝ) * p ^ m) + p ^ m) * (1 - p) := fun m ↦ by
    rw [Nat.cast_succ]
    ring
  rw [tsum_congr hsplit, tsum_mul_right, (h2.add (h1.mul_left 2)).tsum_add h0,
    h2.tsum_add (h1.mul_left 2), tsum_mul_left, tsum_sq_mul_geometric_of_norm_lt_one hpn,
    tsum_coe_mul_geometric_of_norm_lt_one hpn, tsum_geometric_of_lt_one hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

/-- **Variance of the spell length**: `Var(L) = p/(1 − p)²`. -/
theorem variance_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Var[fun u ↦ (geomQuantile p u : ℝ); uniformIco] = p / (1 - p) ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  rw [variance_eq_sub (memLp_geomQuantile hp0 hp1)]
  have hsq : ∫ u, ((fun u ↦ (geomQuantile p u : ℝ)) ^ 2) u ∂uniformIco =
      ∫ u, (geomQuantile p u : ℝ) ^ 2 ∂uniformIco := rfl
  rw [hsq, integral_geomQuantile_sq hp0 hp1, integral_geomQuantile_id hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Stratified inverse-CDF sampling never does worse than i.i.d. sampling** (generic form,
post #3's "one draw in each of `K` equal intervals"): for `V₀, …, V_{K−1}` i.i.d. `U[0,1)` and
any `f ∈ L²(U[0,1))` (e.g. an inverse CDF), the stratified mean `(1/K) Σ_k f((k + V_k)/K)` has
variance at most `Var(f(U))/K`, the variance of the mean of `K` i.i.d. draws. -/
theorem variance_stratified_le_div {K : ℕ} (hK : K ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Fin K → Ω → ℝ} (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean K f (fun k ↦ stratumMap K k (V k ω)); P] ≤ Var[f; uniformIco] / K :=
  variance_sampleMean_le_of_sum_map_eq hK
    (fun k ↦ (measurable_stratumMap K k).comp_aemeasurable (hV k).aemeasurable)
    (hind.comp (fun k ↦ stratumMap K k) (fun k ↦ measurable_stratumMap K k))
    (sum_map_stratified hK hV) hf

/-- **Stratified spell lengths are unbiased for the mean spell length** (post #3, approach
(vii)): with `K` draws `L_k = geomQuantile p ((k + V_k)/K)`, one in each of `K` equal intervals,
`E[(1/K) Σ_k L_k] = 1/(1 − p)`. -/
theorem integral_stratifiedSpell {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} {V : Fin K → Ω → ℝ} (hV : ∀ k, HasLaw (V k) uniformIco P) :
    ∫ ω, sampleMean K (fun u ↦ (geomQuantile p u : ℝ)) (fun k ↦ stratumMap K k (V k ω)) ∂P =
      1 / (1 - p) := by
  have := isProbabilityMeasure_uniformIco
  rw [integral_sampleMean_stratified hK hV ((memLp_geomQuantile hp0 hp1).integrable one_le_two),
    integral_geomQuantile_id hp0 hp1]

/-- **Stratified spell lengths: variance at most that of `K` i.i.d. draws** (post #3, approach
(vii)): `Var((1/K) Σ_k L_k) ≤ Var((1/K) Σ_k L'_k)` where the `L'_k = geomQuantile p W_k` are
i.i.d. with the MC spell-length law (`uniformIco_geomQuantile_eq_firstSpell`). -/
theorem variance_stratifiedSpell_le_iid {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {V W : Fin K → Ω → ℝ}
    (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P)
    (hW : ∀ k, HasLaw (W k) uniformIco P) (hindW : iIndepFun W P) :
    Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ))
        (fun k ↦ stratumMap K k (V k ω)); P] ≤
      Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ)) (fun k ↦ W k ω); P] := by
  rw [variance_sampleMean_iid hW hindW (memLp_geomQuantile hp0 hp1)]
  exact variance_stratified_le_div hK hV hind (memLp_geomQuantile hp0 hp1)

/-- **Stratified spell lengths, explicit bound**: `Var((1/K) Σ_k L_k) ≤ p / ((1 − p)² K)`, the
i.i.d. variance `Var(L)/K` with `Var(L) = p/(1 − p)²`. -/
theorem variance_stratifiedSpell_le {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Fin K → Ω → ℝ}
    (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P) :
    Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ))
        (fun k ↦ stratumMap K k (V k ω)); P] ≤ p / ((1 - p) ^ 2 * K) := by
  have h := variance_stratified_le_div hK hV hind (memLp_geomQuantile hp0 hp1)
  rwa [variance_geomQuantile hp0 hp1, div_div] at h

end RQMCMarkov.MarkovDriving
