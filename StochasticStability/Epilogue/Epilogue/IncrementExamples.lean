/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.GeometricMixing
import Epilogue.CountableIrreducibility

/-!
# The need for (16.26): the chain (16.30) (MT §16.3.1, pp. 408–409)

Meyn and Tweedie, p. 409: the chain on `ℤ₊` with
`P(0, i) = α_i`, `P(i, i − 1) = γ_i`, `P(i, i + n) = (1 − γ_i)(1 − β_i)β_iⁿ` (`n ≥ 0`, `i ≥ 1`)
(`upDownMatrix`, `upDownKernel`) moves down by at most one step at a time, so it satisfies
(16.27) with `V(x) = x`, and with `γ_i` large it is ergodic; but when `β_j → 1` the right tails
are not uniformly geometric, (16.26) fails, and the chain is not geometrically ergodic.

* `isTransitionMatrix_upDownMatrix`: the rows sum to one.
* `upDown_drift` ((V2) for `V(x) = x`): `PV(i) + γ_i = i + (1 − γ_i)β_i/(1 − β_i)` for `i ≥ 1`,
  so `PV ≤ V − ε` off `{0}` when `(1 − γ_i)β_i/(1 − β_i) + ε ≤ γ_i`, the book's condition
  `[1 − γ_i]β_i/[1 − β_i] − γ_i ≤ −ε`; `upDown_left_increments`: (16.27) holds, with `d = 1`.
* `upDown_pow_apply_eq_zero`: the chain is skip-free to the left, `Pᵐ(x, {0}) = 0` for `m < x`.
* `upDown_kendallMoment_ge`: `E_0[r^{τ_0}] ≥ r^{n+2} α_j P(j, j + n)` (a jump to `j + n` at the
  second step keeps the chain away from `0` for `n` more steps);
  `upDown_kendallMoment_eq_top`: if `β_j → 1`, then `E_0[r^{τ_0}] = ∞` for every `r > 1`.
* `upDown_not_geomErgodic` (p. 409): `{0}` is Kendall of no rate and is not a geometrically
  ergodic atom for any invariant probability (Theorem 15.1.5).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-- The transition matrix (16.30): `P(0, i) = α_i`, `P(i, i − 1) = γ_i` and
`P(i, i + n) = (1 − γ_i)(1 − β_i)β_iⁿ` for `i ≥ 1`. -/
noncomputable def upDownMatrix (α γ β : ℕ → ℝ≥0∞) (i j : ℕ) : ℝ≥0∞ :=
  if i = 0 then α j else if j + 1 = i then γ i else
    if i ≤ j then (1 - γ i) * (1 - β i) * β i ^ (j - i) else 0

/-- The chain (16.30). -/
noncomputable abbrev upDownKernel (α γ β : ℕ → ℝ≥0∞) : Kernel ℕ ℕ :=
  matKernel (upDownMatrix α γ β)

/-- `P(i, i + n) = (1 − γ_i)(1 − β_i)β_iⁿ` for `i ≥ 1`. -/
theorem upDownMatrix_up (α γ β : ℕ → ℝ≥0∞) {i : ℕ} (hi : i ≠ 0) (n : ℕ) :
    upDownMatrix α γ β i (n + i) = (1 - γ i) * (1 - β i) * β i ^ n := by
  have h1 : ¬ (n + i + 1 = i) := by omega
  have h2 : i ≤ n + i := by omega
  simp only [upDownMatrix, hi, ite_false, h1, h2, ite_true, Nat.add_sub_cancel]

/-- Below `i − 1` the row `i ≥ 1` vanishes. -/
theorem upDownMatrix_low (α γ β : ℕ → ℝ≥0∞) {i j : ℕ} (hi : i ≠ 0) (hj : j + 1 < i) :
    upDownMatrix α γ β i j = 0 := by
  have h1 : ¬ (j + 1 = i) := by omega
  have h2 : ¬ (i ≤ j) := by omega
  simp only [upDownMatrix, hi, ite_false, h1, h2]

/-- `P(i, i − 1) = γ_i`. -/
theorem upDownMatrix_down (α γ β : ℕ → ℝ≥0∞) (i : ℕ) :
    upDownMatrix α γ β (i + 1) i = γ (i + 1) := by
  simp [upDownMatrix]

/-- **The rows sum to one** when `Σ α = 1`, `γ_i ≤ 1` and `β_i < 1`. -/
theorem isTransitionMatrix_upDownMatrix {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1)
    (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) : IsTransitionMatrix (upDownMatrix α γ β) := by
  intro i
  rcases Nat.eq_zero_or_eq_succ_pred i with hi | hi
  · subst hi; simpa [upDownMatrix] using hα
  set k := i.pred
  rw [hi]
  rw [← Summable.sum_add_tsum_nat_add' (f := fun j => upDownMatrix α γ β (k + 1) j)
    (k := k + 1) ENNReal.summable]
  have hlow : ∑ j ∈ Finset.range (k + 1), upDownMatrix α γ β (k + 1) j = γ (k + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => upDownMatrix_low α γ β
      (Nat.succ_ne_zero k) (by have := Finset.mem_range.1 hj; omega), zero_add,
      upDownMatrix_down]
  have hup : ∑' n, upDownMatrix α γ β (k + 1) (n + (k + 1)) = 1 - γ (k + 1) := by
    simp_rw [upDownMatrix_up α γ β (Nat.succ_ne_zero k)]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, mul_assoc,
      ENNReal.mul_inv_cancel (tsub_pos_of_lt (hβ _)).ne' (ENNReal.sub_ne_top
        ENNReal.one_ne_top), mul_one]
  rw [hlow, hup, add_tsub_cancel_of_le (hγ _)]

/-- The chain (16.30) is a Markov kernel. -/
theorem isMarkovKernel_upDownKernel {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1)
    (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) : IsMarkovKernel (upDownKernel α γ β) :=
  isMarkovKernel_matKernel (isTransitionMatrix_upDownMatrix hα hγ hβ)

/-! ### (16.27) and the failure of (16.26) -/

/-- **(16.27) holds** for `V(x) = x` (MT p. 409): from `i ≥ 1` the only step down is to `i − 1`,
so `Σ_{y < i} P(i, y)(y − i)² = γ_i ≤ 1`. -/
theorem upDown_left_increments (α γ β : ℕ → ℝ≥0∞) (i : ℕ) :
    ∑' y, (if y < i + 1 then upDownMatrix α γ β (i + 1) y * (((i + 1 - y : ℕ) : ℝ≥0∞)) ^ 2
      else 0) = γ (i + 1) := by
  rw [tsum_eq_single i fun y hy => by
    split_ifs with h
    · rw [upDownMatrix_low α γ β (Nat.succ_ne_zero i) (by omega), zero_mul]
    · rfl]
  simp [upDownMatrix_down]

/-- **(16.26) fails** when `β_j → 1` (MT p. 409): for every `θ > 0` some row has
`Σ_{y ≥ i} P(i, y) e^{θ(y − i)} = ∞`. -/
theorem upDown_right_increments_unbounded {α γ β : ℕ → ℝ≥0∞} (hγ1 : ∀ i, γ i < 1)
    (hβ : ∀ i, β i < 1) (hlim : Tendsto β atTop (𝓝 1)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ i, i ≠ 0 ∧ ∑' n, upDownMatrix α γ β i (n + i) * ENNReal.ofReal (Real.exp (θ * n)) = ∞ := by
  have he : ENNReal.ofReal (Real.exp (-θ)) < 1 := by
    rw [ENNReal.ofReal_lt_one]; exact Real.exp_lt_one_iff.2 (by linarith)
  obtain ⟨i, hi, hi1⟩ := ((hlim.eventually (lt_mem_nhds he)).and (eventually_ge_atTop 1)).exists
  have hi0 : i ≠ 0 := by omega
  refine ⟨i, hi0, ?_⟩
  set c := (1 - γ i) * (1 - β i) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (tsub_pos_of_lt (hγ1 i)).ne' (tsub_pos_of_lt (hβ i)).ne'
  have hterm : ∀ n : ℕ, c ≤ upDownMatrix α γ β i (n + i) * ENNReal.ofReal (Real.exp (θ * n)) :=
    fun n => by
      rw [upDownMatrix_up α γ β hi0, ← hc, mul_assoc]
      refine le_mul_of_one_le_right' ?_
      have h1 : 1 ≤ β i * ENNReal.ofReal (Real.exp θ) := by
        have h2 : ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ) = 1 := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
            Real.exp_zero, ENNReal.ofReal_one]
        rw [← h2]
        exact mul_le_mul' hi.le le_rfl
      calc (1 : ℝ≥0∞) ≤ (β i * ENNReal.ofReal (Real.exp θ)) ^ n := one_le_pow₀ h1
        _ = β i ^ n * ENNReal.ofReal (Real.exp (θ * n)) := by
          rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, mul_comm θ]
  exact top_le_iff.1 ((ENNReal.tsum_const_eq_top_of_ne_zero hc0).symm.le.trans
    (ENNReal.tsum_le_tsum hterm))

/-! ### Skip-free to the left -/

/-- **The chain is skip-free to the left**: `Pᵐ(x, {z | z + m < x}) = 0`. -/
theorem upDown_pow_low {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1) (hγ : ∀ i, γ i ≤ 1)
    (hβ : ∀ i, β i < 1) (m x : ℕ) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    (upDownKernel α γ β ^ m) x {z | z + m < x} = 0 := by
  have := isMarkovKernel_upDownKernel hα hγ hβ
  induction m with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
      indicator_of_notMem]
    simp
  | succ m ih =>
    rw [pow_succ_apply' _ m x (Set.to_countable _).measurableSet]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _
      (Set.to_countable _).measurableSet)).2 ?_
    have hae : ∀ᵐ y ∂(upDownKernel α γ β ^ m) x, x ≤ y + m := by
      rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) ih
      simp only [mem_ofPred_eq, not_le] at hy ⊢
      omega
    filter_upwards [hae] with y hy
    change upDownKernel α γ β y {z | z + (m + 1) < x} = 0
    rw [matKernel_apply]
    refine ENNReal.tsum_eq_zero.2 fun z => ?_
    by_cases hz : z ∈ {z | z + (m + 1) < x}
    · rw [indicator_of_mem hz]
      simp only [mem_ofPred_eq] at hz
      exact upDownMatrix_low α γ β (by omega) (by omega)
    · rw [indicator_of_notMem hz]

/-- `Pᵐ(x, {0}) = 0` for `m < x`. -/
theorem upDown_pow_apply_eq_zero {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1) (hγ : ∀ i, γ i ≤ 1)
    (hβ : ∀ i, β i < 1) {m x : ℕ} (hm : m < x) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    (upDownKernel α γ β ^ m) x {0} = 0 :=
  measure_mono_null (fun z hz => by
    rw [mem_singleton_iff] at hz; subst hz; simp only [mem_ofPred_eq]; omega)
    (upDown_pow_low hα hγ hβ m x)

/-! ### Return times to `0` -/

/-- **A lower bound for `E_0[r^{τ_0}]`**: `E_0[r^{τ_0}] ≥ r^{n+2} α_j P(j, j + n)` for `j ≥ 1`: on
`{Φ₁ = j, Φ₂ = j + n}` the chain cannot reach `0` before time `n + 2`. -/
theorem upDown_kendallMoment_ge {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1) (hγ : ∀ i, γ i ≤ 1)
    (hβ : ∀ i, β i < 1) {r : ℝ≥0∞} (hr : 1 ≤ r) {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    r ^ (n + 2) * (α j * ((1 - γ j) * (1 - β j) * β j ^ n)) ≤
      kendallMoment (upDownKernel α γ β) {0} r 0 := by
  have := isMarkovKernel_upDownKernel hα hγ hβ
  set P := upDownKernel α γ β with hP
  have := isMarkovKernel_pathKernel P
  have hms : ∀ s : Set (ℕ × ℕ), MeasurableSet s := fun s => (Set.to_countable s).measurableSet
  -- the two-step event
  have hE : pathKernel P 0 {ω | ω 1 = j ∧ ω 2 = j + n} =
      α j * ((1 - γ j) * (1 - β j) * β j ^ n) := by
    have hm : Measurable fun ω : ℕ → ℕ => (ω 1, ω (1 + 1)) :=
      (measurable_pi_apply 1).prodMk (measurable_pi_apply (1 + 1))
    have hset : {ω : ℕ → ℕ | ω 1 = j ∧ ω 2 = j + n} =
        (fun ω : ℕ → ℕ => (ω 1, ω (1 + 1))) ⁻¹' ({j} ×ˢ {j + n}) := by
      ext ω; simp
    have := isMarkovKernel_pow P 1
    rw [hset, ← Measure.map_apply hm (hms _), pathKernel_map_pair,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton]
    simp only [pow_one]
    rw [hP, matKernel_singleton, matKernel_singleton, add_comm j n, upDownMatrix_up α γ β hj]
    simp [upDownMatrix, mul_comm]
  -- the bad events have probability zero
  have hbad : ∀ i ∈ Finset.range (n - 1),
      pathKernel P 0 {ω | ω 2 = j + n ∧ ω (2 + (i + 1)) = 0} = 0 := fun i hi => by
    have hm : Measurable fun ω : ℕ → ℕ => (ω 2, ω (2 + (i + 1))) :=
      (measurable_pi_apply 2).prodMk (measurable_pi_apply (2 + (i + 1)))
    have hset : {ω : ℕ → ℕ | ω 2 = j + n ∧ ω (2 + (i + 1)) = 0} =
        (fun ω : ℕ → ℕ => (ω 2, ω (2 + (i + 1)))) ⁻¹' ({j + n} ×ˢ {0}) := by
      ext ω; simp
    have hi' : i + 1 < j + n := by have := Finset.mem_range.1 hi; omega
    have := isMarkovKernel_pow P (i + 1)
    have := isMarkovKernel_pow P 2
    rw [hset, ← Measure.map_apply hm (hms _), pathKernel_map_pair,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton, upDown_pow_apply_eq_zero hα hγ hβ hi', zero_mul]
  -- the event `{τ_0 ≥ n + 2}`
  have hsub : {ω : ℕ → ℕ | ω 1 = j ∧ ω 2 = j + n} ⊆
      {ω | WithTop.some (n + 2) ≤ firstReturn {0} ω} ∪
        ⋃ i ∈ Finset.range (n - 1), {ω | ω 2 = j + n ∧ ω (2 + (i + 1)) = 0} := by
    rintro ω ⟨h1, h2⟩
    by_cases hall : ∀ m, 1 ≤ m → m < n + 2 → ω m ∉ ({0} : Set ℕ)
    · exact Or.inl ((le_firstReturn_iff {0} ω (n + 2)).2 hall)
    · push Not at hall
      obtain ⟨m, hm1, hm2, hm0⟩ := hall
      rw [mem_singleton_iff] at hm0
      have hm3 : 3 ≤ m := by
        rcases Nat.lt_or_ge m 3 with h | h
        · interval_cases m
          · rw [h1] at hm0; exact absurd hm0 hj
          · rw [h2] at hm0; omega
        · exact h
      refine Or.inr (mem_iUnion₂.2 ⟨m - 3, Finset.mem_range.2 (by omega), h2, ?_⟩)
      rw [show 2 + (m - 3 + 1) = m by omega]
      exact hm0
  have hτ : α j * ((1 - γ j) * (1 - β j) * β j ^ n) ≤
      pathKernel P 0 {ω | WithTop.some (n + 2) ≤ firstReturn {0} ω} := by
    rw [← hE]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h0 := (measure_biUnion_finset_le (μ := pathKernel P 0) (Finset.range (n - 1))
      (fun i => {ω : ℕ → ℕ | ω 2 = j + n ∧ ω (2 + (i + 1)) = 0})).trans
        (le_of_eq (Finset.sum_eq_zero hbad))
    rw [nonpos_iff_eq_zero.1 h0, add_zero]
  have hmeas : MeasurableSet {ω : ℕ → ℕ | WithTop.some (n + 2) ≤ firstReturn {0} ω} :=
    measurableSet_le_firstReturn (measurableSet_singleton 0) (n + 2)
  calc r ^ (n + 2) * (α j * ((1 - γ j) * (1 - β j) * β j ^ n))
      ≤ r ^ (n + 2) * pathKernel P 0 {ω | WithTop.some (n + 2) ≤ firstReturn {0} ω} :=
        mul_le_mul' le_rfl hτ
    _ = ∫⁻ ω, {ω | WithTop.some (n + 2) ≤ firstReturn {0} ω}.indicator
          (fun _ => r ^ (n + 2)) ω ∂pathKernel P 0 := by
        rw [lintegral_indicator_const hmeas]
    _ ≤ kendallMoment P {0} r 0 := by
        refine lintegral_mono fun ω => ?_
        by_cases h : ω ∈ {ω | WithTop.some (n + 2) ≤ firstReturn {0} ω}
        · rw [indicator_of_mem h, ← tpow_some]
          exact tpow_mono hr h
        · rw [indicator_of_notMem h]; exact zero_le

/-- **`E_0[r^{τ_0}] = ∞` for every `r > 1`** when `β_j → 1` (MT p. 409). -/
theorem upDown_kendallMoment_eq_top {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1)
    (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) (hα0 : ∀ j, j ≠ 0 → 0 < α j) (hγ1 : ∀ i, γ i < 1)
    (hlim : Tendsto β atTop (𝓝 1)) {r : ℝ≥0∞} (hr : 1 < r) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    kendallMoment (upDownKernel α γ β) {0} r 0 = ∞ := by
  have := isMarkovKernel_upDownKernel hα hγ hβ
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hrinv : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr
  obtain ⟨j, hjβ, hj1⟩ := ((hlim.eventually (lt_mem_nhds hrinv)).and
    (eventually_ge_atTop 1)).exists
  have hj : j ≠ 0 := by omega
  have hrβ : 1 < r * β j := by
    rcases eq_or_ne r ∞ with h | h
    · rw [h, ENNReal.top_mul (lt_of_le_of_lt bot_le hjβ).ne']; exact ENNReal.one_lt_top
    · calc (1 : ℝ≥0∞) = r * r⁻¹ := (ENNReal.mul_inv_cancel hr0 h).symm
        _ < r * β j := ENNReal.mul_lt_mul_right hr0 h hjβ
  set c := r ^ 2 * (α j * ((1 - γ j) * (1 - β j))) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr0) (mul_ne_zero (hα0 j hj).ne'
    (mul_ne_zero (tsub_pos_of_lt (hγ1 j)).ne' (tsub_pos_of_lt (hβ j)).ne'))
  have hlim2 : Tendsto (fun n : ℕ => c * (r * β j) ^ n) atTop (𝓝 ∞) := by
    have := ENNReal.Tendsto.const_mul (a := c) (ENNReal.tendsto_pow_atTop_nhds_top_iff.2 hrβ)
      (Or.inl ENNReal.top_ne_zero)
    rwa [ENNReal.mul_top hc0] at this
  have hb : ∀ n : ℕ, c * (r * β j) ^ n ≤ kendallMoment (upDownKernel α γ β) {0} r 0 := fun n => by
    have h := upDown_kendallMoment_ge hα hγ hβ hr.le hj n
    calc c * (r * β j) ^ n = r ^ (n + 2) * (α j * ((1 - γ j) * (1 - β j) * β j ^ n)) := by
          rw [hc, mul_pow]; ring
      _ ≤ _ := h
  exact top_le_iff.1 (le_of_tendsto' hlim2 hb)

/-- The chain (16.30) is irreducible when `α_j > 0` (`j ≥ 1`) and `γ_i > 0`. -/
theorem upDown_isIrreducibleChain {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1)
    (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) (hα0 : ∀ j, j ≠ 0 → 0 < α j)
    (hγ0 : ∀ i, 0 < γ i) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    IsIrreducibleChain (upDownKernel α γ β) := by
  have := isMarkovKernel_upDownKernel hα hγ hβ
  rw [isIrreducibleChain_iff]
  have hx0 : ∀ x, Leads (upDownKernel α γ β) x 0 := fun x => by
    induction x with
    | zero => exact Leads.refl _ 0
    | succ x ih =>
      refine (leads_of_pos ?_).trans ih
      rw [upDownMatrix_down]; exact (hγ0 _).ne'
  have h0y : ∀ y, Leads (upDownKernel α γ β) 0 y := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · exact Leads.refl _ 0
    · exact leads_of_pos (by simpa [upDownMatrix] using (hα0 y hy).ne')
  exact fun x y => ⟨(hx0 x).trans (h0y y), (hx0 y).trans (h0y x)⟩

/-- **The chain (16.30) is not geometrically ergodic when `β_j → 1`** (MT p. 409): `{0}` is Kendall
of no rate, and for no invariant probability `π` is `{0}` a geometrically ergodic atom
(Theorem 15.1.5). -/
theorem upDown_not_geomErgodic {α γ β : ℕ → ℝ≥0∞} (hα : ∑' j, α j = 1)
    (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) (hα0 : ∀ j, j ≠ 0 → 0 < α j)
    (hγ0 : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i < 1) (hlim : Tendsto β atTop (𝓝 1)) :
    haveI := isMarkovKernel_upDownKernel hα hγ hβ
    (∀ κ, ¬ IsKendall (upDownKernel α γ β) {0} κ) ∧
      ∀ (π : Measure ℕ) [IsProbabilityMeasure π], IsInvariant (upDownKernel α γ β) π →
        ¬ IsGeomErgodicAtom (upDownKernel α γ β) π {0} := by
  have := isMarkovKernel_upDownKernel hα hγ hβ
  refine ⟨fun κ hK => ?_, fun π _ hπ hge => ?_⟩
  · obtain ⟨-, hκ, -, M, hM, hb⟩ := hK
    exact hM <| top_le_iff.1 ((upDown_kendallMoment_eq_top hα hγ hβ hα0 hγ1 hlim hκ).symm.le.trans
      (hb 0 rfl))
  have hacc : IsAccessibleAtom (upDownKernel α γ β) Measure.count {0} :=
    ⟨isAtom_singleton _ 0, isMaximalIrreducibility_count _
      (upDown_isIrreducibleChain hα hγ hβ hα0 hγ0), by simp⟩
  obtain ⟨κ, hκ, -, hfull, -⟩ := theorem_15_1_5 hacc hπ hge
  have h0 := Measure.count_eq_zero_iff.1 hfull
  have hmem : (0 : ℕ) ∈ {x | kendallMoment (upDownKernel α γ β) {0} κ x ≠ ∞}ᶜ := fun h' =>
    h' (upDown_kendallMoment_eq_top hα hγ hβ hα0 hγ1 hlim hκ)
  rw [h0] at hmem
  exact hmem

/-! ### The drift of `V(x) = x` -/

/-- `Σₙ n bⁿ = b/(1 − b)²` in `[0, ∞]` for `b < 1`. -/
theorem tsum_nat_mul_pow_of_lt_one {b : ℝ≥0∞} (hb : b < 1) :
    ∑' n : ℕ, (n : ℝ≥0∞) * b ^ n = b * ((1 - b) ^ 2)⁻¹ := by
  have hbt : b ≠ ∞ := (hb.trans ENNReal.one_lt_top).ne
  set c := b.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c < 1 := by
    rw [hc, ← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hb
  have hbc : b = ENNReal.ofReal c := (ENNReal.ofReal_toReal hbt).symm
  have hnorm : ‖c‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hc0]; exact hc1
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have e : ∀ n : ℕ, (n : ℝ≥0∞) * b ^ n = ENNReal.ofReal (n * c ^ n) := fun n => by
    rw [hbc, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hc0]
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq,
    hbc, ENNReal.ofReal_div_of_pos (by nlinarith), show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
    ← ENNReal.ofReal_sub _ hc0, ← ENNReal.ofReal_pow (by linarith), div_eq_mul_inv]

/-- **The drift of `V(x) = x`** (MT p. 409): for `i ≥ 1`,
`PV(i) + γ_i = i + (1 − γ_i) β_i/(1 − β_i)`. -/
theorem upDown_drift {α γ β : ℕ → ℝ≥0∞} (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1) (i : ℕ) :
    ∫⁻ y, (y : ℝ≥0∞) ∂upDownKernel α γ β (i + 1) + γ (i + 1) =
      ((i + 1 : ℕ) : ℝ≥0∞) + (1 - γ (i + 1)) * (β (i + 1) * (1 - β (i + 1))⁻¹) := by
  set g := γ (i + 1)
  set b := β (i + 1)
  have hb1 : 1 - b ≠ 0 := (tsub_pos_of_lt (hβ _)).ne'
  have hbt : 1 - b ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rw [lintegral_matKernel, ← Summable.sum_add_tsum_nat_add'
    (f := fun y => upDownMatrix α γ β (i + 1) y * (y : ℝ≥0∞)) (k := i + 1) ENNReal.summable]
  have hlow : ∑ y ∈ Finset.range (i + 1), upDownMatrix α γ β (i + 1) y * (y : ℝ≥0∞) =
      g * i := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun y hy => by
      rw [upDownMatrix_low α γ β (Nat.succ_ne_zero i) (by have := Finset.mem_range.1 hy; omega),
        zero_mul], zero_add, upDownMatrix_down]
  have hup : ∑' n, upDownMatrix α γ β (i + 1) (n + (i + 1)) * ((n + (i + 1) : ℕ) : ℝ≥0∞) =
      (1 - g) * (b * (1 - b)⁻¹ + ((i : ℝ≥0∞) + 1)) := by
    simp_rw [upDownMatrix_up α γ β (Nat.add_one_ne_zero i), Nat.cast_add, Nat.cast_one]
    have e : ∀ n : ℕ, (1 - g) * (1 - b) * b ^ n * ((n : ℝ≥0∞) + ((i : ℝ≥0∞) + 1)) =
        (1 - g) * (1 - b) * ((n : ℝ≥0∞) * b ^ n) +
          (1 - g) * (1 - b) * ((i : ℝ≥0∞) + 1) * b ^ n := fun n => by ring
    change ∑' n : ℕ, (1 - g) * (1 - b) * b ^ n * ((n : ℝ≥0∞) + ((i : ℝ≥0∞) + 1)) = _
    simp_rw [e]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      tsum_nat_mul_pow_of_lt_one (hβ _), ENNReal.tsum_geometric]
    rw [show ((1 - b) ^ 2)⁻¹ = (1 - b)⁻¹ * (1 - b)⁻¹ by
      rw [pow_two, ENNReal.mul_inv (Or.inl hb1) (Or.inl hbt)]]
    have hc : (1 - b) * (1 - b)⁻¹ = 1 := ENNReal.mul_inv_cancel hb1 hbt
    calc (1 - g) * (1 - b) * (b * ((1 - b)⁻¹ * (1 - b)⁻¹)) +
          (1 - g) * (1 - b) * ((i : ℝ≥0∞) + 1) * (1 - b)⁻¹
        = (1 - g) * ((1 - b) * (1 - b)⁻¹) * (b * (1 - b)⁻¹) +
          (1 - g) * ((1 - b) * (1 - b)⁻¹) * ((i : ℝ≥0∞) + 1) := by ring
      _ = (1 - g) * (b * (1 - b)⁻¹ + ((i : ℝ≥0∞) + 1)) := by rw [hc]; ring
  rw [hlow]
  push_cast at hup ⊢
  rw [hup]
  have hg := hγ (i + 1)
  calc g * i + (1 - g) * (b * (1 - b)⁻¹ + (i + 1)) + g
      = (g + (1 - g)) * (i + 1) + (1 - g) * (b * (1 - b)⁻¹) := by ring
    _ = (i + 1) + (1 - g) * (b * (1 - b)⁻¹) := by rw [add_tsub_cancel_of_le hg, one_mul]

/-- **`V(x) = x` satisfies (V2) off `{0}`** under the book's condition
`(1 − γ_i)β_i/(1 − β_i) + ε ≤ γ_i` (MT p. 409): `PV(i) + ε ≤ i` for `i ≥ 1`. -/
theorem upDown_driftV2 {α γ β : ℕ → ℝ≥0∞} (hγ : ∀ i, γ i ≤ 1) (hβ : ∀ i, β i < 1)
    {ε : ℝ≥0∞} (i : ℕ)
    (hcond : (1 - γ (i + 1)) * (β (i + 1) * (1 - β (i + 1))⁻¹) + ε ≤ γ (i + 1)) :
    ∫⁻ y, (y : ℝ≥0∞) ∂upDownKernel α γ β (i + 1) + ε ≤ ((i + 1 : ℕ) : ℝ≥0∞) := by
  set X := (1 - γ (i + 1)) * (β (i + 1) * (1 - β (i + 1))⁻¹)
  have hX : X ≠ ∞ := ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hγ _))
    (le_self_add.trans hcond)
  have h := upDown_drift (α := α) hγ hβ i
  refine (ENNReal.add_le_add_iff_right hX).1 ?_
  calc ∫⁻ y, (y : ℝ≥0∞) ∂upDownKernel α γ β (i + 1) + ε + X
      = ∫⁻ y, (y : ℝ≥0∞) ∂upDownKernel α γ β (i + 1) + (X + ε) := by ring
    _ ≤ ∫⁻ y, (y : ℝ≥0∞) ∂upDownKernel α γ β (i + 1) + γ (i + 1) := add_le_add le_rfl hcond
    _ = ((i + 1 : ℕ) : ℝ≥0∞) + X := h

end MeynTweedie.Epilogue
