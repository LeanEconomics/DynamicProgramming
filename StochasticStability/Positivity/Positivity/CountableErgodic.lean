/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.AperiodicErgodic

/-!
# Ergodic chains on countable spaces (MT §13.1, Proposition 13.2.4 (ii))

Meyn and Tweedie, pp. 316–320 and 323. `X` is countable with measurable points; a state `α`
is the atom `{α}`.

**The decomposition.**
* (13.27) `tsum_tabooKernel_singleton`: `Σ_y _αPⁿ(x, y) = P_x(τ_α ≥ n)`.
* (13.20) `tendsto_realConv_entryLaw_atomRenewal`: if `u(n) → π(α)` (13.19) and the initial law
  reaches `α` almost surely (13.21), then `a_λ ∗ u (n) → π(α)` (Lemma D.7.1).
* **Proposition 13.1.1** (`proposition_13_1_1`, p. 318): for a positive chain with an accessible
  state `α`,
  `|Pⁿ(x, y) − π(y)| ≤ _αPⁿ(x, y) + |a_x ∗ u − π(α)| ∗ t_y (n) + π(α) Σ_{j > n} t_y(j)`.

**Ergodic theorems.**
* **Theorem 13.1.2** (`theorem_13_1_2`, p. 319): a positive Harris chain on a countable space
  with an ergodic state `α` satisfies `‖Pⁿ(x, ·) − π‖ = Σ_y |Pⁿ(x, y) − π(y)| → 0` for every `x`
  (`theorem_13_1_2_tsum`).
* **Proposition 13.2.4 (ii)** (p. 323), corrected: `proposition_13_2_4_ii` (positive Harris and
  aperiodic: every `x`), `proposition_13_2_4_ii_of_reach` (positive and aperiodic: every `x`
  that reaches an accessible state almost surely, in particular every `x` with `ψ{x} > 0`).

**Counterexamples.**
* `proposition_13_1_1_counterexample`: (13.17) fails for the oscillating chain below with the
  transient state `α = 0`.
* `proposition_13_2_4_ii_counterexample`: the "leaky" chain `leakKernel` on `ℕ` (state `0` is
  absorbing, from `i ≥ 1` the chain moves to `0` with probability `2^{−(i+1)}` and to `i + 1`
  otherwise) is positive (`π = δ₀`), hence recurrent, and aperiodic, but
  `‖Pⁿ(1, ·) − π‖ ≥ 1/2` for every `n`: from `1` it escapes to infinity with probability `≥ 1/2`.
* `theorem_13_3_1_counterexample`: the chain `oscKernel` on `ℕ` (`0 ↦ ½δ₀ + ½δ₁`, `1 ↦ δ₂`,
  `x ≥ 2 ↦ δ₁`) is positive Harris and strongly aperiodic in the sense of p. 114 (`{0}` is
  `½δ₀`-small), yet `‖Pⁿ(1, ·) − π‖ ≥ 1/2` for every `n`: the small set `{0}` is not in `B⁺(X)`
  and the chain has period `2` on `{1, 2}`.

**Corrections.**
* Proposition 13.1.1 is stated "for any `x, y, α ∈ X`", but the representation (13.13) of `π`
  through `α` needs `α ∈ B⁺(X)`; for a transient `α` the bound (13.17) fails
  (`proposition_13_1_1_counterexample`). The proposition is proved for `ψ{α} > 0`.
* Proposition 13.2.4 (ii) as printed ("positive recurrent aperiodic chain on a countable space,
  every initial state") is false: recurrence in the sense of Chapter 8 does not prevent
  transient states from escaping (`proposition_13_2_4_ii_counterexample`). It holds for positive
  Harris chains (in particular when every state communicates, `isHarris_of_countable`), and for
  every state that reaches an accessible state almost surely.
* Theorem 13.3.1 is false for strongly aperiodic chains whose small set is not in `B⁺(X)`
  (`theorem_13_3_1_counterexample`); see `SplitErgodic`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The countable decomposition -/

/-- (13.27): on a countable space, `Σ_y _αPⁿ⁺¹(x, y) = P_x(τ_α ≥ n + 1)`. -/
theorem tsum_tabooKernel_singleton [Countable X] [MeasurableSingletonClass X] (P : Kernel X X)
    {α : Set X} (hα : MeasurableSet α) (n : ℕ) (x : X) :
    ∑' y, tabooKernel P hα n x {y} = tabooKernel P hα n x univ :=
  (measure_univ_eq_tsum_singleton _).symm

/-- (13.20), (13.51): if `u(n) → π(α)` and `Σ a_λ = 1`, then `a_λ ∗ u (n) → π(α)`. -/
theorem tendsto_realConv_entryLaw_atomRenewal {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {a : X} {c : ℝ} (herg : Tendsto (atomRenewal P α a) atTop (𝓝 c))
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : ∫⁻ x, hitProb P α x ∂μ = 1) :
    Tendsto (realConv (entryLaw P hα μ) (atomRenewal P α a)) atTop (𝓝 c) := by
  have hE := hasSum_entryLaw P hα μ
  rw [hμ, ENNReal.toReal_one] at hE
  have := lemma_D_7_1 (entryLaw_nonneg P hα μ) hE.summable herg
  rwa [hE.tsum_eq, mul_one] at this

/-- **Proposition 13.1.1** (MT p. 318): for a positive chain with an accessible state `α` and
invariant probability `π`, for all states `x`, `y` and `n ≥ 1` (here `n + 1`),
`|Pⁿ(x, y) − π(y)| ≤ _αPⁿ(x, y) + |a_x ∗ u − π(α)| ∗ t_y (n) + π(α) Σ_{j > n} t_y(j)`. -/
theorem proposition_13_1_1 [MeasurableSingletonClass X] {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hpos : IsPositive P ψ) {α : X} (hψα : 0 < ψ {α}) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (x y : X) (n : ℕ) :
    |((P ^ (n + 1) : Kernel X X) x {y}).toReal - (π {y}).toReal| ≤
      (tabooKernel P (measurableSet_singleton α) n x {y}).toReal +
        realConv (fun k => |realConv (entryLaw P (measurableSet_singleton α) (Measure.dirac x))
            (atomRenewal P {α} α) k - (π {α}).toReal|)
          (lastExitSeq P (measurableSet_singleton α) α (({y} : Set X).indicator 1)) (n + 1) +
        (π {α}).toReal * ∑' i, lastExitSeq P (measurableSet_singleton α) α
          (({y} : Set X).indicator 1) (i + n + 2) := by
  have h : IsAccessibleAtom P ψ {α} := ⟨isAtom_singleton P α, hpos.1, hψα⟩
  have hrep := eq_smul_atomMeasure_of_accessible h (proposition_10_1_1 hpos) rfl hπ
  have hind : ∀ z, ({y} : Set X).indicator (1 : X → ℝ≥0∞) z ≤ 1 := fun z => by
    by_cases hz : z ∈ ({y} : Set X) <;> simp [hz]
  have hd := regenerative_decomposition_48 h.1 rfl hrep (Measure.dirac x) ENNReal.one_ne_top hind n
  simp only [lintegral_indicator_one (measurableSet_singleton y), dirac_kernel, tabooSeq] at hd
  exact hd

/-! ### Ergodic theorems on countable spaces -/

/-- **Theorem 13.1.2** (MT p. 319): a positive Harris chain on a countable space with an ergodic
state `α` satisfies `‖Pⁿ(x, ·) − π‖ → 0` for every initial state `x`. -/
theorem theorem_13_1_2 [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) {α : X} (hψα : 0 < ψ {α})
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (herg : IsErgodicAtom P π {α}) (x : X) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) := by
  have h := theorem_13_3_1_i hph ⟨isAtom_singleton P α, hph.1.1, hψα⟩ hπ herg (Measure.dirac x)
  simp_rw [dirac_kernel] at h
  exact h

/-- Theorem 13.1.2 in the countable form (13.23)–(13.24): `Σ_y |Pⁿ(x, y) − π(y)| → 0`. -/
theorem theorem_13_1_2_tsum [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) {α : X} (hψα : 0 < ψ {α})
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (herg : IsErgodicAtom P π {α}) (x : X) :
    Tendsto (fun n => ∑' y, |((P ^ n : Kernel X X) x).real {y} - π.real {y}|) atTop (𝓝 0) := by
  have h := theorem_13_1_2 hph hψα hπ herg x
  refine h.congr fun n => ?_
  have := isMarkovKernel_pow P n
  exact tvNorm_eq_tsum _ _

/-- **Proposition 13.2.4 (ii)** (MT p. 323), corrected: a positive Harris aperiodic chain on a
countable space satisfies `‖Pⁿ(x, ·) − π‖ → 0` for every `x`. -/
theorem proposition_13_2_4_ii [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (x : X) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) :=
  theorem_13_3_3_dirac hph hap hπ x

/-- **Proposition 13.2.4 (ii)** for positive aperiodic chains that need not be Harris: the
convergence holds from every state `x` that reaches an accessible state `α` almost surely, in
particular from every `x` with `ψ{x} > 0`. -/
theorem proposition_13_2_4_ii_of_reach [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {α : X} (hψα : 0 < ψ {α})
    {x : X} (hx : hitProb P {α} x = 1) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) := by
  have h : IsAccessibleAtom P ψ {α} := ⟨isAtom_singleton P α, hpos.1, hψα⟩
  have hrep := eq_smul_atomMeasure_of_accessible h (proposition_10_1_1 hpos) rfl hπ
  have herg := proposition_13_2_4_i hpos hap h hπ α rfl
  have hc := tendsto_tvNorm_of_ergodic_atom h.1 rfl hrep herg (Measure.dirac x)
    (by rw [lintegral_dirac' _ (measurable_hitProb P (measurableSet_singleton α)), hx])
  simp_rw [dirac_kernel] at hc
  exact hc

/-- A state `x` with `ψ{x} > 0` reaches itself almost surely (recurrence of the atom `{x}`), so
`proposition_13_2_4_ii_of_reach` applies to it. -/
theorem hitProb_self_eq_one [MeasurableSingletonClass X] {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hpos : IsPositive P ψ) {x : X} (hψx : 0 < ψ {x}) :
    hitProb P {x} x = 1 := by
  have h : IsAccessibleAtom P ψ {x} := ⟨isAtom_singleton P x, hpos.1, hψx⟩
  exact (h.isRecurrentChain_iff (mem_singleton x)).1 (proposition_10_1_1 hpos)

/-! ### The leaky chain: a counterexample to Proposition 13.2.4 (ii) as printed -/

/-- The escape probabilities `q(i) = 2^{−(i+1)}`. -/
noncomputable def leakProb (i : ℕ) : ℝ≥0∞ := 2⁻¹ ^ (i + 1)

/-- The leaky chain on `ℕ`: `0` is absorbing; from `i ≥ 1` the chain jumps to `0` with
probability `2^{−(i+1)}` and to `i + 1` otherwise. -/
noncomputable def leakKernel : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun i =>
    if i = 0 then Measure.dirac 0
    else leakProb i • Measure.dirac 0 + (1 - leakProb i) • Measure.dirac (i + 1)

/-- `P(0, ·) = δ₀`. -/
theorem leakKernel_zero : leakKernel 0 = Measure.dirac 0 := rfl

/-- `P(i, ·) = q(i) δ₀ + (1 − q(i)) δ_{i+1}` for `i ≥ 1`. -/
theorem leakKernel_of_ne {i : ℕ} (hi : i ≠ 0) :
    leakKernel i = leakProb i • Measure.dirac 0 + (1 - leakProb i) • Measure.dirac (i + 1) := by
  change (if i = 0 then _ else _) = _
  simp [hi]

/-- `q(i) ≤ 1`. -/
theorem leakProb_le_one (i : ℕ) : leakProb i ≤ 1 :=
  pow_le_one₀ zero_le (ENNReal.inv_le_one.2 one_le_two)

/-- The leaky chain is a transition kernel. -/
theorem isMarkovKernel_leakKernel : IsMarkovKernel leakKernel := by
  refine ⟨fun i => ⟨?_⟩⟩
  by_cases hi : i = 0
  · rw [hi, leakKernel_zero, measure_univ]
  · rw [leakKernel_of_ne hi, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      add_tsub_cancel_of_le (leakProb_le_one i)]

/-- `δ₀` is invariant for the leaky chain. -/
theorem isInvariant_leakKernel : IsInvariant leakKernel (Measure.dirac 0) := by
  unfold IsInvariant
  rw [dirac_kernel, leakKernel_zero]

/-- From `0`, the chain stays at `0`: `Pⁿ(0, ·) = δ₀`. -/
theorem leakKernel_pow_zero (n : ℕ) : (leakKernel ^ n : Kernel ℕ ℕ) 0 = Measure.dirac 0 := by
  induction n with
  | zero => rw [pow_zero_apply]
  | succ n ih =>
    rw [pow_succ']
    change leakKernel ∘ₘ (leakKernel ^ n : Kernel ℕ ℕ) 0 = _
    rw [ih, dirac_kernel, leakKernel_zero]

/-- The key estimate: `Pⁿ(i, {0}) ≤ 2^{−i}` for `i ≥ 1`. -/
theorem leakKernel_pow_le (n : ℕ) : ∀ i, i ≠ 0 →
    (leakKernel ^ n : Kernel ℕ ℕ) i {0} ≤ 2⁻¹ ^ i := by
  have := isMarkovKernel_leakKernel
  induction n with
  | zero =>
    intro i hi
    rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton 0),
      indicator_of_notMem (by simpa using hi)]
    exact zero_le
  | succ n ih =>
    intro i hi
    rw [pow_succ_apply _ n i (measurableSet_singleton 0), leakKernel_of_ne hi,
      lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac, leakKernel_pow_zero,
      Measure.dirac_apply_of_mem (mem_singleton 0), smul_eq_mul, smul_eq_mul, mul_one]
    have h1 := ih (i + 1) (Nat.succ_ne_zero i)
    calc leakProb i + (1 - leakProb i) * (leakKernel ^ n : Kernel ℕ ℕ) (i + 1) {0}
        ≤ 2⁻¹ ^ (i + 1) + 1 * 2⁻¹ ^ (i + 1) := by
          gcongr
          · exact le_rfl
          · exact tsub_le_self
      _ = 2⁻¹ ^ i := by
          rw [one_mul, ← two_mul, pow_succ, mul_comm (2⁻¹ ^ i), ← mul_assoc,
            ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- From `0`, `L(0, A) = 0` for `0 ∉ A`. -/
theorem leakKernel_hitProb_zero {A : Set ℕ} (hA : (0 : ℕ) ∉ A) :
    haveI := isMarkovKernel_leakKernel; hitProb leakKernel A 0 = 0 := by
  have := isMarkovKernel_leakKernel
  by_contra h
  obtain ⟨n, hn⟩ := (hitProb_pos_iff leakKernel (Set.Countable.measurableSet (Set.to_countable A))
    0).1 (pos_iff_ne_zero.2 h)
  rw [leakKernel_pow_zero, Measure.dirac_apply' _
    (Set.Countable.measurableSet (Set.to_countable A)), indicator_of_notMem hA] at hn
  exact lt_irrefl 0 hn

/-- `δ₀` is a maximal irreducibility measure for the leaky chain. -/
theorem leakKernel_isMaximalIrreducibility :
    haveI := isMarkovKernel_leakKernel
    IsMaximalIrreducibility leakKernel (Measure.dirac 0) := by
  have := isMarkovKernel_leakKernel
  refine ⟨fun h => by simpa using congrArg (fun m : Measure ℕ => m univ) h, fun A hA hpos x => ?_,
    fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
  · have h0A : (0 : ℕ) ∈ A := by
      by_contra h; rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hpos
      exact lt_irrefl 0 hpos
    refine (hitProb_pos_iff leakKernel hA x).2 ⟨0, ?_⟩
    rw [zero_add, pow_one]
    by_cases hx : x = 0
    · rw [hx, leakKernel_zero, Measure.dirac_apply' _ hA, indicator_of_mem h0A]; exact one_pos
    · rw [leakKernel_of_ne hx, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
        indicator_of_mem h0A, smul_eq_mul, Pi.one_apply, mul_one]
      exact lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
        le_self_add
  · have h0A : (0 : ℕ) ∉ A := by
      intro h; rw [Measure.dirac_apply' _ hA, indicator_of_mem h] at h0; simp at h0
    by_contra hne
    have := hφ A hA (pos_iff_ne_zero.2 hne) 0
    rw [leakKernel_hitProb_zero h0A] at this
    exact lt_irrefl 0 this

/-- The leaky chain is positive (with `π = δ₀`), hence recurrent. -/
theorem leakKernel_isPositive :
    haveI := isMarkovKernel_leakKernel; IsPositive leakKernel (Measure.dirac 0) :=
  ⟨leakKernel_isMaximalIrreducibility, Measure.dirac 0, inferInstance, isInvariant_leakKernel⟩

/-- The leaky chain is aperiodic: `{0}` is `δ₀`-small at time `1`. -/
theorem leakKernel_isAperiodic :
    haveI := isMarkovKernel_leakKernel; IsAperiodic leakKernel (Measure.dirac 0) := by
  have := isMarkovKernel_leakKernel
  have hC : IsSmallSet leakKernel 1 (Measure.dirac 0) {0} :=
    ⟨measurableSet_singleton 0, one_pos, by simp, fun x hx => by
      rw [mem_singleton_iff.1 hx, pow_one, leakKernel_zero]⟩
  have h1 : (0 : ℝ≥0∞) < Measure.dirac (0 : ℕ) {0} := by simp
  have hper := isPeriod_gcd leakKernel leakKernel_isMaximalIrreducibility hC h1 h1
  have hg : setGcd (smallTimes leakKernel {0} (Measure.dirac 0)) = 1 :=
    Nat.dvd_one.1 (setGcd_dvd (smallTimes_isAddClosed leakKernel h1)
      (mem_smallTimes_of_isSmallSet hC) one_pos (mem_smallTimes_of_isSmallSet hC))
  rwa [hg] at hper

/-- **The counterexample to Proposition 13.2.4 (ii) as printed**: the leaky chain is positive
(hence recurrent) and aperiodic, but `‖Pⁿ(1, ·) − π‖ ≥ 1/2` for every `n`, so
`Pⁿ(1, ·) ↛ π` in total variation. -/
theorem proposition_13_2_4_ii_counterexample :
    haveI := isMarkovKernel_leakKernel
    IsPositive leakKernel (Measure.dirac 0) ∧ IsRecurrentChain leakKernel (Measure.dirac 0) ∧
      IsAperiodic leakKernel (Measure.dirac 0) ∧
      (∀ n, (1 : ℝ) / 2 ≤ tvNorm ((leakKernel ^ n : Kernel ℕ ℕ) 1) (Measure.dirac 0)) ∧
      ¬ Tendsto (fun n => tvNorm ((leakKernel ^ n : Kernel ℕ ℕ) 1) (Measure.dirac 0)) atTop
        (𝓝 0) := by
  have := isMarkovKernel_leakKernel
  have hbound : ∀ n, (1 : ℝ) / 2 ≤ tvNorm ((leakKernel ^ n : Kernel ℕ ℕ) 1) (Measure.dirac 0) :=
    fun n => by
      have := isMarkovKernel_pow leakKernel n
      have h := abs_measureReal_sub_le_tvNorm ((leakKernel ^ n : Kernel ℕ ℕ) 1) (Measure.dirac 0)
        (measurableSet_singleton 0)
      have hle := leakKernel_pow_le n 1 one_ne_zero
      have hle' : ((leakKernel ^ n : Kernel ℕ ℕ) 1).real {0} ≤ 1 / 2 := by
        rw [measureReal_def]
        have := ENNReal.toReal_mono (by simp) hle
        simpa using this
      rw [measureReal_def (Measure.dirac 0), Measure.dirac_apply_of_mem (mem_singleton 0),
        ENNReal.toReal_one] at h
      refine le_trans ?_ h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  refine ⟨leakKernel_isPositive, proposition_10_1_1 leakKernel_isPositive,
    leakKernel_isAperiodic, hbound, fun h => ?_⟩
  have := (tendsto_order.1 h).2 (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := this.exists
  exact absurd (hbound n) (not_le.2 hn)

/-! ### The oscillating chain: a counterexample to Theorem 13.3.1 as printed -/

/-- The chain on `ℕ` with `0 ↦ ½δ₀ + ½δ₁`, `1 ↦ δ₂` and `x ≥ 2 ↦ δ₁`. -/
noncomputable def oscKernel : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun x =>
    if x = 0 then (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1
    else if x = 1 then Measure.dirac 2 else Measure.dirac 1

/-- `P(0, ·) = ½δ₀ + ½δ₁`. -/
theorem oscKernel_zero :
    oscKernel 0 = (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1 := rfl

/-- `P(1, ·) = δ₂`. -/
theorem oscKernel_one : oscKernel 1 = Measure.dirac 2 := rfl

/-- `P(x, ·) = δ₁` for `x ≥ 2`. -/
theorem oscKernel_of_two_le {x : ℕ} (hx : 2 ≤ x) : oscKernel x = Measure.dirac 1 := by
  change (if x = 0 then _ else if x = 1 then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_right_of_eq_false _ _ (by simp; omega)]

/-- The oscillating chain is a transition kernel. -/
theorem isMarkovKernel_oscKernel : IsMarkovKernel oscKernel := by
  refine ⟨fun x => ⟨?_⟩⟩
  rcases Nat.lt_or_ge x 2 with hx | hx
  · interval_cases x
    · simp only [oscKernel_zero, Measure.add_apply, Measure.smul_apply, measure_univ,
        smul_eq_mul, mul_one, ENNReal.inv_two_add_inv_two]
    · rw [oscKernel_one, measure_univ]
  · rw [oscKernel_of_two_le hx, measure_univ]

/-- `Pⁿ(1, ·)` alternates between `δ₁` and `δ₂`. -/
theorem oscKernel_pow_one (n : ℕ) :
    (oscKernel ^ n : Kernel ℕ ℕ) 1 = Measure.dirac (if n % 2 = 0 then 1 else 2) := by
  induction n with
  | zero => rw [pow_zero_apply]; rfl
  | succ n ih =>
    rw [pow_succ']
    change oscKernel ∘ₘ (oscKernel ^ n : Kernel ℕ ℕ) 1 = _
    rw [ih, dirac_kernel]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [ite_eq_left_of_eq_true _ _ (by simp [h]), oscKernel_one,
        ite_eq_right_of_eq_false _ _ (by simp; omega)]
    · rw [ite_eq_right_of_eq_false _ _ (by simp; omega), oscKernel_of_two_le le_rfl,
        ite_eq_left_of_eq_true _ _ (by simp; omega)]

/-- From `x ≥ 1`, one of `P(x, ·)`, `P²(x, ·)` is `δ₁` and the other `δ₂`. -/
theorem oscKernel_pow_of_pos {x : ℕ} (hx : x ≠ 0) :
    ((oscKernel ^ 1 : Kernel ℕ ℕ) x = Measure.dirac 1 ∧
        (oscKernel ^ 2 : Kernel ℕ ℕ) x = Measure.dirac 2) ∨
      ((oscKernel ^ 1 : Kernel ℕ ℕ) x = Measure.dirac 2 ∧
        (oscKernel ^ 2 : Kernel ℕ ℕ) x = Measure.dirac 1) := by
  have h2 : ∀ y, (oscKernel ^ 2 : Kernel ℕ ℕ) y = oscKernel ∘ₘ oscKernel y := fun y => by
    rw [pow_two]; rfl
  by_cases h1 : x = 1
  · right
    rw [h1, pow_one, h2, oscKernel_one, dirac_kernel, oscKernel_of_two_le le_rfl]
    exact ⟨rfl, rfl⟩
  · left
    rw [pow_one, h2, oscKernel_of_two_le (by omega), dirac_kernel, oscKernel_one]
    exact ⟨rfl, rfl⟩

/-- `ψ = δ₁ + δ₂`. -/
noncomputable def oscPsi : Measure ℕ := Measure.dirac 1 + Measure.dirac 2

/-- `ψ(A) > 0` iff `1 ∈ A` or `2 ∈ A`. -/
theorem oscPsi_pos_iff (A : Set ℕ) : 0 < oscPsi A ↔ 1 ∈ A ∨ 2 ∈ A := by
  have hA := Set.Countable.measurableSet (Set.to_countable A)
  rw [oscPsi, Measure.add_apply, Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hA]
  by_cases h1 : 1 ∈ A <;> by_cases h2 : 2 ∈ A <;> simp [h1, h2]

/-- From `x ≥ 1`, `L(x, A) = 1` for every `A ∈ B⁺(X)`. -/
theorem oscKernel_hitProb_of_pos {x : ℕ} (hx : x ≠ 0) {A : Set ℕ} (hA : 1 ∈ A ∨ 2 ∈ A) :
    haveI := isMarkovKernel_oscKernel; hitProb oscKernel A x = 1 := by
  have := isMarkovKernel_oscKernel
  have hm := Set.Countable.measurableSet (Set.to_countable A)
  refine le_antisymm (hitProb_le_one _ _ _) ?_
  have h1 := pow_le_hitProb oscKernel hm 0 x
  have h2 := pow_le_hitProb oscKernel hm 1 x
  rw [zero_add] at h1
  rcases oscKernel_pow_of_pos hx with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at h1 <;> rw [e2] at h2 <;>
    rcases hA with hA | hA <;>
    first
    | exact (by rw [Measure.dirac_apply_of_mem hA] : (1 : ℝ≥0∞) ≤ _).trans h1
    | exact (by rw [Measure.dirac_apply_of_mem hA] : (1 : ℝ≥0∞) ≤ _).trans h2

/-- From `0`, `L(0, A) = 1` for every `A ∈ B⁺(X)` containing `0`. -/
theorem oscKernel_hitProb_zero {A : Set ℕ} (h0 : (0 : ℕ) ∈ A) (hA : 1 ∈ A ∨ 2 ∈ A) :
    haveI := isMarkovKernel_oscKernel; hitProb oscKernel A 0 = 1 := by
  have := isMarkovKernel_oscKernel
  have hm := Set.Countable.measurableSet (Set.to_countable A)
  refine le_antisymm (hitProb_le_one _ _ _) ?_
  by_cases h1 : (1 : ℕ) ∈ A
  · have h := pow_le_hitProb oscKernel hm 0 0
    simp only [zero_add, pow_one, oscKernel_zero, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem h0, Measure.dirac_apply_of_mem h1, smul_eq_mul, mul_one,
      ENNReal.inv_two_add_inv_two] at h
    exact h
  · have h2 : (2 : ℕ) ∈ A := hA.resolve_left h1
    have hL1 := oscKernel_hitProb_of_pos one_ne_zero (Or.inr h2)
    rw [hitProb_first_step oscKernel hm 0, ← lintegral_indicator hm.compl, oscKernel_zero,
      lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac, indicator_of_notMem (by simpa using h0),
      indicator_of_mem (by simpa using h1), hL1]
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem h0,
      Measure.dirac_apply' _ hm, indicator_of_notMem h1, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add]
    rw [ENNReal.inv_two_add_inv_two]

/-- `ψ = δ₁ + δ₂` is a maximal irreducibility measure for the oscillating chain. -/
theorem oscKernel_isMaximalIrreducibility :
    haveI := isMarkovKernel_oscKernel; IsMaximalIrreducibility oscKernel oscPsi := by
  have := isMarkovKernel_oscKernel
  refine ⟨fun h => ?_, fun A hA hpos x => ?_, fun φ hφ => Measure.AbsolutelyContinuous.mk
    fun A hA h0 => ?_⟩
  · have := congrArg (fun m : Measure ℕ => m {1}) h
    simp [oscPsi] at this
  · rw [oscPsi_pos_iff] at hpos
    by_cases hx : x = 0
    · subst hx
      rcases hpos with h1 | h2
      · refine lt_of_lt_of_le ?_ (pow_le_hitProb oscKernel hA 0 0)
        simp only [zero_add, pow_one, oscKernel_zero, Measure.add_apply, Measure.smul_apply,
          Measure.dirac_apply_of_mem h1, smul_eq_mul, mul_one]
        exact lt_of_lt_of_le (by norm_num) le_add_self
      · refine lt_of_lt_of_le ?_ (pow_le_hitProb oscKernel hA 1 0)
        rw [pow_succ_apply _ 1 0 hA, oscKernel_zero, lintegral_add_measure,
          lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
          pow_one, oscKernel_one, Measure.dirac_apply_of_mem h2, smul_eq_mul, smul_eq_mul,
          mul_one]
        exact lt_of_lt_of_le (by norm_num) le_add_self
    · rw [oscKernel_hitProb_of_pos hx hpos]; exact one_pos
  · have h12 : (1 : ℕ) ∉ A ∧ (2 : ℕ) ∉ A := by
      by_contra h
      rw [not_and_or, not_not, not_not] at h
      exact absurd h0 ((oscPsi_pos_iff A).2 h).ne'
    by_contra hne
    have hL := hφ A hA (pos_iff_ne_zero.2 hne) 1
    obtain ⟨n, hn⟩ := (hitProb_pos_iff oscKernel hA 1).1 hL
    rw [oscKernel_pow_one, Measure.dirac_apply' _ hA] at hn
    split_ifs at hn
    · rw [indicator_of_notMem h12.1] at hn; exact lt_irrefl 0 hn
    · rw [indicator_of_notMem h12.2] at hn; exact lt_irrefl 0 hn

/-- The oscillating chain is Harris. -/
theorem oscKernel_isHarris : haveI := isMarkovKernel_oscKernel; IsHarris oscKernel oscPsi := by
  have := isMarkovKernel_oscKernel
  refine ⟨oscKernel_isMaximalIrreducibility, fun A hA hψA => ?_⟩
  rw [oscPsi_pos_iff] at hψA
  refine (proposition_9_1_1 oscKernel hA fun x hx => ?_).2
  by_cases h0 : x = 0
  · subst h0; exact oscKernel_hitProb_zero hx hψA
  · exact oscKernel_hitProb_of_pos h0 hψA

/-- `π = ½δ₁ + ½δ₂`. -/
noncomputable def oscPi : Measure ℕ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 1 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 2

/-- `π` is an invariant probability for the oscillating chain. -/
theorem oscPi_isInvariant : IsProbabilityMeasure oscPi ∧ IsInvariant oscKernel oscPi := by
  refine ⟨⟨?_⟩, ?_⟩
  · simp only [oscPi, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      ENNReal.inv_two_add_inv_two]
  · unfold IsInvariant
    rw [oscPi, Measure.comp_add, Measure.comp_smul, Measure.comp_smul, dirac_kernel, dirac_kernel,
      oscKernel_one, oscKernel_of_two_le le_rfl, add_comm]

/-- The oscillating chain is strongly aperiodic in the sense of MT p. 114: `{0}` is `½δ₀`-small
at time `1` and `½δ₀({0}) > 0`. -/
theorem oscKernel_isStronglyAperiodic : IsStronglyAperiodic oscKernel := by
  refine ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac 0, {0}, ⟨measurableSet_singleton 0, one_pos, ?_, ?_⟩, ?_⟩
  · intro h; have := congrArg (fun m : Measure ℕ => m {0}) h; simp at this
  · intro x hx
    rw [mem_singleton_iff.1 hx, pow_one, oscKernel_zero]
    exact Measure.le_add_right le_rfl
  · simp

/-- **The counterexample to Theorem 13.3.1 as printed**: the oscillating chain is positive
Harris and strongly aperiodic (with the definition of p. 114), but `‖Pⁿ(1, ·) − π‖ ≥ 1/2` for
every `n`, so it does not converge in total variation. -/
theorem theorem_13_3_1_counterexample :
    haveI := isMarkovKernel_oscKernel
    IsPositiveHarris oscKernel oscPsi ∧ IsStronglyAperiodic oscKernel ∧
      IsProbabilityMeasure oscPi ∧ IsInvariant oscKernel oscPi ∧
      (∀ n, (1 : ℝ) / 2 ≤ tvNorm ((oscKernel ^ n : Kernel ℕ ℕ) ∘ₘ Measure.dirac 1) oscPi) ∧
      ¬ Tendsto (fun n => tvNorm ((oscKernel ^ n : Kernel ℕ ℕ) ∘ₘ Measure.dirac 1) oscPi) atTop
        (𝓝 0) := by
  have := isMarkovKernel_oscKernel
  obtain ⟨hπp, hπi⟩ := oscPi_isInvariant
  have hbound : ∀ n, (1 : ℝ) / 2 ≤
      tvNorm ((oscKernel ^ n : Kernel ℕ ℕ) ∘ₘ Measure.dirac 1) oscPi := fun n => by
    have := isMarkovKernel_pow oscKernel n
    have h := abs_measureReal_sub_le_tvNorm ((oscKernel ^ n : Kernel ℕ ℕ) ∘ₘ Measure.dirac 1)
      oscPi (measurableSet_singleton 1)
    have hπ1 : oscPi.real {1} = 1 / 2 := by
      simp only [measureReal_def, oscPi, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (mem_singleton 1),
        Measure.dirac_apply' _ (measurableSet_singleton 1), smul_eq_mul, mul_one]
      rw [indicator_of_notMem (by simp), mul_zero, add_zero, ENNReal.toReal_inv]
      norm_num
    rw [hπ1, dirac_kernel, oscKernel_pow_one, measureReal_def] at h
    rw [dirac_kernel, oscKernel_pow_one]
    refine le_trans (le_of_eq ?_) h
    split_ifs
    · rw [Measure.dirac_apply_of_mem (mem_singleton 1)]; norm_num
    · rw [Measure.dirac_apply' _ (measurableSet_singleton 1), indicator_of_notMem (by simp)]
      norm_num
  refine ⟨⟨oscKernel_isHarris, oscKernel_isMaximalIrreducibility, oscPi, hπp, hπi⟩,
    oscKernel_isStronglyAperiodic, hπp, hπi, hbound, fun h => ?_⟩
  obtain ⟨n, hn⟩ := ((tendsto_order.1 h).2 (1 / 2) (by norm_num)).exists
  exact absurd (hbound n) (not_le.2 hn)

/-- **The counterexample to Proposition 13.1.1 for a state outside `B⁺(X)`**: for the oscillating
chain (positive Harris), the transient state `α = 0` (with `ψ{0} = 0`) and `x = y = 1`, `n = 1`,
the left side of (13.17) is `|P(1, {1}) − π{1}| = 1/2`, while every term of the right side
vanishes (the chain started at `1` never visits `0`, and `π{0} = 0`). -/
theorem proposition_13_1_1_counterexample :
    haveI := isMarkovKernel_oscKernel
    oscPsi {0} = 0 ∧
    ¬ (|((oscKernel ^ (0 + 1) : Kernel ℕ ℕ) 1 {1}).toReal - (oscPi {1}).toReal| ≤
      (tabooKernel oscKernel (measurableSet_singleton 0) 0 1 {1}).toReal +
        realConv (fun k => |realConv (entryLaw oscKernel (measurableSet_singleton 0)
            (Measure.dirac 1)) (atomRenewal oscKernel {0} 0) k - (oscPi {0}).toReal|)
          (lastExitSeq oscKernel (measurableSet_singleton 0) 0 (({1} : Set ℕ).indicator 1))
          (0 + 1) +
        (oscPi {0}).toReal * ∑' i, lastExitSeq oscKernel (measurableSet_singleton 0) 0
          (({1} : Set ℕ).indicator 1) (i + 0 + 2)) := by
  have := isMarkovKernel_oscKernel
  have hψ0 : oscPsi {0} = 0 := by
    have h := (oscPsi_pos_iff {0}).not.2 (by simp)
    exact nonpos_iff_eq_zero.1 (not_lt.1 h)
  have hπ0 : oscPi {0} = 0 := by
    simp [oscPi]
  have hπ1 : (oscPi {1}).toReal = 1 / 2 := by
    simp only [oscPi, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_singleton 1),
      Measure.dirac_apply' _ (measurableSet_singleton 1), smul_eq_mul, mul_one]
    rw [indicator_of_notMem (by simp), mul_zero, add_zero, ENNReal.toReal_inv]
    norm_num
  have hentry : ∀ k, entryLaw oscKernel (measurableSet_singleton 0) (Measure.dirac 1) k = 0 :=
    fun k => by
      rcases k with _ | k
      · rfl
      · rw [entryLaw_dirac_succ]
        have h := tabooKernel_le_pow oscKernel (measurableSet_singleton 0) k 1
          (measurableSet_singleton 0)
        rw [oscKernel_pow_one, Measure.dirac_apply' _ (measurableSet_singleton 0)] at h
        have h0 : tabooKernel oscKernel (measurableSet_singleton 0) k 1 {0} = 0 := by
          refine nonpos_iff_eq_zero.1 (h.trans (le_of_eq ?_))
          split_ifs <;> simp
        rw [h0, ENNReal.toReal_zero]
  have hconv : realConv (entryLaw oscKernel (measurableSet_singleton 0) (Measure.dirac 1))
      (atomRenewal oscKernel {0} 0) = fun _ => 0 := by
    funext k
    simp [realConv, hentry]
  refine ⟨hψ0, fun h => ?_⟩
  rw [hπ0, ENNReal.toReal_zero, zero_mul, add_zero, hconv, hπ1, zero_add, pow_one,
    oscKernel_one, Measure.dirac_apply' _ (measurableSet_singleton 1),
    tabooKernel_zero, oscKernel_one, Measure.dirac_apply' _ (measurableSet_singleton 1),
    indicator_of_notMem (by simp)] at h
  simp only [sub_zero, abs_zero, ENNReal.toReal_zero, zero_add] at h
  have h2 : realConv (fun _ => (0 : ℝ))
      (lastExitSeq oscKernel (measurableSet_singleton 0) 0 (({1} : Set ℕ).indicator 1)) 1 = 0 := by
    simp [realConv]
  rw [h2] at h
  norm_num at h

end MeynTweedie.Positivity
