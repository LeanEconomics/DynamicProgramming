/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.MM1Spectrum
import Epilogue.UniformErgodic

/-!
# Markov chain Monte Carlo (MT §20.2.2)

Meyn and Tweedie, pp. 522–523. The target `π` and the proposal `q(x, ·)` are densities with
respect to a σ-finite (s-finite) measure `μ` on a general state space (the book takes `X = ℝ` and
Lebesgue measure).

* `mhAccept` (20.21), `mhAccept_mem`, `measurable_mhAccept`: the acceptance probability
  `α(x, y) = min(1, π(y)q(y, x)/(π(x)q(x, y)))`.
* `mhAccept_flow`, `mhAccept_detailed_balance`: `π(x)q(x, y)α(x, y) = min(π(x)q(x, y),
  π(y)q(y, x))` is symmetric in `(x, y)`.
* `mhKernel`, `mhKernel_apply`, `isMarkovKernel_mhKernel`: the Metropolis–Hastings kernel
  `P(x, A) = ∫_A qα dμ + (1 − ∫ qα dμ)δₓ(A)`.
* `mhKernel_isReversible` (p. 522): the chain satisfies the detailed balance equations (20.5) for
  `π(dx) = π(x)μ(dx)`, hence (`IsReversible.isInvariant`) `π` is invariant.
* `indepSampler_minorization`, `indepSampler_uniformlyErgodic` (p. 523, (i), "if" direction): for
  the independence sampler `q(x, y) = p(y)` with `π ≤ Mp`, `P(x, ·) ≥ M⁻¹π`, the whole space is
  small and `‖Pⁿ(x, ·) − π‖ ≤ 2(1 − M⁻¹)ⁿ` (Theorem 16.2.4).

**Not formalised** (results quoted from [256, 179, 330, 331, 79, 335, 125]): the converse in (i)
(if `sup π/p = ∞` the independence sampler is not even geometrically ergodic), and (ii) on the
random-walk Metropolis–Hastings algorithm (rarely uniformly ergodic; geometrically ergodic iff the
tails of `π` are exponentially bounded). These need lower bounds on return times for specific
families of targets, beyond the scope of the Epilogue's own proofs; the fluid-model approach of
[125] and the machine-learning remarks of §20.2.3 are surveys.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The Metropolis–Hastings acceptance probability -/

/-- **The Metropolis–Hastings acceptance probability** (20.21), MT p. 522:
`α(x, y) = min(1, π(y)q(y, x)/(π(x)q(x, y)))`, and `1` when `π(x)q(x, y) = 0`. -/
noncomputable def mhAccept (πd : X → ℝ) (q : X → X → ℝ) (x y : X) : ℝ :=
  if πd x * q x y = 0 then 1 else min 1 (πd y * q y x / (πd x * q x y))

omit [MeasurableSpace X] in
/-- `0 ≤ α ≤ 1`. -/
theorem mhAccept_mem {πd : X → ℝ} {q : X → X → ℝ} (hπ : ∀ x, 0 ≤ πd x)
    (hq : ∀ x y, 0 ≤ q x y) (x y : X) : 0 ≤ mhAccept πd q x y ∧ mhAccept πd q x y ≤ 1 := by
  unfold mhAccept
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_min zero_le_one (div_nonneg (mul_nonneg (hπ y) (hq y x))
      (mul_nonneg (hπ x) (hq x y))), min_le_left _ _⟩

omit [MeasurableSpace X] in
/-- **The Metropolis–Hastings flow is symmetric**: `π(x)q(x, y)α(x, y) = min(π(x)q(x, y),
π(y)q(y, x))`, so `π(x)q(x, y)α(x, y) = π(y)q(y, x)α(y, x)` (the detailed balance of the moves). -/
theorem mhAccept_flow {πd : X → ℝ} {q : X → X → ℝ} (hπ : ∀ x, 0 ≤ πd x)
    (hq : ∀ x y, 0 ≤ q x y) (x y : X) :
    πd x * (q x y * mhAccept πd q x y) = min (πd x * q x y) (πd y * q y x) := by
  unfold mhAccept
  split_ifs with h
  · rw [mul_one, h]
    exact (min_eq_left (mul_nonneg (hπ y) (hq y x))).symm
  · have hpos : 0 < πd x * q x y := lt_of_le_of_ne (mul_nonneg (hπ x) (hq x y)) (Ne.symm h)
    rw [← mul_assoc, mul_min_of_nonneg _ _ hpos.le, mul_one, mul_div_cancel₀ _ h]

omit [MeasurableSpace X] in
/-- The flow identity in symmetric form. -/
theorem mhAccept_detailed_balance {πd : X → ℝ} {q : X → X → ℝ} (hπ : ∀ x, 0 ≤ πd x)
    (hq : ∀ x y, 0 ≤ q x y) (x y : X) :
    πd x * (q x y * mhAccept πd q x y) = πd y * (q y x * mhAccept πd q y x) := by
  rw [mhAccept_flow hπ hq, mhAccept_flow hπ hq, min_comm]

/-- The acceptance probability is measurable. -/
theorem measurable_mhAccept {πd : X → ℝ} {q : X → X → ℝ} (hπ : Measurable πd)
    (hq : Measurable (Function.uncurry q)) : Measurable (Function.uncurry (mhAccept πd q)) := by
  have h1 : Measurable fun p : X × X => πd p.1 * q p.1 p.2 :=
    (hπ.comp measurable_fst).mul hq
  have h2 : Measurable fun p : X × X => πd p.2 * q p.2 p.1 :=
    (hπ.comp measurable_snd).mul (hq.comp measurable_swap)
  exact Measurable.ite (h1 (measurableSet_singleton 0)) measurable_const
    (measurable_const.min (h2.div h1))

/-! ### The Metropolis–Hastings kernel and detailed balance -/

/-- The density `q(x, y)α(x, y)` of the accepted moves. -/
noncomputable def mhMove (πd : X → ℝ) (q : X → X → ℝ) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal (q x y * mhAccept πd q x y)

/-- **The Metropolis–Hastings kernel** (MT p. 522), with proposal density `q(x, ·)` and target
density `π` with respect to `μ`:
`P(x, A) = ∫_A q(x, y)α(x, y) μ(dy) + (1 − ∫ q(x, y)α(x, y) μ(dy)) δₓ(A)`. -/
noncomputable def mhKernel (μ : Measure X) [SFinite μ] (πd : X → ℝ) (q : X → X → ℝ) :
    Kernel X X :=
  Kernel.withDensity (Kernel.const X μ) (mhMove πd q) +
    Kernel.withDensity Kernel.id fun x _ => 1 - ∫⁻ y, mhMove πd q x y ∂μ

/-- `P(x, A) = ∫_A qα dμ + r(x)δₓ(A)`. -/
theorem mhKernel_apply {μ : Measure X} [SFinite μ] {πd : X → ℝ} {q : X → X → ℝ}
    (hπ : Measurable πd) (hq : Measurable (Function.uncurry q)) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    mhKernel μ πd q x A = ∫⁻ y in A, mhMove πd q x y ∂μ +
      (1 - ∫⁻ y, mhMove πd q x y ∂μ) * A.indicator 1 x := by
  have hm : Measurable (Function.uncurry (mhMove πd q)) :=
    ENNReal.measurable_ofReal.comp (hq.mul (measurable_mhAccept hπ hq))
  have hr : Measurable (Function.uncurry fun (x : X) (_ : X) =>
      1 - ∫⁻ y, mhMove πd q x y ∂μ) :=
    (measurable_const.sub (hm.lintegral_prod_right' (ν := μ))).comp measurable_fst
  rw [mhKernel, add_apply, Measure.add_apply, Kernel.withDensity_apply' _ hm,
    Kernel.withDensity_apply' _ hr, Kernel.const_apply, Kernel.id_apply,
    setLIntegral_const, Measure.dirac_apply' _ hA]

/-- **The Metropolis–Hastings chain is a Markov chain** when `q(x, ·)` is a probability density. -/
theorem isMarkovKernel_mhKernel {μ : Measure X} [SFinite μ] {πd : X → ℝ} {q : X → X → ℝ}
    (hπ : Measurable πd) (hq : Measurable (Function.uncurry q)) (hπ0 : ∀ x, 0 ≤ πd x)
    (hq0 : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = 1) :
    IsMarkovKernel (mhKernel μ πd q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [mhKernel_apply hπ hq x MeasurableSet.univ, Measure.restrict_univ,
    indicator_of_mem (mem_univ x), Pi.one_apply, mul_one]
  have hle : ∫⁻ y, mhMove πd q x y ∂μ ≤ 1 := by
    rw [← hq1 x]
    refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    have := mhAccept_mem hπ0 hq0 x y
    nlinarith [hq0 x y]
  exact add_tsub_cancel_of_le hle

/-- **The Metropolis–Hastings chain satisfies detailed balance** (20.5) with respect to
`π(dx) = π(x)μ(dx)` (MT p. 522): it is reversible. -/
theorem mhKernel_isReversible {μ : Measure X} [SFinite μ] {πd : X → ℝ} {q : X → X → ℝ}
    (hπ : Measurable πd) (hq : Measurable (Function.uncurry q)) (hπ0 : ∀ x, 0 ≤ πd x)
    (hq0 : ∀ x y, 0 ≤ q x y) :
    IsReversible (mhKernel μ πd q) (μ.withDensity fun x => ENNReal.ofReal (πd x)) := by
  have hm : Measurable (Function.uncurry (mhMove πd q)) :=
    ENNReal.measurable_ofReal.comp (hq.mul (measurable_mhAccept hπ hq))
  have hπm : Measurable fun x => ENNReal.ofReal (πd x) := ENNReal.measurable_ofReal.comp hπ
  -- the symmetric flow
  set F : X → X → ℝ≥0∞ := fun x y => ENNReal.ofReal (πd x) * mhMove πd q x y with hF
  have hFsymm : ∀ x y, F x y = F y x := fun x y => by
    simp only [hF, mhMove]
    rw [← ENNReal.ofReal_mul (hπ0 x), ← ENNReal.ofReal_mul (hπ0 y),
      mhAccept_detailed_balance hπ0 hq0]
  have hFm : Measurable (Function.uncurry F) := (hπm.comp measurable_fst).mul hm
  have key : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      ∫⁻ x in A, mhKernel μ πd q x B ∂(μ.withDensity fun x => ENNReal.ofReal (πd x)) =
        (∫⁻ x in A, ∫⁻ y in B, F x y ∂μ ∂μ) +
          ∫⁻ x in A ∩ B, ENNReal.ofReal (πd x) * (1 - ∫⁻ y, mhMove πd q x y ∂μ) ∂μ :=
    fun A B hA hB => by
      have hr : Measurable fun x => 1 - ∫⁻ y, mhMove πd q x y ∂μ :=
        measurable_const.sub (hm.lintegral_prod_right' (ν := μ))
      rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hπm
        ((mhKernel μ πd q).measurable_coe hB) hA]
      have e : ∀ x, ((fun x => ENNReal.ofReal (πd x)) * fun x => mhKernel μ πd q x B) x =
          (∫⁻ y in B, F x y ∂μ) +
            B.indicator (fun x => ENNReal.ofReal (πd x) * (1 - ∫⁻ y, mhMove πd q x y ∂μ)) x :=
        fun x => by
          rw [Pi.mul_apply, mhKernel_apply hπ hq x hB, mul_add]
          change _ = ∫⁻ y in B, ENNReal.ofReal (πd x) * mhMove πd q x y ∂μ + _
          have hmx : Measurable fun y => mhMove πd q x y := hm.comp measurable_prodMk_left
          rw [lintegral_const_mul _ hmx]
          congr 1
          by_cases hx : x ∈ B
          · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one]
          · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]
      simp_rw [e]
      rw [lintegral_add_left (f := fun x => ∫⁻ y in B, F x y ∂μ)
        (hFm.lintegral_prod_right' (ν := μ.restrict B)), setLIntegral_indicator hB,
        inter_comm]
  intro A B hA hB
  rw [key A B hA hB, key B A hB hA, inter_comm,
    lintegral_lintegral_swap (hFm.aemeasurable)]
  congr 1
  refine setLIntegral_congr_fun hB fun x _ => setLIntegral_congr_fun hA fun y _ => hFsymm y x


/-! ### The independence sampler -/

/-- **The independence sampler is minorized by `π/M`** (MT p. 523): with proposal
`q(x, y) = p(y)` and `π ≤ Mp`, `P(x, ·) ≥ M⁻¹ π` for every `x`. -/
theorem indepSampler_minorization {μ : Measure X} [SFinite μ] {πd p : X → ℝ}
    (hπ : Measurable πd) (hp : Measurable p) (hπ0 : ∀ x, 0 ≤ πd x) (hp0 : ∀ x, 0 ≤ p x)
    {M : ℝ} (hM : 0 < M) (hbd : ∀ y, πd y ≤ M * p y) (x : X) :
    ENNReal.ofReal M⁻¹ • μ.withDensity (fun y => ENNReal.ofReal (πd y)) ≤
      mhKernel μ πd (fun _ y => p y) x := by
  have hq : Measurable (Function.uncurry fun (_ : X) (y : X) => p y) := hp.comp measurable_snd
  refine Measure.le_intro fun A hA _ => ?_
  have hπm : Measurable fun y => ENNReal.ofReal (πd y) := ENNReal.measurable_ofReal.comp hπ
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA, ← lintegral_const_mul _ hπm,
    mhKernel_apply hπ hq x hA]
  refine le_trans (lintegral_mono fun y => ?_) le_self_add
  rw [mhMove, ← ENNReal.ofReal_mul (inv_nonneg.2 hM.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hy : M⁻¹ * πd y ≤ p y := by
    rw [inv_mul_le_iff₀ hM]; exact hbd y
  unfold mhAccept
  split_ifs with h
  · rw [mul_one]; exact hy
  · have ha : 0 < πd x * p y := lt_of_le_of_ne (mul_nonneg (hπ0 x) (hp0 y)) (Ne.symm h)
    have hπx : 0 < πd x := by
      rcases (hπ0 x).lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1, zero_mul] at ha; exact absurd ha (lt_irrefl 0)
    have hpy : 0 < p y := by
      rcases (hp0 y).lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1, mul_zero] at ha; exact absurd ha (lt_irrefl 0)
    beta_reduce
    rw [mul_min_of_nonneg _ _ (hp0 y), mul_one]
    refine le_min hy ?_
    have e : p y * (πd y * p x / (πd x * p y)) = πd y * p x / πd x := by field_simp
    rw [e, le_div_iff₀ hπx]
    have := mul_le_mul_of_nonneg_left (hbd x) (hπ0 y)
    calc M⁻¹ * πd y * πd x ≤ M⁻¹ * (πd y * (M * p x)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hM.le)
      _ = πd y * p x := by field_simp

/-- **The independence sampler is uniformly ergodic when `sup π/p < ∞`** (MT p. 523, the "if"
direction of (i)): if `π ≤ Mp`, then `‖Pⁿ(x, ·) − π‖ ≤ 2(1 − M⁻¹)ⁿ` for every `x` and `n`
(Theorem 16.2.4 with the whole space small). -/
theorem indepSampler_uniformlyErgodic {μ : Measure X} [SFinite μ] {πd p : X → ℝ}
    (hπ : Measurable πd) (hp : Measurable p) (hπ0 : ∀ x, 0 ≤ πd x) (hp0 : ∀ x, 0 ≤ p x)
    (hπ1 : ∫⁻ y, ENNReal.ofReal (πd y) ∂μ = 1) (hp1 : ∫⁻ y, ENNReal.ofReal (p y) ∂μ = 1)
    {M : ℝ} (hM : 0 < M) (hbd : ∀ y, πd y ≤ M * p y) (x : X) (n : ℕ) :
    tvNorm ((mhKernel μ πd (fun _ y => p y) ^ n) x)
      (μ.withDensity fun y => ENNReal.ofReal (πd y)) ≤ 2 * (1 - M⁻¹) ^ n := by
  have hq : Measurable (Function.uncurry fun (_ : X) (y : X) => p y) := hp.comp measurable_snd
  have := isMarkovKernel_mhKernel (μ := μ) hπ hq hπ0 (fun _ y => hp0 y) (fun _ => hp1)
  set π' := μ.withDensity fun y => ENNReal.ofReal (πd y) with hπ'
  have : IsProbabilityMeasure π' :=
    ⟨by rw [hπ', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hπ1⟩
  have hinv := (mhKernel_isReversible (μ := μ) hπ hq hπ0 (fun _ y => hp0 y)).isInvariant
  have hν0 : ENNReal.ofReal M⁻¹ • π' ≠ 0 := fun h => by
    have := congrArg (fun m : Measure X => m univ) h
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      Measure.coe_zero, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le.2 (inv_pos.2 hM)] at this
  have : IsFiniteMeasure (ENNReal.ofReal M⁻¹ • π') :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩
  have hsmall : IsSmallSet (mhKernel μ πd fun _ y => p y) 1 (ENNReal.ofReal M⁻¹ • π') univ :=
    ⟨MeasurableSet.univ, one_pos, hν0, fun y _ => by
      rw [pow_one]; exact indepSampler_minorization hπ hp hπ0 hp0 hM hbd y⟩
  have h := theorem_16_2_4 hsmall hinv x n
  rwa [Nat.div_one, Measure.real_def, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (inv_nonneg.2 hM.le)] at h

end MeynTweedie.Epilogue
