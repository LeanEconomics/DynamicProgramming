/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SmallSets
import LimitTheorems.RandomWalkIrreducibility
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Small sets for specific models (MT §5.3, and the examples of pp. 96–98)

Meyn and Tweedie, §5.3, pp. 106–110, and the atoms discussed on pp. 96–98.

**Atoms.**
* `isAccessibleAtom_singleton_countable` (p. 96): for an irreducible chain on a countable space
  every point is an accessible atom.
* `map_add_left_inj`, `randomWalk_not_isAccessibleAtom` (p. 96): for random walk on `ℝ` with an
  absolutely continuous increment law there is no accessible atom.
* `halfLine_isAccessibleAtom_zero` (pp. 96, 98): for random walk on a half line with
  `Γ(−∞, 0) > 0`, `{0}` is an accessible atom (for every maximal irreducibility measure).

**Random walk on a half line** (§5.3.1, p. 106).
* `halfLine_isSmallSet_Iic`: if `Γ(−∞, 0) > 0`, every `[0, c]` is small, with minorizing measure
  a multiple of `δ₀`; `halfLine_isSmall_of_isCompact`: every compact set is small.

**Random walk with a density** (§5.3.2, p. 107).
* `randomWalk_isSmallSet_Icc`: if the increment law has a density `γ ≥ δ > 0` on `(−β, β)`, then
  `C = [−β/2, β/2]` is small for the one-step kernel.

**Scalar linear models** (§5.3.5, p. 110, for `n = 1`).
* `ar1_isSmallSet_of_density`: for the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` with an error density
  bounded below on every bounded interval, every bounded measurable set is small (with `m = 1`
  and a multiple of Lebesgue measure on `[−1, 1]`).
* `gaussianReal_density_ge`, `ar1_gaussian_isSmall_of_isCompact`: in the Gaussian case every
  compact set is small; for `α = 1` this is the Gaussian random walk.

**The GI/G/1 queue** (§5.3.3, p. 108).
* **Proposition 5.3.2** (`proposition_5_3_2`): for a ladder kernel on `ℤ₊ × ℝ₊` whose bottom rung
  satisfies `P(0, x; {0} × A) = G(x, ∞) H(A)` (the formula `Λ₀*(x, ·) = H(·) G(x, ∞)` derived in
  the book), `{0} × [0, β]` is `ν₁`-small with `ν₁ = G(β, ∞) H` placed on the bottom rung.

Proposition 5.3.1 (spread-out random walks) is in `SpreadOut`.

**Not formalised here.** Proposition 5.3.3 (the forward recurrence time `δ`-skeleton is not
constructed as a Markov chain in this project) and the multidimensional Gaussian LSS(F, G) claim
of §5.3.5 (it needs the continuity and positivity of the `n`-step Gaussian density). The
derivation of the bottom-rung formula of the GI/G/1 ladder chain from (5.29)–(5.31) is not
formalised: the ladder chain is not constructed from the queue.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-! ### Atoms -/

/-- MT p. 96: for an irreducible chain on a countable space, every point is an accessible atom
(for counting measure, a maximal irreducibility measure). -/
theorem isAccessibleAtom_singleton_countable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] [Nonempty X] (P : Kernel X X) [IsMarkovKernel P]
    (hP : IsIrreducibleChain P) (x : X) : IsAccessibleAtom P Measure.count {x} :=
  ⟨isAtom_singleton P x, isMaximalIrreducibility_count P hP, by simp⟩

/-- MT pp. 96, 98: for random walk on a half line with `Γ(−∞, 0) > 0`, `{0}` is an accessible
atom for every maximal irreducibility measure. -/
theorem halfLine_isAccessibleAtom_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsAccessibleAtom (halfLineWalkKernel Γ) ψ {0} := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨_, hiff⟩ := proposition_4_3_1 Γ
  have hirr := hiff.2 h
  refine ⟨isAtom_singleton _ 0, hψ, (hψ.pos_iff_hitProb_pos (measurableSet_singleton 0)).2
    fun x => hirr {0} (measurableSet_singleton 0) (by simp) x⟩

/-- A probability measure on `ℝ` is moved by every nonzero translation: if
`Γ(· − x) = Γ(· − y)` then `x = y`. -/
theorem map_add_left_inj (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {x y : ℝ}
    (h : Γ.map (x + ·) = Γ.map (y + ·)) : x = y := by
  by_contra hne
  set s := |y - x| with hs
  have hs0 : 0 < s := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have hF : ∀ w, Γ (Iic (w - x)) = Γ (Iic (w - y)) := fun w => by
    have := congrArg (fun μ : Measure ℝ => μ (Iic w)) h
    simp only [Measure.map_apply (measurable_const_add _) measurableSet_Iic] at this
    have e : ∀ c : ℝ, (c + ·) ⁻¹' Iic w = Iic (w - c) := fun c => by
      ext v; simp only [mem_preimage, mem_Iic]; constructor <;> intro <;> linarith
    rwa [e, e] at this
  have hG : ∀ w, Γ (Ici (w - x)) = Γ (Ici (w - y)) := fun w => by
    have := congrArg (fun μ : Measure ℝ => μ (Ici w)) h
    simp only [Measure.map_apply (measurable_const_add _) measurableSet_Ici] at this
    have e : ∀ c : ℝ, (c + ·) ⁻¹' Ici w = Ici (w - c) := fun c => by
      ext v; simp only [mem_preimage, mem_Ici]; constructor <;> intro <;> linarith
    rwa [e, e] at this
  -- both distribution functions are `s`-periodic
  have hFs : ∀ w, Γ (Iic (w + s)) = Γ (Iic w) := fun w => by
    rcases abs_cases (y - x) with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hF (w + y); rw [hs, h1] at *
      rw [show w + y - x = w + (y - x) by ring, show w + y - y = w by ring] at this
      exact this
    · have := hF (w + x); rw [hs, h1] at *
      rw [show w + x - y = w + -(y - x) by ring, show w + x - x = w by ring] at this
      exact this.symm
  have hGs : ∀ w, Γ (Ici (w + s)) = Γ (Ici w) := fun w => by
    rcases abs_cases (y - x) with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hG (w + y); rw [hs, h1] at *
      rw [show w + y - x = w + (y - x) by ring, show w + y - y = w by ring] at this
      exact this
    · have := hG (w + x); rw [hs, h1] at *
      rw [show w + x - y = w + -(y - x) by ring, show w + x - x = w by ring] at this
      exact this.symm
  have hFk : ∀ (k : ℕ) w, Γ (Iic (w + k * s)) = Γ (Iic w) := fun k => by
    induction k with
    | zero => intro w; simp
    | succ k ih => intro w; rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hFs, ih]
  have hGk : ∀ (k : ℕ) w, Γ (Ici (w - k * s)) = Γ (Ici w) := fun k => by
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [← ih w, ← hGs (w - ((k + 1 : ℕ) : ℝ) * s)]
      congr 2
      push_cast
      ring
  -- hence `Γ(−∞, 0] = 1` and `Γ[1, ∞) = 1`, which is impossible
  have hk : Tendsto (fun k : ℕ => (k : ℝ) * s) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hs0
  have hF1 : Γ (Iic 0) = 1 := by
    have h1 := (tendsto_measure_Iic_atTop Γ).comp (tendsto_atTop_add_const_left _ 0 hk)
    rw [measure_univ] at h1
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun k => ?_) h1
    exact (hFk k 0).symm
  have hG1 : Γ (Ici 1) = 1 := by
    have hk' : Tendsto (fun k : ℕ => 1 - (k : ℝ) * s) atTop atBot :=
      tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp hk) |>.congr fun k => by
        simp [sub_eq_add_neg]
    have h1 := (tendsto_measure_Ici_atBot Γ).comp hk'
    rw [measure_univ] at h1
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun k => ?_) h1
    exact (hGk k 1).symm
  have hdisj : Disjoint (Iic (0 : ℝ)) (Ici 1) :=
    Set.disjoint_left.2 fun v h1 h2 => by simp only [mem_Iic, mem_Ici] at h1 h2; linarith
  have := measure_union hdisj measurableSet_Ici (μ := Γ)
  rw [hF1, hG1] at this
  have hle := prob_le_one (μ := Γ) (s := Iic (0 : ℝ) ∪ Ici 1)
  rw [this] at hle
  norm_num at hle

/-- MT p. 96: for random walk on `ℝ` with an increment law absolutely continuous with respect to
Lebesgue measure, accessible atoms do not exist. An atom is at most one point, since a
probability on `ℝ` is moved by every nonzero translation, and a single point is never hit. -/
theorem randomWalk_not_isAccessibleAtom (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ : Γ ≪ volume) {ψ : Measure ℝ} (α : Set ℝ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    ¬ IsAccessibleAtom (randomWalkKernel Γ) ψ α := by
  have := isMarkovKernel_randomWalkKernel Γ
  rintro ⟨⟨hαm, ν, hν⟩, hψ, hpos⟩
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  -- `α = {x}`
  have hsub : α ⊆ {x} := fun y hy => by
    have h := (hν y hy).trans (hν x hx).symm
    rw [randomWalkKernel_apply, randomWalkKernel_apply] at h
    exact mem_singleton_iff.2 (map_add_left_inj Γ h)
  have hxpos : 0 < ψ {x} := hpos.trans_le (measure_mono hsub)
  -- but `{x}` is never hit: `P(y, {x}) = Γ{x − y} = 0`
  have h1 : ∀ y, randomWalkKernel Γ y {x} = 0 := fun y => by
    rw [randomWalkKernel_apply' Γ y (measurableSet_singleton x)]
    refine hΓ (measure_mono_null (fun w hw => ?_) (Real.volume_singleton (a := x - y)))
    simp only [mem_ofPred_eq, mem_singleton_iff] at hw ⊢
    linarith
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurableSet_singleton x) x).1
    (hψ.2.1 {x} (measurableSet_singleton x) hxpos x)
  rw [pow_succ_apply' _ n x (measurableSet_singleton x)] at hn
  simp [h1] at hn

/-! ### Random walk on a half line -/

/-- MT §5.3.1, p. 106: if `Γ(−∞, 0) > 0`, every `[0, c]` is small for random walk on a half
line, with a multiple of `δ₀` as minorizing measure. -/
theorem halfLine_isSmallSet_Iic (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0))
    (c : ℝ≥0) : ∃ (m : ℕ) (δ : ℝ≥0∞), 0 < δ ∧
      IsSmallSet (halfLineWalkKernel Γ) m (δ • Measure.dirac 0) (Iic c) := by
  obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
  obtain ⟨n, hn⟩ := exists_nat_gt ((c : ℝ) / ε)
  have hcn : (c : ℝ) < (n + 1) * ε := by
    have := (div_lt_iff₀ hε).1 hn
    nlinarith
  refine ⟨n + 1, Γ (Iio (-ε)) ^ (n + 1), ENNReal.pow_pos hΓε _, measurableSet_Iic, by omega,
    smul_measure_ne_zero (by simp) (ENNReal.pow_pos hΓε _).ne', fun x hx => ?_⟩
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
  by_cases h0 : (0 : ℝ≥0) ∈ B
  · rw [indicator_of_mem h0, Pi.one_apply, mul_one]
    have hx' : (x : ℝ) < (n + 1) * ε := lt_of_le_of_lt (by exact_mod_cast hx) hcn
    exact (halfLine_pow_zero_ge Γ hε le_rfl n x hx').trans
      (measure_mono (singleton_subset_iff.2 h0))
  · rw [indicator_of_notMem h0, mul_zero]
    exact zero_le

/-- MT §5.3.1, p. 106: if `Γ(−∞, 0) > 0`, every compact subset of `[0, ∞)` is small for random
walk on a half line. -/
theorem halfLine_isSmall_of_isCompact (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {C : Set ℝ≥0} (hC : IsCompact C) : IsSmall (halfLineWalkKernel Γ) C := by
  obtain ⟨c, hc⟩ := hC.bddAbove
  obtain ⟨m, δ, -, hs⟩ := halfLine_isSmallSet_Iic Γ h c
  exact ⟨m, _, hs.mono hC.measurableSet fun x hx => hc hx⟩

/-! ### Random walk with a density -/

/-- MT §5.3.2, p. 107: if the increment law of a random walk on `ℝ` has a density `γ ≥ δ > 0` on
`(−β, β)`, then `C = [−β/2, β/2]` is `δ μ_Leb|_C`-small (with `m = 1`). -/
theorem randomWalk_isSmallSet_Icc (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    (hβ : 0 < β) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    IsSmallSet (randomWalkKernel Γ) 1 (δ • volume.restrict (Icc (-(β / 2)) (β / 2)))
      (Icc (-(β / 2)) (β / 2)) := by
  refine ⟨measurableSet_Icc, one_pos, smul_measure_ne_zero ?_ hδ, fun x hx => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    simp only [ENNReal.ofReal_eq_zero, not_le]
    linarith
  · rw [pow_one]
    refine Measure.le_intro fun B hB _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
    exact (randomWalk_step_ge Γ hγ hγδ hx (hB.inter measurableSet_Icc) inter_subset_right).trans
      (measure_mono inter_subset_left)

/-! ### Scalar linear models -/

/-- MT §5.3.5, p. 110 (`n = 1`): for the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` whose error law has a
density bounded below on every bounded interval, every set `C ⊆ [−R, R]` is small, with `m = 1`
and a multiple of Lebesgue measure on `[−1, 1]` as minorizing measure. -/
theorem ar1_isSmallSet_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ)
    {γ : ℝ → ℝ≥0∞} (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A)
    (hpos : ∀ R : ℝ, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ w ∈ Icc (-R) R, c ≤ γ w) {R : ℝ} {C : Set ℝ}
    (hCm : MeasurableSet C) (hCR : C ⊆ Icc (-R) R) :
    ∃ c : ℝ≥0∞, 0 < c ∧ IsSmallSet (ar1Kernel Γ α) 1 (c • volume.restrict (Icc (-1) 1)) C := by
  obtain ⟨c, hc, hcγ⟩ := hpos (|α| * |R| + 1)
  refine ⟨c, hc, hCm, one_pos, smul_measure_ne_zero ?_ hc.ne', fun x hx => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    norm_num
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB, ar1Kernel_apply' Γ α x hB]
  have hS : MeasurableSet {w | α * x + w ∈ B} := (measurable_const_add (α * x)) hB
  -- the translate of `B ∩ [−1, 1]` lies in `[−R', R']`, where the density is at least `c`
  have hsub : (· + α * x) ⁻¹' (B ∩ Icc (-1) 1) ⊆
      {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1) := by
    intro y hy
    simp only [mem_preimage, mem_inter_iff, mem_Icc] at hy
    obtain ⟨hyB, hy1, hy2⟩ := hy
    have hxR : |x| ≤ |R| := by
      have := hCR hx
      rw [abs_le]; constructor <;> cases abs_cases R <;> linarith [this.1, this.2]
    have hax : |α * x| ≤ |α| * |R| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxR (abs_nonneg α)
    refine ⟨by simpa [add_comm] using hyB, ?_, ?_⟩ <;> cases abs_cases (α * x) <;> linarith
  have hvol : volume (B ∩ Icc (-1) 1) = volume ((· + α * x) ⁻¹' (B ∩ Icc (-1) 1)) :=
    (measure_preimage_add_right volume (α * x) _).symm
  calc c * volume (B ∩ Icc (-1) 1)
      ≤ c * volume ({w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1)) := by
        rw [hvol]; gcongr
    _ = ∫⁻ _ in {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1), c := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in {w | α * x + w ∈ B} ∩ Icc (-(|α| * |R| + 1)) (|α| * |R| + 1), γ w :=
        setLIntegral_mono' (hS.inter measurableSet_Icc) fun w hw => hcγ w hw.2
    _ ≤ ∫⁻ w in {w | α * x + w ∈ B}, γ w := lintegral_mono_set inter_subset_left
    _ ≤ Γ {w | α * x + w ∈ B} := hγ _ hS

/-- The standard Gaussian density is bounded below on every bounded interval:
`φ(w) ≥ (2π)^{−1/2} e^{−R²/2}` for `|w| ≤ R`. -/
theorem gaussianReal_density_ge (R : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ w ∈ Icc (-R) R, c ≤ gaussianPDF 0 1 w := by
  refine ⟨ENNReal.ofReal ((√(2 * Real.pi))⁻¹ * Real.exp (-R ^ 2 / 2)), ?_, fun w hw => ?_⟩
  · rw [ENNReal.ofReal_pos]
    positivity
  · rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have : w ^ 2 ≤ R ^ 2 := sq_le_sq' hw.1 hw.2
    linarith

/-- MT §5.3.5, p. 110 (`n = 1`): for the Gaussian AR(1) model (and, with `α = 1`, the Gaussian
random walk), every compact set is small. -/
theorem ar1_gaussian_isSmall_of_isCompact (α : ℝ) {C : Set ℝ} (hC : IsCompact C) :
    IsSmall (ar1Kernel (gaussianReal 0 1) α) C := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  have hCR : C ⊆ Icc (-R) R := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
    exact this
  have hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, gaussianPDF 0 1 x ≤ gaussianReal 0 1 A :=
    fun A hA => by
      rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ hA]
  obtain ⟨c, -, hs⟩ := ar1_isSmallSet_of_density (gaussianReal 0 1) α hγ gaussianReal_density_ge
    hC.measurableSet hCR
  exact ⟨1, _, hs⟩

/-! ### The GI/G/1 queue: Proposition 5.3.2 -/

/-- **Proposition 5.3.2** (MT p. 108). Let `P` be a transition kernel on `ℤ₊ × ℝ₊` (queue length
and residual service time at arrival epochs) whose bottom rung satisfies
`P(0, x; {0} × A) = G(x, ∞) H(A)`, the formula `Λ₀*(x, ·) = H(·) G(x, ∞)` of the book. If
`G(β, ∞) > 0` and `H` is a probability, then `{0} × [0, β]` is `ν₁`-small with
`ν₁ = G(β, ∞) H` on the bottom rung. -/
theorem proposition_5_3_2 (P : Kernel (ℕ × ℝ≥0) (ℕ × ℝ≥0)) (G : Measure ℝ≥0) (H : Measure ℝ≥0)
    [IsProbabilityMeasure H]
    (hP : ∀ x A, MeasurableSet A → P (0, x) ({0} ×ˢ A) = G (Ioi x) * H A) {β : ℝ≥0}
    (hG : 0 < G (Ioi β)) :
    IsSmallSet P 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y))) ({0} ×ˢ Iic β) := by
  have hmk : Measurable fun y : ℝ≥0 => ((0 : ℕ), y) := measurable_const.prodMk measurable_id
  refine ⟨(measurableSet_singleton 0).prod measurableSet_Iic, one_pos, smul_measure_ne_zero ?_
    hG.ne', fun z hz => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (ℕ × ℝ≥0) => μ univ) h0
    simp [Measure.map_apply hmk MeasurableSet.univ] at this
  obtain ⟨z1, z2⟩ := z
  simp only [mem_prod, mem_singleton_iff, mem_Iic] at hz
  obtain ⟨rfl, hz2⟩ := hz
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmk hB]
  have hsec : MeasurableSet ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B) := hmk hB
  calc G (Ioi β) * H ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B)
      ≤ G (Ioi z2) * H ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B) := by
        gcongr
    _ = P (0, z2) ({0} ×ˢ ((fun y : ℝ≥0 => ((0 : ℕ), y)) ⁻¹' B)) := (hP z2 _ hsec).symm
    _ ≤ P (0, z2) B := by
        refine measure_mono ?_
        rintro ⟨q1, q2⟩ ⟨hq1, hq2⟩
        rw [mem_singleton_iff] at hq1
        subst hq1
        exact hq2

end MeynTweedie.LimitTheorems
