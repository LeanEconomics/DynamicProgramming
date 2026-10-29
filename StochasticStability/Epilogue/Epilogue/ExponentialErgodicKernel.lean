/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.ExponentialErgodic

/-!
# Theorem 20.3.2 at the kernel level (MT §20.3, pp. 527–528)

Theorem 20.3.2 asserts the equivalence of (20.31) (generator drift `AV ≤ −βV + b1_C`, `C`
petite), (20.32) (geometric decay of `Pᵗ(x, C)`-type quantities on a petite set), (20.33)
(exponential moments of the continuous-time hitting time `τ_C`) and the exponential ergodic
theorem (20.34). Without a process construction (càdlàg paths, continuous-time hitting times,
the strong Markov property) we prove the parts that live on the kernels:

* `theorem_20_3_2_skeleton_tfae`: for an irreducible aperiodic `δ`-skeleton, the skeleton
  analogues of (20.32), (20.33) and (20.31) are equivalent (Theorem 15.0.1 for `P^δ`);
* `theorem_20_3_2_kernel`: (20.34) for the semigroup holds if and only if the skeleton satisfies
  (V4) on a skeleton-petite set, under the local bound `PˢV ≤ cV` on `[0, δ]` (Theorem 16.0.1 for
  `P^δ` plus `vUniform_of_skeleton`).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Theorem 20.3.2 for a skeleton -/

variable [MeasurableSpace.CountablyGenerated X] {ψ : Measure X} in
/-- **Theorem 20.3.2 (i) ⇔ (ii) ⇔ (iii) at the skeleton level** (MT p. 527): for a `δ`-skeleton
that is `ψ`-irreducible and aperiodic, the skeleton versions of (20.32) (a petite set with
geometric convergence of `P^{nδ}(x, C)`), of (20.33) (a petite Kendall set: geometric moments of
the skeleton's return time `τ_C`) and of (20.31) ((V4) for the skeleton) are equivalent
(Theorem 15.0.1 for the chain `P^δ`). -/
theorem theorem_20_3_2_skeleton_tfae (S : MarkovSemigroup X) {δ : ℝ}
    (hψ : haveI := S.isMarkovKernel_P δ; IsMaximalIrreducibility (S.P δ) ψ)
    (hap : haveI := S.isMarkovKernel_P δ; IsAperiodic (S.P δ) ψ) :
    haveI := S.isMarkovKernel_P δ
    List.TFAE [IsLocallyGeomErgodic (S.P δ) ψ, HasKendallPetite (S.P δ), HasDriftV4 (S.P δ)] := by
  have := S.isMarkovKernel_P δ
  exact theorem_15_0_1 hψ hap

variable [MeasurableSpace.CountablyGenerated X] {V : X → ℝ} {π : Measure X} {ψ : Measure X} in
/-- **The exponential ergodic theorem (20.34) ⇔ (V4) on a skeleton** (MT pp. 527–528): suppose the
`δ`-skeleton is `ψ`-irreducible and aperiodic, `π` is invariant for every `Pᵗ`, `π(V) < ∞`, and
`PˢV ≤ cV` for `0 ≤ s ≤ δ`. Then the semigroup is exponentially ergodic,
`|||Pᵗ − 1 ⊗ π|||_V ≤ R'ρᵗ` with `0 < ρ < 1`, if and only if the skeleton satisfies (V4) on a set
petite for the skeleton, for some `V₀` equivalent to `V`. -/
theorem theorem_20_3_2_kernel (S : MarkovSemigroup X) [IsProbabilityMeasure π]
    (hinv : ∀ t, 0 ≤ t → IsInvariant (S.P t) π) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hψ : haveI := S.isMarkovKernel_P δ; IsMaximalIrreducibility (S.P δ) ψ)
    (hap : haveI := S.isMarkovKernel_P δ; IsAperiodic (S.P δ) ψ)
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hπV : ∫⁻ y, ENNReal.ofReal (V y) ∂π ≠ ∞)
    (hloc : ∀ s, 0 ≤ s → s ≤ δ → ∀ x,
      ∫⁻ y, ENNReal.ofReal (V y) ∂S.P s x ≤ ENNReal.ofReal (c * V x)) :
    (∃ R' ρ : ℝ, 0 ≤ R' ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ t, 0 ≤ t →
      vOpNorm (eW V) (S.P t) (Kernel.const X π) ≤ ENNReal.ofReal (R' * ρ ^ t)) ↔
    (∃ V₀ : X → ℝ≥0∞, Measurable V₀ ∧ (∀ x, 1 ≤ V₀ x) ∧ ∃ c₀ : ℝ≥0∞, c₀ ≠ ∞ ∧
      (∀ x, eW V x ≤ c₀ * V₀ x ∧ V₀ x ≤ c₀ * eW V x) ∧ ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧
        ∃ C, IsPetite (S.P δ) C ∧ DriftV4 (S.P δ) V₀ ρ b C) := by
  have := S.isMarkovKernel_P δ
  have hVm : Measurable (eW V) := ENNReal.measurable_ofReal.comp hV
  have hV1' : ∀ x, 1 ≤ eW V x := fun x => ENNReal.one_le_ofReal.2 (hV1 x)
  have htfae := theorem_16_0_1 hψ hap hVm hV1' (fun _ => ENNReal.ofReal_ne_top) π (hinv δ hδ.le)
  have h24 := htfae.out 2 4
  constructor
  · rintro ⟨R', ρ, hR', hρ0, hρ1, hb⟩
    refine h24.1 ⟨ENNReal.ofReal (ρ ^ δ)⁻¹, ?_, ENNReal.ofReal R',
      ENNReal.ofReal_ne_top, fun n => ?_⟩
    · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      exact one_lt_inv_iff₀.2 ⟨by positivity, Real.rpow_lt_one hρ0.le hρ1 hδ⟩
    · have h := hb (n * δ) (by positivity)
      rw [S.P_nsmul hδ.le] at h
      refine h.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_inv_of_pos (by positivity), inv_inv, ← ENNReal.ofReal_pow
        (by positivity), ← ENNReal.ofReal_mul hR', ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le,
        mul_comm δ]
  · intro hiv
    obtain ⟨r, hr, R, hR, hbd⟩ := h24.2 hiv
    set r' := min r 2 with hr'
    have hr'1 : 1 < r' := lt_min hr ENNReal.one_lt_two
    have hr't : r' ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right _ _)
    have hr1 : 1 < r'.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr't).2 hr'1
      rwa [ENNReal.toReal_one] at this
    have hskel : ∀ n, vErgDist (eW V) (S.P δ) π n ≤ ENNReal.ofReal (R.toReal * r'.toReal⁻¹ ^ n) :=
      fun n => by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hR,
          ENNReal.ofReal_pow (inv_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
          ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr'1).ne')]
        exact (hbd n).trans (mul_le_mul' le_rfl (pow_le_pow_left' (ENNReal.inv_le_inv.2
          (min_le_left _ _)) n))
    obtain ⟨hρ, hbound⟩ := vUniform_of_skeleton S hinv hV hV1 hπV hδ hc hloc hr1
      ENNReal.toReal_nonneg hskel
    exact ⟨_, _, by positivity, Real.rpow_pos_of_pos (by linarith) _, hρ, hbound⟩

end MeynTweedie.Epilogue
