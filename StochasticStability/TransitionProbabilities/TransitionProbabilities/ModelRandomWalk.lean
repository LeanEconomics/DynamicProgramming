/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransitionProbabilities.ModelRecursion
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Random walks

Copied from the `MarkovModels` project (`MarkovModels/RandomWalk.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

MT, §1.2.3, pp. 10–12, and (RW1), (RW2), (RWHL1) of Appendix C, p. 544.

* `randomWalkKernel Γ`: random walk `Φₖ₊₁ = Φₖ + Wₖ₊₁` with increment law `Γ` (MT, (RW1),
  (1.5)–(1.6), p. 11), on any measurable additive commutative monoid: `ℝ`, `ℝⁿ`, `ℤ`, `ℕ`.
  `P(x, A) = Γ(A − x)`; on `ℝ`, `P(x, (−∞, y]) = Γ(−∞, y − x]`
  (`randomWalkKernel_real_apply_Iic`).
* `orbit_randomWalk`: the sample path is `Φₙ = Φ₀ + W₁ + ⋯ + Wₙ`.
* `convPow Γ n`: the `n`-fold convolution power `Γ^{n∗}`, the law of `W₁ + ⋯ + Wₙ`;
  `randomWalkKernel_pow_apply`: `Pⁿ(x, ·)` is `Γ^{n∗}` shifted by `x`.
* `IsSpreadOut Γ`: (RW2), p. 544: some convolution power is not singular with respect to
  Lebesgue measure.
* `halfLineWalkKernel Γ`: random walk on a half line `Φₖ₊₁ = [Φₖ + Wₖ₊₁]⁺` on `ℝ≥0`
  (MT, (RWHL1), (1.7), p. 12). `P(x, {0}) = Γ(−∞, −x]` (`halfLineWalkKernel_apply_zero`) and
  `P(x, [0, y]) = Γ(−∞, y − x]` (`halfLineWalkKernel_apply_Iic`).
* The path claims of MT, p. 12: the reflected walk follows the unrestricted walk while that stays
  non-negative (`halfLineOrbit_eq_of_nonneg`), and leaves `0` only at a positive increment
  (`halfLineOrbit_succ_of_eq_zero`). Lindley's representation
  `Φₙ = max(x + Sₙ, max_{k ≤ n}(Sₙ − Sₖ))` (`halfLineOrbit_eq_lindley`) makes the first precise.
-/

namespace MeynTweedie.TransitionProbabilities

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Random walk on `G` (MT, (RW1), p. 11): `Φₖ₊₁ = Φₖ + Wₖ₊₁` with i.i.d. increments of law
`Γ`, as a random recursion with `F(x, w) = x + w`. -/
noncomputable def randomWalkKernel (Γ : Measure G) : Kernel G G :=
  recursionKernel Γ fun p => p.1 + p.2

omit [AddCommMonoid G] [MeasurableAdd₂ G] in
/-- The step map `(x, w) ↦ x + w` is measurable. -/
theorem measurable_add_step [Add G] [MeasurableAdd₂ G] :
    Measurable fun p : G × G => p.1 + p.2 :=
  measurable_fst.add measurable_snd

/-- `P(x, ·)` is the increment law shifted by `x`. -/
theorem randomWalkKernel_apply (Γ : Measure G) [SFinite Γ] (x : G) :
    randomWalkKernel Γ x = Γ.map (x + ·) :=
  recursionKernel_apply Γ measurable_add_step x

/-- `P(x, A) = Γ{w : x + w ∈ A}`. -/
theorem randomWalkKernel_apply' (Γ : Measure G) [SFinite Γ] (x : G) {A : Set G}
    (hA : MeasurableSet A) : randomWalkKernel Γ x A = Γ {w | x + w ∈ A} :=
  recursionKernel_apply' Γ measurable_add_step x hA

/-- Random walk is a Markov kernel. -/
theorem isMarkovKernel_randomWalkKernel (Γ : Measure G) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (randomWalkKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_add_step

/-- On `ℝ`, `P(x, (−∞, y]) = Γ(−∞, y − x]`: the transition law is the distribution function
of (1.6) shifted by `x`. -/
theorem randomWalkKernel_real_apply_Iic (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ) :
    randomWalkKernel Γ x (Iic y) = Γ (Iic (y - x)) := by
  rw [randomWalkKernel_apply' Γ x measurableSet_Iic]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Iic]
  constructor <;> intro h <;> linarith

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- The control maps of random walk are partial sums: `Fₙ(x, u) = x + u₁ + ⋯ + uₙ`. -/
theorem controlMap_add (n : ℕ) (x : G) (u : Fin n → G) :
    controlMap (fun p : G × G => p.1 + p.2) n x u = x + ∑ i, u i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ, ih, Fin.sum_univ_castSucc, add_assoc]
    rfl

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- The sample path of random walk is `Φₙ = Φ₀ + W₁ + ⋯ + Wₙ`. -/
theorem orbit_randomWalk (x : G) (ω : ℕ → G) (n : ℕ) :
    orbit (fun p : G × G => p.1 + p.2) x ω n = x + ∑ i ∈ Finset.range n, ω (i + 1) := by
  rw [orbit_eq_controlMap, controlMap_add, Fin.sum_univ_eq_sum_range (fun i => ω (i + 1))]

/-- The `n`-fold convolution power `Γ^{n∗}`: the law of `W₁ + ⋯ + Wₙ` for i.i.d. `Wᵢ ~ Γ`. -/
noncomputable def convPow (Γ : Measure G) (n : ℕ) : Measure G :=
  (Measure.pi fun _ : Fin n => Γ).map fun u => ∑ i, u i

/-- `u ↦ u₁ + ⋯ + uₙ` is measurable. -/
theorem measurable_sum_fin (n : ℕ) : Measurable fun u : Fin n → G => ∑ i, u i :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- **`n`-step random walk.** `Pⁿ(x, ·)` is `Γ^{n∗}` shifted by `x`. -/
theorem randomWalkKernel_pow_apply (Γ : Measure G) [IsProbabilityMeasure Γ] (n : ℕ) (x : G) :
    (randomWalkKernel Γ ^ n) x = (convPow Γ n).map (x + ·) := by
  rw [randomWalkKernel, recursionKernel_pow_apply Γ measurable_add_step n x, convPow,
    Measure.map_map (measurable_const_add x) (measurable_sum_fin n)]
  congr 1
  funext u
  exact controlMap_add n x u

/-- (RW2), MT p. 544: the random walk (or its increment law `Γ`) is *spread out* if some
convolution power `Γ^{n∗}`, `n ≥ 1`, is not singular with respect to Lebesgue measure. -/
def IsSpreadOut (Γ : Measure ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ¬ convPow Γ n ⟂ₘ (volume : Measure ℝ)

/-- The step map `(x, w) ↦ [x + w]⁺` of random walk on a half line. -/
noncomputable def halfLineStep (p : ℝ≥0 × ℝ) : ℝ≥0 := Real.toNNReal (p.1 + p.2)

/-- The half-line step is measurable. -/
theorem measurable_halfLineStep : Measurable halfLineStep :=
  ((measurable_coe_nnreal_real.comp measurable_fst).add measurable_snd).real_toNNReal

/-- Random walk on a half line (MT, (RWHL1), (1.7), p. 12): `Φₖ₊₁ = [Φₖ + Wₖ₊₁]⁺` on
`ℝ≥0 = [0, ∞)`, with i.i.d. increments of law `Γ` on `ℝ`. -/
noncomputable def halfLineWalkKernel (Γ : Measure ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel Γ halfLineStep

/-- Random walk on a half line is a Markov kernel. -/
theorem isMarkovKernel_halfLineWalkKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (halfLineWalkKernel Γ) :=
  isMarkovKernel_recursionKernel Γ measurable_halfLineStep

/-- `P(x, A) = Γ{w : [x + w]⁺ ∈ A}`. -/
theorem halfLineWalkKernel_apply' (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {A : Set ℝ≥0}
    (hA : MeasurableSet A) :
    halfLineWalkKernel Γ x A = Γ {w | Real.toNNReal (x + w) ∈ A} :=
  recursionKernel_apply' Γ measurable_halfLineStep x hA

/-- The walk is held at zero with probability `P(x, {0}) = Γ(−∞, −x]`. -/
theorem halfLineWalkKernel_apply_zero (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) :
    halfLineWalkKernel Γ x {0} = Γ (Iic (-(x : ℝ))) := by
  rw [halfLineWalkKernel_apply' Γ x (measurableSet_singleton 0)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, Real.toNNReal_eq_zero, mem_Iic]
  constructor <;> intro h <;> linarith

/-- `P(x, [0, y]) = Γ(−∞, y − x]` for `y ≥ 0`. -/
theorem halfLineWalkKernel_apply_Iic (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ≥0) :
    halfLineWalkKernel Γ x (Iic y) = Γ (Iic ((y : ℝ) - x)) := by
  rw [halfLineWalkKernel_apply' Γ x measurableSet_Iic]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Iic, Real.toNNReal_le_iff_le_coe]
  constructor <;> intro h <;> linarith

/-- `P(x, (y, ∞)) = Γ(y − x, ∞)` for `y ≥ 0`. -/
theorem halfLineWalkKernel_apply_Ioi (Γ : Measure ℝ) [SFinite Γ] (x y : ℝ≥0) :
    halfLineWalkKernel Γ x (Ioi y) = Γ (Ioi ((y : ℝ) - x)) := by
  rw [halfLineWalkKernel_apply' Γ x measurableSet_Ioi]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_Ioi, Real.lt_toNNReal_iff_coe_lt]
  constructor <;> intro h <;> linarith

/-- A path of random walk on a half line, `Φ₀ = x`, `Φₙ₊₁ = [Φₙ + ωₙ₊₁]⁺`. -/
noncomputable def halfLineOrbit (x : ℝ≥0) (ω : ℕ → ℝ) : ℕ → ℝ≥0 := orbit halfLineStep x ω

/-- The partial sums `Sₙ = ω₁ + ⋯ + ωₙ` of the increments. -/
def partialSum (ω : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ω (i + 1)

/-- In real coordinates the reflected walk satisfies `Φₙ₊₁ = max(Φₙ + ωₙ₊₁, 0)`. -/
theorem halfLineOrbit_succ_coe (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ) :
    (halfLineOrbit x ω (n + 1) : ℝ) = max ((halfLineOrbit x ω n : ℝ) + ω (n + 1)) 0 :=
  Real.coe_toNNReal' _

/-- MT, p. 12: the reflected walk follows the paths of the unrestricted random walk as long as
the latter stays non-negative: if `x + Sₖ ≥ 0` for all `k ≤ n` then `Φₙ = x + Sₙ`. -/
theorem halfLineOrbit_eq_of_nonneg (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ)
    (h : ∀ k ≤ n, 0 ≤ (x : ℝ) + partialSum ω k) :
    (halfLineOrbit x ω n : ℝ) = x + partialSum ω n := by
  induction n with
  | zero => simp [halfLineOrbit, partialSum]
  | succ n ih =>
    rw [halfLineOrbit_succ_coe, ih fun k hk => h k (by omega)]
    have hS : partialSum ω (n + 1) = partialSum ω n + ω (n + 1) := Finset.sum_range_succ _ _
    have h1 := h (n + 1) le_rfl
    rw [hS, ← add_assoc] at h1 ⊢
    exact max_eq_left h1

/-- MT, p. 12: the walk leaves zero only when the next increment is positive. -/
theorem halfLineOrbit_succ_of_eq_zero (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ)
    (h : halfLineOrbit x ω n = 0) :
    halfLineOrbit x ω (n + 1) = Real.toNNReal (ω (n + 1)) := by
  change Real.toNNReal ((halfLineOrbit x ω n : ℝ) + ω (n + 1)) = _
  rw [h, NNReal.coe_zero, zero_add]

/-- **Lindley's representation.** The reflected walk is
`Φₙ = max(x + Sₙ, max_{0 ≤ k ≤ n}(Sₙ − Sₖ))`. -/
theorem halfLineOrbit_eq_lindley (x : ℝ≥0) (ω : ℕ → ℝ) (n : ℕ) :
    (halfLineOrbit x ω n : ℝ) = max ((x : ℝ) + partialSum ω n)
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => partialSum ω n - partialSum ω k) := by
  induction n with
  | zero =>
    simp only [halfLineOrbit, orbit_zero, partialSum, Finset.range_zero, Finset.sum_empty,
      add_zero, zero_add, Finset.range_one, Finset.sup'_singleton, sub_self]
    exact (max_eq_left x.2).symm
  | succ n ih =>
    rw [halfLineOrbit_succ_coe, ih]
    have hS : partialSum ω (n + 1) = partialSum ω n + ω (n + 1) := Finset.sum_range_succ _ _
    have hsup : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω n - partialSum ω k) + ω (n + 1) =
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k) := by
      rw [Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one (· + ω (n + 1))
        (fun a b => (max_add_add_right a b (ω (n + 1))).symm)]
      refine Finset.sup'_congr _ rfl fun k _ => ?_
      simp only [Function.comp_apply, hS]
      ring
    have hins : (Finset.range (n + 1 + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k) =
        max 0 ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => partialSum ω (n + 1) - partialSum ω k)) := by
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun k hk => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hk) with hk' | rfl
        · exact le_max_of_le_right (Finset.le_sup' (fun k => partialSum ω (n + 1) -
            partialSum ω k) (Finset.mem_range.mpr hk'))
        · simp
      · refine max_le ?_ (Finset.sup'_le _ _ fun k hk => ?_)
        · have := Finset.le_sup' (fun k => partialSum ω (n + 1) - partialSum ω k)
            (Finset.self_mem_range_succ (n + 1))
          rwa [sub_self] at this
        · exact Finset.le_sup' (fun k => partialSum ω (n + 1) - partialSum ω k)
            (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    rw [← max_add_add_right, hsup, hins, hS, ← add_assoc, max_comm 0, ← max_assoc]

end MeynTweedie.TransitionProbabilities
