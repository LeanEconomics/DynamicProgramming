/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ConvergenceSLPMonotoneProcesses
import MarkovProcesses.ConvergenceSLPParameters

/-!
# Monotone processes and continuous dependence on parameters

Miao, §3.3.2, pp. 112–113. The book cites SLP for both theorems; the proofs are SLP's
Theorems 12.12 and 12.13, copied in `ConvergenceSLPMonotoneProcesses` and
`ConvergenceSLPParameters`.

* **Definition 3.3.6**: `P` is increasing if `T` maps bounded increasing (measurable) functions to
  increasing functions: SLP's `IsMonotoneTF` (`definition_3_3_6`). "Increasing" is read as
  nondecreasing for the componentwise order, and `f` must be measurable for `Tf` to be defined.
* The **Mixing Condition** (`MixingCondition`), SLP's Assumption 12.1. `X = [a, b] ⊂ ℝˡ` is the
  subtype `Set.Icc a b` of `Fin l → ℝ`, and `[c, b]`, `[a, c]` are `Set.Ici c`, `Set.Iic c` in it.
* **Theorem 3.3.5** (`theorem_3_3_5`): a unique invariant `λ*` and `T*ⁿλ₀ ⇒ λ*` for all `λ₀`.
* **Theorem 3.3.6** (`theorem_3_3_6`, and `theorem_3_3_6_euclidean` in the book's setting
  `X ⊆ ℝˡ` compact, `Θ ⊆ ℝᵐ`): `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. The general version holds for
  any compact metric `X` and metric `Θ`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Definition 3.3.6** (Miao, p. 112): `P` is **increasing** if `Tf` is increasing for every
bounded increasing (measurable) `f`. -/
theorem definition_3_3_6 {X : Type*} [MeasurableSpace X] [Preorder X] (κ : Kernel X X) :
    IsMonotoneTF κ ↔ ∀ f : X → ℝ, Measurable f → (∃ M, ∀ x, |f x| ≤ M) → Monotone f →
      Monotone (markovOpR κ f) := Iff.rfl

variable {l : ℕ} {a b : Fin l → ℝ}

/-- The **Mixing Condition** (Miao, p. 112): `X = [a, b] ⊂ ℝˡ`, and for some `c ∈ X`, `ε > 0`,
`N ≥ 1`: `Pᴺ(a, [c, b]) ≥ ε` and `Pᴺ(b, [a, c]) ≥ ε`. -/
def MixingCondition (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b)) (c : Set.Icc a b)
    (ε : ℝ) (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (gp_IccBot hab)).real (Set.Ici c) ∧
    ε ≤ (kpow κ N (gp_IccTop hab)).real (Set.Iic c)

theorem gp_mixingCondition_iff (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b))
    (c : Set.Icc a b) (ε : ℝ) (N : ℕ) :
    MixingCondition hab κ c ε N ↔ gp_Assumption12_1 hab κ c ε N := Iff.rfl

/-- **Theorem 3.3.5** (Miao, p. 112; SLP Theorem 12.12). On `X = [a, b] ⊂ ℝˡ`, if `P` is
increasing, has the Feller property and satisfies the Mixing Condition, then `P` has a unique
invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀ ∈ P(X, 𝒳)`. -/
theorem theorem_3_3_5 (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Set.Icc a b} {ε : ℝ} {N : ℕ}
    (hmix : MixingCondition hab κ c ε N) :
    ∃ lstar : Measure (Set.Icc a b), IsProbabilityMeasure lstar ∧ adjointOp κ lstar = lstar ∧
      (∀ ν : Measure (Set.Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = lstar) ∧
      ∀ lam₀ : Measure (Set.Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => adjointOp (kpow κ n) lam₀) lstar := by
  obtain ⟨μ, hμ, hinv, huniq, hconv⟩ := slp_theorem_12_12 hab κ hM hF hmix
  refine ⟨μ, hμ, hinv, huniq, fun lam₀ h₀ => ?_⟩
  have := hconv lam₀ h₀
  simpa only [gp_adjointOp_iterate] using this

/-- **Theorem 3.3.6** (Miao, p. 113; SLP Theorem 12.13), for a compact metric state space `X` and
a metric parameter space `Θ`. If (b) `(xₙ, θₙ) → (x₀, θ₀)` implies `P_{θₙ}(xₙ, ·) ⇒ P_{θ₀}(x₀, ·)`
and (c) each `T*_θ` has a unique fixed point `μ_θ`, then `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. -/
theorem theorem_3_3_6 {X Θ : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Θ] [CompactSpace X] (P : Θ → Kernel X X) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (x : ℕ → X) (θ : ℕ → Θ) (x₀ : X) (θ₀ : Θ), Tendsto x atTop (𝓝 x₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (x n)) (P θ₀ x₀))
    (μ : Θ → Measure X) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure X), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) :=
  slp_theorem_12_13 P hcont μ hfix huniq hθ

/-- **Theorem 3.3.6** (Miao, p. 113) in the book's setting: `X ⊆ ℝˡ` compact, `Θ ⊆ ℝᵐ`. -/
theorem theorem_3_3_6_euclidean {m : ℕ} {K : Set (Fin l → ℝ)} (hK : IsCompact K)
    {Θ : Set (Fin m → ℝ)} (P : Θ → Kernel K K) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (x : ℕ → K) (θ : ℕ → Θ) (x₀ : K) (θ₀ : Θ), Tendsto x atTop (𝓝 x₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (x n)) (P θ₀ x₀))
    (μ : Θ → Measure K) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure K), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact theorem_3_3_6 P hcont μ hfix huniq hθ

end Miao.MarkovProcesses
