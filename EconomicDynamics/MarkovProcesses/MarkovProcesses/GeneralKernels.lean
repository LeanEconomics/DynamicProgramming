/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.GeneralSLPTransitionFunctions
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Stochastic kernels, `n`-step transitions and the operators `T`, `T*`

Miao, §3.2, pp. 99–104. A stochastic kernel is a Markov kernel (`definition_3_2_1`); a transition
function is a stochastic kernel from a space to itself (`definition_3_2_1_transition`). Here a
kernel takes values in `[0, ∞]` rather than `[0, 1]`; a probability measure takes values in
`[0, 1]` anyway.

* **Theorem 3.2.1** (`theorem_3_2_1`): the direct product `P₁ ⊗ P₂`, the unique stochastic
  kernel `P₃` on `(W, 𝒳 × 𝒴)` with `P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`. It is Mathlib's
  `P₁ ⊗ₖ P₂` (with `P₂` not depending on `w`); uniqueness holds because finite measures on a
  product agree once they agree on rectangles.
* **Theorem 3.2.5** and **(3.5)**, which **Exercise 3.2** asks for (`theorem_3_2_5`, `eq_3_4`,
  `eq_3_4_unique`, `eq_3_5`, `ex_3_2`): `Pⁿ = kpow P n` is a transition function, it satisfies
  the Chapman–Kolmogorov recursion (3.4), (3.4) determines it, and
  `Pᵐ⁺ⁿ(a, A) = ∫ Pᵐ(x, A) Pⁿ(a, dx)`.
* **Definition 3.2.2**: `T = markovOpR P` on bounded measurable functions and
  `T* = adjointOp P` on probability measures. **Exercise 3.4** (`ex_3_4`): `T` maps `B(X, 𝒳)`
  into itself, `T*` maps `P(X, 𝒳)` into itself, and
  `∫ Tf dλ = ∫ f d(T*λ) = ∫∫ f(y) P(x, dy) λ(dx)`.
* p. 103: `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)` (`eq_p103_T`, `eq_p103_Tstar`);
  p. 104: `λₙ = T*λₙ₋₁ = T*ⁿλ₀` (`eq_p104_iterate`); invariant distributions
  (`IsInvariantDist`, `isInvariantDist_iff`).

The book defines `Pⁿ` by (3.4), `Pⁿ(a, A) = ∫ P(x, A) Pⁿ⁻¹(a, dx)`; the Lean `kpow P n` (from SLP)
is defined by the other recursion `Pⁿ⁺¹(a, A) = ∫ Pⁿ(x, A) P(a, dx)`, and `eq_3_4_unique` shows
that the two agree.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

/-- A **stochastic kernel** (Miao, Definition 3.2.1, p. 99): each `P(x, ·)` is a probability
measure on `(Y, 𝒴)`, and each `P(·, A)` is `𝒳`-measurable. -/
def IsStochasticKernel (P : X → Set Y → ℝ≥0∞) : Prop :=
  (∀ x, ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = P x A) ∧
    ∀ A, MeasurableSet A → Measurable fun x => P x A

/-- **Definition 3.2.1** (Miao, p. 99). Stochastic kernels are exactly Mathlib's Markov kernels. -/
theorem definition_3_2_1 (P : X → Set Y → ℝ≥0∞) :
    IsStochasticKernel P ↔
      ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ ∀ x A, MeasurableSet A → κ x A = P x A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμP using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun x => μ x A) = fun x => P x A := funext fun x => hμP x A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun x => hμ x⟩, fun x A hA => hμP x A hA⟩
  · rintro ⟨κ, hκ, hP⟩
    refine ⟨fun x => ⟨κ x, inferInstance, fun A hA => hP x A hA⟩, fun A hA => ?_⟩
    have : (fun x => P x A) = fun x => κ x A := funext fun x => (hP x A hA).symm
    rw [this]
    exact κ.measurable_coe hA

/-- **Definition 3.2.1** (Miao, p. 100): a **transition function** is a stochastic kernel from
`(X, 𝒳)` to itself; this is SLP's notion `IsTransitionFunction`. -/
theorem definition_3_2_1_transition (P : X → Set X → ℝ≥0∞) :
    IsStochasticKernel P ↔ IsTransitionFunction P := Iff.rfl

/-- **Theorem 3.2.1** (Miao, p. 100; SLP Theorem 8.5). For stochastic kernels `P₁` on `(W, 𝒳)`
and `P₂` on `(X, 𝒴)` there is a unique stochastic kernel `P₃` on `(W, 𝒳 × 𝒴)` with
`P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`; it is the direct product `P₁ ⊗ₖ P₂`. -/
theorem theorem_3_2_1 (P₁ : Kernel W X) [IsMarkovKernel P₁] (P₂ : Kernel X Y)
    [IsMarkovKernel P₂] :
    ∃! P₃ : Kernel W (X × Y), IsMarkovKernel P₃ ∧ ∀ w A B, MeasurableSet A → MeasurableSet B →
      P₃ w (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w := by
  refine ⟨P₁ ⊗ₖ P₂.prodMkLeft W, ⟨inferInstance, fun w A B hA hB => ?_⟩, ?_⟩
  · rw [Kernel.compProd_apply_prod hA hB]
    rfl
  · rintro P₃ ⟨hP₃, h⟩
    ext w : 1
    refine Measure.ext_prod fun {A} {B} hA hB => ?_
    rw [h w A B hA hB, Kernel.compProd_apply_prod hA hB]
    rfl

/-- **(3.4)** (Miao, p. 102), the Chapman–Kolmogorov recursion: `P¹ = P` and
`Pⁿ⁺¹(a, A) = ∫ P(x, A) Pⁿ(a, dx)`. -/
theorem eq_3_4 (P : Kernel X X) (n : ℕ) (a : X) {A : Set X} (hA : MeasurableSet A) :
    kpow P 1 = P ∧ kpow P (n + 1) a A = ∫⁻ x, P x A ∂kpow P n a := by
  refine ⟨gp_kpow_one P, ?_⟩
  rw [gp_kpow_add P n 1, gp_kpow_one, Kernel.comp_apply' _ _ _ hA]

/-- (3.4) determines `Pⁿ` (Miao, p. 102): any sequence of kernels with `Q₁ = P` and
`Qₙ₊₁(a, A) = ∫ P(x, A) Qₙ(a, dx)` is `Qₙ = kpow P n` for all `n ≥ 1`. -/
theorem eq_3_4_unique (P : Kernel X X) (Q : ℕ → Kernel X X) (h1 : Q 1 = P)
    (hs : ∀ n, 1 ≤ n → ∀ a A, MeasurableSet A → Q (n + 1) a A = ∫⁻ x, P x A ∂Q n a) :
    ∀ n, 1 ≤ n → Q n = kpow P n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h1, gp_kpow_one]
  | succ n hn ih =>
    ext a A hA
    rw [hs n hn a A hA, (eq_3_4 P n a hA).2, ih]

/-- **Theorem 3.2.5** (Miao, p. 102). Each `Pⁿ` is a transition function. -/
theorem theorem_3_2_5 (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (kpow P n) :=
  slp_ex_8_4a P n

/-- **(3.5)** (Miao, p. 103): `Pᵐ⁺ⁿ(a, A) = ∫ Pᵐ(x, A) Pⁿ(a, dx)`. -/
theorem eq_3_5 (P : Kernel X X) (m n : ℕ) (a : X) {A : Set X} (hA : MeasurableSet A) :
    kpow P (m + n) a A = ∫⁻ x, kpow P m x A ∂kpow P n a := by
  rw [add_comm, gp_kpow_add, Kernel.comp_apply' _ _ _ hA]

/-- **Exercise 3.2** (Miao, p. 113): Theorem 3.2.5 and (3.5). -/
theorem ex_3_2 (P : Kernel X X) [IsMarkovKernel P] :
    (∀ n, IsMarkovKernel (kpow P n)) ∧
      ∀ m n a A, MeasurableSet A → kpow P (m + n) a A = ∫⁻ x, kpow P m x A ∂kpow P n a :=
  ⟨theorem_3_2_5 P, fun m n a _ hA => eq_3_5 P m n a hA⟩

/-- **Exercise 3.4** (Miao, p. 113; Definition 3.2.2, p. 103). `T` maps bounded measurable
functions to bounded measurable functions, `T*` maps probability measures to probability
measures, and `∫ Tf dλ = ∫ f d(T*λ) = ∫∫ f(y) P(x, dy) λ(dx)`. -/
theorem ex_3_4 (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (lam : Measure X) [IsProbabilityMeasure lam] :
    (Measurable (markovOpR P f) ∧ ∀ x, |markovOpR P f x| ≤ M) ∧
      IsProbabilityMeasure (adjointOp P lam) ∧
      ∫ x, markovOpR P f x ∂lam = ∫ y, f y ∂adjointOp P lam ∧
      ∫ y, f y ∂adjointOp P lam = ∫ x, ∫ y, f y ∂P x ∂lam :=
  ⟨slp_theorem_8_1_cor P hf hM, (slp_theorem_8_2 P lam).1,
    slp_theorem_8_3_cor P lam hf hM, (slp_theorem_8_3_cor P lam hf hM).symm⟩

/-- Miao, p. 103: `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem eq_p103_T (P : Kernel X X) [IsMarkovKernel P] (n m : ℕ) {f : X → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    markovOpR (kpow P (n + m)) f = markovOpR (kpow P n) (markovOpR (kpow P m) f) := by
  have := slp_ex_8_4a P m
  have := slp_ex_8_4a P n
  funext x
  rw [gp_kpow_add]
  exact Kernel.integral_comp (gp_integrable_of_bounded hf hM)

/-- Miao, p. 103: `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem eq_p103_Tstar (P : Kernel X X) (n m : ℕ) (lam : Measure X) :
    adjointOp (kpow P (n + m)) lam = adjointOp (kpow P n) (adjointOp (kpow P m) lam) :=
  (slp_ex_8_4b P n m measurable_const lam (f := fun _ => 0)).2

/-- Miao, p. 104: `λₙ = T*λₙ₋₁ = T*ⁿλ₀`, and each `λₙ` is a probability measure. -/
theorem eq_p104_iterate (P : Kernel X X) [IsMarkovKernel P] (lam₀ : Measure X)
    [IsProbabilityMeasure lam₀] (n : ℕ) :
    (adjointOp P)^[n + 1] lam₀ = adjointOp P ((adjointOp P)^[n] lam₀) ∧
      (adjointOp P)^[n] lam₀ = adjointOp (kpow P n) lam₀ ∧
      IsProbabilityMeasure (adjointOp (kpow P n) lam₀) := by
  have := slp_ex_8_4a P n
  exact ⟨Function.iterate_succ_apply' _ _ _, gp_adjointOp_iterate P n lam₀,
    (slp_theorem_8_2 (kpow P n) lam₀).1⟩

/-- An **invariant (stationary) distribution** (Miao, p. 104): a probability measure `π` with
`T*π = π`. -/
def IsInvariantDist (P : Kernel X X) (π : Measure X) : Prop :=
  IsProbabilityMeasure π ∧ adjointOp P π = π

/-- Miao, p. 104: `π` is invariant iff `π(A) = ∫ P(x, A) π(dx)` for all `A ∈ 𝒳`. -/
theorem isInvariantDist_iff (P : Kernel X X) (π : Measure X) [IsProbabilityMeasure π] :
    IsInvariantDist P π ↔ ∀ A, MeasurableSet A → π A = ∫⁻ x, P x A ∂π := by
  constructor
  · rintro ⟨-, h⟩ A hA
    rw [← gp_adjointOp_apply P π hA, h]
  · intro h
    refine ⟨inferInstance, Measure.ext fun A hA => ?_⟩
    rw [gp_adjointOp_apply P π hA, ← h A hA]

end Miao.MarkovProcesses
