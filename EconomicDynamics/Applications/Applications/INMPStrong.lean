/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INMPConditionM
import Applications.INMPKernels

/-!
# Strong convergence: total variation, Condition M and the Minorization Condition

Copied from `EconomicDynamics/MarkovProcesses` (module `ConvergenceStrong`),
namespace renamed.

Miao, §3.3.1, pp. 104–108.

* (3.6): `dTV λ₁ λ₂ = sup_A |λ₁(A) − λ₂(A)|` (`dTV`). SLP's total variation norm `tvDist` is
  twice it (`gp_tvDist_eq_two_mul_dTV`). p. 105: `dTV` is a metric on probability measures and
  the space is complete (`eq_p105_metric`, `eq_p105_complete`, from SLP Lemma 11.8).
* **Definition 3.3.1** (`ConvStrongly`).
* **Condition M** is SLP's `ConditionMFor κ N ε` (copied in `INMPConditionM`).
* **Theorem 3.3.1** (`theorem_3_3_1`, `theorem_3_3_1_contraction`, `theorem_3_3_1_invariant`,
  `theorem_3_3_1_converse`), from SLP Theorem 11.12. Departure: `X` is assumed nonempty (there
  is no probability measure on `∅`). The limit `π` is also invariant and
  `dTV(T*ⁿλ₀, π) ≤ (1 − ε)^⌊n/N⌋` for every `n`, which the book uses but does not state.
* The **Minorization Condition** (`MinorizationFor`, `Minorization`) and **Proposition 3.3.1**.
  The direction Minorization ⇒ Condition M is proved as in the book (`proposition_3_3_1`, first
  part). The book's proof of the converse ("define `μ = δ_A`") is meaningless, and the converse
  fails with the same `N`: on three states, `P(i, ·)` uniform on the two other states satisfies
  Condition M for `(N, ε) = (1, 1/2)` but no minorization with `N = 1`
  (`proposition_3_3_1_counterexample`). Proved instead: Condition M implies the Minorization
  Condition for some larger `N` whenever the invariant measure of Theorem 3.3.1 has an atom
  (`proposition_3_3_1_of_atom`), in particular on every countable state space
  (`proposition_3_3_1`, second part). The general case (true for countably generated
  σ-algebras by Meyn–Tweedie, Theorem 16.0.2) is not formalised.
* **Examples 3.3.1–3.3.3** (`example_3_3_1`, `example_3_3_2`, `example_3_3_3`,
  `example_3_3_3_finite`). In Example 3.3.3 the finite case is stated for a power `Pᴺ` with
  positive entries; that an irreducible aperiodic finite chain has one is Theorem 3.1.4 (the
  `Chain` modules).
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **(3.6)** (Miao, p. 104): the **total variation distance**
`dTV(λ₁, λ₂) = sup_{A ∈ 𝒳} |λ₁(A) − λ₂(A)|`. -/
noncomputable def dTV (lam₁ lam₂ : Measure X) : ℝ :=
  sSup ((fun A => |lam₁.real A - lam₂.real A|) '' {A | MeasurableSet A})

theorem gp_dTV_eq_supDiff (lam₁ lam₂ : Measure X) : dTV lam₁ lam₂ = gp_supDiff lam₁ lam₂ := rfl

/-- SLP's total variation norm `‖λ₁ − λ₂‖` is `2 dTV(λ₁, λ₂)` (SLP Lemma 11.5). -/
theorem gp_tvDist_eq_two_mul_dTV (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : tvDist lam₁ lam₂ = 2 * dTV lam₁ lam₂ :=
  (slp_lemma_11_5 lam₁ lam₂ (by simp)).1

theorem gp_abs_le_dTV (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] {A : Set X} (hA : MeasurableSet A) :
    |lam₁.real A - lam₂.real A| ≤ dTV lam₁ lam₂ :=
  le_csSup (gp_bddAbove_supDiff lam₁ lam₂) ⟨A, hA, rfl⟩

theorem gp_dTV_le_of_forall (lam₁ lam₂ : Measure X) {δ : ℝ}
    (h : ∀ A, MeasurableSet A → |lam₁.real A - lam₂.real A| ≤ δ) : dTV lam₁ lam₂ ≤ δ := by
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro _ ⟨A, hA, rfl⟩
  exact h A hA

theorem gp_dTV_nonneg (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : 0 ≤ dTV lam₁ lam₂ :=
  (abs_nonneg _).trans (gp_abs_le_dTV lam₁ lam₂ MeasurableSet.empty)

theorem gp_dTV_le_one (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : dTV lam₁ lam₂ ≤ 1 := by
  have := gp_tvDist_le_two lam₁ lam₂
  rw [gp_tvDist_eq_two_mul_dTV] at this
  linarith

/-- Miao, p. 105: `dTV` is a metric on `P(X, 𝒳)`. -/
theorem eq_p105_metric (lam₁ lam₂ lam₃ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] [IsProbabilityMeasure lam₃] :
    0 ≤ dTV lam₁ lam₂ ∧ dTV lam₁ lam₂ = dTV lam₂ lam₁ ∧
      dTV lam₁ lam₃ ≤ dTV lam₁ lam₂ + dTV lam₂ lam₃ ∧ (dTV lam₁ lam₂ = 0 ↔ lam₁ = lam₂) := by
  have h12 := gp_tvDist_eq_two_mul_dTV lam₁ lam₂
  have h21 := gp_tvDist_eq_two_mul_dTV lam₂ lam₁
  have h13 := gp_tvDist_eq_two_mul_dTV lam₁ lam₃
  have h23 := gp_tvDist_eq_two_mul_dTV lam₂ lam₃
  have hc := gp_tvDist_comm lam₁ lam₂
  have ht := gp_tvDist_triangle lam₁ lam₂ lam₃
  refine ⟨gp_dTV_nonneg lam₁ lam₂, by linarith, by linarith, fun h => ?_, fun h => ?_⟩
  · exact gp_eq_of_tvDist_eq_zero (by linarith)
  · subst h
    refine le_antisymm (gp_dTV_le_of_forall _ _ fun A _ => by simp) (gp_dTV_nonneg _ _)

/-- Miao, p. 105 (SLP Lemma 11.8): `P(X, 𝒳)` with the total variation distance is complete. -/
theorem eq_p105_complete (ls : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ls n)]
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, dTV (ls n) (ls m) < ε) :
    ∃ l : Measure X, IsProbabilityMeasure l ∧ Tendsto (fun n => dTV (ls n) l) atTop (𝓝 0) := by
  obtain ⟨l, hl, hconv⟩ := slp_lemma_11_8 ls fun ε hε => by
    obtain ⟨N, hN⟩ := hC (ε / 2) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [gp_tvDist_eq_two_mul_dTV]
    linarith [hN n hn m hm]
  refine ⟨l, hl, ?_⟩
  have : (fun n => dTV (ls n) l) = fun n => tvDist (ls n) l / 2 := funext fun n => by
    rw [gp_tvDist_eq_two_mul_dTV]; ring
  rw [this]
  simpa using hconv.div_const 2

/-- **Definition 3.3.1** (Miao, p. 105): `λₙ` **converges strongly** to `λ` if
`dTV(λₙ, λ) → 0`. -/
def ConvStrongly (ls : ℕ → Measure X) (l : Measure X) : Prop :=
  Tendsto (fun n => dTV (ls n) l) atTop (𝓝 0)

variable {κ : Kernel X X} [IsMarkovKernel κ]

/-- Proof of **Theorem 3.3.1** (Miao, p. 106; SLP Lemma 11.11): under Condition M for `(N, ε)`,
`T*ᴺ` is a contraction of modulus `1 − ε` for the total variation distance. -/
theorem theorem_3_3_1_contraction {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε)
    (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂] :
    dTV (adjointOp (kpow κ N) lam₁) (adjointOp (kpow κ N) lam₂) ≤ (1 - ε) * dTV lam₁ lam₂ := by
  have := gp_isProb_adjoint (κ := κ) N lam₁
  have := gp_isProb_adjoint (κ := κ) N lam₂
  have h := slp_lemma_11_11 hM lam₁ lam₂
  rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV] at h
  linarith

/-- (3.8) in terms of `dTV` is (3.8) in terms of SLP's `tvDist`. -/
theorem gp_eq_3_8_iff {N : ℕ} {ε : ℝ} (pm : Measure X) [IsProbabilityMeasure pm] :
    (∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * dTV l₀ pm) ↔
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        tvDist (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * tvDist l₀ pm := by
  constructor
  · intro h l₀ _ k
    have := gp_isProb_adjoint (κ := κ) (N * k) l₀
    rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV]
    nlinarith [h l₀ k]
  · intro h l₀ _ k
    have := gp_isProb_adjoint (κ := κ) (N * k) l₀
    have := h l₀ k
    rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV] at this
    nlinarith

/-- **Theorem 3.3.1** (Miao, p. 106; SLP Theorem 11.12). If `P` satisfies Condition M for
`N ≥ 1` and `ε > 0`, there is a unique probability measure `π` with
`dTV(T*ᴺᵏλ₀, π) ≤ (1 − ε)ᵏ dTV(λ₀, π)` (3.8) for all `λ₀ ∈ P(X, 𝒳)` and all `k`. -/
theorem theorem_3_3_1 [Nonempty X] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
    ∃! pm : Measure X, IsProbabilityMeasure pm ∧
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * dTV l₀ pm := by
  obtain ⟨pm, hpm, h1, huniq, -, -⟩ := slp_theorem_11_12 hM
  refine ⟨pm, ⟨hpm, (gp_eq_3_8_iff pm).2 h1⟩, ?_⟩
  rintro pm' ⟨hpm', h'⟩
  exact huniq pm' hpm' ((gp_eq_3_8_iff pm').1 h')

/-- Theorem 3.3.1 (Miao, p. 106): the measure `π` is invariant, `T*π = π`, and
`dTV(T*ⁿλ₀, π) ≤ (1 − ε)^⌊n/N⌋` for every `n`. -/
theorem theorem_3_3_1_invariant [Nonempty X] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
    ∃ pm : Measure X, IsProbabilityMeasure pm ∧ adjointOp κ pm = pm ∧
      (∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * dTV l₀ pm) ∧
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (n : ℕ),
        dTV (adjointOp (kpow κ n) l₀) pm ≤ (1 - ε) ^ (n / N) := by
  obtain ⟨pm, hpm, h1, -, hinv, hrate⟩ := slp_theorem_11_12 hM
  refine ⟨pm, hpm, hinv, (gp_eq_3_8_iff pm).2 h1, fun l₀ _ n => ?_⟩
  have := gp_isProb_adjoint (κ := κ) n l₀
  have := hrate l₀ n
  rw [gp_tvDist_eq_two_mul_dTV] at this
  linarith

/-- **Theorem 3.3.1**, converse (Miao, p. 107): if (3.8) holds for some `N ≥ 1`, `0 < ε ≤ 1` and
probability measure `π`, then Condition M holds (for `(NK, 1/4)` with `(1 − ε)ᴷ ≤ 1/4`). -/
theorem theorem_3_3_1_converse {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {pm : Measure X} [IsProbabilityMeasure pm]
    (h : ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
      dTV (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * dTV l₀ pm) :
    ConditionM κ :=
  slp_theorem_11_12_converse hN hε hε1 ((gp_eq_3_8_iff pm).1 h)

omit [IsMarkovKernel κ] in
/-- The **Minorization Condition** for `(N, α, μ)` (Miao, p. 107): `N ≥ 1`, `α > 0`, `μ` is a
probability measure and `Pᴺ(x, ·) ≥ αμ(·)` for all `x`. -/
def MinorizationFor (κ : Kernel X X) (N : ℕ) (α : ℝ) (μ : Measure X) : Prop :=
  1 ≤ N ∧ 0 < α ∧ IsProbabilityMeasure μ ∧
    ∀ x A, MeasurableSet A → α * μ.real A ≤ (kpow κ N x).real A

/-- The **Minorization Condition** holds for some `(N, α, μ)`. -/
def Minorization (κ : Kernel X X) : Prop := ∃ N α μ, MinorizationFor κ N α μ

omit [IsMarkovKernel κ] in
/-- **Proposition 3.3.1**, first half (Miao, p. 107): the Minorization Condition for
`(N, α, μ)` implies Condition M for `(N, α/2)`. -/
theorem proposition_3_3_1_forward {N : ℕ} {α : ℝ} {μ : Measure X}
    (h : MinorizationFor κ N α μ) : ConditionMFor κ N (α / 2) := by
  obtain ⟨hN, hα, hμ, hmin⟩ := h
  refine ⟨hN, by positivity, fun A hA => ?_⟩
  rcases le_total (1 / 2) (μ.real A) with h2 | h2
  · exact Or.inl fun x => by nlinarith [hmin x A hA]
  · refine Or.inr fun x => ?_
    have hc : μ.real Aᶜ = 1 - μ.real A := probReal_compl_eq_one_sub hA
    nlinarith [hmin x Aᶜ hA.compl]

/-- The three-state kernel `P(i, ·) = ½(δ_{i+1} + δ_{i+2})` on `Fin 3`. -/
noncomputable def gp_threeKernel : Kernel (Fin 3) (Fin 3) :=
  Kernel.ofFunOfCountable fun i => (1 / 2 : ℝ≥0∞) • (Measure.dirac (i + 1) + Measure.dirac (i + 2))

theorem gp_threeKernel_real (i : Fin 3) (A : Set (Fin 3)) :
    (gp_threeKernel i).real A =
      (A.indicator (1 : Fin 3 → ℝ) (i + 1) + A.indicator (1 : Fin 3 → ℝ) (i + 2)) / 2 := by
  have h : gp_threeKernel i A =
      2⁻¹ * A.indicator 1 (i + 1) + 2⁻¹ * A.indicator 1 (i + 2) := by
    simp [gp_threeKernel, Kernel.ofFunOfCountable]
  rw [measureReal_def, h]
  by_cases h1 : i + 1 ∈ A <;> by_cases h2 : i + 2 ∈ A <;> simp [h1, h2, ENNReal.inv_two_add_inv_two]

/-- **Proposition 3.3.1**: the converse fails with the same `N`. On `Fin 3`, the kernel
`P(i, ·) = ½(δ_{i+1} + δ_{i+2})` satisfies Condition M for `(1, 1/2)` but the Minorization
Condition for `N = 1` fails for every `α` and `μ` (the book's proof claims `(N, ε)`). -/
theorem proposition_3_3_1_counterexample :
    ConditionMFor gp_threeKernel 1 (1 / 2) ∧ ∀ α μ, ¬ MinorizationFor gp_threeKernel 1 α μ := by
  refine ⟨⟨le_rfl, by norm_num, fun A _ => ?_⟩, fun α μ ⟨_, hα, hμ, hmin⟩ => ?_⟩
  · simp only [gp_kpow_one, gp_threeKernel_real]
    by_cases h0 : (0 : Fin 3) ∈ A <;> by_cases h1 : (1 : Fin 3) ∈ A <;>
      by_cases h2 : (2 : Fin 3) ∈ A
    all_goals try (left; intro i; fin_cases i <;> simp_all <;> norm_num; done)
    all_goals (right; intro i; fin_cases i <;> simp_all <;> norm_num)
  · have hz : ∀ i : Fin 3, μ {i} = 0 := fun i => by
      have := hmin i {i} (MeasurableSet.singleton i)
      rw [gp_kpow_one, gp_threeKernel_real] at this
      have hne1 : i + 1 ≠ i := by fin_cases i <;> decide
      have hne2 : i + 2 ≠ i := by fin_cases i <;> decide
      rw [Set.indicator_of_notMem (by simp [hne1]),
        Set.indicator_of_notMem (by simp [hne2]), add_zero, zero_div] at this
      have h0 : μ.real {i} = 0 :=
        le_antisymm (by nlinarith [measureReal_nonneg (μ := μ) (s := {i})]) measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top μ _)).1 h0
    have : μ Set.univ ≤ ∑' i : Fin 3, μ {i} := by
      rw [← Set.iUnion_of_singleton (α := Fin 3)]
      exact measure_iUnion_le _
    simp [hz] at this

/-- Corrected **Proposition 3.3.1**, converse: if Condition M holds and the invariant measure
`π` of Theorem 3.3.1 has an atom `x₀`, the Minorization Condition holds with `μ = δ_{x₀}`. -/
theorem proposition_3_3_1_of_atom [MeasurableSingletonClass X] {N : ℕ} {ε : ℝ}
    (hM : ConditionMFor κ N ε) {pm : Measure X} [IsProbabilityMeasure pm]
    (h38 : ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
      dTV (adjointOp (kpow κ (N * k)) l₀) pm ≤ (1 - ε) ^ k * dTV l₀ pm)
    {x₀ : X} (hx₀ : 0 < pm.real {x₀}) : Minorization κ := by
  obtain ⟨hN, hε, hMA⟩ := hM
  have hε1 : ε ≤ 1 := by
    have := gp_isMarkov_kpow (κ := κ) N
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h x₀; simp at this; linarith
    · have := h x₀; simp at this; linarith
  have hlim : Tendsto (fun k => (1 - ε) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  obtain ⟨K₀, hK₀⟩ := (hlim.eventually (gt_mem_nhds (half_pos hx₀))).exists_forall_of_atTop
  set K := K₀ + 1
  have hK : (1 - ε) ^ K < pm.real {x₀} / 2 := hK₀ K (by omega)
  have hNK : 1 ≤ N * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have := gp_isMarkov_kpow (κ := κ) (N * K)
  have hclose : ∀ x, pm.real {x₀} / 2 ≤ (kpow κ (N * K) x).real {x₀} := fun x => by
    have e : adjointOp (kpow κ (N * K)) (Measure.dirac x) = kpow κ (N * K) x :=
      Measure.dirac_bind (Kernel.measurable _) x
    have h1 := h38 (Measure.dirac x) K
    rw [e] at h1
    have h2 := gp_abs_le_dTV (kpow κ (N * K) x) pm (MeasurableSet.singleton x₀)
    have h3 := gp_dTV_le_one (Measure.dirac x) pm
    have h4 : (1 - ε) ^ K * dTV (Measure.dirac x) pm ≤ (1 - ε) ^ K :=
      mul_le_of_le_one_right (pow_nonneg (by linarith) _) h3
    have := (abs_le.1 (h2.trans (h1.trans h4))).1
    linarith
  refine ⟨N * K, pm.real {x₀} / 2, Measure.dirac x₀, hNK, half_pos hx₀, inferInstance,
    fun x A hA => ?_⟩
  by_cases hA0 : x₀ ∈ A
  · have h1 : (Measure.dirac x₀).real A = 1 := by
      simp [measureReal_def, Measure.dirac_apply_of_mem hA0]
    rw [h1, mul_one]
    exact (hclose x).trans (measureReal_mono (Set.singleton_subset_iff.2 hA0))
  · have h0 : (Measure.dirac x₀).real A = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hA, Set.indicator_of_notMem hA0]
    rw [h0, mul_zero]
    exact measureReal_nonneg

/-- **Proposition 3.3.1** (Miao, p. 107), corrected. The Minorization Condition implies
Condition M; on a nonempty countable state space (with measurable singletons) Condition M
implies the Minorization Condition. (On `X = ∅` Condition M holds vacuously and the
Minorization Condition fails, since there is no probability measure.) -/
theorem proposition_3_3_1 :
    (Minorization κ → ConditionM κ) ∧
      (∀ [Countable X] [MeasurableSingletonClass X] [Nonempty X],
        ConditionM κ → Minorization κ) := by
  refine ⟨fun ⟨N, α, μ, h⟩ => ⟨N, α / 2, proposition_3_3_1_forward h⟩, fun hM => ?_⟩
  obtain ⟨N, ε, hM⟩ := hM
  obtain ⟨pm, ⟨hpm, h38⟩, -⟩ := theorem_3_3_1 hM
  have : ∃ x₀, 0 < pm.real {x₀} := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ x, pm {x} = 0 := fun x =>
      (measureReal_eq_zero_iff (measure_ne_top pm _)).1 (le_antisymm (hcon x) measureReal_nonneg)
    have := pm.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
    simp [hz] at this
  obtain ⟨x₀, hx₀⟩ := this
  exact proposition_3_3_1_of_atom hM h38 hx₀

/-- **Example 3.3.1** (Miao, p. 108). If `Pᴺ(x, {x₀}) > ε` for all `x`, Condition M holds for
`(N, ε)`: a set containing `x₀`, or its complement, has `Pᴺ`-mass at least `ε` from every `x`. -/
theorem example_3_3_1 [MeasurableSingletonClass X] {x₀ : X} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ x, ε < (kpow κ N x).real {x₀}) : ConditionMFor κ N ε := by
  have := gp_isMarkov_kpow (κ := κ) N
  refine ⟨hN, hε, fun A _ => ?_⟩
  by_cases hA : x₀ ∈ A
  · exact Or.inl fun x => (h x).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hA))
  · exact Or.inr fun x => (h x).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hA))

/-- **Example 3.3.2** (Miao, p. 108). If `P(x, A) = ∫_A p(x, x′) μ(dx′)` with `p ≥ ε > 0` and `μ`
a probability measure, the Minorization Condition holds for `(1, ε, μ)`. -/
theorem example_3_3_2 {μ : Measure X} [IsProbabilityMeasure μ] {p : X → X → ℝ≥0∞} {ε : ℝ}
    (hε : 0 < ε) (hp : ∀ x y, ENNReal.ofReal ε ≤ p x y)
    (hP : ∀ x A, MeasurableSet A → κ x A = ∫⁻ y in A, p x y ∂μ) :
    MinorizationFor κ 1 ε μ := by
  refine ⟨le_rfl, hε, inferInstance, fun x A hA => ?_⟩
  rw [gp_kpow_one]
  have hle : ENNReal.ofReal ε * μ A ≤ κ x A := by
    rw [hP x A hA, ← setLIntegral_const]
    exact lintegral_mono fun y => hp x y
  have := ENNReal.toReal_mono (measure_ne_top (κ x) A) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le] at this

/-- **Example 3.3.3** (Miao, p. 108). On a countable `X`, if
`α = Σ_y inf_x Pᴺ(x, {y}) > 0` (3.9), the Minorization Condition holds for `(N, α, ν)` with
`ν{y} = α⁻¹ inf_x Pᴺ(x, {y})`. -/
theorem example_3_3_3 [Countable X] [MeasurableSingletonClass X] {N : ℕ} (hN : 1 ≤ N)
    (hα : 0 < ∑' y, ⨅ x, kpow κ N x {y}) :
    ∃ ν : Measure X, (∀ y, ν {y} = (∑' y, ⨅ x, kpow κ N x {y})⁻¹ * ⨅ x, kpow κ N x {y}) ∧
      MinorizationFor κ N (∑' y, ⨅ x, kpow κ N x {y}).toReal ν := by
  have := gp_isMarkov_kpow (κ := κ) N
  set m : X → ℝ≥0∞ := fun y => ⨅ x, kpow κ N x {y}
  set α := ∑' y, m y
  have hX : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    simp [α] at hα
  obtain ⟨x₀⟩ := hX
  have hα1 : α ≤ 1 := by
    calc α ≤ ∑' y, kpow κ N x₀ {y} := ENNReal.tsum_le_tsum fun y => iInf_le _ x₀
      _ = kpow κ N x₀ Set.univ := by
          simpa using (kpow κ N x₀).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := measure_univ
  have hαt : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hα1
  set ν : Measure X := Measure.sum fun y => (α⁻¹ * m y) • Measure.dirac y
  have hνA : ∀ A, MeasurableSet A → ν A = ∑' y, A.indicator (fun y => α⁻¹ * m y) y := by
    intro A hA
    simp only [ν, Measure.sum_apply _ hA, Measure.smul_apply, Measure.dirac_apply' _ hA,
      smul_eq_mul]
    congr 1
    funext y
    by_cases hy : y ∈ A <;> simp [hy]
  have hν1 : ν Set.univ = 1 := by
    rw [hνA _ MeasurableSet.univ]
    simp only [Set.indicator_univ]
    rw [ENNReal.tsum_mul_left, ENNReal.inv_mul_cancel hα.ne' hαt]
  have hνp : IsProbabilityMeasure ν := ⟨hν1⟩
  refine ⟨ν, fun y => ?_, hN, ENNReal.toReal_pos hα.ne' hαt, hνp, fun x A hA => ?_⟩
  · rw [hνA _ (MeasurableSet.singleton y), tsum_eq_single y fun z hz => by simp [hz]]
    simp [m]
  · have hle : α * ν A ≤ kpow κ N x A := by
      rw [hνA A hA, ← ENNReal.tsum_mul_left,
        ← (kpow κ N x).tsum_indicator_apply_singleton A hA]
      refine ENNReal.tsum_le_tsum fun y => ?_
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy]
        rw [← mul_assoc, ENNReal.mul_inv_cancel hα.ne' hαt, one_mul]
        exact iInf_le _ x
      · simp [hy]
    have := ENNReal.toReal_mono (measure_ne_top _ A) hle
    rwa [ENNReal.toReal_mul] at this

omit [IsMarkovKernel κ] in
/-- **Example 3.3.3**, finite case (Miao, p. 108): if `X` is finite and nonempty and some power
`Pᴺ` has all entries positive (by Theorem 3.1.4 this holds for an irreducible aperiodic chain),
then (3.9) holds. -/
theorem example_3_3_3_finite [Finite X] [Nonempty X] {N : ℕ}
    (hpos : ∀ x y, 0 < kpow κ N x {y}) : 0 < ∑' y, ⨅ x, kpow κ N x {y} := by
  obtain ⟨y₀⟩ := ‹Nonempty X›
  obtain ⟨x₁, hx₁⟩ := exists_eq_ciInf_of_finite (f := fun x => kpow κ N x {y₀})
  calc (0 : ℝ≥0∞) < ⨅ x, kpow κ N x {y₀} := by rw [← hx₁]; exact hpos x₁ y₀
    _ ≤ ∑' y, ⨅ x, kpow κ N x {y} := ENNReal.le_tsum (f := fun y => ⨅ x, kpow κ N x {y}) y₀

end Miao.Applications
