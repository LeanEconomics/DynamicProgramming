/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.GeneralKernels
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Measures on sequence spaces: Ionescu Tulcea, Kolmogorov and the Markov process of `(μ₀, P)`

Miao, §3.2, pp. 100–102.

* `gp_eq_of_map_frestrictLe`: a probability measure on `Π n, Xₙ` is determined by its
  finite-dimensional distributions (the uniqueness half of Theorems 3.2.2–3.2.4).
* **Theorem 3.2.4** (Ionescu Tulcea, `theorem_3_2_4`, `tulceaFD`, `tulceaFD_zero`,
  `tulceaFD_succ`): given `Q₀` on `Ω₀` and kernels `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)`, the measures `Pₙ`
  on `Ω₀ × ⋯ × Ωₙ` defined by the iterated integrals, and a unique `Pr` on `Π Ωₙ` whose
  finite-dimensional distributions are the `Pₙ`; the coordinate process realises them. The
  construction is Mathlib's `Kernel.trajMeasure`.
* **Theorem 3.2.2** (Kolmogorov extension, `theorem_3_2_2`, `eq_3_2_iff`): a sequence of
  probability measures `μₜ` on `Xᵗ⁺¹` satisfying the consistency condition (3.2) extends uniquely
  to `X^∞`. Departure: `X` is assumed to be a standard Borel space. Mathlib has no general
  Kolmogorov extension theorem, and the theorem is false for arbitrary measurable spaces (the
  classical counterexamples of Andersen and Jessen; not formalised here). The proof derives
  Kolmogorov from Ionescu Tulcea: disintegrating `μₜ₊₁` over its first `t + 1` coordinates
  (`Measure.condKernel`, which needs a standard Borel `X`) gives kernels `κₜ` with
  `μₜ₊₁ = μₜ ⊗ κₜ`.
* **Theorem 3.2.3** (`theorem_3_2_3`, `markovPath`) and **Remark 3.2.1** (the coordinate
  process `Xₜ(ω) = ωₜ` on the canonical space): for `μ₀` and a transition function `P` the
  canonical process is Markov with transition function `P`, in the rigorous form that the joint
  law of `(X₀, …, Xₜ, Xₜ₊₁)` is the law of `(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`; in particular
  `Pr(Xₜ ∈ A, Xₜ₊₁ ∈ B) = ∫_A P(x, B) Pr(Xₜ ∈ dx)`, which is the meaning of
  `Pr(Xₜ₊₁ ∈ B | Xₜ = x) = P(x, B)`. `X₀ ~ μ₀`, `Xₜ ~ T*ᵗμ₀`, and `Pr` is the unique measure with
  these properties.

Typo in Theorem 3.2.4: the kernels are stated as `Qₙ : (Ω₀ × ⋯ × Ωₙ) × 𝓕ₙ₊₁ → [0, 1]` for
`n ≥ 1`, but the formula for `Pₙ` uses `Q₁(ω₀; dω₁), …, Qₙ(ω₀, …, ωₙ₋₁; dωₙ)`; the Lean kernel
`κ n` is the book's `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)`, `n ≥ 0`. The finite products are indexed by
`Finset.Iic n = {0, …, n}`, so the book's `Xᵗ` is `Π i : Iic (t - 1), X`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology Preorder
open scoped ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Probability measures on `Π n, Xₙ` with the same finite-dimensional distributions on the
initial segments `{0, …, n}` are equal. -/
theorem gp_eq_of_map_frestrictLe {ν ν' : Measure (Π n, X n)} [IsProbabilityMeasure ν]
    (h : ∀ n, ν'.map (frestrictLe n) = ν.map (frestrictLe n)) : ν' = ν := by
  have hproj : IsProjectiveMeasureFamily (fun I : Finset ℕ => ν.map I.restrict) :=
    isProjectiveMeasureFamily_map_restrict (X := fun n (ω : Π n, X n) => ω n) (P := ν)
      (fun t => (measurable_pi_apply t).aemeasurable)
  have h1 : IsProjectiveLimit ν (fun I : Finset ℕ => ν.map I.restrict) := fun _ => rfl
  have h2 : IsProjectiveLimit ν' (fun I : Finset ℕ => ν.map I.restrict) :=
    (isProjectiveLimit_nat_iff hproj ν').2 fun n => h n
  exact h2.unique h1

/-- The finite-dimensional distributions `Pₙ` on `Ω₀ × ⋯ × Ωₙ` of Theorem 3.2.4 (Miao, p. 102):
`P₀ = Q₀` and `Pₙ₊₁` is `Pₙ` followed by `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)` (`tulceaFD_succ`). -/
noncomputable def tulceaFD (Q₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) (n : ℕ) :
    Measure (Π i : Finset.Iic n, X i) :=
  Kernel.partialTraj κ 0 n ∘ₘ Q₀.map (MeasurableEquiv.piUnique _).symm

variable (Q₀ : Measure (X 0)) [IsProbabilityMeasure Q₀]
  (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

omit [IsProbabilityMeasure Q₀] in
/-- The marginals of `trajMeasure` are the measures `Pₙ`. -/
theorem gp_trajMeasure_map_frestrictLe (n : ℕ) :
    (Kernel.trajMeasure Q₀ κ).map (frestrictLe n) = tulceaFD Q₀ κ n := by
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe, tulceaFD]

omit [IsProbabilityMeasure Q₀] [∀ n, IsMarkovKernel (κ n)] in
/-- Theorem 3.2.4 (Miao, p. 102): `P₀ = Q₀` (on the one-point product `Ω₀`). -/
theorem tulceaFD_zero : tulceaFD Q₀ κ 0 = Q₀.map (MeasurableEquiv.piUnique _).symm := by
  rw [tulceaFD, Kernel.partialTraj_self, Measure.id_comp]

/-- Theorem 3.2.4 (Miao, p. 102), the iterated integrals:
`Pₙ₊₁(A × Aₙ₊₁) = ∫_A Qₙ₊₁(ω₀, …, ωₙ; Aₙ₊₁) Pₙ(dω₀ ⋯ dωₙ)` for measurable `A ⊆ Ω₀ × ⋯ × Ωₙ`;
for `A = A₀ × ⋯ × Aₙ` and iterated, this is the book's formula for `Pₙ₊₁(A₀ × ⋯ × Aₙ₊₁)`. -/
theorem tulceaFD_succ (n : ℕ) {A : Set (Π i : Finset.Iic n, X i)} (hA : MeasurableSet A)
    {B : Set (X (n + 1))} (hB : MeasurableSet B) :
    tulceaFD Q₀ κ (n + 1)
        {y | frestrictLe₂ (Nat.le_succ n) y ∈ A ∧ y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ B} =
      ∫⁻ ω in A, κ n ω B ∂tulceaFD Q₀ κ n := by
  have hm : Measurable fun x : Π n, X n => (frestrictLe n x, x (n + 1)) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  have hS : MeasurableSet
      {y : Π i : Finset.Iic (n + 1), X i |
        frestrictLe₂ (Nat.le_succ n) y ∈ A ∧ y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ B} :=
    ((measurable_frestrictLe₂ _) hA).inter ((measurable_pi_apply _) hB)
  rw [← gp_trajMeasure_map_frestrictLe, Measure.map_apply (measurable_frestrictLe _) hS,
    ← gp_trajMeasure_map_frestrictLe, ← Measure.compProd_apply_prod hA hB,
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_apply hm (hA.prod hB)]
  rfl

/-- **Theorem 3.2.4** (Ionescu Tulcea, Miao, p. 102). There is a unique probability measure `Pr`
on `(Π Ωₙ, ⊗ 𝓕ₙ)` whose finite-dimensional distributions are the `Pₙ`, and the coordinate
process `Xₙ(ω) = ωₙ` satisfies `Pr(X₀ ∈ A₀, …, Xₙ ∈ Aₙ) = Pₙ(A₀ × ⋯ × Aₙ)`. -/
theorem theorem_3_2_4 :
    ∃! Pr : Measure (Π n, X n), IsProbabilityMeasure Pr ∧
      (∀ n, Pr.map (frestrictLe n) = tulceaFD Q₀ κ n) ∧
      ∀ (n : ℕ) (A : (i : Finset.Iic n) → Set (X i)), (∀ i, MeasurableSet (A i)) →
        Pr {ω | ∀ i : Finset.Iic n, ω i ∈ A i} = tulceaFD Q₀ κ n (Set.univ.pi A) := by
  refine ⟨Kernel.trajMeasure Q₀ κ, ⟨inferInstance, gp_trajMeasure_map_frestrictLe Q₀ κ,
    fun n A hA => ?_⟩, ?_⟩
  · rw [← gp_trajMeasure_map_frestrictLe, Measure.map_apply (measurable_frestrictLe n)
      (MeasurableSet.univ_pi hA)]
    congr 1
    ext ω
    simp [frestrictLe_apply]
  · rintro Pr ⟨hPr, hmarg, -⟩
    refine gp_eq_of_map_frestrictLe fun n => ?_
    rw [hmarg, gp_trajMeasure_map_frestrictLe]

/-! ### One state space: the snoc map on initial segments -/

variable {Z : Type*} [MeasurableSpace Z]

/-- Append a last coordinate: `((x₀, …, xₜ), z) ↦ (x₀, …, xₜ, z)`. -/
def gp_snocIic (t : ℕ) (p : (Π _ : Finset.Iic t, Z) × Z) : Π _ : Finset.Iic (t + 1), Z :=
  fun i => if h : i.1 ≤ t then p.1 ⟨i.1, Finset.mem_Iic.2 h⟩ else p.2

theorem gp_measurable_snocIic (t : ℕ) : Measurable (gp_snocIic (Z := Z) t) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i.1 ≤ t
  · simp only [gp_snocIic, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [gp_snocIic, h, ↓reduceDIte]
    exact measurable_snd

omit [MeasurableSpace Z] in
theorem gp_snocIic_pair (t : ℕ) (ω : ℕ → Z) :
    gp_snocIic t (frestrictLe t ω, ω (t + 1)) = frestrictLe (t + 1) ω := by
  funext i
  by_cases h : i.1 ≤ t
  · simp [gp_snocIic, h, frestrictLe_apply]
  · have hi : i.1 = t + 1 := by have := Finset.mem_Iic.1 i.2; omega
    simp [gp_snocIic, frestrictLe_apply, hi]

omit [MeasurableSpace Z] in
theorem gp_snocIic_restrict (t : ℕ) (y : Π _ : Finset.Iic (t + 1), Z) :
    gp_snocIic t (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) y,
      y ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩) = y := by
  funext i
  by_cases h : i.1 ≤ t
  · simp [gp_snocIic, h, frestrictLe₂_apply]
  · have hi : i = ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      have := Finset.mem_Iic.1 i.2; ext; simp only; omega
    simp [gp_snocIic, hi]

theorem gp_frestrictLe_zero (ω : ℕ → Z) :
    frestrictLe 0 ω = (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm (ω 0) := by
  funext i
  have hi : i.1 = 0 := Finset.mem_Iic.1 i.2 |>.antisymm (Nat.zero_le _)
  simp [frestrictLe_apply, hi]

/-! ### Theorem 3.2.3 -/

/-- The kernels `(x₀, …, xₙ) ↦ P(xₙ, ·)` that drive the Markov process. -/
noncomputable def gp_lastKernel (P : Kernel Z Z) (n : ℕ) : Kernel (Π _ : Finset.Iic n, Z) Z :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem gp_isMarkovKernel_lastKernel (P : Kernel Z Z) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (gp_lastKernel P n) := by
  unfold gp_lastKernel
  infer_instance

/-- The law `Pr` on `(X^∞, 𝒳^∞)` of the Markov process with initial distribution `μ₀` and
transition function `P` (Miao, Theorem 3.2.3, p. 101), built by Ionescu Tulcea. -/
noncomputable def markovPath (P : Kernel Z Z) [IsMarkovKernel P] (μ₀ : Measure Z) :
    Measure (ℕ → Z) :=
  have := gp_isMarkovKernel_lastKernel P
  Kernel.trajMeasure (X := fun _ => Z) μ₀ (gp_lastKernel P)

variable (P : Kernel Z Z) [IsMarkovKernel P] (μ₀ : Measure Z) [IsProbabilityMeasure μ₀]

theorem gp_isProbabilityMeasure_markovPath : IsProbabilityMeasure (markovPath P μ₀) := by
  have := gp_isMarkovKernel_lastKernel P
  unfold markovPath
  infer_instance

/-- The Markov property of `markovPath`: the law of `((X₀, …, Xₜ), Xₜ₊₁)` is the law of
`(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`. -/
theorem gp_markovPath_markov (t : ℕ) :
    (markovPath P μ₀).map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      (markovPath P μ₀).map (frestrictLe t) ⊗ₘ gp_lastKernel P t := by
  have := gp_isMarkovKernel_lastKernel P
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Z) (μ₀ := μ₀) (κ := gp_lastKernel P) (a := t)).symm

omit [IsProbabilityMeasure μ₀] in
/-- The initial distribution of `markovPath` is `μ₀`. -/
theorem gp_markovPath_map_zero : (markovPath P μ₀).map (fun ω => ω 0) = μ₀ := by
  have := gp_isMarkovKernel_lastKernel P
  have h0 := gp_trajMeasure_map_frestrictLe (X := fun _ => Z) μ₀ (gp_lastKernel P) 0
  rw [tulceaFD_zero] at h0
  have he : (fun ω : ℕ → Z => ω 0) =
      (fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 :=
    rfl
  have hev : Measurable fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  rw [he, ← Measure.map_map hev (measurable_frestrictLe 0)]
  change ((Kernel.trajMeasure (X := fun _ => Z) μ₀ (gp_lastKernel P)).map (frestrictLe 0)).map _
    = μ₀
  rw [h0, Measure.map_map hev (MeasurableEquiv.measurable _)]
  exact Measure.map_id

/-- Uniqueness for Theorem 3.2.3: a probability measure on paths with initial law `μ₀` and the
Markov property for `P` is `markovPath P μ₀`. -/
theorem gp_markovPath_unique {Pr : Measure (ℕ → Z)} [IsProbabilityMeasure Pr]
    (h0 : Pr.map (fun ω => ω 0) = μ₀)
    (hM : ∀ t, Pr.map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      Pr.map (frestrictLe t) ⊗ₘ gp_lastKernel P t) : Pr = markovPath P μ₀ := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  have := gp_isMarkovKernel_lastKernel P
  refine gp_eq_of_map_frestrictLe fun t => ?_
  induction t with
  | zero =>
    have he : (frestrictLe 0 : (ℕ → Z) → _) =
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm ∘ fun ω => ω 0 :=
      funext gp_frestrictLe_zero
    have hev0 : Measurable fun ω : ℕ → Z => ω 0 := measurable_pi_apply 0
    rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) hev0,
      ← Measure.map_map (MeasurableEquiv.measurable _) hev0, h0,
      gp_markovPath_map_zero]
  | succ t ih =>
    have hp : Measurable fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1)) :=
      (measurable_frestrictLe t).prodMk (measurable_pi_apply _)
    have he : (frestrictLe (t + 1) : (ℕ → Z) → _) =
        gp_snocIic t ∘ fun ω => (frestrictLe t ω, ω (t + 1)) :=
      funext fun ω => (gp_snocIic_pair t ω).symm
    rw [he, ← Measure.map_map (gp_measurable_snocIic t) hp,
      ← Measure.map_map (gp_measurable_snocIic t) hp, hM, gp_markovPath_markov, ih]

/-- **Theorem 3.2.3** (Miao, p. 101). For a probability measure `μ₀` and a transition function
`P` there is a unique probability measure `Pr` on `(X^∞, 𝒳^∞)` under which the coordinate process
`Xₜ(ω) = ωₜ` (Remark 3.2.1) has `X₀ ~ μ₀` and is Markov with transition function `P`: the joint
law of `((X₀, …, Xₜ), Xₜ₊₁)` is the law of `(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`. -/
theorem theorem_3_2_3 :
    ∃! Pr : Measure (ℕ → Z), IsProbabilityMeasure Pr ∧ Pr.map (fun ω => ω 0) = μ₀ ∧
      ∀ t, Pr.map (fun ω => (frestrictLe t ω, ω (t + 1))) =
        Pr.map (frestrictLe t) ⊗ₘ gp_lastKernel P t := by
  refine ⟨markovPath P μ₀, ⟨gp_isProbabilityMeasure_markovPath P μ₀,
    gp_markovPath_map_zero P μ₀, gp_markovPath_markov P μ₀⟩, ?_⟩
  rintro Pr ⟨hPr, h0, hM⟩
  exact gp_markovPath_unique P μ₀ h0 hM

/-- **Theorem 3.2.3 (a)** (Miao, p. 101): `Pr(Xₜ₊₁ ∈ B | Xₜ = x) = P(x, B)`, in the form
`law(Xₜ, Xₜ₊₁) = law(Xₜ) ⊗ P`, that is `Pr(Xₜ ∈ A, Xₜ₊₁ ∈ B) = ∫_A P(x, B) Pr(Xₜ ∈ dx)`. -/
theorem theorem_3_2_3_transition (t : ℕ) :
    (markovPath P μ₀).map (fun ω => (ω t, ω (t + 1))) =
        (markovPath P μ₀).map (fun ω => ω t) ⊗ₘ P ∧
      ∀ A B, MeasurableSet A → MeasurableSet B →
        markovPath P μ₀ {ω | ω t ∈ A ∧ ω (t + 1) ∈ B} =
          ∫⁻ x in A, P x B ∂(markovPath P μ₀).map (fun ω => ω t) := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  have := gp_isMarkovKernel_lastKernel P
  have hpair : Measurable fun ω : ℕ → Z => (ω t, ω (t + 1)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hlaw : (markovPath P μ₀).map (fun ω => (ω t, ω (t + 1))) =
      (markovPath P μ₀).map (fun ω => ω t) ⊗ₘ P := by
    refine Measure.ext_prod fun {A} {B} hA hB => ?_
    have hev : Measurable fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩ :=
      measurable_pi_apply _
    have hp : Measurable fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1)) :=
      (measurable_frestrictLe t).prodMk (measurable_pi_apply _)
    have hset : (fun ω : ℕ → Z => (ω t, ω (t + 1))) ⁻¹' A ×ˢ B =
        (fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1))) ⁻¹'
          (((fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' A) ×ˢ B) :=
      rfl
    have hlt : (fun ω : ℕ → Z => ω t) =
        (fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘ frestrictLe t := rfl
    rw [Measure.map_apply hpair (hA.prod hB), hset, ← Measure.map_apply hp ((hev hA).prod hB),
      gp_markovPath_markov, Measure.compProd_apply_prod (hev hA) hB,
      Measure.compProd_apply_prod hA hB, hlt, ← Measure.map_map hev (measurable_frestrictLe t),
      setLIntegral_map hA (P.measurable_coe hB) hev]
    rfl
  refine ⟨hlaw, fun A B hA hB => ?_⟩
  rw [← Measure.compProd_apply_prod hA hB, ← hlaw, Measure.map_apply hpair (hA.prod hB)]
  rfl

/-- Theorem 3.2.3 and p. 104: under `Pr`, `X₀ ~ μ₀` and `Xₜ ~ T*ᵗμ₀ = λₜ`. -/
theorem theorem_3_2_3_marginal (t : ℕ) :
    (markovPath P μ₀).map (fun ω => ω t) = adjointOp (kpow P t) μ₀ := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  induction t with
  | zero => rw [gp_markovPath_map_zero, ← gp_adjointOp_iterate P 0 μ₀]; rfl
  | succ t ih =>
    have hpair : Measurable fun ω : ℕ → Z => (ω t, ω (t + 1)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hs : (markovPath P μ₀).map (fun ω => ω (t + 1)) =
        ((markovPath P μ₀).map (fun ω => (ω t, ω (t + 1)))).snd := by
      rw [Measure.snd, Measure.map_map measurable_snd hpair]
      rfl
    rw [hs, (theorem_3_2_3_transition P μ₀ t).1, Measure.snd_compProd, ih, add_comm,
      eq_p103_Tstar, gp_kpow_one]
    rfl

/-! ### Theorem 3.2.2 (Kolmogorov extension) -/

/-- Append `X` as the last factor of a rectangle: `A₀ × ⋯ × Aₜ ↦ A₀ × ⋯ × Aₜ × X`. -/
def gp_extendBox (t : ℕ) (A : Finset.Iic t → Set Z) : Finset.Iic (t + 1) → Set Z :=
  fun i => if h : i.1 ≤ t then A ⟨i.1, Finset.mem_Iic.2 h⟩ else Set.univ

omit [MeasurableSpace Z] in
theorem gp_preimage_extendBox (t : ℕ) (A : Finset.Iic t → Set Z) :
    frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) ⁻¹' Set.univ.pi A =
      Set.univ.pi (gp_extendBox t A) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, frestrictLe₂_apply]
  constructor
  · intro h i
    by_cases hi : i.1 ≤ t
    · simpa [gp_extendBox, hi] using h ⟨i.1, Finset.mem_Iic.2 hi⟩
    · simp [gp_extendBox, hi]
  · intro h i
    have := h ⟨i.1, Finset.mem_Iic.2 ((Finset.mem_Iic.1 i.2).trans (Nat.le_succ t))⟩
    simpa [gp_extendBox, Finset.mem_Iic.1 i.2] using this

/-- **(3.2)** (Miao, p. 100), the Kolmogorov consistency condition
`μₜ(A₀ × ⋯ × Aₜ) = μₜ₊₁(A₀ × ⋯ × Aₜ × X)`, is equivalent to `μₜ` being the image of `μₜ₊₁`
under the projection forgetting the last coordinate. -/
theorem eq_3_2_iff (μ : (n : ℕ) → Measure (Π _ : Finset.Iic n, Z))
    [∀ n, IsProbabilityMeasure (μ n)] (t : ℕ) :
    (∀ A : Finset.Iic t → Set Z, (∀ i, MeasurableSet (A i)) →
        μ t (Set.univ.pi A) = μ (t + 1) (Set.univ.pi (gp_extendBox t A))) ↔
      (μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) = μ t := by
  have hm : Measurable (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) :=
    measurable_frestrictLe₂ _
  constructor
  · intro h
    have : IsProbabilityMeasure
        ((μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t))) := inferInstance
    refine (ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ (by simp)).symm
    rintro _ ⟨A, hA, rfl⟩
    rw [h A fun i => hA i (Set.mem_univ i), Measure.map_apply hm
      (MeasurableSet.univ_pi fun i => hA i (Set.mem_univ i)), gp_preimage_extendBox]
  · intro h A hA
    rw [← h, Measure.map_apply hm (MeasurableSet.univ_pi hA), gp_preimage_extendBox]

/-- **Theorem 3.2.2** (Kolmogorov extension, Miao, p. 100). Let `X` be a standard Borel space and
`μₜ` probability measures on `Xᵗ⁺¹ = Π i ∈ {0, …, t}, X` satisfying the consistency condition
(3.2). Then there is a unique probability measure `μ` on `X^∞` with `μ(A × X^∞) = μₜ(A)` for all
measurable `A ⊆ Xᵗ⁺¹`, i.e. `μₜ` is the image of `μ` under `ω ↦ (ω₀, …, ωₜ)`. The proof
disintegrates `μₜ₊₁ = μₜ ⊗ κₜ` and applies Ionescu Tulcea (Theorem 3.2.4). -/
theorem theorem_3_2_2 [StandardBorelSpace Z] (μ : (n : ℕ) → Measure (Π _ : Finset.Iic n, Z))
    [∀ n, IsProbabilityMeasure (μ n)]
    (h32 : ∀ t (A : Finset.Iic t → Set Z), (∀ i, MeasurableSet (A i)) →
      μ t (Set.univ.pi A) = μ (t + 1) (Set.univ.pi (gp_extendBox t A))) :
    ∃! ν : Measure (ℕ → Z), IsProbabilityMeasure ν ∧ ∀ n, ν.map (frestrictLe n) = μ n := by
  have hcons : ∀ t, (μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) = μ t :=
    fun t => (eq_3_2_iff μ t).1 (h32 t)
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure (μ 0)
  have : Nonempty Z := ⟨y₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩⟩
  -- the pair `((x₀, …, xₜ), xₜ₊₁)` of an element of `Xᵗ⁺²`
  let pr : (t : ℕ) → (Π _ : Finset.Iic (t + 1), Z) → (Π _ : Finset.Iic t, Z) × Z := fun t y =>
    (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) y, y ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩)
  have hpr : ∀ t, Measurable (pr t) := fun t =>
    (measurable_frestrictLe₂ (X := fun _ => Z) (Nat.le_succ t)).prodMk
      (measurable_pi_apply (⟨t + 1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic (t + 1)))
  let ρ : (t : ℕ) → Measure ((Π _ : Finset.Iic t, Z) × Z) := fun t => (μ (t + 1)).map (pr t)
  have hρ : ∀ t, IsProbabilityMeasure (ρ t) := fun t =>
    inferInstance
  have hfst : ∀ t, (ρ t).fst = μ t := fun t => by
    rw [Measure.fst, Measure.map_map measurable_fst (hpr t)]
    exact hcons t
  let κ : (t : ℕ) → Kernel (Π _ : Finset.Iic t, Z) Z := fun t => (ρ t).condKernel
  have hdis : ∀ t, μ t ⊗ₘ κ t = ρ t := fun t => by
    rw [← hfst t]
    exact (ρ t).disintegrate (ρ t).condKernel
  let μ₀ : Measure Z := (μ 0).map fun y => y ⟨0, Finset.mem_Iic.2 le_rfl⟩
  have hμ₀ : IsProbabilityMeasure μ₀ :=
    inferInstance
  let ν : Measure (ℕ → Z) := Kernel.trajMeasure (X := fun _ => Z) μ₀ κ
  have hmarg : ∀ n, ν.map (frestrictLe n) = μ n := by
    intro n
    induction n with
    | zero =>
      have h0 := gp_trajMeasure_map_frestrictLe (X := fun _ => Z) μ₀ κ 0
      rw [tulceaFD_zero] at h0
      change (Kernel.trajMeasure (X := fun _ => Z) μ₀ κ).map (frestrictLe 0) = μ 0
      rw [h0]
      change Measure.map _ (Measure.map
        (fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) (μ 0)) = μ 0
      have hev : Measurable fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
        measurable_pi_apply _
      rw [Measure.map_map (MeasurableEquiv.measurable _) hev]
      have hid : ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm ∘
          fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) = id := by
        funext y i
        have hi : i = ⟨0, Finset.mem_Iic.2 le_rfl⟩ := Subsingleton.elim _ _
        subst hi
        rfl
      rw [hid, Measure.map_id]
    | succ n ih =>
      have hp : Measurable fun ω : ℕ → Z => (frestrictLe n ω, ω (n + 1)) :=
        (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
      have he : (frestrictLe (n + 1) : (ℕ → Z) → _) =
          gp_snocIic n ∘ fun ω => (frestrictLe n ω, ω (n + 1)) :=
        funext fun ω => (gp_snocIic_pair n ω).symm
      have hkey := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => Z) (μ₀ := μ₀) (κ := κ) (a := n)
      have hid : gp_snocIic n ∘ pr n = id := funext fun y => gp_snocIic_restrict n y
      rw [he, ← Measure.map_map (gp_measurable_snocIic n) hp]
      change ((Kernel.trajMeasure (X := fun _ => Z) μ₀ κ).map _).map _ = _
      rw [← hkey]
      change (ν.map (frestrictLe n) ⊗ₘ κ n).map _ = _
      rw [ih, hdis, Measure.map_map (gp_measurable_snocIic n) (hpr n), hid, Measure.map_id]
  have hν : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure (Kernel.trajMeasure (X := fun _ => Z) μ₀ κ)
    infer_instance
  refine ⟨ν, ⟨hν, hmarg⟩, ?_⟩
  rintro ν' ⟨hν', hmarg'⟩
  exact gp_eq_of_map_frestrictLe fun n => by rw [hmarg', hmarg]

end Miao.MarkovProcesses
