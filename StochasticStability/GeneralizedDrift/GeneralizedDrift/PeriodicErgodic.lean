/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.AperiodicErgodic
import GeneralizedDrift.CycleAperiodic

/-!
# Periodic chains and chains that are not Harris (MT Theorem 13.3.4)

Meyn and Tweedie, Theorem 13.3.4, pp. 328–329: (i) a positive Harris chain with period `d`
satisfies `‖d⁻¹ Σ_{r<d} λP^{nd+r} − π‖ → 0` for every initial distribution `λ`; (ii) for a
positive recurrent chain the same holds for every `λ` that does not charge a `ψ`-null set `N`.

The book's proof is one line ("the chain restricted to each cyclic set is aperiodic and positive
Harris on the `d`-skeleton", and Theorem 9.1.5 for (ii)). A chain restricted to an absorbing set
is made into a chain on all of `X` by `absorbKernel`: it moves by the given kernel on the set and
jumps to a fixed probability off it.

**Chains agreeing on an absorbing set.** `H` is absorbing for `Q` (`Q(x, Hᶜ) = 0` on `H`) and
`K = absorbKernel Q hH σ` (`K = Q` on `H`, `K = σ` off `H`).
* `absorbKernel_pow_of_mem`, `comp_absorbKernel_pow`: `Kⁿ = Qⁿ` on `H`, and `λKⁿ = λQⁿ` for `λ`
  concentrated on `H`;
* `tabooKernel_absorbKernel_of_mem`, `hitProb_absorbKernel_of_mem`: the taboo kernels and the
  return probabilities of `K` and `Q` agree on `H`.

**Cycles.** For a `d`-cycle `{Dᵢ}` (Theorem 5.4.4) of a positive Harris chain:
* `IsCycle.measure_eq`, `IsCycle.measure_mul_eq_one`: `π(Dᵢ) = 1/d`; `cycleInv π D i =
  d π(· ∩ Dᵢ)` is a probability, invariant for `Pᵈ`, with `πᵢPʳ = π_{i+r}`
  (`IsCycle.comp_pow_cycleInv`);
* `IsCycle.hitProb_pow_eq_one`: from `x ∈ Dᵢ` the skeleton `Pᵈ` reaches every `A ⊆ Dᵢ` with
  `ψ(A) > 0` almost surely (visits to `Dᵢ` happen only at multiples of `d`);
* `IsCycle.tendsto_tvNorm_pow_mul`: for `λ` concentrated on `Dᵢ`, `‖λP^{nd} − πᵢ‖ → 0`; the chain
  moving by `Pᵈ` on `Dᵢ` and jumping to `πᵢ` off `Dᵢ` is positive Harris and aperiodic, so
  Theorem 13.3.3 applies to it;
* `phaseAvg P d n λ = d⁻¹ Σ_{r<d} λP^{dn+r}` and its linearity; `IsCycle.tendsto_phaseAvg_of_union`
  (the phase averages converge for measures on `⋃ Dᵢ`); `IsCycle.tendsto_compl_iUnion`
  (`λPᵏ((⋃ Dᵢ)ᶜ) → 0` for a Harris chain).

**Restriction to the maximal Harris set.** `absorbKernel_maximalHarris`: for a positive chain and
its maximal Harris set `H` (Theorem 9.1.5), the chain moving by `P` on `H` and jumping to `π` off
`H` is positive Harris, has `π` as invariant probability and has the period of `P`.

**Results.**
* **Theorem 13.3.4 (i)** (`theorem_13_3_4_i`, p. 328), (13.61).
* **Theorem 13.3.4 (ii)** (`theorem_13_3_4_ii`, p. 328), (13.62).
* `tendsto_tvNorm_of_isPositive`: the aperiodic case, Theorem 13.3.3 for positive chains that
  need not be Harris, off a `ψ`-null set.
* **Theorem 13.3.5** in the book's form (`theorem_13_3_5_null`, p. 329), (13.64): positivity and
  convergence off a `ψ`-null set.

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Chains that agree on an absorbing set -/

/-- The chain that moves by `Q` on `H` and jumps to `σ` off `H`. -/
noncomputable def absorbKernel (Q : Kernel X X) {H : Set X} (hH : MeasurableSet H)
    (σ : Measure X) : Kernel X X := by
  classical exact Kernel.piecewise hH Q (Kernel.const X σ)

/-- `K = Q` on `H`. -/
theorem absorbKernel_of_mem (Q : Kernel X X) {H : Set X} (hH : MeasurableSet H)
    (σ : Measure X) {x : X} (hx : x ∈ H) : absorbKernel Q hH σ x = Q x := by
  classical
  rw [absorbKernel, Kernel.piecewise_apply]
  simp [hx]

/-- `K = σ` off `H`. -/
theorem absorbKernel_of_notMem (Q : Kernel X X) {H : Set X} (hH : MeasurableSet H)
    (σ : Measure X) {x : X} (hx : x ∉ H) : absorbKernel Q hH σ x = σ := by
  classical
  rw [absorbKernel, Kernel.piecewise_apply]
  simp [hx]

/-- The restricted chain is a transition kernel. -/
theorem isMarkovKernel_absorbKernel (Q : Kernel X X) [IsMarkovKernel Q] {H : Set X}
    (hH : MeasurableSet H) (σ : Measure X) [IsProbabilityMeasure σ] :
    IsMarkovKernel (absorbKernel Q hH σ) := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x ∈ H
  · rw [absorbKernel_of_mem Q hH σ hx]; infer_instance
  · rw [absorbKernel_of_notMem Q hH σ hx]; infer_instance

/-- Kernels that agree on a set carrying `μ` have the same composition with `μ`. -/
theorem comp_congr_of_compl_eq_zero {κ η : Kernel X X} {H : Set X} {μ : Measure X}
    (hμ : μ Hᶜ = 0) (h : ∀ y ∈ H, κ y = η y) : κ ∘ₘ μ = η ∘ₘ μ := by
  ext B hB
  rw [measure_kernel_apply _ _ hB, measure_kernel_apply _ _ hB]
  refine lintegral_congr_ae ?_
  have : ∀ᵐ y ∂μ, y ∈ H := by
    rw [ae_iff]; exact hμ
  filter_upwards [this] with y hy
  rw [h y hy]

/-- `(κ ∘ₘ μ)(Hᶜ) = 0` when `μ(Hᶜ) = 0` and `κ(y, Hᶜ) = 0` on `H`. -/
theorem comp_compl_eq_zero {κ : Kernel X X} {H : Set X} (hH : MeasurableSet H) {μ : Measure X}
    (hμ : μ Hᶜ = 0) (h : ∀ y ∈ H, κ y Hᶜ = 0) : (κ ∘ₘ μ) Hᶜ = 0 := by
  rw [measure_kernel_apply _ _ hH.compl, ← lintegral_add_compl _ hH,
    setLIntegral_congr_fun hH h, lintegral_zero, Measure.restrict_eq_zero.2 hμ,
    lintegral_zero_measure, add_zero]

/-- An absorbing set stays absorbing for the powers: `Qⁿ(x, Hᶜ) = 0` on `H`. -/
theorem pow_compl_eq_zero_of_absorbing (Q : Kernel X X) {H : Set X} (hH : MeasurableSet H)
    (hQ : ∀ x ∈ H, Q x Hᶜ = 0) (n : ℕ) : ∀ x ∈ H, (Q ^ n : Kernel X X) x Hᶜ = 0 := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero_apply, Measure.dirac_apply' _ hH.compl, indicator_of_notMem (by simpa using hx)]
  | succ n ih =>
    intro x hx
    rw [pow_succ']
    change (Q ∘ₘ (Q ^ n : Kernel X X) x) Hᶜ = 0
    exact comp_compl_eq_zero hH (ih x hx) hQ

variable {Q : Kernel X X} {H : Set X} {σ : Measure X}

/-- `Kⁿ = Qⁿ` on `H`. -/
theorem absorbKernel_pow_of_mem (hH : MeasurableSet H) (hQ : ∀ x ∈ H, Q x Hᶜ = 0) (n : ℕ) :
    ∀ x ∈ H, (absorbKernel Q hH σ ^ n : Kernel X X) x = (Q ^ n : Kernel X X) x := by
  induction n with
  | zero => intro x _; rw [pow_zero_apply, pow_zero_apply]
  | succ n ih =>
    intro x hx
    rw [pow_succ', pow_succ']
    change absorbKernel Q hH σ ∘ₘ (absorbKernel Q hH σ ^ n : Kernel X X) x =
      Q ∘ₘ (Q ^ n : Kernel X X) x
    rw [ih x hx]
    exact comp_congr_of_compl_eq_zero (pow_compl_eq_zero_of_absorbing Q hH hQ n x hx)
      fun y hy => absorbKernel_of_mem Q hH σ hy

/-- `λKⁿ = λQⁿ` for `λ` concentrated on `H`. -/
theorem comp_absorbKernel_pow (hH : MeasurableSet H) (hQ : ∀ x ∈ H, Q x Hᶜ = 0) (n : ℕ)
    {μ : Measure X} (hμ : μ Hᶜ = 0) :
    (absorbKernel Q hH σ ^ n : Kernel X X) ∘ₘ μ = (Q ^ n : Kernel X X) ∘ₘ μ :=
  comp_congr_of_compl_eq_zero hμ fun y hy => absorbKernel_pow_of_mem hH hQ n y hy

/-- The taboo kernels of an absorbing set are concentrated on it. -/
theorem tabooKernel_compl_eq_zero_of_absorbing [IsMarkovKernel Q] (hH : MeasurableSet H)
    (hQ : ∀ x ∈ H, Q x Hᶜ = 0) {A : Set X} (hA : MeasurableSet A) (n : ℕ) {x : X}
    (hx : x ∈ H) : tabooKernel Q hA n x Hᶜ = 0 := by
  have := isMarkovKernel_pathKernel Q
  refine nonpos_iff_eq_zero.1 ?_
  rw [← tabooProb_eq_tabooKernel Q hA n x hH.compl, tabooProb]
  calc pathKernel Q x ({ω | ω (n + 1) ∈ Hᶜ} ∩ {ω | WithTop.some (n + 1) ≤ firstReturn A ω})
      ≤ pathKernel Q x {ω | ω (n + 1) ∈ Hᶜ} := measure_mono inter_subset_left
    _ = (Q ^ (n + 1) : Kernel X X) x Hᶜ := pathKernel_coord_mem Q x (n + 1) hH.compl
    _ = 0 := pow_compl_eq_zero_of_absorbing Q hH hQ (n + 1) x hx

/-- The taboo kernels of `K` and `Q` agree on `H`. -/
theorem tabooKernel_absorbKernel_of_mem [IsMarkovKernel Q] (hH : MeasurableSet H)
    (hQ : ∀ x ∈ H, Q x Hᶜ = 0) {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    ∀ x ∈ H, tabooKernel (absorbKernel Q hH σ) hA n x = tabooKernel Q hA n x := by
  induction n with
  | zero => intro x hx; rw [tabooKernel_zero, tabooKernel_zero, absorbKernel_of_mem Q hH σ hx]
  | succ n ih =>
    intro x hx
    have e1 : tabooKernel (absorbKernel Q hH σ) hA (n + 1) x =
        tabooKernel (absorbKernel Q hH σ) hA n ∘ₘ (Q x).restrict Aᶜ := by
      rw [tabooKernel_succ_eq', Kernel.comp_apply, comp_indKernel_eq_restrict,
        absorbKernel_of_mem Q hH σ hx]
    have e2 : tabooKernel Q hA (n + 1) x = tabooKernel Q hA n ∘ₘ (Q x).restrict Aᶜ := by
      rw [tabooKernel_succ_eq', Kernel.comp_apply, comp_indKernel_eq_restrict]
    rw [e1, e2]
    refine comp_congr_of_compl_eq_zero ?_ ih
    rw [Measure.restrict_apply hH.compl]
    exact nonpos_iff_eq_zero.1 ((measure_mono inter_subset_left).trans (hQ x hx).le)

/-- The return probabilities of `K` and `Q` agree on `H`. -/
theorem hitProb_absorbKernel_of_mem [IsMarkovKernel Q] [IsProbabilityMeasure σ]
    (hH : MeasurableSet H) (hQ : ∀ x ∈ H, Q x Hᶜ = 0) {A : Set X} (hA : MeasurableSet A)
    {x : X} (hx : x ∈ H) :
    haveI := isMarkovKernel_absorbKernel Q hH σ
    hitProb (absorbKernel Q hH σ) A x = hitProb Q A x := by
  have := isMarkovKernel_absorbKernel Q hH σ
  rw [hitProb_eq_tsum _ hA, hitProb_eq_tsum _ hA]
  exact tsum_congr fun n => by rw [tabooKernel_absorbKernel_of_mem hH hQ hA n x hx]

/-! ### Cycles -/

variable {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ} {D : ZMod d → Set X}

/-- `Pᵈ(x, Dᵢᶜ) = 0` on `Dᵢ`: each class is absorbing for `Pᵈ`. -/
theorem IsCycle.pow_d_compl_eq_zero (hD : IsCycle P ψ d D) (i : ZMod d) :
    ∀ x ∈ D i, (P ^ d : Kernel X X) x (D i)ᶜ = 0 := fun x hx => by
  have := isMarkovKernel_pow P d
  have h := hD.pow_apply d hx
  rw [ZMod.natCast_self, add_zero] at h
  exact (prob_compl_eq_zero_iff (hD.measurableSet i)).2 h

/-- `Pʳ(x, D_{i+r}ᶜ) = 0` on `Dᵢ`. -/
theorem IsCycle.pow_compl_eq_zero (hD : IsCycle P ψ d D) (r : ℕ) {i : ZMod d} {x : X}
    (hx : x ∈ D i) : (P ^ r : Kernel X X) x (D (i + r))ᶜ = 0 := by
  have := isMarkovKernel_pow P r
  exact (prob_compl_eq_zero_iff (hD.measurableSet _)).2 (hD.pow_apply r hx)

/-- `π(D_i)Pʳ = π(D_{i+r})`-restrictions: `(π|_{Dᵢ})Pʳ ≤ π|_{D_{i+r}}`. -/
theorem IsCycle.comp_pow_restrict_le (hD : IsCycle P ψ d D) {π : Measure X}
    (hπ : IsInvariant P π) (r : ℕ) (i : ZMod d) :
    (P ^ r : Kernel X X) ∘ₘ π.restrict (D i) ≤ π.restrict (D (i + r)) := by
  have := isMarkovKernel_pow P r
  refine Measure.le_intro fun B hB _ => ?_
  rw [measure_kernel_apply _ _ hB, Measure.restrict_apply hB]
  have h1 : ∀ x ∈ D i, (P ^ r : Kernel X X) x B ≤ (P ^ r : Kernel X X) x (B ∩ D (i + r)) :=
    fun x hx => by
      calc (P ^ r : Kernel X X) x B
          ≤ (P ^ r : Kernel X X) x (B ∩ D (i + r)) + (P ^ r : Kernel X X) x (D (i + r))ᶜ := by
            refine (measure_mono fun y hy => ?_).trans (measure_union_le _ _)
            by_cases h : y ∈ D (i + r)
            · exact Or.inl ⟨hy, h⟩
            · exact Or.inr h
        _ = _ := by rw [hD.pow_compl_eq_zero r hx, add_zero]
  calc ∫⁻ x in D i, (P ^ r : Kernel X X) x B ∂π
      ≤ ∫⁻ x in D i, (P ^ r : Kernel X X) x (B ∩ D (i + r)) ∂π :=
        setLIntegral_mono (Kernel.measurable_coe _ (hB.inter (hD.measurableSet _))) h1
    _ ≤ ∫⁻ x, (P ^ r : Kernel X X) x (B ∩ D (i + r)) ∂π := setLIntegral_le_lintegral _ _
    _ = π (B ∩ D (i + r)) := by
        rw [← measure_kernel_apply _ _ (hB.inter (hD.measurableSet _)), (hπ.pow r :)]

/-- `π(Dᵢ) ≤ π(D_{i+r})`. -/
theorem IsCycle.measure_le (hD : IsCycle P ψ d D) {π : Measure X} (hπ : IsInvariant P π)
    (r : ℕ) (i : ZMod d) : π (D i) ≤ π (D (i + r)) := by
  have := isMarkovKernel_pow P r
  have h := hD.comp_pow_restrict_le hπ r i
  have := congrArg (fun m => m univ) (show (P ^ r : Kernel X X) ∘ₘ π.restrict (D i) =
    (P ^ r : Kernel X X) ∘ₘ π.restrict (D i) from rfl)
  calc π (D i) = ((P ^ r : Kernel X X) ∘ₘ π.restrict (D i)) univ := by
        rw [Measure.comp_apply_univ, Measure.restrict_apply_univ]
    _ ≤ π.restrict (D (i + r)) univ := h univ
    _ = π (D (i + r)) := Measure.restrict_apply_univ _

/-- All the cycle classes have the same `π`-mass. -/
theorem IsCycle.measure_eq (hd : 0 < d) (hD : IsCycle P ψ d D) {π : Measure X}
    (hπ : IsInvariant P π) (i j : ZMod d) : π (D i) = π (D j) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hij : ∀ i j : ZMod d, π (D i) ≤ π (D j) := fun i j => by
    have h := hD.measure_le hπ (j - i).val i
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at h
  exact le_antisymm (hij i j) (hij j i)

/-- `(π|_{Dᵢ})Pʳ = π|_{D_{i+r}}`. -/
theorem IsCycle.comp_pow_restrict (hd : 0 < d) (hD : IsCycle P ψ d D) {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) (r : ℕ) (i : ZMod d) :
    (P ^ r : Kernel X X) ∘ₘ π.restrict (D i) = π.restrict (D (i + r)) := by
  have := isMarkovKernel_pow P r
  refine Measure.eq_of_le_of_measure_univ_eq (hD.comp_pow_restrict_le hπ r i) ?_
  rw [Measure.comp_apply_univ, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
    hD.measure_eq hd hπ]

variable [MeasurableSpace.CountablyGenerated X] in
/-- For an invariant probability of a recurrent chain, `π(Dᵢ) = 1/d`. -/
theorem IsCycle.measure_mul_eq_one (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hrec : IsRecurrentChain P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) : (d : ℝ≥0∞) * π (D i) = 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hac := (theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)).1
  have hN : π (⋃ j, D j)ᶜ = 0 := hac hD.null_compl
  have hU : π (⋃ j, D j) = 1 := by
    rwa [prob_compl_eq_zero_iff (MeasurableSet.iUnion hD.measurableSet)] at hN
  rw [measure_iUnion (fun j k hjk => hD.disjoint j k hjk) hD.measurableSet, tsum_fintype] at hU
  rw [← hU, Finset.sum_congr rfl fun j _ => hD.measure_eq hd hπ j i, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- The normalised restriction `πᵢ = d · π(· ∩ Dᵢ)`. -/
noncomputable def cycleInv (π : Measure X) (D : ZMod d → Set X) (i : ZMod d) : Measure X :=
  (d : ℝ≥0∞) • π.restrict (D i)

variable [MeasurableSpace.CountablyGenerated X] in
/-- `πᵢ` is a probability. -/
theorem IsCycle.isProbabilityMeasure_cycleInv (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hrec : IsRecurrentChain P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) : IsProbabilityMeasure (cycleInv π D i) :=
  ⟨by rw [cycleInv, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    hD.measure_mul_eq_one hd hrec hπ i]⟩

/-- `πᵢPʳ = π_{i+r}`. -/
theorem IsCycle.comp_pow_cycleInv (hd : 0 < d) (hD : IsCycle P ψ d D) {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) (r : ℕ) (i : ZMod d) :
    (P ^ r : Kernel X X) ∘ₘ cycleInv π D i = cycleInv π D (i + r) := by
  rw [cycleInv, Measure.comp_smul, hD.comp_pow_restrict hd hπ r i, cycleInv]

/-- `πᵢ` is invariant for `Pᵈ`. -/
theorem IsCycle.isInvariant_pow_cycleInv (hd : 0 < d) (hD : IsCycle P ψ d D) {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) (i : ZMod d) :
    IsInvariant (P ^ d : Kernel X X) (cycleInv π D i) := by
  unfold IsInvariant
  rw [hD.comp_pow_cycleInv hd hπ d i, ZMod.natCast_self, add_zero]

/-- `πᵢ(Dᵢᶜ) = 0`. -/
theorem cycleInv_compl (π : Measure X) {D : ZMod d → Set X} (hDm : ∀ i, MeasurableSet (D i))
    (i : ZMod d) : cycleInv π D i (D i)ᶜ = 0 := by
  rw [cycleInv, Measure.smul_apply, Measure.restrict_apply (hDm i).compl, compl_inter_self,
    measure_empty, smul_zero]

variable [MeasurableSpace.CountablyGenerated X] in
/-- From `x ∈ Dᵢ` the skeleton `Pᵈ` reaches every measurable `A ⊆ Dᵢ` with `ψ(A) > 0` almost
surely: visits of the chain to `Dᵢ` happen only at multiples of `d`. -/
theorem IsCycle.hitProb_pow_eq_one (hd : 0 < d) (hD : IsCycle P ψ d D) (hH : IsHarris P ψ)
    {i : ZMod d} {A : Set X} (hA : MeasurableSet A) (hAD : A ⊆ D i) (hψA : 0 < ψ A) {x : X}
    (hx : x ∈ D i) :
    haveI := isMarkovKernel_pow P d; hitProb (P ^ d : Kernel X X) A x = 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  have := isMarkovKernel_pow P d
  have := isMarkovKernel_pathKernel P
  have h1 := hH.hitProb_eq_one hA hψA x
  have hae : ∀ᵐ ω ∂pathKernel P x, ∀ k : ℕ, ω k ∈ D (i + k) := by
    rw [ae_all_iff]
    intro k
    rw [ae_iff]
    have := pathKernel_coord_mem P x k (hD.measurableSet (i + k)).compl
    rw [hD.pow_compl_eq_zero k hx] at this
    simpa using this
  have hmeas : Measurable fun (ω : ℕ → X) (n : ℕ) => ω (d * n) :=
    measurable_pi_iff.2 fun n => measurable_pi_apply _
  refine le_antisymm (hitProb_le_one _ _ _) ?_
  rw [hitProb, ← pathKernel_map_skeleton P d x, Measure.map_apply hmeas
    (measurableSet_firstReturn_ne_top hA), ← h1, hitProb]
  refine measure_mono_ae ?_
  filter_upwards [hae] with ω hω hret
  obtain ⟨k, hk, hkA⟩ := (firstReturn_ne_top_iff A ω).1 hret
  have hk0 : ((k : ℕ) : ZMod d) = 0 := by
    by_contra hne
    have hdis := hD.disjoint (i + k) i (by intro h; apply hne; simpa using h)
    exact Set.disjoint_left.1 hdis (hω k) (hAD hkA)
  obtain ⟨n, rfl⟩ := (ZMod.natCast_eq_zero_iff k d).1 hk0
  simp only [Set.mem_preimage, mem_ofPred_eq, firstReturn_ne_top_iff]
  refine ⟨n, ?_, hkA⟩
  rcases n with _ | n
  · simp at hk
  · omega



variable [MeasurableSpace.CountablyGenerated X] in
/-- **The chain `Φ_d` on a cycle class.** For a positive Harris chain of period `d` with
`d`-cycle `{Dᵢ}` and a probability `λ` concentrated on `Dᵢ`, `‖λP^{dn} − πᵢ‖ → 0`, where
`πᵢ = d π(· ∩ Dᵢ)`. The proof applies Theorem 13.3.3 to the chain that moves by `Pᵈ` on `Dᵢ` and
jumps to `πᵢ` off `Dᵢ`, which is positive Harris and aperiodic (Proposition 5.4.6). -/
theorem IsCycle.tendsto_tvNorm_pow_mul (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ (D i)ᶜ = 0) :
    Tendsto (fun n => tvNorm ((P ^ (d * n) : Kernel X X) ∘ₘ μ) (cycleInv π D i)) atTop (𝓝 0) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hψ := hph.1.1
  have hrec := proposition_10_1_1 hph.2
  set H := D i with hHdef
  have hH : MeasurableSet H := hD.measurableSet i
  have := isMarkovKernel_pow P d
  set Q : Kernel X X := P ^ d with hQdef
  have hσp : IsProbabilityMeasure (cycleInv π D i) :=
    hD.isProbabilityMeasure_cycleInv hd hrec hπ i
  set σ := cycleInv π D i with hσdef
  have hQ : ∀ x ∈ H, Q x Hᶜ = 0 := hD.pow_d_compl_eq_zero i
  have hσ : σ Hᶜ = 0 := cycleInv_compl π hD.measurableSet i
  have := isMarkovKernel_absorbKernel Q hH σ
  have hψH : 0 < ψ H := hD.measure_pos hψ hd i
  have hac := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  -- from `Dᵢ` the restricted chain reaches every set charging `Dᵢ` almost surely
  have hLH : ∀ x ∈ H, ∀ A, MeasurableSet A → 0 < ψ (A ∩ H) →
      hitProb (absorbKernel Q hH σ) A x = 1 :=
    fun x hx A hA hψA => by
      rw [hitProb_absorbKernel_of_mem hH hQ hA hx]
      exact le_antisymm (hitProb_le_one _ _ _)
        ((hD.hitProb_pow_eq_one hd hph.1 (hA.inter hH) inter_subset_right hψA hx).symm.le.trans
          (hitProb_mono _ inter_subset_left x))
  -- irreducibility
  have hirr : IsPhiIrreducible (absorbKernel Q hH σ) (ψ.restrict H) := fun A hA hpos x => by
    rw [Measure.restrict_apply hA] at hpos
    by_cases hx : x ∈ H
    · rw [hLH x hx A hA hpos]; exact one_pos
    · refine lt_of_lt_of_le ?_ (pow_le_hitProb (absorbKernel Q hH σ) hA 0 x)
      rw [zero_add, pow_one, absorbKernel_of_notMem Q hH σ hx, hσdef, cycleInv,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
      refine ENNReal.mul_pos (by exact_mod_cast hd.ne') fun h0 => ?_
      exact absurd (hac.2 h0) hpos.ne'
  have hmax : IsMaximalIrreducibility (absorbKernel Q hH σ) (ψ.restrict H) := by
    refine ⟨fun h0 => ?_, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
    · have := congrArg (fun m : Measure X => m univ) h0
      simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact hψH.ne' this
    · rw [Measure.restrict_apply hA] at h0
      by_contra hne
      have hpos := hφ A hA (pos_iff_ne_zero.2 hne)
      have hnull := hψ.hitSet_null (hA.inter hH) h0
      obtain ⟨x, hxH, hx⟩ : ∃ x ∈ H, ¬ 0 < hitProb P (A ∩ H) x := by
        by_contra hall
        push Not at hall
        exact hψH.ne' (nonpos_iff_eq_zero.1 (hnull ▸ measure_mono fun y hy => hall y hy))
      have hx0 : hitProb P (A ∩ H) x = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hx)
      have hK0 : hitProb (absorbKernel Q hH σ) A x = 0 := by
        rw [hitProb_absorbKernel_of_mem hH hQ hA hxH, hitProb_eq_tsum _ hA]
        refine ENNReal.tsum_eq_zero.2 fun n => nonpos_iff_eq_zero.1 ?_
        calc tabooKernel Q hA n x A
            ≤ tabooKernel Q hA n x (A ∩ H) + tabooKernel Q hA n x Hᶜ := by
              refine (measure_mono fun y hy => ?_).trans (measure_union_le _ _)
              by_cases h : y ∈ H
              · exact Or.inl ⟨hy, h⟩
              · exact Or.inr h
          _ = tabooKernel Q hA n x (A ∩ H) := by
              rw [tabooKernel_compl_eq_zero_of_absorbing hH hQ hA n hxH, add_zero]
          _ ≤ (Q ^ (n + 1) : Kernel X X) x (A ∩ H) := tabooKernel_le_pow Q hA n x (hA.inter hH)
          _ = (P ^ (d * (n + 1) - 1 + 1) : Kernel X X) x (A ∩ H) := by
              rw [hQdef, ← pow_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
                (Nat.mul_ne_zero hd.ne' (Nat.succ_ne_zero n)))]
          _ ≤ hitProb P (A ∩ H) x := pow_le_hitProb P (hA.inter hH) _ x
          _ = 0 := hx0
      exact absurd hK0 (hpos x).ne'
  -- Harris
  have hHK : IsHarris (absorbKernel Q hH σ) (ψ.restrict H) := by
    refine ⟨hmax, fun A hA hψA => (proposition_9_1_1 (absorbKernel Q hH σ) hA fun x hx => ?_).2⟩
    rw [Measure.restrict_apply hA] at hψA
    by_cases hxH : x ∈ H
    · exact hLH x hxH A hA hψA
    · rw [hitProb_first_step (absorbKernel Q hH σ) hA x, absorbKernel_of_notMem Q hH σ hxH]
      have hae : ∀ᵐ y ∂σ, y ∈ Aᶜ → hitProb (absorbKernel Q hH σ) A y = 1 := by
        have : ∀ᵐ y ∂σ, y ∈ H := by rw [ae_iff]; exact hσ
        filter_upwards [this] with y hy _
        exact hLH y hy A hA hψA
      rw [setLIntegral_congr_fun_ae hA.compl hae, setLIntegral_one,
        measure_add_measure_compl hA, measure_univ]
  -- positivity
  have hσinv : IsInvariant (absorbKernel Q hH σ) σ := by
    unfold IsInvariant
    rw [comp_congr_of_compl_eq_zero hσ fun y hy => absorbKernel_of_mem Q hH σ hy]
    exact hD.isInvariant_pow_cycleInv hd hπ i
  have hposK : IsPositive (absorbKernel Q hH σ) (ψ.restrict H) := ⟨hmax, σ, hσp, hσinv⟩
  -- aperiodicity
  have hapK : IsAperiodic (absorbKernel Q hH σ) (ψ.restrict H) := by
    obtain ⟨C, hCH, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ hH hψH
    have hgcd : d = setGcd (smallTimes P C ν) := hper.eq_gcd hψ hC hψC hνC
    obtain ⟨N, hN⟩ := exists_isSmallSet_mul_gcd hC hνC
    rw [← hgcd] at hN
    have hKsmall : ∀ n ≥ N, ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ x ∈ C, δ • ν ≤ (absorbKernel Q hH σ ^ n : Kernel X X) x :=
      fun n hn => by
        obtain ⟨δ, hδ, hsm⟩ := hN n hn
        refine ⟨δ, hδ, fun x hx => ?_⟩
        rw [absorbKernel_pow_of_mem hH hQ n x (hCH hx), hQdef, ← pow_mul, mul_comm]
        exact hsm.2.2.2 x hx
    have hmem : ∀ n ≥ N + 1, n ∈ smallTimes (absorbKernel Q hH σ) C ν := fun n hn => by
      obtain ⟨δ, hδ, h⟩ := hKsmall n (by omega)
      exact ⟨by omega, δ, hδ, h⟩
    obtain ⟨δ₀, hδ₀, h₀⟩ := hKsmall (N + 1) (by omega)
    have hν0 : (δ₀ • ν) ≠ 0 := smul_measure_ne_zero hC.2.2.1 hδ₀.ne'
    have hsC : IsSmallSet (absorbKernel Q hH σ) (N + 1) (δ₀ • ν) C := ⟨hC.1, by omega, hν0, h₀⟩
    have hψC' : 0 < (ψ.restrict H) C := by
      rw [Measure.restrict_apply hC.1, inter_eq_left.2 hCH]; exact hψC
    have hδν : 0 < (δ₀ • ν) C := by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ₀.ne' hνC.ne'
    have hδt : δ₀ ≠ ∞ := by
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
      have := isMarkovKernel_pow (absorbKernel Q hH σ) (N + 1)
      intro htop
      have h1 := (h₀ x hx C).trans prob_le_one
      rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.top_mul hνC.ne'] at h1
      exact absurd h1 (by simp)
    have hperK := isPeriod_gcd (absorbKernel Q hH σ) hmax hsC hψC' hδν
    rw [smallTimes_smul (absorbKernel Q hH σ) C ν hδ₀.ne' hδt] at hperK
    have hS := smallTimes_isAddClosed (absorbKernel Q hH σ) hνC
    have h1 := setGcd_dvd hS (hmem (N + 1) le_rfl) (by omega) (hmem (N + 1) le_rfl)
    have h2 := setGcd_dvd hS (hmem (N + 1) le_rfl) (by omega) (hmem (N + 2) (by omega))
    have hg : setGcd (smallTimes (absorbKernel Q hH σ) C ν) = 1 :=
      Nat.dvd_one.1 (by simpa using Nat.dvd_sub h2 h1)
    rwa [hg] at hperK
  -- Theorem 13.3.3 for the restricted chain
  have hconv := theorem_13_3_3 ⟨hHK, hposK⟩ hapK hσinv μ
  refine hconv.congr fun n => ?_
  rw [comp_absorbKernel_pow hH hQ n hμ, hQdef, ← pow_mul]

/-! ### Phase averages -/


/-- The phase average `d⁻¹ Σ_{r<d} λP^{dn+r}` of (13.61). -/
noncomputable def phaseAvg (P : Kernel X X) (d n : ℕ) (μ : Measure X) : Measure X :=
  (d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ

/-- `κ ∘ₘ 0 = 0`. -/
theorem comp_zero_measure (κ : Kernel X X) : κ ∘ₘ (0 : Measure X) = 0 := by
  ext B hB
  rw [measure_kernel_apply _ _ hB, lintegral_zero_measure, Measure.coe_zero, Pi.zero_apply]

/-- The phase average is additive. -/
theorem phaseAvg_add (P : Kernel X X) (d n : ℕ) (μ ν : Measure X) :
    phaseAvg P d n (μ + ν) = phaseAvg P d n μ + phaseAvg P d n ν := by
  simp only [phaseAvg, Measure.comp_add, Finset.sum_add_distrib, smul_add]

/-- The phase average is homogeneous. -/
theorem phaseAvg_smul (P : Kernel X X) (d n : ℕ) (c : ℝ≥0∞) (μ : Measure X) :
    phaseAvg P d n (c • μ) = c • phaseAvg P d n μ := by
  simp only [phaseAvg, Measure.comp_smul, ← Finset.smul_sum]
  rw [smul_comm]

/-- The phase average of `0` is `0`. -/
theorem phaseAvg_zero (P : Kernel X X) (d n : ℕ) : phaseAvg P d n 0 = 0 := by
  simp [phaseAvg]

/-- The phase average of a finite sum. -/
theorem phaseAvg_finsetSum (P : Kernel X X) (d n : ℕ) {ι : Type*} (s : Finset ι)
    (μ : ι → Measure X) : phaseAvg P d n (∑ j ∈ s, μ j) = ∑ j ∈ s, phaseAvg P d n (μ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phaseAvg_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phaseAvg_add, ih]

/-- Time shift: `phaseAvg (n + k) λ = phaseAvg n (λP^{dk})`. -/
theorem phaseAvg_shift (P : Kernel X X) (d n k : ℕ) (μ : Measure X) :
    phaseAvg P d (n + k) μ = phaseAvg P d n ((P ^ (d * k) : Kernel X X) ∘ₘ μ) := by
  simp only [phaseAvg]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [measure_kernel_assoc, ← pow_add_eq, show d * k + (d * n + r) = d * (n + k) + r by ring]

/-- The phase average preserves mass. -/
theorem phaseAvg_univ (hd : 0 < d) (n : ℕ) (μ : Measure X) : phaseAvg P d n μ univ = μ univ := by
  simp only [phaseAvg, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have h : ∀ r, ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ) univ = μ univ := fun r => by
    have := isMarkovKernel_pow P (d * n + r)
    exact Measure.comp_apply_univ
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hd.ne') (ENNReal.natCast_ne_top d), one_mul]

/-- The phase average of a finite measure is finite. -/
theorem isFiniteMeasure_phaseAvg (hd : 0 < d) (n : ℕ) (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasure (phaseAvg P d n μ) :=
  ⟨by rw [phaseAvg_univ hd]; exact measure_lt_top μ univ⟩

/-- `Σ_{r<d} f(i + r) = Σ_{j ∈ ZMod d} f(j)`. -/
theorem sum_range_add_zmod [NeZero d] {M : Type*} [AddCommMonoid M] (f : ZMod d → M)
    (i : ZMod d) : ∑ r ∈ range d, f (i + r) = ∑ j, f j := by
  refine Finset.sum_nbij' (fun r : ℕ => i + (r : ZMod d)) (fun j : ZMod d => (j - i).val)
    (fun _ _ => mem_univ _) (fun j _ => Finset.mem_range.2 (ZMod.val_lt _)) (fun r hr => ?_)
    (fun j _ => ?_) (fun _ _ => rfl)
  · rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
  · rw [ZMod.natCast_zmod_val, add_sub_cancel]

variable [MeasurableSpace.CountablyGenerated X] in
/-- The restrictions of `π` to the cycle classes add up to `π`. -/
theorem IsCycle.sum_restrict [NeZero d] (hD : IsCycle P ψ d D) (hrec : IsRecurrentChain P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∑ j, π.restrict (D j) = π := by
  have hac := (theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)).1
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion (fun j k hjk => hD.disjoint j k hjk)
    hD.measurableSet]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  exact hac hD.null_compl

omit [IsMarkovKernel P] in
/-- A measure concentrated on `⋃ Dᵢ` is the sum of its restrictions to the classes. -/
theorem IsCycle.sum_restrict_of_compl [NeZero d] (hD : IsCycle P ψ d D)
    {ρ : Measure X} (hρ : ρ (⋃ j, D j)ᶜ = 0) : ∑ j, ρ.restrict (D j) = ρ := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion (fun j k hjk => hD.disjoint j k hjk)
    hD.measurableSet]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  exact hρ

/-- `‖λP^{dn+r} − π_{i+r}‖ ≤ ‖λP^{dn} − πᵢ‖`. -/
theorem IsCycle.tvNorm_pow_add_le (hd : 0 < d) (hD : IsCycle P ψ d D) {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) (i : ZMod d) (μ : Measure X) [IsFiniteMeasure μ]
    (n r : ℕ) [IsFiniteMeasure (cycleInv π D i)] :
    tvNorm ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ) (cycleInv π D (i + r)) ≤
      tvNorm ((P ^ (d * n) : Kernel X X) ∘ₘ μ) (cycleInv π D i) := by
  have := isMarkovKernel_pow P r
  have := isMarkovKernel_pow P (d * n)
  have h1 : (P ^ (d * n + r) : Kernel X X) ∘ₘ μ =
      (P ^ r : Kernel X X) ∘ₘ ((P ^ (d * n) : Kernel X X) ∘ₘ μ) := by
    rw [measure_kernel_assoc, ← pow_add_eq]
  rw [h1, ← hD.comp_pow_cycleInv hd hπ r i]
  exact tvNorm_comp_le _ _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- `π = d⁻¹ Σ_{r<d} π_{i+r}`. -/
theorem IsCycle.eq_smul_sum_cycleInv (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hrec : IsRecurrentChain P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) :
    π = (d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, cycleInv π D (i + r) := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [sum_range_add_zmod (cycleInv π D) i]
  simp only [cycleInv]
  rw [← Finset.smul_sum, hD.sum_restrict hrec hπ, smul_smul,
    ENNReal.inv_mul_cancel (by exact_mod_cast hd.ne') (ENNReal.natCast_ne_top d), one_smul]

variable [MeasurableSpace.CountablyGenerated X] in
/-- `‖d⁻¹ Σ_{r<d} λP^{dn+r} − π‖ ≤ ‖λP^{dn} − πᵢ‖`. -/
theorem IsCycle.tvNorm_phaseAvg_le (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hrec : IsRecurrentChain P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    tvNorm (phaseAvg P d n μ) π ≤ tvNorm ((P ^ (d * n) : Kernel X X) ∘ₘ μ) (cycleInv π D i) := by
  have hσp := hD.isProbabilityMeasure_cycleInv hd hrec hπ
  have hfin : ∀ r, IsFiniteMeasure ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ) := fun r => by
    have := isMarkovKernel_pow P (d * n + r); infer_instance
  have hσfin : ∀ r : ℕ, IsFiniteMeasure (cycleInv π D (i + r)) := fun r => by
    have := hσp (i + r); infer_instance
  have := hσp i
  have h1 : tvNorm (phaseAvg P d n μ) ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, cycleInv π D (i + r)) ≤
      ((d : ℝ≥0∞)⁻¹).toReal * ∑ r ∈ range d,
        tvNorm ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ) (cycleInv π D (i + r)) :=
    (tvNorm_smul_le _ _ _).trans
      (mul_le_mul_of_nonneg_left (tvNorm_finsetSum_le _ _ _) ENNReal.toReal_nonneg)
  have h2 : ∑ r ∈ range d, tvNorm ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ) (cycleInv π D (i + r)) ≤
      d * tvNorm ((P ^ (d * n) : Kernel X X) ∘ₘ μ) (cycleInv π D i) := by
    refine (Finset.sum_le_sum fun r _ => hD.tvNorm_pow_add_le hd hπ i μ n r).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hD.eq_smul_sum_cycleInv hd hrec hπ i] at h1
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 ENNReal.toReal_nonneg).trans (le_of_eq ?_))
  rw [← mul_assoc, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_mul]

variable [MeasurableSpace.CountablyGenerated X] in
/-- (13.61) for an initial probability on one cycle class. -/
theorem IsCycle.tendsto_phaseAvg_of_class (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ (D i)ᶜ = 0) :
    Tendsto (fun n => tvNorm (phaseAvg P d n μ) π) atTop (𝓝 0) :=
  squeeze_zero (fun _ => tvNorm_nonneg _ _)
    (fun n => hD.tvNorm_phaseAvg_le hd (proposition_10_1_1 hph.2) hπ i μ n)
    (hD.tendsto_tvNorm_pow_mul hd hper hph hπ i μ hμ)

variable [MeasurableSpace.CountablyGenerated X] in
/-- (13.61) for a finite initial measure on one cycle class. -/
theorem IsCycle.tendsto_phaseAvg_of_class_finite (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (i : ZMod d) (ρ : Measure X) [IsFiniteMeasure ρ]
    (hρ : ρ (D i)ᶜ = 0) :
    Tendsto (fun n => tvNorm (phaseAvg P d n ρ) (ρ univ • π)) atTop (𝓝 0) := by
  by_cases h0 : ρ univ = 0
  · have hρ0 : ρ = 0 := Measure.measure_univ_eq_zero.1 h0
    subst hρ0
    simp [phaseAvg_zero, tvNorm_self]
  · set c := ρ univ
    have hct : c ≠ ∞ := measure_ne_top ρ univ
    set μ := c⁻¹ • ρ
    have hμp : IsProbabilityMeasure μ := ⟨by
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hct]⟩
    have hμ : μ (D i)ᶜ = 0 := by rw [Measure.smul_apply, hρ, smul_zero]
    have hρμ : ρ = c • μ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hct, one_smul]
    have hlim := hD.tendsto_phaseAvg_of_class hd hper hph hπ i μ hμ
    have hfin := fun n => isFiniteMeasure_phaseAvg (P := P) hd n μ
    refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_)
      (by simpa using hlim.const_mul c.toReal)
    have := hfin n
    conv_lhs => rw [hρμ, phaseAvg_smul]
    exact tvNorm_smul_le _ _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- (13.61) for a finite initial measure concentrated on `⋃ Dᵢ`. -/
theorem IsCycle.tendsto_phaseAvg_of_union (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (ρ : Measure X) [IsFiniteMeasure ρ] (hρ : ρ (⋃ j, D j)ᶜ = 0) :
    Tendsto (fun n => tvNorm (phaseAvg P d n ρ) (ρ univ • π)) atTop (𝓝 0) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hdec := hD.sum_restrict_of_compl hρ
  have hρj : ∀ j, (ρ.restrict (D j)) (D j)ᶜ = 0 := fun j => by
    rw [Measure.restrict_apply (hD.measurableSet j).compl, compl_inter_self, measure_empty]
  have hlim := tendsto_finsetSum (Finset.univ : Finset (ZMod d)) fun j _ =>
    hD.tendsto_phaseAvg_of_class_finite hd hper hph hπ j (ρ.restrict (D j)) (hρj j)
  simp only [Finset.sum_const_zero] at hlim
  refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_) hlim
  have hfin : ∀ j, IsFiniteMeasure (phaseAvg P d n (ρ.restrict (D j))) := fun j =>
    isFiniteMeasure_phaseAvg hd n _
  have hfin' : ∀ j, IsFiniteMeasure (ρ.restrict (D j) univ • π) := fun j =>
    Measure.smul_finite π (measure_ne_top _ _)
  have h1 : phaseAvg P d n ρ = ∑ j, phaseAvg P d n (ρ.restrict (D j)) := by
    conv_lhs => rw [← hdec]
    exact phaseAvg_finsetSum P d n _ _
  have h2 : ρ univ • π = ∑ j, ρ.restrict (D j) univ • π := by
    rw [← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← hdec]
    rw [Measure.finsetSum_apply]
  rw [h1, h2]
  exact tvNorm_finsetSum_le _ _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a Harris chain the mass outside `⋃ Dᵢ` vanishes: `λPᵏ((⋃ Dᵢ)ᶜ) → 0`. -/
theorem IsCycle.tendsto_compl_iUnion (hd : 0 < d) (hD : IsCycle P ψ d D) (hH : IsHarris P ψ)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ((P ^ (k + 1) : Kernel X X) ∘ₘ μ) (⋃ j, D j)ᶜ) atTop (𝓝 0) := by
  have : NeZero d := ⟨hd.ne'⟩
  set U := ⋃ j, D j
  have hU : MeasurableSet U := MeasurableSet.iUnion hD.measurableSet
  have hψU : 0 < ψ U := lt_of_lt_of_le (hD.measure_pos hH.1 hd 0)
    (measure_mono (subset_iUnion D 0))
  have habs : ∀ x ∈ U, P x Uᶜ = 0 := fun x hx => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    refine nonpos_iff_eq_zero.1 ((measure_mono (compl_subset_compl.2
      (subset_iUnion D (j + 1)))).trans ?_)
    exact ((prob_compl_eq_zero_iff (hD.measurableSet _)).2 (hD.step j x hj)).le
  have hpt : ∀ k x, (P ^ (k + 1) : Kernel X X) x Uᶜ = tabooKernel P hU k x Uᶜ := fun k x => by
    rw [pow_succ_eq_firstEntrance P hU k x, Measure.add_apply, Measure.finsetSum_apply,
      Finset.sum_eq_zero fun j _ => ?_, add_zero]
    refine comp_compl_eq_zero hU ?_ (pow_compl_eq_zero_of_absorbing P hU habs _)
    rw [Measure.restrict_apply hU.compl, compl_inter_self, measure_empty]
  have hL := hH.hitProb_eq_one hU hψU
  have hlim : Tendsto (fun k => ∫⁻ x, tabooKernel P hU k x univ ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun k => Kernel.measurable_coe _ MeasurableSet.univ)
      (fun k => Eventually.of_forall fun x => tabooKernel_apply_le_one P hU k x univ)
      (by rw [lintegral_one, measure_univ]; exact ENNReal.one_ne_top)
      (Eventually.of_forall fun x => Minorization.tendsto_tabooKernel_univ P hU (hL x))
  rw [lintegral_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le)
    fun k => ?_
  rw [measure_kernel_apply _ _ hU.compl]
  refine lintegral_mono fun x => ?_
  rw [hpt]
  exact measure_mono (subset_univ _)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.4 (i)** (MT p. 328): if the chain is positive Harris with period `d`, then for
every initial distribution `λ`, `‖d⁻¹ Σ_{r<d} λP^{nd+r} − π‖ → 0` (13.61). -/
theorem theorem_13_3_4_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {d : ℕ} (hper : IsPeriod P ψ d) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (μ : Measure X) [IsProbabilityMeasure μ] :
    Tendsto (fun n => tvNorm ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ)
      π) atTop (𝓝 0) := by
  have hd : 0 < d := hper.1
  obtain ⟨D, hD⟩ := hper.2.1
  have : NeZero d := ⟨hd.ne'⟩
  set U := ⋃ j, D j with hUdef
  have hU : MeasurableSet U := MeasurableSet.iUnion hD.measurableSet
  change Tendsto (fun n => tvNorm (phaseAvg P d n μ) π) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a time `d k` after which little mass lies outside `⋃ Dᵢ`
  have habs := hD.tendsto_compl_iUnion hd hph.1 μ
  obtain ⟨K₀, hK₀⟩ := (tendsto_order.1 habs).2 (ENNReal.ofReal (ε / 4))
    (ENNReal.ofReal_pos.2 (by linarith)) |>.exists_forall_of_atTop
  set k := K₀ + 1
  have hdk : d * k = (d * k - 1) + 1 := by
    have : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (Nat.succ_ne_zero _))
    omega
  have hsmall : ((P ^ (d * k) : Kernel X X) ∘ₘ μ) Uᶜ < ENNReal.ofReal (ε / 4) := by
    rw [hdk]
    exact hK₀ _ (by have : k ≤ d * k := Nat.le_mul_of_pos_left k hd; omega)
  have := isMarkovKernel_pow P (d * k)
  set ρ := (P ^ (d * k) : Kernel X X) ∘ₘ μ with hρdef
  set ρU := ρ.restrict U
  set ρN := ρ.restrict Uᶜ
  have hρUc : ρU Uᶜ = 0 := by
    rw [Measure.restrict_apply hU.compl, compl_inter_self, measure_empty]
  have hconvU := hD.tendsto_phaseAvg_of_union hd hper hph hπ ρU hρUc
  rw [Metric.tendsto_atTop] at hconvU
  obtain ⟨M, hM⟩ := hconvU (ε / 2) (by linarith)
  refine ⟨M + k, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have hm := hM m (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvNorm_nonneg _ _)] at hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvNorm_nonneg _ _), phaseAvg_shift, ← hρdef]
  have hρ : ρ = ρU + ρN := (Measure.restrict_add_restrict_compl hU).symm
  have hπ1 : π = ρU univ • π + ρN univ • π := by
    rw [← add_smul, ← Measure.add_apply, ← hρ, measure_univ, one_smul]
  have := isFiniteMeasure_phaseAvg (P := P) hd m ρU
  have := isFiniteMeasure_phaseAvg (P := P) hd m ρN
  have := Measure.smul_finite π (measure_ne_top ρU univ)
  have := Measure.smul_finite π (measure_ne_top ρN univ)
  have hN : tvNorm (phaseAvg P d m ρN) (ρN univ • π) ≤ 2 * (ρN univ).toReal := by
    refine (tvNorm_le_add_measureReal _ _).trans (le_of_eq ?_)
    rw [measureReal_def, measureReal_def, phaseAvg_univ hd, Measure.smul_apply, smul_eq_mul,
      measure_univ (μ := π), mul_one]
    ring
  have hNsmall : (ρN univ).toReal < ε / 4 := by
    rw [Measure.restrict_apply_univ]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hsmall |>.trans_le
      (by rw [ENNReal.toReal_ofReal (by linarith)])
  calc tvNorm (phaseAvg P d m ρ) π
      = tvNorm (phaseAvg P d m ρU + phaseAvg P d m ρN) (ρU univ • π + ρN univ • π) := by
        rw [← phaseAvg_add, ← hρ, ← hπ1]
    _ ≤ tvNorm (phaseAvg P d m ρU) (ρU univ • π) + tvNorm (phaseAvg P d m ρN) (ρN univ • π) :=
        tvNorm_add_le _ _ _ _
    _ < ε := by linarith

/-! ### Restriction to the maximal Harris set -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a positive chain with a maximal Harris set `H` (Theorem 9.1.5), the chain that moves by `P`
on `H` and jumps to `π` off `H` is positive Harris, and it has the same period as `P`. -/
theorem absorbKernel_maximalHarris (hpos : IsPositive P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {H : Set X} (hHmax : IsMaximalHarrisSet P ψ H)
    (hHnull : ψ Hᶜ = 0) :
    haveI := isMarkovKernel_absorbKernel P hHmax.1 π
    IsPositiveHarris (absorbKernel P hHmax.1 π) ψ ∧ IsInvariant (absorbKernel P hHmax.1 π) π ∧
      ∀ d, IsPeriod P ψ d → IsPeriod (absorbKernel P hHmax.1 π) ψ d := by
  have hψ := hpos.1
  have hH := hHmax.1
  have := isMarkovKernel_absorbKernel P hH π
  have hrec := proposition_10_1_1 hpos
  have hac := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hQ : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hH).2 (hHmax.2.2.1 x hx)
  have hπH : π Hᶜ = 0 := hac.1 hHnull
  have hψH : 0 < ψ H := by
    have hu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
    calc 0 < ψ univ := hu
      _ ≤ ψ H + ψ Hᶜ := by rw [← union_compl_self H]; exact measure_union_le _ _
      _ = ψ H := by rw [hHnull, add_zero]
  -- irreducibility and maximality
  have hirr : IsPhiIrreducible (absorbKernel P hH π) ψ := fun A hA hpos x => by
    by_cases hx : x ∈ H
    · rw [hitProb_absorbKernel_of_mem hH hQ hA hx]; exact hψ.2.1 A hA hpos x
    · refine lt_of_lt_of_le ?_ (pow_le_hitProb _ hA 0 x)
      rw [zero_add, pow_one, absorbKernel_of_notMem P hH π hx]
      exact pos_iff_ne_zero.2 fun h0 => hpos.ne' (hac.2 h0)
  have hmax : IsMaximalIrreducibility (absorbKernel P hH π) ψ := by
    refine ⟨hψ.1, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
    by_contra hne
    have hnull := hψ.hitSet_null hA h0
    obtain ⟨x, hxH, hx⟩ : ∃ x ∈ H, ¬ 0 < hitProb P A x := by
      by_contra hall
      push Not at hall
      exact hψH.ne' (nonpos_iff_eq_zero.1 (hnull ▸ measure_mono fun y hy => hall y hy))
    have h1 := hφ A hA (pos_iff_ne_zero.2 hne) x
    rw [hitProb_absorbKernel_of_mem hH hQ hA hxH] at h1
    exact hx h1
  -- Harris
  have hLH : ∀ x ∈ H, ∀ A, MeasurableSet A → 0 < ψ A →
      hitProb (absorbKernel P hH π) A x = 1 := fun x hx A hA hψA => by
    rw [hitProb_absorbKernel_of_mem hH hQ hA hx]
    exact le_antisymm (hitProb_le_one _ _ _)
      ((hHmax.2.2.2.2 A hA hψA x hx).symm.le.trans (harrisQ_le_hitProb P A x))
  have hHarris : IsHarris (absorbKernel P hH π) ψ := by
    refine ⟨hmax, fun A hA hψA => (proposition_9_1_1 _ hA fun x _ => ?_).2⟩
    by_cases hxH : x ∈ H
    · exact hLH x hxH A hA hψA
    · rw [hitProb_first_step _ hA x, absorbKernel_of_notMem P hH π hxH]
      have hae : ∀ᵐ y ∂π, y ∈ Aᶜ → hitProb (absorbKernel P hH π) A y = 1 := by
        have : ∀ᵐ y ∂π, y ∈ H := by rw [ae_iff]; exact hπH
        filter_upwards [this] with y hy _
        exact hLH y hy A hA hψA
      rw [setLIntegral_congr_fun_ae hA.compl hae, setLIntegral_one,
        measure_add_measure_compl hA, measure_univ]
  have hinv : IsInvariant (absorbKernel P hH π) π := by
    unfold IsInvariant
    rw [comp_congr_of_compl_eq_zero hπH fun y hy => absorbKernel_of_mem P hH π hy]
    exact hπ
  refine ⟨⟨hHarris, hmax, π, inferInstance, hinv⟩, hinv, fun d hper => ?_⟩
  obtain ⟨C, hCH, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ hH hψH
  have hgcd := hper.eq_gcd hψ hC hψC hνC
  have hCK : IsSmallSet (absorbKernel P hH π) m ν C :=
    ⟨hC.1, hC.2.1, hC.2.2.1, fun x hx => by
      rw [absorbKernel_pow_of_mem hH hQ m x (hCH hx)]; exact hC.2.2.2 x hx⟩
  have hst : smallTimes (absorbKernel P hH π) C ν = smallTimes P C ν := by
    ext n
    constructor
    · rintro ⟨hn, δ, hδ, h⟩
      exact ⟨hn, δ, hδ, fun x hx => by
        rw [← absorbKernel_pow_of_mem (σ := π) hH hQ n x (hCH hx)]; exact h x hx⟩
    · rintro ⟨hn, δ, hδ, h⟩
      exact ⟨hn, δ, hδ, fun x hx => by
        rw [absorbKernel_pow_of_mem hH hQ n x (hCH hx)]; exact h x hx⟩
  have := isPeriod_gcd _ hmax hCK hψC hνC
  rwa [hst, ← hgcd] at this

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.4 (ii)** (MT p. 328): if the chain is positive recurrent with period `d`, there
is a `ψ`-null set `N` such that `‖d⁻¹ Σ_{r<d} λP^{nd+r} − π‖ → 0` for every initial distribution
`λ` with `λ(N) = 0` (13.62). -/
theorem theorem_13_3_4_ii (hpos : IsPositive P ψ) {d : ℕ} (hper : IsPeriod P ψ d)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ N : Set X, MeasurableSet N ∧ ψ N = 0 ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ], μ N = 0 →
      Tendsto (fun n => tvNorm ((d : ℝ≥0∞)⁻¹ •
        ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨H, hHmax, -, hHnull⟩ := theorem_9_1_5 (proposition_10_1_1 hpos)
  have := isMarkovKernel_absorbKernel P hHmax.1 π
  obtain ⟨hph, hinv, hperK⟩ := absorbKernel_maximalHarris hpos hπ hHmax hHnull
  have hQ : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hHmax.1).2 (hHmax.2.2.1 x hx)
  refine ⟨Hᶜ, hHmax.1.compl, hHnull, fun μ _ hμ => ?_⟩
  have h := theorem_13_3_4_i hph (hperK d hper) hinv μ
  refine h.congr fun n => ?_
  congr 2
  exact Finset.sum_congr rfl fun r _ => comp_absorbKernel_pow hHmax.1 hQ _ hμ

variable [MeasurableSpace.CountablyGenerated X] in
/-- The aperiodic case of Theorem 13.3.4 (ii), and the version of Theorem 13.3.3 for positive
chains that need not be Harris: there is a `ψ`-null set `N` with `‖λPⁿ − π‖ → 0` whenever
`λ(N) = 0`. -/
theorem tendsto_tvNorm_of_isPositive (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ N : Set X, MeasurableSet N ∧ ψ N = 0 ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ], μ N = 0 →
      Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨H, hHmax, -, hHnull⟩ := theorem_9_1_5 (proposition_10_1_1 hpos)
  have := isMarkovKernel_absorbKernel P hHmax.1 π
  obtain ⟨hph, hinv, hperK⟩ := absorbKernel_maximalHarris hpos hπ hHmax hHnull
  have hQ : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hHmax.1).2 (hHmax.2.2.1 x hx)
  refine ⟨Hᶜ, hHmax.1.compl, hHnull, fun μ _ hμ => ?_⟩
  have h := theorem_13_3_3 hph (hperK 1 hap) hinv μ
  exact h.congr fun n => by rw [comp_absorbKernel_pow hHmax.1 hQ n hμ]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.5** (MT p. 329) in the book's form: under the hypotheses of
`theorem_13_3_5_positive` the chain is positive, and there is a `ψ`-null set `N` such that
`‖λPⁿ − π‖ → 0` for every initial distribution `λ` with `λ(N) = 0` (13.64). -/
theorem theorem_13_3_5_null (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {m : ℕ}
    {ν : Measure X} {C : Set X} (hC : IsSmallSet P m ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C)
    {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n => (((P ^ n : Kernel X X) ∘ₘ ((ν C)⁻¹ • ν.restrict C)) C).toReal)
      atTop (𝓝 c)) :
    ∃ hpos : IsPositive P ψ, ∃ N : Set X, MeasurableSet N ∧ ψ N = 0 ∧
      ∀ (μ : Measure X) [IsProbabilityMeasure μ], μ N = 0 →
        haveI := isProbabilityMeasure_stationaryDist hpos
        Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) (stationaryDist P hpos)) atTop
          (𝓝 0) := by
  have hpos := theorem_13_3_5_positive hψ hap hC hψC hνC hc hlim
  have := isProbabilityMeasure_stationaryDist hpos
  obtain ⟨N, hN, hψN, h⟩ := tendsto_tvNorm_of_isPositive hpos hap (isInvariant_stationaryDist hpos)
  exact ⟨hpos, N, hN, hψN, h⟩

end MeynTweedie.GeneralizedDrift
