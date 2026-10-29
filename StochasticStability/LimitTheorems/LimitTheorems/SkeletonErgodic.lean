/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SkeletonLimitTheorems
import LimitTheorems.AperiodicErgodic
import LimitTheorems.HarrisDecomposition
import LimitTheorems.AtomInvariant
import LimitTheorems.GeometricAtoms

/-!
# The split `m`-skeleton of an ergodic chain (MT §17.3)

Meyn and Tweedie, §17.3.1 (p. 433) and Theorems 17.3.2 (p. 436) and 17.3.6 (p. 441), with the
hypotheses of `SkeletonLimitTheorems` (a minorization of `Pᵐ` on `C ∈ B⁺(X)`, a Harris
`m`-skeleton, `0 < π(C) < ∞`) discharged as in the book.

**The split skeleton.**
* `exists_skeleton_split` (§17.3.1, through Theorem 5.2.2, Proposition 5.4.5 and Theorem
  9.1.6): an aperiodic Harris chain has, for some `m ≥ 1`, a minorization
  `Pᵐ(x, ·) ≥ δ 1_C(x) ν` with `ψ(C) > 0` and `ν(C) > 0`, and its `m`-skeleton is Harris.
* `Minorization.isPetite_of_pow`: the set of a minorization of `Pᵐ` is petite for `P`;
  `Minorization.measure_pos_lt_top`: a nonzero σ-finite invariant measure has `0 < π(C) < ∞`.
* `skeleton_isHarris_counterexample`: the flip chain on `Bool` (period `2`) is positive Harris,
  but its `2`-skeleton `P² = I` is Harris for no measure, so the aperiodicity of §17.3.1 is
  needed for the split skeleton to be Harris.

**Results under the book's hypotheses.**
* **Theorem 17.3.2** (iii) ⇒ (i) (`theorem_17_3_2_skeleton`): for an aperiodic Harris chain with
  a nonzero σ-finite invariant measure `π`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every
  initial law, by the book's route (the split `m`-skeleton).
* **Theorem 17.3.6** (`theorem_17_3_6_skeleton`, the CLT; `theorem_17_3_6_lil_skeleton`, the
  LIL): for an ergodic chain (positive Harris and aperiodic) and a split `m`-skeleton (any
  minorization of a skeleton `Pᵐ`, `m ≥ 1`, on a set `C ∈ B⁺(X)`) satisfying (17.31), the CLT
  and the LIL hold under every initial law with the variance (17.32).

**Corrections.** Theorem 17.3.2 assumes only Harris recurrence, while its proof ("by considering
the split skeleton") needs the split skeleton of §17.3.1, which is built for aperiodic chains:
without aperiodicity the `m`-skeleton need not be Harris (`skeleton_isHarris_counterexample`).
`theorem_17_3_2_skeleton` therefore assumes aperiodicity; Theorem 17.3.2 for every Harris chain
is `theorem_17_3_2_harris` (`GapsChaconOrnstein`, by another route).

**Hypotheses.** "Ergodic" (MT p. 316) is positive Harris and aperiodic. The book asks
`γ_g² > 0` in Theorem 17.3.6; with `N(0, 0) = δ₀` and the LIL with constant `0` no positivity is
needed.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} {m : ℕ}

/-! ### Existence of the split skeleton -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The split `m`-skeleton exists** (MT §17.3.1, p. 433, through Theorem 5.2.2, Proposition
5.4.5 and Theorem 9.1.6): an aperiodic Harris chain has a skeleton `Pᵐ`, `m ≥ 1`, with a
minorization `Pᵐ(x, ·) ≥ δ 1_C(x) ν` on a set `C` with `ψ(C) > 0` and `ν(C) > 0`, and that
skeleton is Harris. -/
theorem exists_skeleton_split [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (hap : IsAperiodic P ψ) :
    ∃ m, 1 ≤ m ∧ ∃ M : Minorization (P ^ m : Kernel X X), 0 < ψ M.C ∧ 0 < M.ν M.C ∧
      (haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hH.1 hap
  exact ⟨m, hm, M, hψC, hνC, (theorem_9_1_6 hH.1 hap).1 hH m hm⟩

/-- The set of a minorization of `Pᵐ`, `m ≥ 1`, is petite for `P`. -/
theorem Minorization.isPetite_of_pow [NeZero m] (M : Minorization (P ^ m)) : IsPetite P M.C := by
  have := M.isProbabilityMeasure_ν
  refine ⟨_, _, proposition_5_5_3 (m := m) (ν := M.δ • M.ν) ⟨M.measurableSet_C,
    Nat.pos_of_ne_zero (NeZero.ne m), ?_, fun x hx => M.le x hx⟩⟩
  intro h
  have h1 := congrArg (fun μ : Measure X => μ univ) h
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.coe_zero,
    Pi.zero_apply] at h1
  exact M.δ_pos.ne' h1

/-- A nonzero σ-finite invariant measure of a `ψ`-irreducible chain has `0 < π(C) < ∞` on the set
of a minorization of a skeleton with `ψ(C) > 0`. -/
theorem Minorization.measure_pos_lt_top [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hψC : 0 < ψ M.C) {π : Measure X}
    [SigmaFinite π] (hπ : IsInvariant P π) (hπ0 : π ≠ 0) : 0 < π M.C ∧ π M.C < ∞ :=
  ⟨IsSubinvariant.pos_of_pos hψ.2.1 hπ.isSubinvariant hπ0 M.measurableSet_C hψC,
    IsSubinvariantMeasure.measure_lt_top_of_petite hψ ⟨inferInstance, hπ.isSubinvariant⟩
      M.isPetite_of_pow⟩

/-! ### Skeletons of periodic chains -/

/-- `Pⁿ⁺¹(x, ·) = Pⁿ(¬x, ·)` for the flip chain. -/
theorem flipKernel_pow_succ (n : ℕ) (x : Bool) :
    (flipKernel ^ (n + 1)) x = (flipKernel ^ n) (!x) := by
  rw [pow_succ]
  change ((flipKernel ^ n) ∘ₖ flipKernel) x = _
  rw [Kernel.comp_apply, flipKernel_apply, Measure.dirac_bind (Kernel.measurable _)]

/-- The even powers of the flip chain are the identity: `P²ⁿ(x, ·) = δₓ`. -/
theorem flipKernel_pow_two_mul (n : ℕ) (x : Bool) :
    (flipKernel ^ (2 * n)) x = Measure.dirac x := by
  induction n generalizing x with
  | zero => exact pow_zero_apply flipKernel x
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, flipKernel_pow_succ, flipKernel_pow_succ, ih,
      Bool.not_not]

/-- **Harris recurrence does not pass to skeletons of periodic chains** (the hypothesis
"`Φ` aperiodic" of §17.3.1, p. 433, cannot be dropped from Theorem 9.1.6 or from the split
`m`-skeleton route). The flip chain on `Bool` (period `2`) is positive Harris with maximal
irreducibility measure `count`, but its `2`-skeleton `P² = I` is not `φ`-irreducible for any
`φ ≠ 0`, so it is Harris for no measure. -/
theorem skeleton_isHarris_counterexample :
    haveI := isMarkovKernel_flipKernel
    IsPositiveHarris flipKernel Measure.count ∧
      haveI := isMarkovKernel_pow flipKernel 2
      ∀ ψ : Measure Bool, ¬ IsHarris (flipKernel ^ 2) ψ := by
  have := isMarkovKernel_flipKernel
  have := isMarkovKernel_pow flipKernel 2
  have hirr : IsIrreducibleChain flipKernel := by
    have hleads : ∀ x y : Bool, Leads flipKernel x y := fun x y => by
      by_cases hxy : x = y
      · exact Or.inl hxy
      · refine (leads_iff_exists_pow flipKernel x y).2 ⟨1, ?_⟩
        have hy : y = !x := by cases x <;> cases y <;> simp_all
        rw [pow_one, flipKernel_apply, hy, Measure.dirac_apply_of_mem (mem_singleton _)]
        exact one_pos
    exact ⟨true, eq_univ_of_forall fun y => ⟨hleads true y, hleads y true⟩⟩
  have hmax := isMaximalIrreducibility_count flipKernel hirr
  have hpos : IsPositive flipKernel Measure.count :=
    ⟨hmax, flipPi, isProbabilityMeasure_flipPi, isInvariant_flipPi⟩
  refine ⟨⟨isHarris_of_countable hirr (proposition_10_1_1 hpos), hpos⟩, fun ψ hψ => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : Bool, 0 < ψ {b} := by
    by_contra h
    push Not at h
    refine hψ.1.1 (Measure.measure_univ_eq_zero.1 ?_)
    rw [show (univ : Set Bool) = {true} ∪ {false} by ext x; cases x <;> simp]
    exact le_antisymm ((measure_union_le _ _).trans (by simp [nonpos_iff_eq_zero.1 (h true),
      nonpos_iff_eq_zero.1 (h false)])) zero_le
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurableSet_singleton b) (!b)).1
    (hψ.1.2.1 {b} (measurableSet_singleton b) hb (!b))
  rw [← pow_mul, flipKernel_pow_two_mul, Measure.dirac_apply' _ (measurableSet_singleton b),
    indicator_of_notMem (by cases b <;> simp)] at hn
  exact lt_irrefl 0 hn

/-! ### Theorems 17.3.2 and 17.3.6 under the book's hypotheses -/

variable [MeasurableSpace.CountablyGenerated X]

/-- **Theorem 17.3.2** (iii) ⇒ (i) (MT p. 436) by the book's route, the split `m`-skeleton of
§17.3.1, under its hypotheses: for an aperiodic Harris chain with a nonzero σ-finite invariant
measure `π`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every initial law, for `f, g ∈ L¹(π)`
with `π(g) ≠ 0`. (Aperiodicity is needed by the route, `skeleton_isHarris_counterexample`; the
statement without it is `theorem_17_3_2_harris`.) -/
theorem theorem_17_3_2_skeleton [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (hap : IsAperiodic P ψ) {π : Measure X} [SigmaFinite π] (hπ : IsInvariant P π)
    (hπ0 : π ≠ 0) {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f π) (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  obtain ⟨m, hm, M, hψC, -, hHm⟩ := exists_skeleton_split hH hap
  have : NeZero m := ⟨by omega⟩
  obtain ⟨h0, h1⟩ := M.measure_pos_lt_top hH.1 hψC hπ hπ0
  exact theorem_17_3_2_general M hHm hψC hπ h0.ne' h1.ne hfm hgm hfi hgi hg μ

/-- **Theorem 17.3.6**, the CLT (MT p. 441), under the book's hypotheses: `Φ` ergodic (positive
Harris and aperiodic), with invariant probability `π`, and the moment condition (17.31) for a
split `m`-skeleton (any minorization of a skeleton `Pᵐ`, `m ≥ 1`, on `C ∈ B⁺(X)`; one exists by
`exists_skeleton_split`). Then `n^{−1/2} Sₙ(g − π(g)) ⇒ N(0, γ_g²)` under every initial law,
with `γ_g²` given by (17.32) (`skelCLTVariance`, which is `≥ 0`, `skelCLTVariance_nonneg`). -/
theorem theorem_17_3_6_skeleton [IsMarkovKernel P] [NeZero m] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) (M : Minorization (P ^ m))
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M))
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z' : Ω' → ℝ}
    (hZ' : HasLaw Z' (gaussianReal 0 (skelCLTVariance M π g).toNNReal) P')
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω) atTop Z'
      (fun _ => pathMeasure P μ) P' :=
  theorem_17_3_6_general M ((theorem_9_1_6 hph.1.1 hap).1 hph.1 m
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))) hψC hπ hgm hg2 hT2 hZ' μ

/-- **Theorem 17.3.6**, the LIL (MT p. 441), under the book's hypotheses: `Φ` ergodic, with
invariant probability `π`, and (17.31) for a split `m`-skeleton. Then almost surely from every
initial law `Sₙ(g − π(g))` has the LIL with constant `γ_g` of (17.32). -/
theorem theorem_17_3_6_lil_skeleton [IsMarkovKernel P] [NeZero m] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) (M : Minorization (P ^ m))
    (hψC : 0 < ψ M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M))
    (hT2 : MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, HasLIL (fun n => pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      (√(skelCLTVariance M π g)) :=
  theorem_17_3_6_lil_general M ((theorem_9_1_6 hph.1.1 hap).1 hph.1 m
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))) hψC hπ hgm hg2 hT2 μ

end MeynTweedie.LimitTheorems
