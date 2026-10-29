/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.LLNApplications
import LimitTheorems.SplitErgodic

/-!
# Limit theorems for general Harris chains through splitting (MT §17.3)

Meyn and Tweedie, §17.3, pp. 433–442: Theorems 17.3.1, 17.3.2 and 17.3.6, for chains with a
one-step minorization `P(x, ·) ≥ δ 1_C(x) ν` on a set `C ∈ B⁺(X)` (the case `m = 1` of the book's
construction (17.21); `M : Minorization P`, `P̌ = M.splitKernel`, `α̌ = C₁ = M.checkAlpha`; the
case of a general `m` is in the `Skeleton…` modules). The
first coordinates of the split chain started from `μ*` form the original chain started from `μ`
(Theorem 5.1.3, `theorem_5_1_3_i_path`), the split chain reaches its atom `α̌` almost surely from
every state when `Φ` is Harris (`Minorization.hitProb_checkAlpha_eq_one`), and the results of
§17.2 for chains with an atom apply to `Φ̌`.

**Transfer.**
* `measurable_fstPath`, `ae_of_split`: a path property of `(Φ̌ₙ.1)` holding `P̌_{μ*}`-a.s. holds
  `P_μ`-a.s.;
* `ae_firstHit_split`: for a Harris chain the split chain reaches `α̌` a.s. from `μ*` and `ν*`;
* `tendstoInDistribution_of_map`: convergence in distribution of functionals of a pushed-forward
  process.

**Results.**
* `ratio_lln_of_accessibleAtom`: the ratio limit theorem for a recurrent chain with an accessible
  atom reached almost surely from every state, an invariant measure `π` with `0 < π(α) < ∞`, and
  every initial law.
* **Theorem 17.3.1** (`theorem_17_3_1`, p. 435) for `m = 1`: the cycle sums `sᵢ(f)` of the split
  chain are i.i.d. under `P̌_{μ*}` for every initial law, with mean
  `Ě[sᵢ(f)] = δ⁻¹ π(C)⁻¹ ∫ f dπ` (17.23). For a general `m`: `theorem_17_3_1_general` and
  `theorem_17_3_1_general_mean` (`SkeletonCycles`).
* **Theorem 17.3.2** (iii) ⇒ (i) (`theorem_17_3_2`, p. 436): for a Harris chain with a
  minorization on `C ∈ B⁺(X)` and an invariant measure `π` with `0 < π(C) < ∞` (not necessarily
  finite, so null recurrent chains are included), `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from
  every initial law, for `f, g ∈ L¹(π)` with `π(g) ≠ 0`. For a split `m`-skeleton:
  `theorem_17_3_2_general` (`SkeletonLimitTheorems`) and `theorem_17_3_2_skeleton`
  (`SkeletonErgodic`, the book's route with its hypotheses).
* **Theorem 17.3.6** (`theorem_17_3_6`, p. 441), the CLT part, for `m = 1`: for a positive Harris
  chain with a minorization on `C ∈ B⁺(X)` and the CLT moment condition for the split chain
  (17.31), `n^{−1/2} Sₙ(g − π(g)) ⇒ N(0, γ_g²)` under every initial law, where
  `γ_g² = π̌(α̌) Ě_α̌[s₁(ḡ)²]` (17.32) and `π̌(α̌) = δ π(C)`. For a split `m`-skeleton:
  `theorem_17_3_6_general` (`SkeletonLimitTheorems`) and `theorem_17_3_6_skeleton`
  (`SkeletonErgodic`).
* `atomMean_split_eq`: the stationary mean of the split chain is `π(g)`, and (17.32) for `m = 1`.

**Reading.** Theorem 17.3.2 (i) asks `∫ g dπ ≠ 0` (p. 436), as assumed here.

**Hypotheses and omissions.** The book splits an `m`-skeleton (17.21) of an aperiodic chain and
then has to handle the one-dependence of the cycle sums (Theorem 17.3.1, the blocking argument
(17.36)). This module is the case `m = 1` (a minorization for `P` itself on a set of positive
`ψ`-measure, the corrected strong aperiodicity of Theorem 13.3.1). The general case is in the
`Skeleton…` modules: the chain on blocks (`SkeletonSplit`), the one-dependent limit theorems
(`SkeletonOneDependent`), Theorem 17.3.1 (`SkeletonCycles`), Theorems 17.3.2 and 17.3.6
(`SkeletonLimitTheorems`), and the existence of the split skeleton with the book's hypotheses
(`SkeletonErgodic`, where `skeleton_isHarris_counterexample` shows that aperiodicity is needed).
In Theorem 17.3.2, (iii) ⇒ (i) without a minorization is `theorem_17_3_2_positive` for positive
Harris chains and `theorem_17_3_2_harris` (in `GapsChaconOrnstein`, by Hopf's maximal-lemma
argument instead of the split `m`-skeleton) for every Harris chain; (i) ⇒ (iii) and, for recurrent
chains, (i) ⇔ (ii) are `theorem_17_3_2_i_iii` and `theorem_17_3_2_tfae` there. The LIL of Theorem
17.3.6 is `theorem_17_3_6_lil` (`ChainLIL`, `m = 1`), `theorem_17_3_6_lil_general` and
`theorem_17_3_6_lil_skeleton` (general `m`).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Transfer between the split chain and the original chain -/

/-- Convergence in distribution of `Fₙ(T(·))` under `Q` is convergence in distribution of `Fₙ`
under `Q ∘ T⁻¹`. -/
theorem tendstoInDistribution_of_map {Ω₁ Ω₂ Ω' : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Ω'] {Q : Measure Ω₁} [IsProbabilityMeasure Q] {T : Ω₁ → Ω₂}
    (hT : Measurable T) {Q' : Measure Ω₂} [IsProbabilityMeasure Q'] (hQ : Q.map T = Q')
    {F : ℕ → Ω₂ → ℝ} (hF : ∀ n, Measurable (F n)) {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (h : TendstoInDistribution (fun n ω => F n (T ω)) atTop Z (fun _ => Q) P') :
    TendstoInDistribution F atTop Z (fun _ => Q') P' := by
  subst hQ
  refine ⟨fun n => (hF n).aemeasurable, h.aemeasurable_limit, ?_⟩
  have heq : (fun n => (⟨(Q.map T).map (F n), inferInstance⟩ : ProbabilityMeasure ℝ)) =
      fun n => ⟨Q.map fun ω => F n (T ω), inferInstance⟩ :=
    funext fun n => Subtype.ext (Measure.map_map (hF n) hT)
  rw [heq]
  exact h.tendsto

/-- The map `ω̌ ↦ (ω̌ₙ.1)ₙ` from split paths to paths is measurable. -/
theorem measurable_fstPath :
    Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
  measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)

/-- A property of `(Φ̌ₙ.1)ₙ` holding `P̌_{μ*}`-a.s. holds for `Φ` `P_μ`-a.s. -/
theorem ae_of_split {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P) (μ : Measure X)
    [IsProbabilityMeasure μ] {E : Set (ℕ → X)} (hE : MeasurableSet E)
    (h : haveI := M.isMarkovKernel_splitKernel
      ∀ᵐ ω ∂pathMeasure M.splitKernel (M.split μ), (fun n => (ω n).1) ∈ E) :
    ∀ᵐ ω ∂pathMeasure P μ, ω ∈ E := by
  have := M.isMarkovKernel_splitKernel
  rw [← M.theorem_5_1_3_i_path μ]
  exact (ae_map_iff measurable_fstPath.aemeasurable hE).2 h

/-! ### The ratio limit theorem at an accessible atom -/

variable {Y : Type*} [MeasurableSpace Y] in
/-- The ratio limit theorem for a recurrent chain with an accessible atom `α` reached almost
surely from every state, and an invariant measure `π` with `0 < π(α) < ∞`: for `f, g ∈ L¹(π)`
with `π(g) ≠ 0`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)`, `P_μ`-a.s., for every initial law `μ`. -/
theorem ratio_lln_of_accessibleAtom {P : Kernel Y Y} [IsMarkovKernel P] {ψ : Measure Y}
    {α : Set Y} (hacc : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ) {a : Y}
    (ha : a ∈ α) (hhit : ∀ y, hitProb P α y = 1) {π : Measure Y} (hπ : IsInvariant P π)
    (hπ0 : π α ≠ 0) (hπtop : π α ≠ ∞) {f g : Y → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f π) (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0) (μ : Measure Y)
    [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  have := isMarkovKernel_pathKernel P
  have hπeq := theorem_10_2_1_ii_smul hacc hrec ha hπ.isSubinvariant hπ0 hπtop
  set c := π α with hc
  have hc0 : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hπ0, hπtop⟩
  have hfi' : Integrable f (atomMeasure P hacc.1.1 a) := by
    rw [hπeq] at hfi; exact (integrable_smul_measure hπ0 hπtop).1 hfi
  have hgi' : Integrable g (atomMeasure P hacc.1.1 a) := by
    rw [hπeq] at hgi; exact (integrable_smul_measure hπ0 hπtop).1 hgi
  have hint : ∀ u : Y → ℝ, ∫ y, u y ∂π = c.toReal * ∫ y, u y ∂atomMeasure P hacc.1.1 a := by
    intro u; conv_lhs => rw [hπeq]
    rw [integral_smul_measure, smul_eq_mul]
  have hg' : ∫ y, g y ∂atomMeasure P hacc.1.1 a ≠ 0 := by
    intro h0; apply hg; rw [hint, h0, mul_zero]
  have hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤ :=
    ae_pathMeasure_of_forall P μ (measurableSet_ne_top (isStoppingTime_firstHit hacc.1.1))
      fun y => ae_firstHit_ne_top_of_hitProb_eq_one P hacc.1.1 (hhit y)
  have h := theorem_17_2_1 P hacc.1 ha (hhit a) μ hμ hfm hgm hfi' hgi' hg'
  rw [hint f, hint g, mul_div_mul_left _ _ hc0]
  exact h

/-! ### Theorem 17.3.2 -/

variable [MeasurableSpace.CountablyGenerated X]

/-- **Theorem 17.3.2** (iii) ⇒ (i) (MT p. 436), for a Harris chain with a minorization on a set
`C ∈ B⁺(X)`: for an invariant measure `π` with `0 < π(C) < ∞` (finite or not) and `f, g ∈ L¹(π)`
with `π(g) ≠ 0`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every initial law. -/
theorem theorem_17_3_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (M : Minorization P) (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π)
    (hπ0 : π M.C ≠ 0) (hπC : π M.C ≠ ∞) {f g : X → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) (hfi : Integrable f π) (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  obtain ⟨c, hc⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hca : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hH.1.2.1 hψC).2.2 _ (M.isMaximalIrreducibility_split hH.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain hH.isRecurrentChain
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 hπ
  have hLs := M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hα : M.split π M.checkAlpha = M.δ * π M.C := by
    rw [Minorization.checkAlpha, M.split_apply_true π M.measurableSet_C, inter_self]
  have hα0 : M.split π M.checkAlpha ≠ 0 := by
    rw [hα]; exact mul_ne_zero M.δ_pos.ne' hπ0
  have hαtop : M.split π M.checkAlpha ≠ ∞ := by
    rw [hα]; exact ENNReal.mul_ne_top M.δ_ne_top hπC
  have hmap := M.split_map_fst π
  have hint : ∀ u : X → ℝ, Measurable u →
      ∫ z, u z.1 ∂M.split π = ∫ y, u y ∂π := fun u hu => by
    rw [← integral_map measurable_fst.aemeasurable hu.aestronglyMeasurable, hmap]
  have hI : ∀ u : X → ℝ, Integrable u π → Integrable (fun z : X × Bool => u z.1) (M.split π) :=
    fun u hu => by
      rw [← hmap] at hu
      exact hu.comp_measurable measurable_fst
  have hgs : ∫ z, g z.1 ∂M.split π ≠ 0 := by rw [hint g hgm]; exact hg
  have h := ratio_lln_of_accessibleAtom (f := fun z : X × Bool => f z.1)
    (g := fun z : X × Bool => g z.1) hacc hrec hca hLs hπs hα0 hαtop
    (hfm.comp measurable_fst) (hgm.comp measurable_fst) (hI f hfi) (hI g hgi) hgs (M.split μ)
  rw [hint f hfm, hint g hgm] at h
  refine ae_of_split M μ ?_ h
  exact measurableSet_tendsto (𝓝 _) fun n =>
    (measurable_pathSum hfm n).div (measurable_pathSum hgm n)

/-! ### Theorem 17.3.1 -/

/-- The split chain of a Harris chain reaches `α̌` almost surely from `μ*`, and from `ν*`. -/
theorem ae_firstHit_split {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (M : Minorization P) (hψC : 0 < ψ M.C) (μ : Measure X) :
    haveI := M.isMarkovKernel_splitKernel
    (∀ᵐ ω ∂pathMeasure M.splitKernel (M.split μ), firstHit M.checkAlpha ω ≠ ⊤) ∧
      ∀ a, ∀ᵐ ω ∂pathMeasure M.splitKernel (M.splitKernel a), firstHit M.checkAlpha ω ≠ ⊤ := by
  have := M.isMarkovKernel_splitKernel
  have hLs := M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  exact ⟨ae_pathMeasure_of_forall _ _ (measurableSet_ne_top
    (isStoppingTime_firstHit M.measurableSet_checkAlpha)) fun y =>
      ae_firstHit_ne_top_of_hitProb_eq_one _ M.measurableSet_checkAlpha (hLs y),
    fun a => ae_firstHit_ne_top_of_hitProb _ M.measurableSet_checkAlpha (hLs a)⟩

/-- **Theorem 17.3.1** (MT p. 435), for `m = 1`: for a Harris chain with a minorization on
`C ∈ B⁺(X)`, an invariant measure `π` with `0 < π(C) < ∞`, `f ∈ L¹(π)` and any initial law `μ`, the
cycle sums `sⱼ(f) = Σ_{σ_α̌(j) < i ≤ σ_α̌(j+1)} f(Φᵢ)` of the split chain are independent and
identically distributed under `P̌_{μ*}`, with common law that of `Σ_{i ≤ σ_α̌} f(Φᵢ)` under
`P̌_{ν*}` (17.22), and mean `Ě[sⱼ(f)] = δ⁻¹ π(C)⁻¹ ∫ f dπ` (17.23). For `m = 1` the book's
one-dependence is independence. -/
theorem theorem_17_3_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (M : Minorization P) (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π)
    (hπ0 : π M.C ≠ 0) (hπC : π M.C ≠ ∞) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable f π) (μ : Measure X) [IsProbabilityMeasure μ] {a : X × Bool}
    (ha : a ∈ M.checkAlpha) :
    haveI := M.isMarkovKernel_splitKernel
    iIndepFun (fun j ω => cycleSum M.checkAlpha (fun z => f z.1) (cycle M.checkAlpha (j + 1) ω))
      (pathMeasure M.splitKernel (M.split μ)) ∧
    (∀ j, (pathMeasure M.splitKernel (M.split μ)).map
      (fun ω => cycleSum M.checkAlpha (fun z => f z.1) (cycle M.checkAlpha (j + 1) ω)) =
        (cycleLaw M.splitKernel M.checkAlpha a).map (cycleSum M.checkAlpha fun z => f z.1)) ∧
    ∫ e, cycleSum M.checkAlpha (fun z => f z.1) e ∂cycleLaw M.splitKernel M.checkAlpha a =
      (∫ y, f y ∂π) / (M.δ * π M.C).toReal := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  obtain ⟨hμ, hν⟩ := ae_firstHit_split hH M hψC μ
  have hφ : Measurable (cycleSum M.checkAlpha fun z : X × Bool => f z.1) :=
    measurable_cycleSum M.measurableSet_checkAlpha (hfm.comp measurable_fst)
  refine ⟨iIndepFun_cycles _ M.isAtom_checkAlpha ha (hν a) _ hμ hφ,
    fun j => map_cycle_eq _ M.isAtom_checkAlpha ha (hν a) _ hμ hφ j, ?_⟩
  -- the mean
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hH.1.2.1 hψC).2.2 _ (M.isMaximalIrreducibility_split hH.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain hH.isRecurrentChain
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 hπ
  have hLs := M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hα : M.split π M.checkAlpha = M.δ * π M.C := by
    rw [Minorization.checkAlpha, M.split_apply_true π M.measurableSet_C, inter_self]
  have hα0 : M.split π M.checkAlpha ≠ 0 := by
    rw [hα]; exact mul_ne_zero M.δ_pos.ne' hπ0
  have hαtop : M.split π M.checkAlpha ≠ ∞ := by
    rw [hα]; exact ENNReal.mul_ne_top M.δ_ne_top hπC
  have hπeq := theorem_10_2_1_ii_smul hacc hrec ha hπs.isSubinvariant hα0 hαtop
  have hmap := M.split_map_fst π
  have hfi2 : Integrable (fun z : X × Bool => f z.1) (M.split π) := by
    rw [← hmap] at hfi
    exact hfi.comp_measurable measurable_fst
  have hfi3 : Integrable (fun z : X × Bool => f z.1)
      (atomMeasure M.splitKernel hacc.1.1 a) := by
    rw [hπeq] at hfi2; exact (integrable_smul_measure hα0 hαtop).1 hfi2
  rw [integral_cycleSum _ M.isAtom_checkAlpha (hLs a) (f := fun z : X × Bool => f z.1)
    (hfm.comp measurable_fst) hfi3]
  have hint : ∫ y, f y ∂π = (M.split π M.checkAlpha).toReal *
      ∫ z, f z.1 ∂atomMeasure M.splitKernel hacc.1.1 a := by
    have e1 : ∫ y, f y ∂π = ∫ z, f z.1 ∂M.split π := by
      rw [← integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable, hmap]
    rw [e1]
    conv_lhs => rw [hπeq]
    rw [integral_smul_measure, smul_eq_mul]
  have hc0 : (M.split π M.checkAlpha).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hα0, hαtop⟩
  rw [hint, ← hα, mul_div_cancel_left₀ _ hc0]

/-! ### Theorem 17.3.6 -/

/-- The stationary mean of the split chain is `π(g)`: for a positive Harris chain with a
minorization on `C ∈ B⁺(X)`, invariant probability `π`, and cycle sums of `|g|` integrable,
`E_ρ[s(g)]/m = π(g)`; moreover the invariant probability of the split chain is `π*`, with
`π*(α̌) = δ π(C) = 1/m`. -/
theorem atomMean_split_eq {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {a : X × Bool} (ha : a ∈ M.checkAlpha)
    {g : X → ℝ} (hgm : Measurable g)
    (hg1 : haveI := M.isMarkovKernel_splitKernel
      Integrable (cycleSum M.checkAlpha fun z => |g z.1|) (cycleLaw M.splitKernel M.checkAlpha a))
    (hL : haveI := M.isMarkovKernel_splitKernel
      Integrable (fun e => (hitNat M.checkAlpha e : ℝ) + 1)
        (cycleLaw M.splitKernel M.checkAlpha a)) :
    haveI := M.isMarkovKernel_splitKernel
    atomMean M.splitKernel M.checkAlpha a (fun z => g z.1) = ∫ y, g y ∂π ∧
      cltVariance M.splitKernel M.checkAlpha a (fun z => g z.1) =
        (M.δ * π M.C).toReal * ∫ ω, (∑ i ∈ Finset.range (hitNat M.checkAlpha (shift 1 ω) + 1),
          (g (ω (i + 1)).1 - ∫ y, g y ∂π)) ^ 2 ∂pathKernel M.splitKernel a := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split π
  have hLs := M.hitProb_checkAlpha_eq_one (hph.1.hitProb_eq_one M.measurableSet_C hψC)
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hph.1.1.2.1 hψC).2.2 _
    (M.isMaximalIrreducibility_split hph.1.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain hph.1.isRecurrentChain
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 hπ
  have hπeq := eq_smul_atomMeasure_of_accessible hacc hrec ha hπs
  obtain ⟨-, -, hpia, hmean, hvar⟩ := theorem_17_2_2_variance _ M.isAtom_checkAlpha ha (hLs a)
    (g := fun z : X × Bool => g z.1) (hgm.comp measurable_fst) hg1 hL
  -- `π* = (μ°(X̌))⁻¹ μ°`
  set μa := atomMeasure M.splitKernel M.isAtom_checkAlpha.1 a with hμa
  have huniv : M.split π M.checkAlpha * μa univ = 1 := by
    have h := congrArg (fun ν : Measure (X × Bool) => ν univ) hπeq
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ] at h
    exact h.symm
  have hcα : M.split π M.checkAlpha = (μa univ)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left huniv
  have hpis : M.split π = (μa univ)⁻¹ • μa := by rw [← hcα]; exact hπeq
  have hmap := M.split_map_fst π
  have hint : ∫ y, g y ∂π = ∫ z, g z.1 ∂M.split π := by
    rw [← integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable, hmap]
  have hmeanπ : atomMean M.splitKernel M.checkAlpha a (fun z => g z.1) = ∫ y, g y ∂π := by
    rw [hint, hpis]; exact hmean.symm
  refine ⟨hmeanπ, ?_⟩
  rw [hvar, hmeanπ]
  congr 2
  rw [← hpis, Minorization.checkAlpha, M.split_apply_true π M.measurableSet_C, inter_self]

/-- **Theorem 17.3.6** (MT p. 441), the CLT part, for `m = 1`: for a positive Harris chain with a
minorization on `C ∈ B⁺(X)` and invariant probability `π`, if the split chain satisfies the CLT
moment condition (17.31), `Ě_{ν*}[(Σ_{n ≤ σ_α̌} |g(Φₙ)|)²] < ∞` and `Ě_{ν*}[σ_α̌²] < ∞`, then
`n^{−1/2} Sₙ(g − π(g)) ⇒ N(0, γ_g²)` under `P_μ` for every initial law `μ`, with `γ_g²` given by
(17.32) (`atomMean_split_eq`). No positivity of `γ_g²` is needed. -/
theorem theorem_17_3_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {a : X × Bool} (ha : a ∈ M.checkAlpha)
    {g : X → ℝ} (hgm : Measurable g)
    (hg2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (cycleSum M.checkAlpha fun z => |g z.1|) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    (hL2 : haveI := M.isMarkovKernel_splitKernel
      MemLp (fun e => (hitNat M.checkAlpha e : ℝ) + 1) 2 (cycleLaw M.splitKernel M.checkAlpha a))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : haveI := M.isMarkovKernel_splitKernel
      HasLaw Z (gaussianReal 0
        (cltVariance M.splitKernel M.checkAlpha a fun z => g z.1).toNNReal) P')
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω) atTop Z
      (fun _ => pathMeasure P μ) P' := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  have := isProbabilityMeasure_pathMeasure P μ
  have := isProbabilityMeasure_pathMeasure M.splitKernel (M.split μ)
  have := isProbabilityMeasure_cycleLaw M.splitKernel M.checkAlpha a
  obtain ⟨hμ, -⟩ := ae_firstHit_split hph.1 M hψC μ
  have hLs := M.hitProb_checkAlpha_eq_one (hph.1.hitProb_eq_one M.measurableSet_C hψC)
  have h := theorem_17_2_2 M.splitKernel M.isAtom_checkAlpha ha (hLs a) (M.split μ) hμ
    (g := fun z : X × Bool => g z.1) (hgm.comp measurable_fst) hg2 hL2 hZ
  rw [(atomMean_split_eq hph M hψC hπ ha hgm (hg2.integrable one_le_two)
    (hL2.integrable one_le_two)).1] at h
  exact tendstoInDistribution_of_map measurable_fstPath (M.theorem_5_1_3_i_path μ)
    (fun n => measurable_const.mul (measurable_pathSum (hgm.sub measurable_const) n)) h

end MeynTweedie.LimitTheorems
