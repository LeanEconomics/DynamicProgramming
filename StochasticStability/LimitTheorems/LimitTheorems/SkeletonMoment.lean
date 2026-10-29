/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SkeletonErgodic
import LimitTheorems.ChainLIL
import LimitTheorems.FSplitChain
import LimitTheorems.FSkeletons

/-!
# The moment bound for the split skeleton (MT Lemma 17.5.2 (ii)) and the LIL of §17.5

Meyn and Tweedie, Lemma 17.5.2 (ii) (p. 451, proof pp. 451–452) and the LIL parts of Theorems
17.5.3 (p. 452), 17.5.4 (p. 453) and 17.0.1 (iv) (p. 422), by the book's route: the moment bound
(17.53) for a split `m`-skeleton gives the moment condition (17.31), and Theorem 17.3.6
(`SkeletonLimitTheorems`) gives the LIL. Notation: `s₋₁(f) = skelPreSumE M f` is the sum of
`f(Φₜ)` up to the end of the block after the first visit `σ_α̌` of the split skeleton to `α̌`
(under `P̌_{ν*} = skelFreshLaw M` it has the law (17.22) of every cycle sum), and
`Zₙ(f) = blockSumE f ∘ θⁿ` are the block sums.

**The square of the cycle sum.**
* `skelPreSumE_of_hitNat_eq_succ`, `skelPreSumE_le_add_shift`: `s₋₁(f) = Z₀(f) + s₋₁(f) ∘ θ`
  before the visit; `sq_skelPreSumE_le`: `s₋₁(f)² ≤ 2 Σ_{n ≤ σ_α̌} (Z₀(f) s₋₁(f)) ∘ θⁿ`.
* `lintegral_sum_shift_hitNat`: sums up to the first visit, conditioned on the skeleton states;
  `lintegral_cycleSumE_skelFreshLaw`: the cycle formula
  `Ě_{ν*}[Σ_{n ≤ σ_α̌} g(Φ̌ₙ)] = (δ π(C))⁻¹ π*(g)` (Theorem 10.0.1 for the split skeleton).
* `blockMeanE_le`: `Ě[Z₀(f) | Φ̌₀ = (x, i)] ≤ (1 + δ⁻¹ + (1 − δ)⁻¹) f^{(m)}(x) + m ν(f)` (the
  constant `R₁` of the book, from (17.21)).
* `lintegral_skelPreSumE_pathKernel_le`: `Ě_v[s₋₁(f)] ≤ A V(Φ₀) + B` from every state (the
  bound `R₀ R₁ (V + 1)` of the book, through Theorems 14.2.3 and 14.2.10 for the skeleton).
* `lintegral_sq_skelPreSumE_ne_top`: `Ě_{ν*}[s₋₁(f)²] < ∞` from `π(f²), π(V²) < ∞` ((17.54),
  (17.55) and the Markov property at the end of each block).

**Results.**
* **Lemma 17.5.2 (ii)** (`lemma_17_5_2_ii`): under the CLT moment condition, every split
  `m`-skeleton (any minorization of `Pᵐ`, `m ≥ 1`, on `C ∈ B⁺(X)`) has `Ě_{ν*}[s₋₁(f)²] < ∞`
  (17.53), and the moment condition (17.31) holds for every `g` with `|g| ≤ f`.
* `skelCLTVariance_eq_poissonVariance`: the variance (17.32) of every such split skeleton is
  `γ_g² = π(ĝ² − (Pĝ)²)`.
* **Theorem 17.5.3**, the LIL (`theorem_17_5_3_lil_skeleton`); **Theorem 17.5.4**, the LIL
  (`theorem_17_5_4_lil_skeleton`); **Theorem 17.0.1 (iv)**, the LIL
  (`theorem_17_0_1_iv_lil_skeleton`): almost surely from every initial state, with the CLT
  constant, and with no minorization hypothesis (compare `theorem_17_5_3_lil` and
  `theorem_17_0_1_iv_lil` in `ChainLIL`, which assume a one-step minorization and (17.31)).

**Hypotheses.** The CLT moment condition (MT p. 450) includes "`Φ` ergodic", taken as positive
Harris and aperiodic. The book's proof takes the split set `C` to be a sublevel set of `V` (so
that the split skeleton is `f^{(m)}`-regular); the bound holds for every minorization of a
skeleton on a set of positive `ψ`-measure, since the cost of reaching `α̌` is bounded through a
set `R ∈ B⁺(X)` (`Minorization.exists_tabooPotFn_le`). The book asks `γ_g² > 0` for the LIL; the
LIL with constant `0` needs no positivity.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} {m : ℕ}

/-- If `σ_α = n + 1`, then `σ_α ∘ θ = n`. -/
theorem firstHit_shift_one_of_eq_succ {Y : Type*} {α : Set Y} {ω : ℕ → Y} {n : ℕ}
    (h : firstHit α ω = ((n + 1 : ℕ) : WithTop ℕ)) : firstHit α (shift 1 ω) = (n : WithTop ℕ) := by
  obtain ⟨h1, h2⟩ := (firstHit_eq_coe_iff α ω (n + 1)).1 h
  refine (firstHit_eq_coe_iff α (shift 1 ω) n).2 ⟨?_, fun j hj => ?_⟩
  · rw [shift_apply, add_comm]; exact h1
  · rw [shift_apply]; exact h2 (1 + j) (by omega)

/-- If `σ_α̌ = 0` (or `α̌` is never hit), `s₋₁(f)` is the first block sum. -/
theorem skelPreSumE_of_hitNat_eq_zero [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞)
    {ω : ℕ → (Fin m → X) × Bool} (h : hitNat (skelAtom M) ω = 0) :
    skelPreSumE M f ω = blockSumE f ω := by
  rw [skelPreSumE, h, zero_add, mul_one, blockSumE]

/-- If `σ_α̌ = n + 1`, `s₋₁(f) = Z₀(f) + s₋₁(f) ∘ θ`, with `σ_α̌ ∘ θ = n`. -/
theorem skelPreSumE_of_hitNat_eq_succ [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞)
    {ω : ℕ → (Fin m → X) × Bool} (hne : firstHit (skelAtom M) ω ≠ ⊤) {n : ℕ}
    (h : hitNat (skelAtom M) ω = n + 1) :
    firstHit (skelAtom M) (shift 1 ω) ≠ ⊤ ∧ hitNat (skelAtom M) (shift 1 ω) = n ∧
      skelPreSumE M f ω = blockSumE f ω + skelPreSumE M f (shift 1 ω) := by
  have h1 : firstHit (skelAtom M) ω = ((n + 1 : ℕ) : WithTop ℕ) := by
    rw [firstHit_eq_hitNat hne, h]; rfl
  have h2 := firstHit_shift_one_of_eq_succ h1
  have h3 : hitNat (skelAtom M) (shift 1 ω) = n := by rw [hitNat, h2]; rfl
  refine ⟨by rw [h2]; exact WithTop.coe_ne_top, h3, ?_⟩
  rw [skelPreSumE, skelPreSumE, h, h3, show m * (n + 1 + 1) = m + m * (n + 1) by ring,
    Finset.sum_range_add, blockSumE]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [skelRecover_shift, mul_one]

/-- `s₋₁(f) ≤ Z₀(f) + s₋₁(f) ∘ θ`. -/
theorem skelPreSumE_le_add_shift [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞)
    {ω : ℕ → (Fin m → X) × Bool} (hne : firstHit (skelAtom M) ω ≠ ⊤) :
    skelPreSumE M f ω ≤ blockSumE f ω + skelPreSumE M f (shift 1 ω) := by
  rcases Nat.eq_zero_or_eq_succ_pred (hitNat (skelAtom M) ω) with h | h
  · rw [skelPreSumE_of_hitNat_eq_zero M f h]; exact le_self_add
  · exact ((skelPreSumE_of_hitNat_eq_succ M f hne h).2.2).le

/-- **The square of the pre-visit sum** (MT p. 452): with `Zₙ = Z₀ ∘ θⁿ` the block sums,
`s₋₁(f)² ≤ 2 Σ_{n ≤ σ_α̌} (Z₀(f) s₋₁(f)) ∘ θⁿ`, since `s₋₁(f) ∘ θⁿ = Σ_{n ≤ k ≤ σ_α̌} Zₖ(f)`. -/
theorem sq_skelPreSumE_le [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞) :
    ∀ (N : ℕ) (ω : ℕ → (Fin m → X) × Bool), firstHit (skelAtom M) ω ≠ ⊤ →
      hitNat (skelAtom M) ω = N → skelPreSumE M f ω ^ 2 ≤ 2 * ∑ n ∈ Finset.range (N + 1),
        blockSumE f (shift n ω) * skelPreSumE M f (shift n ω) := by
  intro N
  induction N with
  | zero =>
    intro ω _ h
    rw [skelPreSumE_of_hitNat_eq_zero M f h, zero_add, Finset.sum_range_one, shift_zero,
      skelPreSumE_of_hitNat_eq_zero M f h, sq, two_mul]
    exact le_self_add
  | succ n ih =>
    intro ω hne h
    obtain ⟨hne', h3, hS⟩ := skelPreSumE_of_hitNat_eq_succ M f hne h
    have hi := ih (shift 1 ω) hne' h3
    simp_rw [shift_shift] at hi
    rw [Finset.sum_range_succ', shift_zero, mul_add, hS]
    set Z := blockSumE f ω
    set S' := skelPreSumE M f (shift 1 ω)
    have e : ∀ k ∈ Finset.range (n + 1), blockSumE f (shift (1 + k) ω) *
        skelPreSumE M f (shift (1 + k) ω) = blockSumE f (shift (k + 1) ω) *
        skelPreSumE M f (shift (k + 1) ω) := fun k _ => by rw [add_comm]
    rw [Finset.sum_congr rfl e] at hi
    calc (Z + S') ^ 2 ≤ (Z + S') ^ 2 + Z ^ 2 := le_self_add
      _ = S' ^ 2 + 2 * (Z * (Z + S')) := by ring
      _ ≤ _ := add_le_add hi le_rfl

/-! ### Conditioning on the skeleton states -/

variable [MeasurableSpace.CountablyGenerated X]

/-- `E_v[W]` depends only on the skeleton state of `v` when `W ∘ skelFresh = W`. -/
theorem lintegral_pathKernel_skelFresh [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {W : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hW : Measurable W)
    (hWf : ∀ ω, W (skelFresh ω) = W ω) (v : (Fin m → X) × Bool) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, W ω ∂pathKernel (skelKernel M) v =
      ∫⁻ ω, W ω ∂pathKernel (skelKernel M) (skelVirt (skelState v)) := by
  have := isMarkovKernel_skelKernel M
  have h := pathMeasure_map_skelFresh M (Measure.dirac v)
  rw [pathMeasure_dirac, Measure.map_dirac' (measurable_skelVirt.comp measurable_skelState),
    pathMeasure_dirac] at h
  simp only [Function.comp_apply] at h
  rw [← h, lintegral_map hW measurable_skelFresh]
  simp_rw [hWf]

/-- **Sums up to the first visit, conditioned on the skeleton** (the step of MT p. 451): for
`W ≥ 0` with `W ∘ skelFresh = W`, `E_ρ[Σ_{n ≤ σ_α̌} W ∘ θⁿ] = E_ρ[Σ_{n ≤ σ_α̌} Ŵ(Φ̌ₙ)]` with
`Ŵ(z) = E_{λ_z}[W]` and `Φ̌ₙ = (Φ_{nm}, Yₙ)` the split skeleton. -/
theorem lintegral_sum_shift_hitNat [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {W : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hW : Measurable W)
    (hWf : ∀ ω, W (skelFresh ω) = W ω) (ρ : Measure ((Fin m → X) × Bool))
    [IsProbabilityMeasure ρ]
    (hρ : haveI := isMarkovKernel_skelKernel M
      ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, firstHit (skelAtom M) ω ≠ ⊤) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), W (shift n ω)
        ∂pathMeasure (skelKernel M) ρ =
      ∫⁻ ω, cycleSumE M.checkAlpha (fun z => ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt z))
        (fun n => skelState (ω n)) ∂pathMeasure (skelKernel M) ρ := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  set G : ℕ → Set (ℕ → (Fin m → X) × Bool) :=
    fun n => {ω | WithTop.some n ≤ firstHit (skelAtom M) ω} with hG
  have hGm : ∀ n, MeasurableSet (G n) := fun n =>
    (natFilt (X := (Fin m → X) × Bool)).le n _ (measurableSet_le_firstHit_natFilt M n)
  have hb : ∀ n, Measurable fun ω : ℕ → (Fin m → X) × Bool => W (shift n ω) :=
    fun n => hW.comp (measurable_shift n)
  have hw : Measurable fun z : X × Bool => ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt z) :=
    hW.lintegral_kernel.comp measurable_skelVirt
  have hh : ∀ n, Measurable fun ω : ℕ → (Fin m → X) × Bool =>
      ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt (skelState (ω n))) :=
    fun n => hw.comp (measurable_skelState.comp (measurable_pi_apply n))
  calc ∫⁻ ω, ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), W (shift n ω)
        ∂pathMeasure (skelKernel M) ρ
      = ∫⁻ ω, ∑' n, (G n).indicator (fun ω => W (shift n ω)) ω
          ∂pathMeasure (skelKernel M) ρ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hρ] with ω hω
        rw [sum_range_hitNat_eq_tsum hω]
        exact tsum_congr fun n => by simp only [hG, Set.indicator_apply]
    _ = ∑' n, ∫⁻ ω in G n, W (shift n ω) ∂pathMeasure (skelKernel M) ρ := by
        rw [lintegral_tsum fun n => ((hb n).indicator (hGm n)).aemeasurable]
        exact tsum_congr fun n => lintegral_indicator (hGm n) _
    _ = ∑' n, ∫⁻ ω in G n, ∫⁻ w, W w ∂pathKernel (skelKernel M)
          (skelVirt (skelState (ω n))) ∂pathMeasure (skelKernel M) ρ := by
        refine tsum_congr fun n => ?_
        rw [markov_lintegral _ ρ (measurableSet_le_firstHit_natFilt M n) hW]
        exact setLIntegral_congr_fun (hGm n) fun ω _ => lintegral_pathKernel_skelFresh M hW hWf _
    _ = _ := by
        rw [← tsum_congr fun n => lintegral_indicator (hGm n) _, ← lintegral_tsum fun n =>
          ((hh n).indicator (hGm n)).aemeasurable]
        refine lintegral_congr_ae ?_
        filter_upwards [hρ] with ω hω
        symm
        rw [cycleSumE, show hitNat M.checkAlpha (fun n => skelState (ω n)) =
          hitNat (skelAtom M) ω from rfl, sum_range_hitNat_eq_tsum hω]
        exact tsum_congr fun n => by simp only [hG, Set.indicator_apply]

/-- **The cycle formula for the split skeleton** (Theorem 10.0.1 for the split `m`-skeleton, as in
MT p. 435): for a Harris `m`-skeleton, `C ∈ B⁺(X)`, `π` invariant with `0 < π(C) < ∞` and
measurable `g ≥ 0` on `X × {0, 1}`, `Ě_{ν*}[Σ_{n ≤ σ_α̌} g(Φ̌ₙ)] = (δ π(C))⁻¹ ∫ g dπ*`. -/
theorem lintegral_cycleSumE_skelFreshLaw [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m)) {ψ : Measure X}
    (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0) (hπC : π M.C ≠ ∞)
    {g : X × Bool → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, cycleSumE M.checkAlpha g (fun n => skelState (ω n)) ∂skelFreshLaw M =
      (M.δ * π M.C)⁻¹ * ∫⁻ z, g z ∂M.split π := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_skelKernel M
  have := M.isProbabilityMeasure_ν
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  obtain ⟨c, hc⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hπ0
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hH.1.2.1 hψC).2.2 _ (M.isMaximalIrreducibility_split hH.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain hH.isRecurrentChain
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 (hπ.pow m)
  have hα : M.split π M.checkAlpha = M.δ * π M.C := by
    rw [Minorization.checkAlpha, M.split_apply_true π M.measurableSet_C, inter_self]
  have hα0 : M.split π M.checkAlpha ≠ 0 := by rw [hα]; exact mul_ne_zero M.δ_pos.ne' hπ0
  have hαtop : M.split π M.checkAlpha ≠ ∞ := by rw [hα]; exact ENNReal.mul_ne_top M.δ_ne_top hπC
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hπeq := theorem_10_2_1_ii_smul hacc hrec ha hπs.isSubinvariant hα0 hαtop
  have hcyc : Measurable (cycleSumE M.checkAlpha g) :=
    measurable_cycleSumE M.measurableSet_checkAlpha hg
  have hπ' : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => skelState (ω n) :=
    measurable_pi_iff.2 fun n => measurable_skelState.comp (measurable_pi_apply n)
  rw [skelFreshLaw]
  rw [← lintegral_map hcyc hπ', skel_map_skelState M M.ν, ← M.splitKernel_apply_true c]
  have h1 := lintegral_cycleSumE M.splitKernel M.isAtom_checkAlpha (hL (c, true)) hg
  rw [cycleLaw, lintegral_map hcyc (measurable_excursion M.measurableSet_checkAlpha)] at h1
  simp_rw [cycleSumE_excursion] at h1
  rw [h1]
  have h2 : ∫⁻ z, g z ∂M.split π =
      M.split π M.checkAlpha *
        ∫⁻ z, g z ∂atomMeasure M.splitKernel M.isAtom_checkAlpha.1 (c, true) := by
    conv_lhs => rw [hπeq]
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [h2, hα, ← mul_assoc, ENNReal.inv_mul_cancel (hα ▸ hα0) (hα ▸ hαtop), one_mul]

/-- `∫ E_{λ_z}[W] μ*(dz) = E_{λ_μ}[W]`. -/
theorem lintegral_split_pathKernel_skelVirt [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m)) {W : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hW : Measurable W)
    (μ : Measure X) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ z, ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt z) ∂M.split μ =
      ∫⁻ ω, W ω ∂pathMeasure (skelKernel M) (skelInit M μ) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _) hW.aemeasurable,
    skelInit, lintegral_map hW.lintegral_kernel measurable_skelVirt]

/-! ### The block means -/

/-- `∫ g d(d · μ) ≤ c ∫ g dμ` for a density `d ≤ c`. -/
theorem lintegral_withDensity_le_mul {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {d g : Y → ℝ≥0∞} (hd : Measurable d) (hg : Measurable g) {c : ℝ≥0∞} (hdc : ∀ y, d y ≤ c) :
    ∫⁻ y, g y ∂μ.withDensity d ≤ c * ∫⁻ y, g y ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hg, ← lintegral_const_mul c hg]
  exact lintegral_mono fun y => mul_le_mul' (hdc y) le_rfl

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `Φ_{j+1}` is the `j`-th entry of the block `B₁` for `j < m`. -/
theorem skelRecover_succ_of_lt [NeZero m] (ω : ℕ → (Fin m → X) × Bool) {j : ℕ} (hj : j < m) :
    skelRecover ω (j + 1) = (ω 1).1 ⟨j, hj⟩ := by
  simp [skelRecover, unblock, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

omit [MeasurableSpace.CountablyGenerated X] in
/-- `∫ f(b_j) K(x, db) = Pʲ⁺¹f(x)`. -/
theorem lintegral_blockKernel_entry [IsMarkovKernel P] {f : X → ℝ≥0∞} (hf : Measurable f)
    {j : ℕ} (hj : j < m) (x : X) :
    ∫⁻ b, f (b ⟨j, hj⟩) ∂blockKernel P m x = ∫⁻ y, f y ∂(P ^ (j + 1)) x := by
  have := isMarkovKernel_pathKernel P
  rw [blockKernel_apply, lintegral_map (f := fun b : Fin m → X => f (b ⟨j, hj⟩))
    (hf.comp (measurable_pi_apply _)) (measurable_blockMap m),
    ← pathKernel_map_coord P x (j + 1), lintegral_map hf (measurable_pi_apply _)]
  rfl

/-- The entries of the next block of the split skeleton: from `(x, i)`,
`∫ f(b_j) W(xᵢ, db) ≤ (1 + δ⁻¹ + (1 − δ)⁻¹) Pʲ⁺¹f(x) + ν(f)` (from (17.21): on `C` the block law has
a density at most `δ⁻¹` or `(1 − δ)⁻¹` with respect to `K(x, ·)`). -/
theorem lintegral_blockW_entry_le [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) {j : ℕ} (hj : j < m) (z : X × Bool) :
    ∫⁻ b, f (b ⟨j, hj⟩) ∂blockW M z ≤
      (1 + M.δ⁻¹ + (1 - M.δ)⁻¹) * ∫⁻ y, f y ∂(P ^ (j + 1)) z.1 + ∫⁻ y, f y ∂M.ν := by
  obtain ⟨x, i⟩ := z
  have hT : Measurable fun b : Fin m → X => f (b ⟨j, hj⟩) := hf.comp (measurable_pi_apply _)
  have hK := lintegral_blockKernel_entry (P := P) hf hj x
  have h1 : (1 : ℝ≥0∞) ≤ 1 + M.δ⁻¹ + (1 - M.δ)⁻¹ := le_self_add.trans le_self_add
  have h2 : M.δ⁻¹ ≤ 1 + M.δ⁻¹ + (1 - M.δ)⁻¹ := le_add_self.trans le_self_add
  have h3 : (1 - M.δ)⁻¹ ≤ 1 + M.δ⁻¹ + (1 - M.δ)⁻¹ := le_add_self
  cases i with
  | false =>
    by_cases hx : x ∈ M.C
    · rw [blockW_false_of_mem M hx, blockBotC_apply]
      refine (lintegral_withDensity_le_mul _ ((measurable_botDensity M).comp
        (measurable_const.prodMk measurable_id)) hT (c := (1 - M.δ)⁻¹) fun b => ?_).trans ?_
      · exact mul_le_of_le_one_right zero_le tsub_le_self
      · rw [hK]; exact le_add_right (mul_le_mul' h3 le_rfl)
    · rw [blockW_false_of_notMem M hx, hK]
      exact le_add_right (le_mul_of_one_le_left zero_le h1)
  | true =>
    by_cases hx : x ∈ M.C
    · rw [blockW_true_of_mem M hx, blockTopC_apply]
      refine (lintegral_withDensity_le_mul _ ((measurable_topDensity M).comp
        (measurable_const.prodMk measurable_id)) hT (c := M.δ⁻¹) fun b => ?_).trans ?_
      · exact mul_le_of_le_one_right zero_le (skelDensity_le_one M _ _)
      · rw [hK]; exact le_add_right (mul_le_mul' h2 le_rfl)
    · rw [blockW_true_of_notMem M hx, lintegral_map hT
        (measurable_pi_iff.2 fun _ => measurable_id : Measurable fun (y : X) (_ : Fin m) => y)]
      exact le_add_self

/-- **The block means** (MT p. 451, "from (17.21) we may find `R₁`"):
`Ě[Z₀(f) | Φ̌₀ = (x, i)] ≤ (1 + δ⁻¹ + (1 − δ)⁻¹) f^{(m)}(x) + m ν(f)`. -/
theorem blockMeanE_le [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) (z : X × Bool) :
    blockMeanE M f z ≤ (1 + M.δ⁻¹ + (1 - M.δ)⁻¹) * fSkel P m f z.1 + m * ∫⁻ y, f y ∂M.ν := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have h1 : (1 : ℝ≥0∞) ≤ 1 + M.δ⁻¹ + (1 - M.δ)⁻¹ := le_self_add.trans le_self_add
  unfold blockMeanE blockSumE
  rw [lintegral_finsetSum (f := fun k (ω : ℕ → (Fin m → X) × Bool) => f (skelRecover ω k)) _
    fun k _ => hf.comp ((measurable_pi_apply k).comp measurable_skelRecover), fSkel,
    Finset.mul_sum]
  have hm : (m : ℝ≥0∞) * ∫⁻ y, f y ∂M.ν = ∑ _k ∈ Finset.range m, ∫⁻ y, f y ∂M.ν := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  rcases k with _ | j
  · have e : ∫⁻ ω, f (skelRecover ω 0) ∂pathKernel (skelKernel M) (skelVirt z) =
        ∫⁻ ω, f (blockLast (ω 0).1) ∂pathKernel (skelKernel M) (skelVirt z) := rfl
    rw [e, ← lintegral_map (f := fun v : (Fin m → X) × Bool => f (blockLast v.1))
      (g := fun ω : ℕ → (Fin m → X) × Bool => ω 0)
      (hf.comp (measurable_blockLast.comp measurable_fst)) (measurable_pi_apply 0),
      pathKernel_map_zero, lintegral_dirac' (f := fun v : (Fin m → X) × Bool => f (blockLast v.1))
      _ (hf.comp (measurable_blockLast.comp measurable_fst)), pow_zero_apply, lintegral_dirac' _ hf]
    exact le_add_right (le_mul_of_one_le_left zero_le h1)
  · have hj : j < m := by have := Finset.mem_range.1 hk; omega
    have hF : Measurable fun u : (Fin m → X) × Bool => f (u.1 ⟨j, hj⟩) :=
      hf.comp ((measurable_pi_apply _).comp measurable_fst)
    have e : ∫⁻ ω, f (skelRecover ω (j + 1)) ∂pathKernel (skelKernel M) (skelVirt z) =
        ∫⁻ ω, f ((ω 1).1 ⟨j, hj⟩) ∂pathKernel (skelKernel M) (skelVirt z) :=
      lintegral_congr fun ω => by rw [skelRecover_succ_of_lt ω hj]
    rw [e, ← lintegral_map (f := fun u : (Fin m → X) × Bool => f (u.1 ⟨j, hj⟩))
      (g := fun ω : ℕ → (Fin m → X) × Bool => ω 1) hF (measurable_pi_apply 1),
      pathKernel_map_coord, pow_one,
      skelKernel_apply, skelState_skelVirt, lintegral_skelJ M z
      (F := fun u : (Fin m → X) × Bool => f (u.1 ⟨j, hj⟩)) hF]
    simp_rw [← add_mul, tsub_add_cancel_of_le (M.splitProb_le_one _), one_mul]
    exact lintegral_blockW_entry_le M hf hj z

/-! ### The expected sum up to the first visit -/

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `Σ_{n ≤ σ_α} g(eₙ) ≤ Σ_{n < σ_α + 1} g(eₙ)` (with equality when `α` is hit). -/
theorem cycleSumE_le_sumBefore {Y : Type*} (α : Set Y) (g : Y → ℝ≥0∞) (e : ℕ → Y) :
    cycleSumE α g e ≤ sumBefore (fun ω => firstHit α ω + 1) (fun k ω => g (ω k)) e := by
  by_cases h : firstHit α e = ⊤
  · unfold cycleSumE sumBefore
    calc ∑ i ∈ Finset.range (hitNat α e + 1), g (e i)
        = ∑ i ∈ Finset.range (hitNat α e + 1),
            {ω : ℕ → Y | (i : WithTop ℕ) < firstHit α ω + 1}.indicator (fun ω => g (ω i)) e :=
          Finset.sum_congr rfl fun i _ => by
            rw [indicator_of_mem]
            change (i : WithTop ℕ) < firstHit α e + 1
            rw [h, top_add]
            exact WithTop.coe_lt_top _
      _ ≤ _ := ENNReal.sum_le_tsum _
  · rw [cycleSumE, sum_range_hitNat_eq_tsum h]
    refine le_of_eq (tsum_congr fun n => ?_)
    have hiff : WithTop.some n ≤ firstHit α e ↔ (n : WithTop ℕ) < firstHit α e + 1 :=
      (ENat.lt_add_one_iff h).symm
    by_cases hn : WithTop.some n ≤ firstHit α e
    · rw [indicator_of_mem (show e ∈ {ω : ℕ → Y | WithTop.some n ≤ firstHit α ω} from hn),
        indicator_of_mem (show e ∈ {ω : ℕ → Y | (n : WithTop ℕ) < firstHit α ω + 1} from
          hiff.1 hn)]
    · rw [indicator_of_notMem (show e ∉ {ω : ℕ → Y | WithTop.some n ≤ firstHit α ω} from hn),
        indicator_of_notMem (show e ∉ {ω : ℕ → Y | (n : WithTop ℕ) < firstHit α ω + 1} from
          fun h' => hn (hiff.2 h'))]

/-- **The `f`-cost of reaching `α̌`** (MT p. 451, from Theorems 14.2.3 and 14.2.10 for the
`m`-skeleton): if the `m`-skeleton is Harris and satisfies (V3) for `V` with `f' = F` on a petite
set, `π` is an invariant probability of `P` with `π(F) < ∞`, and the block means are bounded by
`A₁ F`, then `Ě_v[s₋₁(f)] ≤ A V(Φ₀) + B` for every state `v` of the chain on blocks. -/
theorem lintegral_skelPreSumE_pathKernel_le [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m)) {ψ : Measure X}
    (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) {V F : X → ℝ≥0∞} (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞)
    (hF : Measurable F) {b' : ℝ≥0∞} (hb' : b' ≠ ∞) {C' : Set X}
    (hC' : IsPetite (P ^ m : Kernel X X) C') (hd : DriftV3 (P ^ m : Kernel X X) V F b' C')
    (hπF : ∫⁻ x, F x ∂π ≠ ∞) {A₁ : ℝ≥0∞} (hA₁ : A₁ ≠ ∞)
    (hblock : ∀ z, blockMeanE M f z ≤ A₁ * F z.1) :
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧ ∀ v : (Fin m → X) × Bool,
      ∫⁻ ω, skelPreSumE M f ω ∂@pathKernel _ _ (skelKernel M) (isMarkovKernel_skelKernel M) v ≤
        A * V (blockLast v.1) + B := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have := isMarkovKernel_pathKernel M.splitKernel
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hpos : IsPositive (P ^ m : Kernel X X) ψ := ⟨hH.1, π, inferInstance, hπ.pow m⟩
  set G : X → ℝ≥0∞ := fun x => A₁ * F x with hGdef
  have hG : Measurable G := hF.const_mul _
  have hπG : ∫⁻ x, G x ∂π ≠ ∞ := by
    rw [hGdef, lintegral_const_mul _ hF]; exact ENNReal.mul_ne_top hA₁ hπF
  have hGs : Measurable fun z : X × Bool => G z.1 := hG.comp measurable_fst
  obtain ⟨R, hRm, hψR, K, hK, hU⟩ := M.exists_tabooPotFn_le hpos hψC (hπ.pow m) hG hπG
  obtain ⟨cR, hcR, hfr⟩ := theorem_14_2_3_i hH.1 hV hF hb' hC' hd hRm hψR
  obtain ⟨c₀, hc₀⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  -- `E_x[Σ_{k<τ_R} G] = A₁ E_x[Σ_{k<τ_R} F]`
  have hscale : ∀ x, fSumReturn (P ^ m : Kernel X X) R G x =
      A₁ * fSumReturn (P ^ m : Kernel X X) R F x := fun x => by
    rw [fSumReturn, fSumReturn, ← lintegral_const_mul' _ _ hA₁]
    refine lintegral_congr fun ω => ?_
    simp only [sumBefore]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    by_cases hk : ω ∈ {ω : ℕ → X | (k : WithTop ℕ) < firstReturn R ω}
    · rw [indicator_of_mem hk, indicator_of_mem hk]
    · rw [indicator_of_notMem hk, indicator_of_notMem hk, mul_zero]
  set fsr := fSumReturn M.splitKernel (Prod.fst ⁻¹' R) (fun z : X × Bool => G z.1) with hfsr
  have hfsrm : Measurable fsr := measurable_fSumReturn _ (measurable_fst hRm) hGs
  have hsplit : ∀ x, (1 - M.splitProb x) * fsr (x, false) + M.splitProb x * fsr (x, true) ≤
      A₁ * (V x + cR) := fun x => by
    rw [← M.lintegral_splitK x hfsrm, hfsr, M.fSumReturn_splitK hRm hG x, hscale]
    exact mul_le_mul' le_rfl (hfr x)
  have h1δ : 1 - M.δ ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hfalse : ∀ x, fsr (x, false) ≤ (1 - M.δ)⁻¹ * (A₁ * (V x + cR)) := fun x => by
    refine le_trans (ENNReal.inv_mul_cancel_left M.one_sub_δ_ne_zero h1δ).symm.le
      (mul_le_mul' le_rfl (le_trans ?_ ((le_self_add).trans (hsplit x))))
    exact mul_le_mul' (tsub_le_tsub_left (M.splitProb_le x) 1) le_rfl
  have htrue : fsr (c₀, true) ≤ M.δ⁻¹ * (A₁ * (V c₀ + cR)) := by
    refine le_trans (ENNReal.inv_mul_cancel_left M.δ_pos.ne' M.δ_ne_top).symm.le
      (mul_le_mul' le_rfl (le_trans ?_ ((le_add_self).trans (hsplit c₀))))
    rw [M.splitProb_of_mem hc₀]
  set U := tabooPotFn M.splitKernel M.checkAlpha (fun z : X × Bool => G z.1) with hUdef
  have hUle : ∀ z : X × Bool, U z ≤
      (1 - M.δ)⁻¹ * (A₁ * (V z.1 + cR)) + (M.δ⁻¹ * (A₁ * (V c₀ + cR)) + K) := by
    rintro ⟨x, i⟩
    cases i with
    | false => exact (hU (x, false)).trans (add_le_add (hfalse x) le_add_self)
    | true =>
      have e : U (x, true) = U (c₀, true) := tabooPotFn_eq_of_kernel_eq M.measurableSet_checkAlpha
        hGs (by rw [M.splitKernel_apply_true, M.splitKernel_apply_true])
      rw [e]
      exact (hU (c₀, true)).trans (le_add_left (add_le_add htrue le_rfl))
  have hFle : ∀ x, F x ≤ V x + b' := fun x =>
    le_add_self.trans ((hd x).trans (add_le_add le_rfl
      (Set.indicator_le (g := fun _ => b') (fun _ _ => le_rfl) x)))
  refine ⟨A₁ + (1 - M.δ)⁻¹ * A₁, A₁ * b' + (1 - M.δ)⁻¹ * (A₁ * cR) +
    (M.δ⁻¹ * (A₁ * (V c₀ + cR)) + K), ?_, ?_, fun v => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨hA₁, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
      M.one_sub_δ_ne_zero) hA₁⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA₁ hb',
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 M.one_sub_δ_ne_zero)
        (ENNReal.mul_ne_top hA₁ hcR)⟩, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.2 M.δ_pos.ne') (ENNReal.mul_ne_top hA₁
            (ENNReal.add_ne_top.2 ⟨hVfin c₀, hcR⟩)), hK⟩⟩
  have hρ := ae_firstHit_skelAtom_measure M hL (Measure.dirac v)
  rw [pathMeasure_dirac] at hρ
  have h1 := lintegral_skelPreSumE M hf (Measure.dirac v) (by rwa [pathMeasure_dirac])
  rw [pathMeasure_dirac] at h1
  have hcyc : Measurable (cycleSumE M.checkAlpha (blockMeanE M f)) :=
    measurable_cycleSumE M.measurableSet_checkAlpha (measurable_blockMeanE M hf)
  have hπ' : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => skelState (ω n) :=
    measurable_pi_iff.2 fun n => measurable_skelState.comp (measurable_pi_apply n)
  rw [h1, ← lintegral_map hcyc hπ', pathKernel_map_lump (skelKernel M) M.splitKernel
    measurable_skelState (skelKernel_map_skelState M) v]
  set z := skelState v with hz
  calc ∫⁻ e, cycleSumE M.checkAlpha (blockMeanE M f) e ∂pathKernel M.splitKernel z
      ≤ ∫⁻ e, sumBefore (fun ω => firstHit M.checkAlpha ω + 1)
          (fun k ω => G (ω k).1) e ∂pathKernel M.splitKernel z :=
        lintegral_mono fun e => le_trans (Finset.sum_le_sum fun i _ => hblock (e i))
          (cycleSumE_le_sumBefore M.checkAlpha (fun z : X × Bool => G z.1) e)
    _ = G z.1 + M.checkAlphaᶜ.indicator U z :=
        gKernelFn_eq M.splitKernel M.measurableSet_checkAlpha hGs z
    _ ≤ A₁ * (V z.1 + b') + ((1 - M.δ)⁻¹ * (A₁ * (V z.1 + cR)) +
          (M.δ⁻¹ * (A₁ * (V c₀ + cR)) + K)) :=
        add_le_add (mul_le_mul' le_rfl (hFle z.1)) ((indicator_le_self _ _ _).trans (hUle z))
    _ = _ := by
        have hz1 : z.1 = blockLast v.1 := rfl
        rw [hz1]; ring

/-! ### Square integrability -/

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `ab ≤ a² + b²` in `[0, ∞]`. -/
theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `∫ (a + b)² < ∞` if `∫ a² < ∞` and `∫ b² < ∞`. -/
theorem lintegral_sq_add_ne_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : Ω → ℝ≥0∞} (ha : Measurable a) (ha2 : ∫⁻ ω, a ω ^ 2 ∂μ ≠ ∞)
    (hb2 : ∫⁻ ω, b ω ^ 2 ∂μ ≠ ∞) : ∫⁻ ω, (a ω + b ω) ^ 2 ∂μ ≠ ∞ := by
  have hle : ∀ ω, (a ω + b ω) ^ 2 ≤ 3 * (a ω ^ 2 + b ω ^ 2) := fun ω => by
    calc (a ω + b ω) ^ 2 = a ω ^ 2 + b ω ^ 2 + 2 * (a ω * b ω) := by ring
      _ ≤ a ω ^ 2 + b ω ^ 2 + 2 * (a ω ^ 2 + b ω ^ 2) :=
          add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_sq_add_sq _ _))
      _ = 3 * (a ω ^ 2 + b ω ^ 2) := by ring
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left (ha.pow_const 2)]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨ha2, hb2⟩)

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `∫ (Σᵢ aᵢ)² < ∞` if every `∫ aᵢ² < ∞`. -/
theorem lintegral_sq_sum_ne_top {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) {a : ι → Ω → ℝ≥0∞} (ha : ∀ i ∈ s, Measurable (a i))
    (ha2 : ∀ i ∈ s, ∫⁻ ω, a i ω ^ 2 ∂μ ≠ ∞) : ∫⁻ ω, (∑ i ∈ s, a i ω) ^ 2 ∂μ ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact lintegral_sq_add_ne_top (ha i (Finset.mem_insert_self i s))
      (ha2 i (Finset.mem_insert_self i s))
      (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        fun j hj => ha2 j (Finset.mem_insert_of_mem hj))

omit [MeasurableSpace.CountablyGenerated X] in
/-- Under `P_π` with `π` invariant, `E_π[g(Φₖ)] = π(g)`. -/
theorem lintegral_coord_of_isInvariant [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ≥0∞} (hg : Measurable g)
    (k : ℕ) : ∫⁻ φ, g (φ k) ∂pathMeasure P π = ∫⁻ x, g x ∂π := by
  rw [← lintegral_map (f := g) (g := fun φ : ℕ → X => φ k) hg (measurable_pi_apply k),
    pathMeasure_map_coord, hπ.pow k]

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `Φₘ` is the last entry of the block `B₁`. -/
theorem skelRecover_blockEnd [NeZero m] (ω : ℕ → (Fin m → X) × Bool) :
    skelRecover ω m = blockLast (ω 1).1 := by
  have h := skelRecover_succ_of_lt ω (Nat.sub_one_lt (NeZero.ne m))
  rw [Nat.sub_add_cancel (NeZero.pos m)] at h
  exact h

omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁(f)` is measurable for `f ≥ 0`. -/
theorem measurable_skelPreSumE [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ≥0∞}
    (hf : Measurable f) : Measurable (skelPreSumE M f) := by
  have hF : Measurable fun p : (ℕ → (Fin m → X) × Bool) × ℕ =>
      ∑ t ∈ Finset.range (m * (p.2 + 1)), f (skelRecover p.1 t) :=
    measurable_from_prod_countable_left fun n => by
      dsimp only
      exact Finset.measurable_sum _ fun t _ =>
        hf.comp ((measurable_pi_apply t).comp measurable_skelRecover)
  exact hF.comp (measurable_id.prodMk (measurable_hitNat (measurableSet_skelAtom M)))

omit [MeasurableSpace.CountablyGenerated X] in
/-- The first block sum `Z₀(f)` is `𝓕₁`-measurable. -/
theorem measurable_blockSumE_natFilt_one [NeZero m] {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable[natFilt (X := (Fin m → X) × Bool) 1] (blockSumE (m := m) f) := by
  have hpair : Measurable fun p : ((Fin m → X) × Bool) × ((Fin m → X) × Bool) =>
      (fun n : ℕ => if n = 0 then p.1 else p.2) :=
    measurable_pi_iff.2 fun n => by
      by_cases hn : n = 0
      · simp only [hn, ↓reduceIte]; exact measurable_fst
      · simp only [hn, ↓reduceIte]; exact measurable_snd
  have e : blockSumE (m := m) f = (fun p => blockSumE f (fun n : ℕ => if n = 0 then p.1 else p.2))
      ∘ fun ω : ℕ → (Fin m → X) × Bool => (ω 0, ω 1) := by
    funext ω
    simp only [Function.comp, blockSumE]
    refine Finset.sum_congr rfl fun k hk => congrArg f (skelRecover_congr (n := 1)
      (fun i hi => ?_) (by have := Finset.mem_range.1 hk; omega))
    interval_cases i <;> simp
  have h0 : Measurable[natFilt (X := (Fin m → X) × Bool) 1]
      fun ω : ℕ → (Fin m → X) × Bool => (ω 0, ω 1) :=
    ((measurable_coord_natFilt 0).mono ((natFilt (X := (Fin m → X) × Bool)).mono zero_le_one)
      le_rfl).prodMk (measurable_coord_natFilt 1)
  have h1 := (measurable_blockSumE (m := m) hf).comp hpair
  rw [e]
  exact h1.comp h0

/-- **The second moment of the cycle sums** (MT p. 452, (17.54), (17.55) and the final Markov
property computation): if `π(f²) < ∞`, `π(V²) < ∞` and `Ě_v[s₋₁(f)] ≤ A V(Φ₀) + B`, then
`Ě_{ν*}[s₋₁(f)²] < ∞`. -/
theorem lintegral_sq_skelPreSumE_ne_top [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf2 : ∫⁻ x, f x ^ 2 ∂π ≠ ∞) {V : X → ℝ≥0∞} (hV : Measurable V)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    (hh : ∀ v : (Fin m → X) × Bool,
      ∫⁻ ω, skelPreSumE M f ω ∂@pathKernel _ _ (skelKernel M) (isMarkovKernel_skelKernel M) v ≤
        A * V (blockLast v.1) + B) :
    ∫⁻ ω, skelPreSumE M f ω ^ 2 ∂skelFreshLaw M ≠ ∞ := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have := M.isProbabilityMeasure_ν
  have := isProbabilityMeasure_skelInit M M.ν
  have := isProbabilityMeasure_skelInit M π
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  obtain ⟨hπ0, hπC⟩ := M.measure_pos_lt_top hψ hψC hπ (IsProbabilityMeasure.ne_zero π)
  have hZm : Measurable (blockSumE (m := m) f) := measurable_blockSumE hf
  have hSm : Measurable (skelPreSumE M f) := measurable_skelPreSumE M hf
  set W : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞ := fun ω => blockSumE f ω * skelPreSumE M f ω
    with hWdef
  have hWm : Measurable W := hZm.mul hSm
  have hWf : ∀ ω, W (skelFresh ω) = W ω := fun ω => by
    simp only [hWdef, blockSumE, skelPreSumE, skelRecover_skelFresh, hitNat_skelFresh]
  have hw : Measurable fun z : X × Bool => ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt z) :=
    hWm.lintegral_kernel.comp measurable_skelVirt
  -- the square through the cycle formula
  have hρΛ : ∀ᵐ ω ∂pathMeasure (skelKernel M) (skelInit M M.ν),
      firstHit (skelAtom M) ω ≠ ⊤ := ae_firstHit_skelAtom_measure M hL _
  have e1 : ∫⁻ ω, ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), W (shift n ω) ∂skelFreshLaw M =
      ∫⁻ ω, cycleSumE M.checkAlpha (fun z => ∫⁻ w, W w ∂pathKernel (skelKernel M) (skelVirt z))
        (fun n => skelState (ω n)) ∂skelFreshLaw M :=
    lintegral_sum_shift_hitNat M hWm hWf (skelInit M M.ν) hρΛ
  have step1 : ∫⁻ ω, skelPreSumE M f ω ^ 2 ∂skelFreshLaw M ≤
      2 * ((M.δ * π M.C)⁻¹ *
        ∫⁻ ω, W ω ∂pathMeasure (skelKernel M) (skelInit M π)) := by
    calc ∫⁻ ω, skelPreSumE M f ω ^ 2 ∂skelFreshLaw M
        ≤ ∫⁻ ω, 2 * ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), W (shift n ω)
            ∂skelFreshLaw M :=
          lintegral_mono_ae (hρΛ.mono fun ω hω => sq_skelPreSumE_le M f _ ω hω rfl)
      _ = 2 * ∫⁻ ω, ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), W (shift n ω)
            ∂skelFreshLaw M := lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ = _ := by
          rw [e1, lintegral_cycleSumE_skelFreshLaw M hH hψC hπ hπ0.ne' hπC.ne hw,
            lintegral_split_pathKernel_skelVirt M hWm π]
  -- one step of the Markov property
  have hρπ : ∀ᵐ ω ∂pathMeasure (skelKernel M) (skelInit M π), firstHit (skelAtom M) ω ≠ ⊤ :=
    ae_firstHit_skelAtom_measure M hL _
  have step2 : ∫⁻ ω, W ω ∂pathMeasure (skelKernel M) (skelInit M π) ≤
      ∫⁻ ω, blockSumE f ω * blockSumE f ω ∂pathMeasure (skelKernel M) (skelInit M π) +
        ∫⁻ ω, blockSumE f ω * (A * V (skelRecover ω m) + B)
          ∂pathMeasure (skelKernel M) (skelInit M π) := by
    calc ∫⁻ ω, W ω ∂pathMeasure (skelKernel M) (skelInit M π)
        ≤ ∫⁻ ω, (blockSumE f ω * blockSumE f ω + blockSumE f ω * skelPreSumE M f (shift 1 ω))
            ∂pathMeasure (skelKernel M) (skelInit M π) :=
          lintegral_mono_ae (hρπ.mono fun ω hω => by
            rw [hWdef, ← mul_add]
            exact mul_le_mul' le_rfl (skelPreSumE_le_add_shift M f hω))
      _ = ∫⁻ ω, blockSumE f ω * blockSumE f ω ∂pathMeasure (skelKernel M) (skelInit M π) +
          ∫⁻ ω, blockSumE f ω * skelPreSumE M f (shift 1 ω)
            ∂pathMeasure (skelKernel M) (skelInit M π) :=
          lintegral_add_left (hZm.mul hZm) _
      _ = ∫⁻ ω, blockSumE f ω * blockSumE f ω ∂pathMeasure (skelKernel M) (skelInit M π) +
          ∫⁻ ω, blockSumE f ω * ∫⁻ w, skelPreSumE M f w ∂pathKernel (skelKernel M) (ω 1)
            ∂pathMeasure (skelKernel M) (skelInit M π) := by
          rw [markov_lintegral_mul _ _ (measurable_blockSumE_natFilt_one hf) hSm]
      _ ≤ _ := add_le_add le_rfl (lintegral_mono fun ω => mul_le_mul' le_rfl (by
          rw [skelRecover_blockEnd]; exact hh (ω 1)))
  -- back to the original chain
  set u : (ℕ → X) → ℝ≥0∞ := fun φ => ∑ k ∈ Finset.range m, f (φ k) with hu
  have hum : Measurable u := Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply k)
  have hwm : Measurable fun φ : ℕ → X => A * V (φ m) + B :=
    ((hV.comp (measurable_pi_apply m)).const_mul A).add_const B
  have e2 : ∀ Φ : (ℕ → X) → ℝ≥0∞, Measurable Φ →
      ∫⁻ ω, Φ (skelRecover ω) ∂pathMeasure (skelKernel M) (skelInit M π) =
        ∫⁻ φ, Φ φ ∂pathMeasure P π := fun Φ hΦ => by
    rw [← lintegral_map hΦ measurable_skelRecover, skel_map_recover M π]
  have hZu : ∀ ω, blockSumE f ω = u (skelRecover ω) := fun ω => rfl
  simp_rw [hZu] at step2
  rw [e2 (fun φ => u φ * u φ) (hum.mul hum),
    e2 (fun φ => u φ * (A * V (φ m) + B)) (hum.mul hwm)] at step2
  -- finiteness
  have := isProbabilityMeasure_pathMeasure P π
  have hcoord := fun (g : X → ℝ≥0∞) (hg : Measurable g) (k : ℕ) =>
    lintegral_coord_of_isInvariant hπ hg k
  have hu2 : ∫⁻ φ, u φ ^ 2 ∂pathMeasure P π ≠ ∞ :=
    lintegral_sq_sum_ne_top (Finset.range m) (fun k _ => hf.comp (measurable_pi_apply k))
      fun k _ => by rw [hcoord (fun x => f x ^ 2) (hf.pow_const 2) k]; exact hπf2
  have hw2 : ∫⁻ φ, (A * V (φ m) + B) ^ 2 ∂pathMeasure P π ≠ ∞ := by
    refine lintegral_sq_add_ne_top ((hV.comp (measurable_pi_apply m)).const_mul A) ?_ ?_
    · simp_rw [mul_pow]
      rw [lintegral_const_mul (f := fun φ : ℕ → X => V (φ m) ^ 2) _
        ((hV.comp (measurable_pi_apply m)).pow_const 2),
        hcoord (fun x => V x ^ 2) (hV.pow_const 2) m]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) hπV2
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.pow_ne_top hB
  have huu : ∫⁻ φ, u φ * u φ ∂pathMeasure P π ≠ ∞ := by
    simp_rw [← sq]; exact hu2
  have huw : ∫⁻ φ, u φ * (A * V (φ m) + B) ∂pathMeasure P π ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun φ => mul_le_sq_add_sq _ _)
    rw [lintegral_add_left (hum.pow_const 2)]
    exact ENNReal.add_ne_top.2 ⟨hu2, hw2⟩
  refine ne_top_of_le_ne_top ?_ step1
  refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (mul_ne_zero M.δ_pos.ne' hπ0.ne')) ?_)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨huu, huw⟩) step2

/-! ### Lemma 17.5.2 (ii) -/

/-- **Lemma 17.5.2 (ii)** (MT p. 451), the moment bound (17.53): under the CLT moment condition
((V3) with `f ≥ 1`, `V` finite, `C` petite, `π(V²) < ∞`) for an ergodic chain, every split
`m`-skeleton (any minorization of `Pᵐ`, `m ≥ 1`, on a set `C ∈ B⁺(X)`) has
`Ě_{ν*}[s₋₁(f)²] < ∞`, the second moment of the cycle sum (17.22) of `f`; hence the CLT moment
condition (17.31) holds for every `g` with `|g| ≤ f`. -/
theorem lemma_17_5_2_ii [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ)
    (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) [NeZero m]
    (M : Minorization (P ^ m)) (hψC : 0 < ψ M.C) :
    ∫⁻ ω, skelPreSumE M f ω ^ 2 ∂skelFreshLaw M ≠ ∞ ∧
      ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
        MemLp (skelPreSum M fun x => |g x|) 2 (skelFreshLaw M) ∧
          MemLp (fun ω => (hitNat (skelAtom M) ω : ℝ)) 2 (skelFreshLaw M) := by
  have := isMarkovKernel_pow P m
  have := M.isProbabilityMeasure_ν
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hHm := (theorem_9_1_6 hph.1.1 hap).1 hph.1 m hm
  obtain ⟨C', b', hsmall, hb', hd'⟩ := driftV3_skeleton hph.1.1 hap hV hf hf1 hb hpet hdrift hm
  have hC' : IsPetite (P ^ m : Kernel X X) C' := by
    obtain ⟨m', ν', hs⟩ := hsmall
    exact ⟨_, _, proposition_5_5_3 hs⟩
  have hfV : ∀ x, f x ≤ V x + b := fun x => le_add_self.trans ((hdrift x).trans
    (add_le_add le_rfl (Set.indicator_le (g := fun _ => b) (fun _ _ => le_rfl) x)))
  have hπV : ∫⁻ x, V x ∂π ≠ ∞ := lintegral_ne_top_of_sq hπV2
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hfV)
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨hπV, hb⟩
  have hπf2 : ∫⁻ x, f x ^ 2 ∂π ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => pow_le_pow_left' (hfV x) 2)
    refine lintegral_sq_add_ne_top hV hπV2 ?_
    rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.pow_ne_top hb
  -- the function `F = f^{(m)}/2` of the skeleton drift
  set F : X → ℝ≥0∞ := fun x => 2⁻¹ * fSkel P m f x with hFdef
  have hF : Measurable F := (measurable_fSkel P m hf).const_mul _
  have hπF : ∫⁻ x, F x ∂π ≠ ∞ := by
    rw [hFdef, lintegral_const_mul _ (measurable_fSkel P m hf)]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 two_ne_zero) ?_
    unfold fSkel
    rw [lintegral_finsetSum _ fun i _ => hf.lintegral_kernel]
    refine ENNReal.sum_ne_top.2 fun i _ => ?_
    have := isMarkovKernel_pow P i
    rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
    change ∫⁻ y, f y ∂((P ^ i) ∘ₘ π) ≠ ∞
    rw [hπ.pow i]; exact hπf
  -- `ν(f) < ∞`
  obtain ⟨c₀, hc₀⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hνf : ∫⁻ y, f y ∂M.ν ≠ ∞ := by
    have h1 : M.δ * ∫⁻ y, f y ∂M.ν ≤ ∫⁻ y, f y ∂(P ^ m : Kernel X X) c₀ :=
      calc M.δ * ∫⁻ y, f y ∂M.ν = ∫⁻ y, f y ∂(M.δ • M.ν) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ _ := lintegral_mono' (M.le c₀ hc₀) le_rfl
    have h2 : ∫⁻ y, V y ∂(P ^ m : Kernel X X) c₀ ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (le_self_add.trans (driftV3_iterate hV
        (by obtain ⟨_, _, hP⟩ := hpet; exact hP.1) hdrift m c₀))
      refine ENNReal.add_ne_top.2 ⟨hVfin c₀, ENNReal.mul_ne_top hb (ENNReal.sum_ne_top.2
        fun i _ => ?_)⟩
      have := isMarkovKernel_pow P i
      exact measure_ne_top _ _
    have h3 : ∫⁻ y, f y ∂(P ^ m : Kernel X X) c₀ ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hfV)
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_ne_top.2 ⟨h2, hb⟩
    intro htop
    rw [htop, ENNReal.mul_top M.δ_pos.ne'] at h1
    exact h3 (top_le_iff.1 h1)
  -- the block means
  set c₁ : ℝ≥0∞ := 1 + M.δ⁻¹ + (1 - M.δ)⁻¹ with hc₁
  have hc₁t : c₁ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.inv_ne_top.2 M.δ_pos.ne'⟩, ENNReal.inv_ne_top.2 M.one_sub_δ_ne_zero⟩
  have hblock : ∀ z : X × Bool, blockMeanE M f z ≤ (2 * (c₁ + m * ∫⁻ y, f y ∂M.ν)) * F z.1 := by
    intro z
    have hfs1 : 1 ≤ fSkel P m f z.1 := by
      refine (hf1 z.1).trans ?_
      have h0 : f z.1 = ∫⁻ y, f y ∂(P ^ 0 : Kernel X X) z.1 := by
        rw [pow_zero_apply, lintegral_dirac' _ hf]
      rw [h0, fSkel]
      exact Finset.single_le_sum (f := fun i => ∫⁻ y, f y ∂(P ^ i : Kernel X X) z.1)
        (fun _ _ => zero_le) (Finset.mem_range.2 (NeZero.pos m))
    have e : (2 * (c₁ + m * ∫⁻ y, f y ∂M.ν)) * F z.1 =
        (c₁ + m * ∫⁻ y, f y ∂M.ν) * fSkel P m f z.1 := by
      rw [hFdef]
      simp only
      rw [mul_comm 2, mul_assoc, ← mul_assoc 2, ENNReal.mul_inv_cancel two_ne_zero
        ENNReal.ofNat_ne_top, one_mul]
    rw [e, add_mul]
    exact (blockMeanE_le M hf z).trans (add_le_add le_rfl (le_mul_of_one_le_right zero_le hfs1))
  have hA₁ : 2 * (c₁ + m * ∫⁻ y, f y ∂M.ν) ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.2 ⟨hc₁t, ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hνf⟩)
  obtain ⟨A, B, hA, hB, hh⟩ := lintegral_skelPreSumE_pathKernel_le M hHm hψC hπ hf hV hVfin hF
    hb' hC' hd' hπF hA₁ hblock
  have hS2 := lintegral_sq_skelPreSumE_ne_top M hph.1.1 hHm hψC hπ hf hπf2 hV hπV2 hA hB hh
  refine ⟨hS2, fun g hgm hgf => ⟨?_, ?_⟩⟩
  · have hgE : Measurable fun x => ENNReal.ofReal |g x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hgm)
    have e : skelPreSum M (fun x => |g x|) =
        fun ω => (skelPreSumE M (fun x => ENNReal.ofReal |g x|) ω).toReal := funext fun ω => by
      rw [← ofReal_skelPreSum M (fun x => abs_nonneg _),
        ENNReal.toReal_ofReal (show 0 ≤ skelPreSum M (fun x => |g x|) ω from
          Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    rw [e]
    refine memLp_toReal_of_lintegral_sq (measurable_skelPreSumE M hgE)
      (ne_top_of_le_ne_top hS2 (lintegral_mono fun ω => pow_le_pow_left' ?_ 2))
    exact Finset.sum_le_sum fun t _ => hgf _
  · have e : (fun ω => (hitNat (skelAtom M) ω : ℝ)) =
        fun ω => ((hitNat (skelAtom M) ω : ℝ≥0∞)).toReal :=
      funext fun ω => (ENNReal.toReal_natCast _).symm
    rw [e]
    refine memLp_toReal_of_lintegral_sq
      (measurable_from_nat.comp (measurable_hitNat (measurableSet_skelAtom M)))
      (ne_top_of_le_ne_top hS2 (lintegral_mono fun ω => pow_le_pow_left' ?_ 2))
    have h1 : (Finset.range (m * (hitNat (skelAtom M) ω + 1))).card • (1 : ℝ≥0∞) ≤
        skelPreSumE M f ω :=
      Finset.card_nsmul_le_sum _ _ _ fun t _ => hf1 _
    rw [Finset.card_range, nsmul_eq_mul, mul_one] at h1
    refine le_trans ?_ h1
    exact_mod_cast (show hitNat (skelAtom M) ω ≤ m * (hitNat (skelAtom M) ω + 1) by
      nlinarith [NeZero.pos m])

/-! ### The LIL of Theorems 17.5.3, 17.5.4 and 17.0.1 (iv) -/

/-- **(17.32) is the variance of Theorem 17.5.3**: under the CLT moment condition and `|g| ≤ f`,
for every split `m`-skeleton (any minorization of `Pᵐ`, `m ≥ 1`, on `C ∈ B⁺(X)`) the variance
(17.32) of the cycle sums equals `γ_g² = π(ĝ² − (Pĝ)²)` (the two CLTs along `n^{−1/2} Sₙ(ḡ)` have
the same limit). -/
theorem skelCLTVariance_eq_poissonVariance [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x) [NeZero m] (M : Minorization (P ^ m))
    (hψC : 0 < ψ M.C) :
    skelCLTVariance M π g =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_pathKernel P
  have hHm := (theorem_9_1_6 hph.1.1 hap).1 hph.1 m (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))
  obtain ⟨hg2, hT2⟩ := (lemma_17_5_2_ii hph hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 M
    hψC).2 g hgm hgf
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at this
    exact zero_ne_one this
  have hvar1 := skelCLTVariance_nonneg M hHm hψC hπ hgm hg2 hT2
  have hvar2 := (theorem_17_5_3 hph.1.1 hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 hgm
    hgf).2.2.1
  have hclt1 := theorem_17_3_6_general M hHm hψC hπ hgm hg2 hT2 (Z' := id) HasLaw.id
    (Measure.dirac x₀)
  have hclt2 := theorem_17_5_3_clt hph hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 hgm hgf
    (Z := id) HasLaw.id x₀
  have := isProbabilityMeasure_pathMeasure P (Measure.dirac x₀)
  have heq := eq_of_tendstoInDistribution_gaussianReal (pathMeasure_dirac P x₀) hclt1 hclt2
  have := congrArg (fun v : NNReal => (v : ℝ)) heq
  simpa only [Real.coe_toNNReal _ hvar1, Real.coe_toNNReal _ hvar2] using this

/-- **Theorem 17.5.3**, the LIL (MT p. 452), by the book's route (Lemma 17.5.2 (ii) and Theorem
17.3.6 for a split `m`-skeleton): for an ergodic chain under the CLT moment condition and
`|g| ≤ f`, `Sₙ(ḡ)` obeys the LIL with constant `γ_g = π(ĝ² − (Pĝ)²)^{1/2}` almost surely from
every initial state. No minorization is assumed. -/
theorem theorem_17_5_3_lil_skeleton [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x) :
    ∀ x, ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) := by
  obtain ⟨m, hm, M, hψC, -, hHm⟩ := exists_skeleton_split hph.1 hap
  have : NeZero m := ⟨by omega⟩
  obtain ⟨hg2, hT2⟩ := (lemma_17_5_2_ii hph hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2 M
    hψC).2 g hgm hgf
  have hvar := skelCLTVariance_eq_poissonVariance hph hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2
    hgm hgf M hψC
  intro x
  have hlil := theorem_17_3_6_lil_general M hHm hψC hπ hgm hg2 hT2 (Measure.dirac x)
  rw [pathMeasure_dirac, hvar] at hlil
  exact hlil

/-- **Theorem 17.5.4**, the LIL (MT p. 453), by the book's route: for an ergodic chain with (V4)
for `V ≥ 1` finite and a petite set (`V`-uniform ergodicity) and `g² ≤ V`, `Sₙ(ḡ)` obeys the LIL
with constant `γ_g = π(ĝ² − (Pĝ)²)^{1/2}` almost surely from every initial state. -/
theorem theorem_17_5_4_lil_skeleton [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) :
    ∀ x, ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) := by
  obtain ⟨ρ', b', C', hρ', hb', hC', h3, hπV2⟩ := lemma_17_5_1 hph.1.1 hap hV hV1 hVfin hρ hb
    hC h hπ
  have hct : (1 - ρ')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne'
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    simpa using ENNReal.rpow_le_rpow (hV1 x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact theorem_17_5_3_lil_skeleton hph hap hWm hW1 hC' (hWm.const_mul _) (fun x =>
    ENNReal.mul_ne_top hct (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hVfin x)))
    (ENNReal.mul_ne_top hct hb') h3 hπ hπV2 hgm (ofReal_abs_le_sqrt hg)

/-- **Theorem 17.0.1 (iv)**, the LIL (MT p. 422), by the book's route: under the hypotheses of
Theorem 17.0.1 (ii) (an ergodic chain with (V4) for `V ≥ 1` finite and a petite set, `g² ≤ V`),
`Sₙ(ḡ)` obeys the LIL with constant `γ_g`, `γ_g²` the series (17.3), almost surely from every
initial state. -/
theorem theorem_17_0_1_iv_lil_skeleton [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) :
    ∀ x, ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(asymptoticVariance P π g)) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := theorem_17_5_4 hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg
  have heq : asymptoticVariance P π g =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := h6.symm
  rw [heq]
  exact theorem_17_5_4_lil_skeleton hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg

end MeynTweedie.LimitTheorems
