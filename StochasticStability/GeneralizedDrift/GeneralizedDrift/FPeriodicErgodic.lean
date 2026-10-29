/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.FNormErgodicTheorem

/-!
# `f`-norm convergence for periodic chains (MT Theorem 14.3.6)

Meyn and Tweedie, Theorem 14.3.6, p. 351. The book states the theorem without proof. For a chain
of period `d` with a `d`-cycle `{Dᵢ}` and invariant probability `π`, write
`πᵢ = d π(· ∩ Dᵢ)` (`cycleInv π D i`) and `f^{(d)} = Σ_{r<d} Pʳf` (`fSkel P d f`).

**The chain on a cycle class.** `absorbKernel (Pᵈ) Dᵢ πᵢ` moves by `Pᵈ` on `Dᵢ` and jumps to `πᵢ`
off `Dᵢ` (MT Theorem 13.3.4).
* `IsCycle.absorbKernel_isPositiveHarris`: for a positive Harris chain it is positive Harris and
  aperiodic, with invariant probability `πᵢ` (the argument of `IsCycle.tendsto_tvNorm_pow_mul`).
* `IsCycle.fRegular_absorbKernel`: its `f^{(d)}`-regular states are `ψ`-almost all of `Dᵢ`, and
  from such a state `x ∈ Dᵢ`, `‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0` for every `r < d`
  (Theorem 14.3.3 for the restricted chain, then `‖λPʳ − σPʳ‖_f ≤ ‖λ − σ‖_{Pʳf}`).
* `fSumReturn_eq_add_tabooPotFn`: `E_x[Σ_{k<τ_B} f(Φ_k)] = f(x) + U_B(x, f 1_{Bᶜ})`;
  `fSumReturn_absorbKernel_of_mem`: these sums only depend on the chain inside an absorbing set.
* `IsCycle.fSumReturn_skeleton_le`: for `x ∈ Dᵢ` and `B ⊆ Dᵢ`,
  `E^{(d)}_x[Σ_{j<τ_B^{(d)}} f^{(d)}(Φ_{dj})] ≤ E_x[Σ_{k<τ_B} f(Φ_k)]`, since from `Dᵢ` the chain
  can visit `B` only at multiples of `d` (the reverse of `fSumReturn_le_skeleton`).
* `fNorm_smul_sum_le`: `‖c Σ μᵣ − c Σ νᵣ‖_f ≤ c Σ ‖μᵣ − νᵣ‖_f`.

**Results.**
* **Theorem 14.3.6 (i)** (`theorem_14_3_6_i`, p. 351), (14.26): for a positive recurrent chain
  with `π(f) < ∞`, `f ≥ 1`, there are the period `d`, a `d`-cycle `{Dᵢ}`, a full set `S_f` and
  probabilities `πᵢ` with `‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0` for `x ∈ Dᵢ ∩ S_f` and `r < d`.
* **Theorem 14.3.6 (ii)** (`theorem_14_3_6_ii`, p. 351), (14.27): for an `f`-regular chain of
  period `d` and every `d`-cycle, `‖d⁻¹ Σ_{r<d} P^{nd+r}(x, ·) − π‖_f → 0` for every `x` in the
  cycle `⋃ Dᵢ` (a full set).

**Deviations from the book.**
* (i): the book asks for the cycle to lie inside `S_f`; here the convergence holds on
  `Dᵢ ∩ S_f`, which is all of `Dᵢ` up to a `ψ`-null set. The book's limit for `x ∈ D_r` at the
  times `nd + r` is `π_{2r}` in the natural labelling `πᵢ = d π(· ∩ Dᵢ)`; the statement here gives
  the limit for every class and every phase `r < d`, which contains (14.26).
* (ii): the book claims (14.27) for every `x`; it is proved here for every `x` in the cycle
  `⋃ Dᵢ`, whose complement is `ψ`-null. Points of the null set `(⋃ Dᵢ)ᶜ` are not covered.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The chain on a cycle class -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The chain on a cycle class** (MT Theorem 13.3.4): for a positive Harris chain of period `d`
with `d`-cycle `{Dᵢ}`, the chain that moves by `Pᵈ` on `Dᵢ` and jumps to `πᵢ = d π(· ∩ Dᵢ)` off
`Dᵢ` is positive Harris and aperiodic for `ψ` restricted to `Dᵢ`, with invariant probability
`πᵢ`. The argument is that of `IsCycle.tendsto_tvNorm_pow_mul`. -/
theorem IsCycle.absorbKernel_isPositiveHarris {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} {d : ℕ} {D : ZMod d → Set X} (hd : 0 < d) (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hph : IsPositiveHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (i : ZMod d) :
    haveI := isMarkovKernel_pow P d
    haveI := hD.isProbabilityMeasure_cycleInv hd (proposition_10_1_1 hph.2) hπ i
    haveI := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i)
      (cycleInv π D i)
    IsPositiveHarris (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
        (ψ.restrict (D i)) ∧
      IsAperiodic (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
        (ψ.restrict (D i)) ∧
      IsInvariant (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
        (cycleInv π D i) := by
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
  exact ⟨⟨hHK, hposK⟩, hapK, hσinv⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **`f`-norm convergence on a cycle class.** For a positive Harris chain of period `d` with
`d`-cycle `{Dᵢ}`, invariant probability `π`, `f ≥ 1` and `π(f) < ∞`: the `f^{(d)}`-regular states
of the chain on `Dᵢ` are `ψ`-almost all of `Dᵢ`, and from such a state `x ∈ Dᵢ`,
`‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0` for every `r < d`. -/
theorem IsCycle.fRegular_absorbKernel {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {d : ℕ} {D : ZMod d → Set X} (hd : 0 < d) (hD : IsCycle P ψ d D) (hper : IsPeriod P ψ d)
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞)
    (i : ZMod d) :
    haveI := isMarkovKernel_pow P d
    haveI := hD.isProbabilityMeasure_cycleInv hd (proposition_10_1_1 hph.2) hπ i
    haveI := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i)
      (cycleInv π D i)
    IsFull (ψ.restrict (D i)) {x | IsFRegularState
        (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
        (ψ.restrict (D i)) (fSkel P d f) x} ∧
      ∀ x ∈ D i, IsFRegularState
        (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
        (ψ.restrict (D i)) (fSkel P d f) x →
        ∀ r < d, Tendsto (fun n => fNorm f ((P ^ (d * n + r) : Kernel X X) x)
          (cycleInv π D (i + r))) atTop (𝓝 0) := by
  have := isMarkovKernel_pow P d
  have hrec := proposition_10_1_1 hph.2
  have hσp := hD.isProbabilityMeasure_cycleInv hd hrec hπ
  have := hσp i
  have := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i)
  obtain ⟨hphK, hapK, hσinv⟩ := hD.absorbKernel_isPositiveHarris hd hper hph hπ i
  have hf' := measurable_fSkel P d hf
  have hf'1 := one_le_fSkel P hd hf hf1
  -- `πᵢ(f^{(d)}) ≤ d π(f^{(d)}) = d² π(f) < ∞`
  have hσf : ∫⁻ x, fSkel P d f x ∂cycleInv π D i ≠ ∞ := by
    rw [cycleInv, lintegral_smul_measure]
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ne_top_of_le_ne_top ?_
      (lintegral_mono' Measure.restrict_le_self le_rfl))
    rw [lintegral_fSkel P hπ d hf]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) hπf
  obtain ⟨hfull, -, hconv⟩ := theorem_14_3_3_ii hphK.2 hapK hσinv hf' hf'1 hσf
  refine ⟨hfull, fun x hx hreg r hr => ?_⟩
  have h := hconv x hreg
  have hQ := hD.pow_d_compl_eq_zero i
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => ?_
  have := isMarkovKernel_pow P r
  have := isMarkovKernel_pow P (d * n)
  have e1 : (P ^ (d * n + r) : Kernel X X) x =
      (P ^ r : Kernel X X) ∘ₘ (P ^ (d * n) : Kernel X X) x := by
    rw [add_comm, pow_add]; rfl
  have e2 : (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i) ^ n :
      Kernel X X) x = (P ^ (d * n) : Kernel X X) x := by
    rw [absorbKernel_pow_of_mem (hD.measurableSet i) hQ n x hx, ← pow_mul]
  change fNorm f ((P ^ (d * n + r) : Kernel X X) x) (cycleInv π D (i + r)) ≤
    fNorm (fSkel P d f) ((absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i)
      (cycleInv π D i) ^ n : Kernel X X) x) (cycleInv π D i)
  rw [e1, e2, ← hD.comp_pow_cycleInv hd hπ r i]
  exact (fNorm_comp_le (P ^ r) f _ _).trans
    (fNorm_mono (fun y => lintegral_pow_le_fSkel P hr f y) _ _)

/-! ### Theorem 14.3.6 (i) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.6 (i)** (MT p. 351), (14.26): if the chain is positive recurrent with
invariant probability `π`, `f ≥ 1` and `π(f) < ∞`, then for its period `d` there are a `d`-cycle
`{Dᵢ}` and a full set `S_f` such that the probabilities `πᵢ = d π(· ∩ Dᵢ)` satisfy
`‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0` for every class `i`, phase `r < d` and `x ∈ Dᵢ ∩ S_f`. -/
theorem theorem_14_3_6_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ d : ℕ, IsPeriod P ψ d ∧ ∃ D : ZMod d → Set X, IsCycle P ψ d D ∧
      (∀ i, IsProbabilityMeasure (cycleInv π D i)) ∧ ∃ S : Set X, IsFull ψ S ∧
        ∀ i : ZMod d, ∀ r < d, ∀ x ∈ D i ∩ S,
          Tendsto (fun n => fNorm f ((P ^ (d * n + r) : Kernel X X) x) (cycleInv π D (i + r)))
            atTop (𝓝 0) := by
  have hrec := proposition_10_1_1 hpos
  obtain ⟨H, hHmax, -, hHnull⟩ := theorem_9_1_5 hrec
  have hHm := hHmax.1
  have := isMarkovKernel_absorbKernel P hHm π
  obtain ⟨hph', hinv', hperK⟩ := absorbKernel_maximalHarris hpos hπ hHmax hHnull
  set P' := absorbKernel P hHm π with hP'
  have hQH : ∀ x ∈ H, P x Hᶜ = 0 := fun x hx =>
    (prob_compl_eq_zero_iff hHm).2 (hHmax.2.2.1 x hx)
  have hac := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hπH : π Hᶜ = 0 := hac.1 hHnull
  obtain ⟨d, hper⟩ := exists_isPeriod P hpos.1
  have hd := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hper' := hperK d hper
  obtain ⟨D, hD⟩ := hper'.2.1
  -- the cycle of `P` inside the maximal Harris set
  set E : ZMod d → Set X := fun i => D i ∩ H with hE
  have hEm : ∀ i, MeasurableSet (E i) := fun i => (hD.measurableSet i).inter hHm
  have hEcyc : IsCycle P ψ d E := by
    refine ⟨hEm, fun i j hij => (hD.disjoint i j hij).mono inter_subset_left inter_subset_left,
      fun i x hx => ?_, ?_⟩
    · have h1 : P x (D (i + 1)) = 1 := by
        have h := hD.step i x hx.1
        rwa [hP', absorbKernel_of_mem P hHm π hx.2] at h
      have hc : P x (D (i + 1) ∩ H)ᶜ = 0 := by
        rw [compl_inter]
        exact measure_union_null ((prob_compl_eq_zero_iff (hD.measurableSet _)).2 h1)
          (hQH x hx.2)
      exact (prob_compl_eq_zero_iff (hEm _)).1 hc
    · refine measure_mono_null (fun y hy => ?_) (measure_union_null hD.null_compl hHnull)
      by_cases hyH : y ∈ H
      · refine Or.inl fun hyD => hy ?_
        obtain ⟨j, hj⟩ := mem_iUnion.1 hyD
        exact mem_iUnion.2 ⟨j, hj, hyH⟩
      · exact Or.inr hyH
  -- the limits are the same for both cycles
  have hinvE : ∀ j, cycleInv π E j = cycleInv π D j := fun j => by
    rw [cycleInv, cycleInv]
    congr 1
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    refine le_antisymm (measure_mono (inter_subset_inter_right _ inter_subset_left)) ?_
    rw [← measure_inter_add_sdiff (B ∩ D j) hHm]
    have h0 : π ((B ∩ D j) \ H) = 0 := measure_mono_null (fun y hy => hy.2) hπH
    rw [h0, add_zero]
    exact measure_mono fun y hy => ⟨hy.1.1, hy.1.2, hy.2⟩
  have hσp := hD.isProbabilityMeasure_cycleInv hd (proposition_10_1_1 hph'.2) hinv'
  -- the regular states of the chains on the classes
  have hreg := fun i => hD.fRegular_absorbKernel hd hper' hph' hinv' hf hf1 hπf i
  set T : ZMod d → Set X := fun i => {x | haveI := isMarkovKernel_pow P' d
    haveI := hσp i
    haveI := isMarkovKernel_absorbKernel (P' ^ d : Kernel X X) (hD.measurableSet i)
      (cycleInv π D i)
    IsFRegularState (absorbKernel (P' ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
      (ψ.restrict (D i)) (fSkel P' d f) x} with hT
  refine ⟨d, hper, E, hEcyc, fun j => by rw [hinvE j]; exact hσp j,
    H ∩ {x | ∀ i, x ∈ D i → x ∈ T i}, ?_, fun i r hr x hx => ?_⟩
  · -- the set is full
    have hnull : ∀ i, ψ (D i ∩ (T i)ᶜ) = 0 := fun i => by
      have h := (hreg i).1
      unfold IsFull at h
      rw [Measure.restrict_apply' (hD.measurableSet i)] at h
      rw [inter_comm]
      exact h
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null hHnull (measure_iUnion_null hnull))
    by_cases hyH : y ∈ H
    · refine Or.inr (mem_iUnion.2 ?_)
      by_contra hall
      push Not at hall
      refine hy ⟨hyH, fun i hyi => ?_⟩
      by_contra hyT
      exact hall i ⟨hyi, hyT⟩
    · exact Or.inl hyH
  · obtain ⟨⟨hxD, hxH⟩, -, hxT⟩ := hx
    have h := (hreg i).2 x hxD (hxT i hxD) r hr
    rw [hinvE]
    refine h.congr fun n => ?_
    rw [hP', absorbKernel_pow_of_mem hHm hQH (d * n + r) x hxH]

/-! ### Return sums inside an absorbing set -/

omit [MeasurableSpace X] in
/-- Pathwise, `Σ_{k<τ_B} f(Φ_k) = f(Φ₀) + Σ_{k<τ_B} (f 1_{Bᶜ})(Φ_{k+1})`: before the return time
the chain is outside `B`, and at the return time it is in `B`. -/
theorem sumBefore_firstReturn_eq_add (B : Set X) (f : X → ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (firstReturn B) (fun k ω => f (ω k)) ω =
      f (ω 0) + sumBefore (firstReturn B) (fun k ω => Bᶜ.indicator f (ω (k + 1))) ω := by
  unfold sumBefore
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine congrArg₂ (· + ·) ?_ ?_
  · have h0 : ((0 : ℕ) : WithTop ℕ) < firstReturn B ω :=
      lt_of_lt_of_le (by rw [Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 one_pos)
        (one_le_firstReturn B ω)
    exact indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : WithTop ℕ) < firstReturn B ω} from h0) _
  · refine tsum_congr fun k => ?_
    by_cases hk1 : ((k + 1 : ℕ) : WithTop ℕ) < firstReturn B ω
    · have hk : (k : WithTop ℕ) < firstReturn B ω :=
        lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) hk1
      rw [indicator_of_mem
          (show ω ∈ {ω | ((k + 1 : ℕ) : WithTop ℕ) < firstReturn B ω} from hk1),
        indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn B ω} from hk)]
      have hle : WithTop.some (k + 2) ≤ firstReturn B ω := by
        cases h : firstReturn B ω with
        | top => exact le_top
        | coe t =>
          rw [h] at hk1
          have : k + 1 < t := WithTop.coe_lt_coe.1 hk1
          exact WithTop.coe_le_coe.2 (by omega)
      have hnot : ω (k + 1) ∉ B := (le_firstReturn_iff B ω (k + 2)).1 hle (k + 1) (by omega)
        (by omega)
      exact (indicator_of_mem (show ω (k + 1) ∈ Bᶜ from hnot) f).symm
    · rw [indicator_of_notMem
        (show ω ∉ {ω | ((k + 1 : ℕ) : WithTop ℕ) < firstReturn B ω} from hk1)]
      by_cases hk : (k : WithTop ℕ) < firstReturn B ω
      · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn B ω} from hk)]
        -- the return happens at `k + 1`
        have heq : firstReturn B ω = WithTop.some (k + 1) := by
          cases h : firstReturn B ω with
          | top => rw [h] at hk1; exact absurd (WithTop.coe_lt_top _) hk1
          | coe t =>
            rw [h] at hk1 hk
            have h1 : ¬ k + 1 < t := fun h' => hk1 (WithTop.coe_lt_coe.2 h')
            have h2 : k < t := WithTop.coe_lt_coe.1 hk
            exact congrArg WithTop.some (by omega)
        have hmem : ω (k + 1) ∈ B := mem_of_firstReturn_eq heq
        exact (indicator_of_notMem (show ω (k + 1) ∉ Bᶜ from fun h => h hmem) f).symm
      · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstReturn B ω} from hk)]

/-- `E_x[Σ_{k<τ_B} f(Φ_k)] = f(x) + U_B(x, f 1_{Bᶜ})`. -/
theorem fSumReturn_eq_add_tabooPotFn (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    fSumReturn P B f x = f x + tabooPotFn P B (Bᶜ.indicator f) x := by
  have := isMarkovKernel_pathKernel P
  have hm : Measurable (sumBefore (firstReturn B) fun k (ω : ℕ → X) =>
      Bᶜ.indicator f (ω (k + 1))) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hB)
      fun k => (hf.indicator hB.compl).comp (measurable_pi_apply (k + 1))
  rw [fSumReturn, lintegral_congr (sumBefore_firstReturn_eq_add B f),
    lintegral_add_right _ hm, lintegral_coord_zero P x hf, tabooPotFn]

/-- The taboo potentials of `absorbKernel Q H σ` and `Q` agree on the absorbing set `H`. -/
theorem tabooPotFn_absorbKernel_of_mem {Q : Kernel X X} [IsMarkovKernel Q] {H : Set X}
    (hH : MeasurableSet H) (hQ : ∀ x ∈ H, Q x Hᶜ = 0) (σ : Measure X) [IsProbabilityMeasure σ]
    {A : Set X} (hA : MeasurableSet A) {g : X → ℝ≥0∞} (hg : Measurable g) {x : X}
    (hx : x ∈ H) :
    haveI := isMarkovKernel_absorbKernel Q hH σ
    tabooPotFn (absorbKernel Q hH σ) A g x = tabooPotFn Q A g x := by
  have := isMarkovKernel_absorbKernel Q hH σ
  rw [← lintegral_tabooPotKernel _ hA hg x, ← lintegral_tabooPotKernel _ hA hg x, tabooPotKernel,
    tabooPotKernel, Kernel.sum_apply, Kernel.sum_apply, lintegral_sum_measure,
    lintegral_sum_measure]
  exact tsum_congr fun n => by rw [tabooKernel_absorbKernel_of_mem hH hQ hA n x hx]

/-- The return sums of `absorbKernel Q H σ` and `Q` agree on the absorbing set `H`. -/
theorem fSumReturn_absorbKernel_of_mem {Q : Kernel X X} [IsMarkovKernel Q] {H : Set X}
    (hH : MeasurableSet H) (hQ : ∀ x ∈ H, Q x Hᶜ = 0) (σ : Measure X) [IsProbabilityMeasure σ]
    {B : Set X} (hB : MeasurableSet B) {g : X → ℝ≥0∞} (hg : Measurable g) {x : X}
    (hx : x ∈ H) :
    haveI := isMarkovKernel_absorbKernel Q hH σ
    fSumReturn (absorbKernel Q hH σ) B g x = fSumReturn Q B g x := by
  have := isMarkovKernel_absorbKernel Q hH σ
  rw [fSumReturn_eq_add_tabooPotFn _ hB hg, fSumReturn_eq_add_tabooPotFn _ hB hg,
    tabooPotFn_absorbKernel_of_mem hH hQ σ hB (hg.indicator hB.compl) hx]

/-! ### The skeleton on a cycle class -/

/-- **The skeleton on a cycle class**: for a `d`-cycle `{Dᵢ}`, `x ∈ Dᵢ` and `B ⊆ Dᵢ`,
`E^{(d)}_x[Σ_{j<τ_B^{(d)}} f^{(d)}(Φ_{dj})] ≤ E_x[Σ_{k<τ_B} f(Φ_k)]`: from `Dᵢ` the chain is in
`D_{i+t}` at time `t` almost surely, so it can visit `B` only at multiples of `d`, and
`d τ_B^{(d)} ≤ τ_B`. -/
theorem IsCycle.fSumReturn_skeleton_le {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {d : ℕ} {D : ZMod d → Set X} (hd : 0 < d) (hD : IsCycle P ψ d D) {i : ZMod d} {B : Set X}
    (hB : MeasurableSet B) (hBD : B ⊆ D i) {f : X → ℝ≥0∞} (hf : Measurable f) {x : X}
    (hx : x ∈ D i) :
    haveI := isMarkovKernel_pow P d
    fSumReturn (P ^ d : Kernel X X) B (fSkel P d f) x ≤ fSumReturn P B f x := by
  have := isMarkovKernel_pow P d
  have := isMarkovKernel_pathKernel P
  have hm : 1 ≤ d := hd
  set s : (ℕ → X) → (ℕ → X) := fun ω n => ω (d * n) with hsdef
  have hs : Measurable s := measurable_pi_iff.2 fun n => measurable_pi_apply (d * n)
  have hGm : ∀ j : ℕ, MeasurableSet {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B (s ω)} :=
    fun j => (natFilt (X := X)).le _ _ (measurableSet_natFilt_lt_firstReturn_skeleton hB d j)
  -- the left side on the original path space
  have hR : fSumReturn (P ^ d : Kernel X X) B (fSkel P d f) x =
      ∑' j : ℕ, ∑ r ∈ range d, ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
        f (ω (d * j + r)) ∂pathKernel P x := by
    have hcomp : ∀ a : ℕ → X, sumBefore (firstReturn B) (fun k ω => fSkel P d f (ω k)) (s a) =
        sumBefore (fun ω => firstReturn B (s ω)) (fun k ω => fSkel P d f (s ω k)) a := fun a => by
      simp only [sumBefore, Set.indicator_apply, mem_ofPred_eq]
    rw [fSumReturn, ← pathKernel_map_skeleton P d x,
      lintegral_map (measurable_sumBefore_firstReturn hB (measurable_fSkel P d hf)) hs,
      lintegral_congr hcomp, lintegral_sumBefore _ (fun j => hGm j)
        (F := fun k ω => fSkel P d f (s ω k)) fun j => (measurable_fSkel P d hf).comp
        ((measurable_pi_apply j).comp hs)]
    refine tsum_congr fun j => ?_
    simp only [fSkel, hsdef]
    rw [lintegral_finsetSum (f := fun r (ω : ℕ → X) => ∫⁻ y, f y ∂(P ^ r : Kernel X X) (ω (d * j)))
      _ fun r _ => hf.lintegral_kernel.comp (measurable_pi_apply (d * j))]
    refine Finset.sum_congr rfl fun r _ => ?_
    -- the Markov property at time `dj`
    have hmk := markov_lintegral P (Measure.dirac x)
      (measurableSet_natFilt_lt_firstReturn_skeleton hB d j) (H := fun ω : ℕ → X => f (ω r))
      (hf.comp (measurable_pi_apply r))
    rw [pathMeasure_dirac] at hmk
    rw [show (∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B fun n => ω (d * n)},
      f (ω (d * j + r)) ∂pathKernel P x) = ∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) <
        firstReturn B fun n => ω (d * n)}, f (shift (d * j) ω r) ∂pathKernel P x from rfl, hmk]
    refine setLIntegral_congr_fun (hGm j) fun ω _ => ?_
    rw [lintegral_coord_eq_pow P (ω (d * j)) r hf]
  -- almost every path follows the cycle
  have hae : ∀ᵐ ω ∂pathKernel P x, ∀ t : ℕ, ω t ∈ D (i + t) := by
    refine ae_all_iff.2 fun t => ae_iff.2 ?_
    have h1 : pathKernel P x {ω | ω t ∈ D (i + t)} = 1 := by
      rw [pathKernel_coord_mem P x t (hD.measurableSet _)]
      exact hD.pow_apply t hx
    exact (prob_compl_eq_zero_iff (measurable_pi_apply t (hD.measurableSet _))).2 h1
  rw [hR, fSumReturn, lintegral_sumBefore _ (measurableSet_lt_firstReturn hB)
    (F := fun k (ω : ℕ → X) => f (ω k)) fun k => hf.comp (measurable_pi_apply k),
    tsum_eq_tsum_sum_block (fun k : ℕ => ∫⁻ ω in {ω | (k : WithTop ℕ) < firstReturn B ω},
      f (ω k) ∂pathKernel P x) hm]
  refine ENNReal.tsum_le_tsum fun j => Finset.sum_le_sum fun r hr => ?_
  refine lintegral_mono_set' (hae.mono fun ω hω hj => ?_)
  have hr' : r < d := Finset.mem_range.1 hr
  simp only [mem_ofPred_eq] at hj ⊢
  by_contra hc
  push Not at hc
  -- the return time `t ≤ dj + r` is a multiple of `d`
  obtain ⟨t, ht⟩ : ∃ t : ℕ, firstReturn B ω = t := by
    cases h : firstReturn B ω with
    | top => rw [h] at hc; exact absurd (lt_of_le_of_lt hc (WithTop.coe_lt_top _)) (lt_irrefl _)
    | coe t => exact ⟨t, rfl⟩
  have htj : t ≤ d * j + r := by rw [ht] at hc; exact_mod_cast hc
  have ht1 : 1 ≤ t := by
    have := one_le_firstReturn B ω; rw [ht] at this; exact WithTop.coe_le_coe.1 this
  have hmem : ω t ∈ B := mem_of_firstReturn_eq ht
  have hii : i + t = i := by
    by_contra hne
    exact Set.disjoint_left.1 (hD.disjoint _ _ hne) (hω t) (hBD hmem)
  have hdvd : d ∣ t := (ZMod.natCast_eq_zero_iff t d).1 (by
    have h' : (i + (t : ZMod d)) - i = i - i := by rw [hii]
    rwa [add_sub_cancel_left, sub_self] at h')
  obtain ⟨t', rfl⟩ := hdvd
  have ht'1 : 1 ≤ t' := by
    rcases Nat.eq_zero_or_pos t' with h | h
    · rw [h, mul_zero] at ht1; omega
    · exact h
  have ht'j : t' ≤ j := by
    by_contra h
    push Not at h
    have : d * (j + 1) ≤ d * t' := Nat.mul_le_mul_left d h
    nlinarith
  have hle := firstReturn_le_of_mem (A := B) (ω := s ω) (j := t') ht'1 hmem
  have : (j : WithTop ℕ) < WithTop.some t' := lt_of_lt_of_le hj hle
  have : j < t' := WithTop.coe_lt_coe.1 this
  omega

/-! ### Phase averages in `f`-norm -/

/-- `‖c Σ μᵣ − c Σ νᵣ‖_f ≤ c Σ ‖μᵣ − νᵣ‖_f` for finite sums and `c < ∞`. -/
theorem fNorm_smul_sum_le {ι : Type*} (s : Finset ι) (f : X → ℝ≥0∞) (μ ν : ι → Measure X)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    fNorm f (c • ∑ r ∈ s, μ r) (c • ∑ r ∈ s, ν r) ≤ c * ∑ r ∈ s, fNorm f (μ r) (ν r) := by
  refine fNorm_le fun g hg => ?_
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul, zero_smul, integral_zero_measure, sub_self, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  have hμ := (integrable_finsetSum_measure.1 ((integrable_smul_measure hc0 hc).1 hg.2.2.1))
  have hν := (integrable_finsetSum_measure.1 ((integrable_smul_measure hc0 hc).1 hg.2.2.2))
  rw [integral_smul_measure, integral_smul_measure, integral_finsetSum_measure hμ,
    integral_finsetSum_measure hν, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hc, ← Finset.sum_sub_distrib]
  refine mul_le_mul' le_rfl ((ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun r _ => abs_nonneg _]
  exact Finset.sum_le_sum fun r hr => ofReal_abs_integral_sub_le_fNorm
    ⟨hg.1, hg.2.1, hμ r hr, hν r hr⟩

/-! ### Theorem 14.3.6 (ii) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.6 (ii)** (MT p. 351), (14.27): if the chain is `f`-regular, `f ≥ 1`, with
period `d`, invariant probability `π` and a `d`-cycle `{Dᵢ}`, then
`‖d⁻¹ Σ_{r<d} P^{nd+r}(x, ·) − π‖_f → 0` for every `x` in the cycle `⋃ Dᵢ`. -/
theorem theorem_14_3_6_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hreg : IsFRegularChain P ψ f) {d : ℕ} (hper : IsPeriod P ψ d) {D : ZMod d → Set X}
    (hD : IsCycle P ψ d D) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {x : X} (hx : x ∈ ⋃ i, D i) :
    Tendsto (fun n => fNorm f ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) x) π)
      atTop (𝓝 0) := by
  have hd := hper.1
  have hph : IsPositiveHarris P ψ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    exact IsRegularChain.isPositiveHarris hψ ⟨Cs, fun n => (hCs n).isRegularSet hf1, hcov⟩
  have hrec := proposition_10_1_1 hph.2
  have hπf := hreg.lintegral_ne_top hrec hf hf1 hπ
  obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
  have := isMarkovKernel_pow P d
  have := hD.isProbabilityMeasure_cycleInv hd hrec hπ i
  have := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i)
  have hQ := hD.pow_d_compl_eq_zero i
  -- `x` is `f^{(d)}`-regular for the chain on `Dᵢ`
  have hxreg : IsFRegularState
      (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) (cycleInv π D i))
      (ψ.restrict (D i)) (fSkel P d f) x := fun B hB hψB => by
    rw [Measure.restrict_apply hB] at hψB
    have hBD := hB.inter (hD.measurableSet i)
    refine ne_top_of_le_ne_top ?_ (fSumReturn_anti_set _ (inter_subset_left (t := D i)) _ x)
    rw [fSumReturn_absorbKernel_of_mem (hD.measurableSet i) hQ _ hBD
      (measurable_fSkel P d hf) hxi]
    refine ne_top_of_le_ne_top ?_ (hD.fSumReturn_skeleton_le hd hBD inter_subset_right hf hxi)
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
    exact (hCs m).isFRegularState hm _ hBD hψB
  have hconv := (hD.fRegular_absorbKernel hd hper hph hπ hf hf1 hπf i).2 x hxi hxreg
  have hsum : Tendsto (fun n => (d : ℝ≥0∞)⁻¹ * ∑ r ∈ range d,
      fNorm f ((P ^ (d * n + r) : Kernel X X) x) (cycleInv π D (i + r))) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (tendsto_finsetSum (range d) fun r hr =>
      hconv r (Finset.mem_range.1 hr)) (a := (d : ℝ≥0∞)⁻¹) (Or.inr (ENNReal.inv_ne_top.2
        (by exact_mod_cast hd.ne')))
    rw [Finset.sum_const_zero, mul_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => ?_
  change fNorm f ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) x) π ≤ _
  conv_lhs => rw [hD.eq_smul_sum_cycleInv hd hrec hπ i]
  exact fNorm_smul_sum_le (range d) f _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hd.ne'))

end MeynTweedie.GeneralizedDrift
