/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FPeriodicErgodic

/-!
# Theorem 14.2.11 without aperiodicity, through the lazy chain

Meyn and Tweedie, Theorem 14.2.11, p. 348: for a positive recurrent chain with `π(f) < ∞` there
are `f`-regular sets `S_f(n)` whose union is full. `theorem_14_2_11` (`FNormErgodic`) proves this
for aperiodic chains; here the aperiodicity is removed with the lazy chain `K = ½ (I + P)`
(`lazyKernel`), as Theorem 11.1.4 is proved in `RegularityConverse`.

* `sumBefore_firstHit_add_one_indicator`: pathwise, `Σ_{k ≤ σ_B} (f 1_{Bᶜ})(Φ_k) =
  Σ_{k < σ_B} f(Φ_k)`, so `G_B(·, f 1_{Bᶜ})` is the sum of `f` before the hitting time `σ_B`.
* `fSumReturn_eq_add_lintegral_gKernelFn`:
  `E_x[Σ_{k<τ_B} f(Φ_k)] = f(x) + ∫ P(x, dy) G_B(y, f 1_{Bᶜ})`;
  `gKernelFn_indicator_of_notMem`: `G_B(y, f 1_{Bᶜ}) = f(y) + P G_B(·, f 1_{Bᶜ})(y)` off `B`.
* `fSumReturn_le_lazy`: `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ E^K_x[Σ_{k<τ_B} f(Φ_k)]`. Off `B`,
  `W = ½ G^K_B(·, f 1_{Bᶜ})` solves `PW + f ≤ W`, so the Comparison Theorem bounds the sums of
  `P` before `σ_B` by `W`.
* `half_le_lazyKernel`: `K(x, A) ≥ ½` for `x ∈ A`;
  `isAperiodic_lazyKernel`: the lazy chain is aperiodic, since `K(x, {x}) ≥ ½` rules out cycles
  of length `d ≥ 2`.
* **Theorem 14.2.11** (`theorem_14_2_11_of_isPositive`, p. 348) for every positive chain.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- Pathwise, `Σ_{k ≤ σ_B} (f 1_{Bᶜ})(Φ_k) = Σ_{k < σ_B} f(Φ_k)`. -/
theorem sumBefore_firstHit_add_one_indicator (B : Set X) (f : X → ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (fun ω => firstHit B ω + 1) (fun k ω => Bᶜ.indicator f (ω k)) ω =
      sumBefore (firstHit B) (fun k ω => f (ω k)) ω := by
  unfold sumBefore
  refine tsum_congr fun k => ?_
  by_cases hk : (k : WithTop ℕ) < firstHit B ω
  · have hk1 : (k : WithTop ℕ) < firstHit B ω + 1 :=
      lt_of_lt_of_le hk le_self_add
    have hnot : ω k ∉ B := by
      have hle : WithTop.some (k + 1) ≤ firstHit B ω := by
        cases h : firstHit B ω with
        | top => exact le_top
        | coe t =>
          rw [h] at hk
          exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 hk)
      exact (le_firstHit_iff B ω (k + 1)).1 hle k (Nat.lt_succ_self k)
    rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstHit B ω + 1} from hk1),
      indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstHit B ω} from hk)]
    exact indicator_of_mem (show ω k ∈ Bᶜ from hnot) f
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstHit B ω} from hk)]
    by_cases hk1 : (k : WithTop ℕ) < firstHit B ω + 1
    · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstHit B ω + 1} from hk1)]
      -- the hitting time is `k`
      cases h : firstHit B ω with
      | top => rw [h] at hk; exact absurd (WithTop.coe_lt_top k) hk
      | coe t =>
        rw [h] at hk hk1
        have h3 : ¬ k < t := fun h' => hk (by rw [Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 h')
        have h4 : k < t + 1 := by
          have h5 := hk1
          rw [Nat.cast_withTop, ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_lt_coe] at h5
          exact h5
        obtain rfl : t = k := by omega
        have hmem : ω t ∈ B := by
          by_contra hc
          have h6 : WithTop.some (t + 1) ≤ firstHit B ω := (le_firstHit_iff B ω (t + 1)).2
            fun j hj => by
              rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
              · exact (le_firstHit_iff B ω t).1 (le_of_eq h.symm) j hj
              · rw [hj]; exact hc
          rw [h] at h6
          exact absurd (WithTop.coe_le_coe.1 h6) (by omega)
        exact indicator_of_notMem (show ω t ∉ Bᶜ from fun h' => h' hmem) f
    · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstHit B ω + 1} from hk1)]

/-- `G_B(y, f 1_{Bᶜ}) = E_y[Σ_{k<σ_B} f(Φ_k)]`. -/
theorem gKernelFn_indicator_eq (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (f : X → ℝ≥0∞)
    (y : X) :
    gKernelFn P B (Bᶜ.indicator f) y =
      ∫⁻ ω, sumBefore (firstHit B) (fun k ω => f (ω k)) ω ∂pathKernel P y :=
  lintegral_congr fun ω => sumBefore_firstHit_add_one_indicator B f ω

/-- `E_x[Σ_{k<τ_B} f(Φ_k)] = f(x) + ∫ P(x, dy) G_B(y, f 1_{Bᶜ})`. -/
theorem fSumReturn_eq_add_lintegral_gKernelFn (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    fSumReturn P B f x = f x + ∫⁻ y, gKernelFn P B (Bᶜ.indicator f) y ∂P x := by
  rw [fSumReturn_eq_add_tabooPotFn P hB hf, lintegral_gKernelFn P hB (hf.indicator hB.compl)]

/-- Off `B`, `G_B(y, f 1_{Bᶜ}) = f(y) + ∫ P(y, dz) G_B(z, f 1_{Bᶜ})`. -/
theorem gKernelFn_indicator_of_notMem (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) {y : X} (hy : y ∉ B) :
    gKernelFn P B (Bᶜ.indicator f) y = f y + ∫⁻ z, gKernelFn P B (Bᶜ.indicator f) z ∂P y := by
  rw [gKernelFn_eq P hB (hf.indicator hB.compl), indicator_of_mem (show y ∈ Bᶜ from hy),
    indicator_of_mem (show y ∈ Bᶜ from hy), lintegral_gKernelFn P hB (hf.indicator hB.compl)]

/-- **Return sums of the lazy chain**: `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ E^K_x[Σ_{k<τ_B} f(Φ_k)]` for the
lazy chain `K = ½ (I + P)`. -/
theorem fSumReturn_le_lazy (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    haveI := isMarkovKernel_lazyKernel P
    fSumReturn P B f x ≤ fSumReturn (lazyKernel P) B f x := by
  have := isMarkovKernel_lazyKernel P
  set g := Bᶜ.indicator f with hg
  have hgm : Measurable g := hf.indicator hB.compl
  set h := gKernelFn (lazyKernel P) B g with hh
  have hhm : Measurable h := measurable_gKernelFn hB hgm
  -- `W = ½ h` solves `PW + f ≤ W` off `B`
  have hdrift : ∀ y ∈ Bᶜ, ∫⁻ z, 2⁻¹ * h z ∂P y + f y ≤ 2⁻¹ * h y + 0 := fun y hy => by
    rw [add_zero, lintegral_const_mul _ hhm]
    have h1 := gKernelFn_indicator_of_notMem (lazyKernel P) hB hf hy
    rw [lintegral_lazyKernel P hhm] at h1
    by_cases hinf : h y = ∞
    · rw [hinf, ENNReal.mul_top (by norm_num)]
      exact le_top
    · have hne : 2⁻¹ * h y ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hinf
      have h2 : 2⁻¹ * h y + (2⁻¹ * ∫⁻ z, h z ∂P y + f y) ≤ 2⁻¹ * h y + 2⁻¹ * h y := by
        refine le_of_eq ?_
        calc 2⁻¹ * h y + (2⁻¹ * ∫⁻ z, h z ∂P y + f y)
            = f y + (2⁻¹ * h y + 2⁻¹ * ∫⁻ z, h z ∂P y) := by ring
          _ = h y := h1.symm
          _ = 2⁻¹ * h y + 2⁻¹ * h y := by
              rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      exact (ENNReal.add_le_add_iff_left hne).1 h2
  -- the Comparison Theorem before `σ_B`
  have hcomp : ∀ y, gKernelFn P B g y ≤ 2⁻¹ * h y := fun y => by
    have hc := comparison_theorem_pathKernel P (hhm.const_mul _) hf measurable_const
      (D := Bᶜ) hdrift (proposition_3_4_4 hB).2 (fun ω k hk => (le_firstHit_iff B ω (k + 1)).1
        (by
          cases h' : firstHit B ω with
          | top => exact le_top
          | coe t =>
            rw [h'] at hk
            exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 hk)) k (Nat.lt_succ_self k)) y
    have h0 : ∫⁻ ω, sumBefore (firstHit B) (fun k (ω : ℕ → X) => (0 : ℝ≥0∞)) ω
        ∂pathKernel P y = 0 := by
      refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun ω => ?_)
      exact ENNReal.tsum_eq_zero.2 fun k => Set.indicator_apply_eq_zero.2 fun _ => rfl
    rw [h0, add_zero] at hc
    calc gKernelFn P B g y
        = ∫⁻ ω, sumBefore (firstHit B) (fun k ω => f (ω k)) ω ∂pathKernel P y :=
          gKernelFn_indicator_eq P B f y
      _ ≤ 2⁻¹ * h y := hc
  calc fSumReturn P B f x = f x + ∫⁻ y, gKernelFn P B g y ∂P x :=
        fSumReturn_eq_add_lintegral_gKernelFn P hB hf x
    _ ≤ f x + ∫⁻ y, 2⁻¹ * h y ∂P x := add_le_add le_rfl (lintegral_mono hcomp)
    _ = f x + 2⁻¹ * ∫⁻ y, h y ∂P x := by rw [lintegral_const_mul _ hhm]
    _ ≤ f x + (2⁻¹ * h x + 2⁻¹ * ∫⁻ y, h y ∂P x) := add_le_add le_rfl le_add_self
    _ = f x + ∫⁻ y, h y ∂lazyKernel P x := by rw [lintegral_lazyKernel P hhm]
    _ = fSumReturn (lazyKernel P) B f x :=
        (fSumReturn_eq_add_lintegral_gKernelFn (lazyKernel P) hB hf x).symm

/-- The lazy chain stays put with probability at least `½`: `K(x, A) ≥ ½` for `x ∈ A`. -/
theorem half_le_lazyKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) {x : X}
    (hx : x ∈ A) : 2⁻¹ ≤ lazyKernel P x A := by
  have h := lintegral_lazyKernel P (measurable_one.indicator hA) x
  rw [lintegral_indicator_one hA, indicator_of_mem hx, Pi.one_apply, mul_one] at h
  rw [h]
  exact le_self_add

/-- **The lazy chain is aperiodic**: a `d`-cycle with `d ≥ 2` would move every point of `Dᵢ` to
the disjoint `D_{i+1}` with probability one, while `K(x, Dᵢ) ≥ ½`. -/
theorem isAperiodic_lazyKernel (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : haveI := isMarkovKernel_lazyKernel P; IsMaximalIrreducibility (lazyKernel P) ψ) :
    IsAperiodic (lazyKernel P) ψ := by
  have := isMarkovKernel_lazyKernel P
  refine ⟨one_pos, ⟨fun _ => univ, ⟨fun _ => MeasurableSet.univ,
    fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ x _ => measure_univ, ?_⟩⟩,
    fun d' D' hd' hD' => ?_⟩
  · rw [iUnion_const, compl_univ]
    exact measure_empty
  · by_contra hlt
    push Not at hlt
    -- a point of the cycle
    obtain ⟨x, hx⟩ : (⋃ i, D' i).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      have h0 := hD'.null_compl
      rw [hemp, compl_empty] at h0
      exact hψ.1 (Measure.measure_univ_eq_zero.1 h0)
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    have hne : i + 1 ≠ i := by
      intro h
      have h1 : ((1 : ℕ) : ZMod d') = 0 := by
        rw [Nat.cast_one]
        have := congrArg (fun z => z - i) h
        rwa [add_sub_cancel_left, sub_self] at this
      have := (ZMod.natCast_eq_zero_iff 1 d').1 h1
      have := Nat.le_of_dvd one_pos this
      omega
    have hdis := hD'.disjoint (i + 1) i hne
    have h1 := hD'.step i x hi
    have h2 := half_le_lazyKernel P (hD'.measurableSet i) hi
    have hsum : lazyKernel P x (D' (i + 1)) + lazyKernel P x (D' i) ≤ 1 := by
      rw [← measure_union hdis (hD'.measurableSet i)]
      exact prob_le_one
    rw [h1] at hsum
    have h3 : (1 : ℝ≥0∞) + 2⁻¹ ≤ 1 := (add_le_add le_rfl h2).trans hsum
    have h4 : (1 : ℝ≥0∞) < 1 + 2⁻¹ := ENNReal.lt_add_right ENNReal.one_ne_top (by norm_num)
    exact absurd (lt_of_lt_of_le h4 h3) (lt_irrefl _)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.11** (MT p. 348) for every positive chain, aperiodic or not: if `π(f) < ∞`
there are `f`-regular sets `S_f(n)` whose union is full. The lazy chain `K = ½ (I + P)` is
positive and aperiodic with the same `ψ` and `π`, Theorem 14.2.11 applies to it, and an
`f`-regular set of `K` is `f`-regular for `P` (`fSumReturn_le_lazy`). -/
theorem theorem_14_2_11_of_isPositive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ S : ℕ → Set X, (∀ n, IsFRegularSet P ψ f (S n)) ∧ IsFull ψ (⋃ n, S n) := by
  have := isMarkovKernel_lazyKernel P
  have hψK : IsMaximalIrreducibility (lazyKernel P) ψ := by
    have h := isMaximalIrreducibility_lazy_pow hpos.1 (le_refl 1)
    convert h using 1
    exact (pow_one _).symm
  have hπK : IsInvariant (lazyKernel P) π := hπ.sampledKernel isSamplingDist_lazyWeights
  obtain ⟨S, hS, hfull⟩ := theorem_14_2_11 ⟨hψK, π, inferInstance, hπK⟩
    (isAperiodic_lazyKernel P hψK) hπK hf hπf
  refine ⟨S, fun n => ⟨(hS n).1, fun B hB hψB => ?_⟩, hfull⟩
  obtain ⟨M, hM, h⟩ := (hS n).2 B hB hψB
  exact ⟨M, hM, fun x hx => (fSumReturn_le_lazy P hB hf x).trans (h x hx)⟩

end MeynTweedie.FErgodicity
