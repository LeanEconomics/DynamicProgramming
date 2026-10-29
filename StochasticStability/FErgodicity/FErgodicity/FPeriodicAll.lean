/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FPeriodicCycle

/-!
# Theorem 14.3.6 (ii) for every initial state

Meyn and Tweedie, Theorem 14.3.6 (ii), p. 351, (14.27): if the chain is `f`-regular, then
`‖d⁻¹ Σ_{r<d} P^{nd+r}(x, ·) − π‖_f → 0` for **every** `x`. `theorem_14_3_6_ii` proves it on the
cycle; here the null set off the cycle is covered by mixture convergence over the first-entrance
laws into a part of one cycle class.

**`f`-norm algebra.** `fNorm_add_add_le`
(`‖(μ₁ + μ₂) − (ν₁ + ν₂)‖_f ≤ ‖μ₁ − ν₁‖_f + ‖μ₂ − ν₂‖_f`),
`fNorm_finsetSum_le`, `fNorm_smul_le`, `fNorm_add_left_le`, `fNorm_add_cancel_le`.

**Sequences.** `tendsto_of_tendsto_mul_add` (a sequence whose `d` phases tend to `0` tends to `0`),
`tendsto_tsum_of_le` (dominated convergence for series).

**Mixtures from one class.** For the chain `K` on the class `D₀` (positive Harris, aperiodic,
`π₀`-invariant) and its drift `W = G_C(·, f^{(d)})`, put `B = D₀ ∩ {W ≤ L}`.
* `mixture_bound`: `sup_n ‖λKⁿ − π₀‖_{f^{(d)}} ≤ M` for probabilities `λ` on `B`, from the pairwise
  summability `Σₙ ‖Kⁿ(y, ·) − Kⁿ(z, ·)‖ ≤ A (W(y) + W(z)) + B'` of Theorem 14.0.1;
* `tendsto_fNorm_mixture`: for every finite `ν` on `B`, `‖νPᵏ − ν(X) π_{k}‖_f → 0` (`πₛ` the cycle
  probabilities, `k` read in `ℤ/d`), and `‖νPᵏ − ν(X) π_k‖_f ≤ ν(X) M`.

**Result.**
* **Theorem 14.3.6 (ii)** for every `x` (`theorem_14_3_6_ii_all`, p. 351): by the first-entrance
  decomposition (8.18) into `B` (`pow_succ_eq_firstEntrance`),
  `P^{m+1}(x, ·) = _BP^{m+1}(x, ·) + Σ_{j<m} (_BP^{j+1}(x, ·)|_B) P^{m−j}`;
  the first term has summable `f`-mass (`x` is `f`-regular and `f ≤ L` on `B`), the mixtures
  converge by dominated convergence for series, and the phases average to `π` because the chain
  reaches `B` almost surely (Harris).

**Hypotheses.** As stated in each theorem; `theorem_14_3_6_ii_all` needs no finiteness of `f`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### `f`-norm algebra -/

/-- `‖(μ₁ + μ₂) − (ν₁ + ν₂)‖_f ≤ ‖μ₁ − ν₁‖_f + ‖μ₂ − ν₂‖_f`. -/
theorem fNorm_add_add_le (f : X → ℝ≥0∞) (μ₁ μ₂ ν₁ ν₂ : Measure X) :
    fNorm f (μ₁ + μ₂) (ν₁ + ν₂) ≤ fNorm f μ₁ ν₁ + fNorm f μ₂ ν₂ := by
  refine fNorm_le fun g hg => ?_
  obtain ⟨hμ₁, hμ₂⟩ := integrable_add_measure.1 hg.2.2.1
  obtain ⟨hν₁, hν₂⟩ := integrable_add_measure.1 hg.2.2.2
  rw [integral_add_measure hμ₁ hμ₂, integral_add_measure hν₁ hν₂]
  have h1 := ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hμ₁, hν₁⟩
  have h2 := ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hμ₂, hν₂⟩
  refine le_trans ?_ (add_le_add h1 h2)
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∫ x, g x ∂μ₁ + ∫ x, g x ∂μ₂ - (∫ x, g x ∂ν₁ + ∫ x, g x ∂ν₂) =
      (∫ x, g x ∂μ₁ - ∫ x, g x ∂ν₁) + (∫ x, g x ∂μ₂ - ∫ x, g x ∂ν₂) := by ring
  rw [e]
  exact abs_add_le _ _

/-- `‖Σ μⱼ − Σ νⱼ‖_f ≤ Σ ‖μⱼ − νⱼ‖_f` for finite sums. -/
theorem fNorm_finsetSum_le {ι : Type*} (s : Finset ι) (f : X → ℝ≥0∞) (μ ν : ι → Measure X) :
    fNorm f (∑ j ∈ s, μ j) (∑ j ∈ s, ν j) ≤ ∑ j ∈ s, fNorm f (μ j) (ν j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, fNorm_self]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (fNorm_add_add_le f _ _ _ _).trans (add_le_add le_rfl ih)

/-- `‖cμ − cν‖_f ≤ c ‖μ − ν‖_f` for `c < ∞`. -/
theorem fNorm_smul_le (f : X → ℝ≥0∞) (μ ν : Measure X) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    fNorm f (c • μ) (c • ν) ≤ c * fNorm f μ ν := by
  have h := fNorm_smul_sum_le (Finset.range 1) f (fun _ => μ) (fun _ => ν) hc
  rwa [Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one] at h

/-- `‖(μ₀ + μ) − ν‖_f ≤ μ₀(f) + ‖μ − ν‖_f`. -/
theorem fNorm_add_left_le (f : X → ℝ≥0∞) (μ₀ μ ν : Measure X) :
    fNorm f (μ₀ + μ) ν ≤ ∫⁻ x, f x ∂μ₀ + fNorm f μ ν := by
  have h := fNorm_add_add_le f μ₀ μ 0 ν
  rw [zero_add] at h
  refine h.trans (add_le_add ?_ le_rfl)
  refine (fNorm_le_add f μ₀ 0).trans (le_of_eq ?_)
  rw [lintegral_zero_measure, add_zero]

/-- `‖(α + E) − (α + F)‖_f ≤ ‖E − F‖_f`. -/
theorem fNorm_add_cancel_le (f : X → ℝ≥0∞) (α E F : Measure X) :
    fNorm f (α + E) (α + F) ≤ fNorm f E F := by
  have h := fNorm_add_add_le f α E α F
  rwa [fNorm_self, zero_add] at h

/-! ### Sequences -/

/-- A sequence whose `d` phases `n ↦ u(dn + r)`, `r < d`, tend to `0` tends to `0`. -/
theorem tendsto_of_tendsto_mul_add {u : ℕ → ℝ≥0∞} {d : ℕ} (hd : 0 < d)
    (h : ∀ r < d, Tendsto (fun n => u (d * n + r)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hev : ∀ r < d, ∃ N, ∀ n ≥ N, u (d * n + r) ≤ ε := fun r hr =>
    eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 (h r hr)) ε hε)
  choose! N hN using hev
  refine eventually_atTop.2 ⟨d * ∑ r ∈ Finset.range d, N r, fun k hk => ?_⟩
  have hr : k % d < d := Nat.mod_lt k hd
  have hdiv : N (k % d) ≤ k / d := by
    have h1 : N (k % d) ≤ ∑ r ∈ Finset.range d, N r :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hr)
    have h2 : ∑ r ∈ Finset.range d, N r ≤ k / d := (Nat.le_div_iff_mul_le hd).2 (by
      rw [mul_comm]; exact hk)
    omega
  have := hN (k % d) hr (k / d) hdiv
  rwa [Nat.div_add_mod] at this

/-- **Dominated convergence for series**: if `aₙⱼ → 0` for each `j`, `aₙⱼ ≤ bⱼ` and `Σ bⱼ < ∞`,
then `Σⱼ aₙⱼ → 0`. -/
theorem tendsto_tsum_of_le {a : ℕ → ℕ → ℝ≥0∞} {b : ℕ → ℝ≥0∞} (hab : ∀ n j, a n j ≤ b j)
    (hb : ∑' j, b j ≠ ∞) (ha : ∀ j, Tendsto (fun n => a n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, a n j) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := Measure.count) b
    (F := a) (f := fun _ => 0) (fun n => measurable_from_top) (fun n =>
      Eventually.of_forall fun j => hab n j) (by rw [lintegral_count]; exact hb)
    (Eventually.of_forall fun j => ha j)
  simp_rw [lintegral_count] at h
  rwa [tsum_zero] at h

/-! ### A uniform bound from (V3) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **A uniform bound from (V3)**: for an aperiodic positive chain with (V3) for a petite set and
`π(f) < ∞`, there are `A, M < ∞` with `‖λKⁿ − π‖_f ≤ A λ(V) + M` for every probability `λ` and
every `n`. The pairwise sums `Σₙ ‖Kⁿ(y, ·) − Kⁿ(z₀, ·)‖_f ≤ A (V(y) + V(z₀)) + B` (Theorem 14.0.1)
bound the distance to the reference law `Kⁿ(z₀, ·)`, which converges to `π`. -/
theorem exists_mixture_bound {K : Kernel X X} [IsMarkovKernel K] {ψ : Measure X}
    (hpos : IsPositive K ψ) (hap : IsAperiodic K ψ) {σ : Measure X} [IsProbabilityMeasure σ]
    (hσ : IsInvariant K σ) {W g : X → ℝ≥0∞} (hW : Measurable W) (hg : Measurable g)
    (hg1 : ∀ x, 1 ≤ g x) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite K C)
    (h : DriftV3 K W g b C) (hσg : ∫⁻ x, g x ∂σ ≠ ∞) {z₀ : X} (hz₀ : W z₀ ≠ ∞) :
    ∃ A M : ℝ≥0∞, A ≠ ∞ ∧ M ≠ ∞ ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ),
      fNorm g ((K ^ n : Kernel X X) ∘ₘ μ) σ ≤ A * ∫⁻ y, W y ∂μ + M := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨A, B, hA, hB, hsum⟩ := tsum_fNorm_le_of_driftV3 hpos hap hσ hW hg hg1 hb hC h hσg
  -- `Kⁿ(z₀, g) < ∞`
  have hfin : ∀ n, ∫⁻ y, g y ∂(K ^ n : Kernel X X) z₀ ≠ ∞ := fun n => by
    have h1 := (theorem_14_2_2 K hW hg (measurable_const.indicator hCm) h z₀).1 n
    refine ne_top_of_le_ne_top ?_ ((Finset.single_le_sum (f := fun k =>
      ∫⁻ y, g y ∂(K ^ k : Kernel X X) z₀) (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_self n))).trans h1)
    refine ENNReal.add_ne_top.2 ⟨hz₀, ENNReal.sum_ne_top.2 fun k _ => ?_⟩
    have := isMarkovKernel_pow K k
    refine ne_top_of_le_ne_top (b := ∫⁻ _, b ∂(K ^ k : Kernel X X) z₀) ?_
      (lintegral_mono fun y => indicator_le_self' (fun _ _ => zero_le) y)
    rw [lintegral_const, measure_univ, mul_one]
    exact hb
  -- the reference law converges, hence is bounded
  have hconv := tendsto_fNorm_of_driftV3 hpos hap hσ hW hg hg1 hb hC h hσg (Measure.dirac z₀)
    (by rw [lintegral_dirac' _ hW]; exact hz₀)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hconv) 1 one_pos)
  set M₀ := 1 + ∑ n ∈ Finset.range N, fNorm g ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) σ
  have hM₀ : M₀ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2
    fun n _ => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨by rw [dirac_kernel]; exact hfin n,
      hσg⟩) (fNorm_le_add g _ σ)⟩
  have hbd : ∀ n, fNorm g ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) σ ≤ M₀ := fun n => by
    rcases Nat.lt_or_ge n N with hn | hn
    · exact (Finset.single_le_sum (f := fun n =>
        fNorm g ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) σ) (fun _ _ => zero_le)
        (Finset.mem_range.2 hn)).trans le_add_self
    · exact (hN n hn).trans le_self_add
  refine ⟨A, A * W z₀ + B + M₀, hA, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top hA hz₀, hB⟩, hM₀⟩, fun μ _ n => ?_⟩
  have := isMarkovKernel_pow K n
  have hmid : ∫⁻ y, g y ∂((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) ≠ ∞ := by
    rw [dirac_kernel]; exact hfin n
  refine (fNorm_triangle _ _ σ hmid).trans ?_
  have h1 : fNorm g ((K ^ n : Kernel X X) ∘ₘ μ) ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) ≤
      A * ∫⁻ y, W y ∂μ + (A * W z₀ + B) := by
    refine (fNorm_comp_le_lintegral (K ^ n) g μ (Measure.dirac z₀)).trans ?_
    calc ∫⁻ y, ∫⁻ z, fNorm g ((K ^ n : Kernel X X) y) ((K ^ n : Kernel X X) z)
          ∂Measure.dirac z₀ ∂μ
        ≤ ∫⁻ y, (A * W y + (A * W z₀ + B)) ∂μ := by
          refine lintegral_mono fun y => (lintegral_dirac_le z₀ _).trans ?_
          refine (ENNReal.le_tsum (f := fun n => fNorm g ((K ^ n : Kernel X X) y)
            ((K ^ n : Kernel X X) z₀)) n).trans ((hsum y z₀).trans (le_of_eq ?_))
          ring
      _ = A * ∫⁻ y, W y ∂μ + (A * W z₀ + B) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hW, lintegral_const,
            measure_univ, mul_one]
  calc fNorm g ((K ^ n : Kernel X X) ∘ₘ μ) ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) +
        fNorm g ((K ^ n : Kernel X X) ∘ₘ Measure.dirac z₀) σ
      ≤ A * ∫⁻ y, W y ∂μ + (A * W z₀ + B) + M₀ := add_le_add h1 (hbd n)
    _ = A * ∫⁻ y, W y ∂μ + (A * W z₀ + B + M₀) := by ring

/-! ### The chain on a cycle class from an `f`-regular chain -/

/-- For an `f`-regular chain every point of a cycle class `Dᵢ` is `f^{(d)}`-regular for the chain
that moves by `Pᵈ` on `Dᵢ` (the skeleton return sums are bounded by those of `P`). -/
theorem IsCycle.isFRegularState_absorbKernel {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} {d : ℕ} {D : ZMod d → Set X} (hd : 0 < d) (hD : IsCycle P ψ d D)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hreg : IsFRegularChain P ψ f) (σ : Measure X)
    [IsProbabilityMeasure σ] (i : ZMod d) {x : X} (hxi : x ∈ D i) :
    haveI := isMarkovKernel_pow P d
    haveI := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) σ
    IsFRegularState (absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) σ)
      (ψ.restrict (D i)) (fSkel P d f) x := fun B hB hψB => by
  have := isMarkovKernel_pow P d
  have := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) (hD.measurableSet i) σ
  have hQ := hD.pow_d_compl_eq_zero i
  rw [Measure.restrict_apply hB] at hψB
  have hBD := hB.inter (hD.measurableSet i)
  refine ne_top_of_le_ne_top ?_ (fSumReturn_anti_set _ (inter_subset_left (t := D i)) _ x)
  rw [fSumReturn_absorbKernel_of_mem (hD.measurableSet i) hQ _ hBD
    (measurable_fSkel P d hf) hxi]
  refine ne_top_of_le_ne_top ?_ (hD.fSumReturn_skeleton_le hd hBD inter_subset_right hf hxi)
  obtain ⟨Cs, hCs, hcov⟩ := hreg
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  exact (hCs m).isFRegularState hm _ hBD hψB

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Mixtures started in one cycle class.** For an `f`-regular chain of period `d` with `d`-cycle
`{Dᵢ}`, there are a measurable `B ⊆ D₀` with `ψ(B) > 0`, a bound `f ≤ L` on `B` and `M < ∞` such
that for every finite `ν` carried by `B` and every `k`,
`‖νPᵏ − ν(X) π_k‖_f ≤ ν(X) M` and `‖νPᵏ − ν(X) π_k‖_f → 0`, where `π_k = d π(· ∩ D_k)`. -/
theorem IsCycle.exists_mixture_set {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {d : ℕ} {D : ZMod d → Set X} (hper : IsPeriod P ψ d)
    (hD : IsCycle P ψ d D) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hreg : IsFRegularChain P ψ f) :
    ∃ B : Set X, MeasurableSet B ∧ 0 < ψ B ∧ B ⊆ D 0 ∧ ∃ L : ℝ≥0∞, L ≠ ∞ ∧ (∀ y ∈ B, f y ≤ L) ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ (ν : Measure X) [IsFiniteMeasure ν], ν Bᶜ = 0 →
        (∀ k : ℕ, fNorm f ((P ^ k : Kernel X X) ∘ₘ ν) (ν univ • cycleInv π D (k : ZMod d)) ≤
          ν univ * M) ∧
        Tendsto (fun k : ℕ => fNorm f ((P ^ k : Kernel X X) ∘ₘ ν)
          (ν univ • cycleInv π D (k : ZMod d))) atTop (𝓝 0) := by
  have hd := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hph : IsPositiveHarris P ψ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    exact IsRegularChain.isPositiveHarris hψ ⟨Cs, fun n => (hCs n).isRegularSet hf1, hcov⟩
  have hrec := proposition_10_1_1 hph.2
  have hπf := hreg.lintegral_ne_top hrec hf hf1 hπ
  have := isMarkovKernel_pow P d
  have hσp := hD.isProbabilityMeasure_cycleInv hd hrec hπ
  have := hσp 0
  set D₀ := D 0 with hD₀
  have hD₀m : MeasurableSet D₀ := hD.measurableSet 0
  set σ₀ := cycleInv π D 0 with hσ₀
  have := isMarkovKernel_absorbKernel (P ^ d : Kernel X X) hD₀m σ₀
  set K := absorbKernel (P ^ d : Kernel X X) hD₀m σ₀ with hK
  obtain ⟨hphK, hapK, hσinv⟩ := hD.absorbKernel_isPositiveHarris hd hper hph hπ 0
  set f' := fSkel P d f with hf'def
  have hf' : Measurable f' := measurable_fSkel P d hf
  have hf'1 : ∀ x, 1 ≤ f' x := one_le_fSkel P hd hf hf1
  have hσf : ∫⁻ x, f' x ∂σ₀ ≠ ∞ := by
    rw [hσ₀, cycleInv, lintegral_smul_measure]
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ne_top_of_le_ne_top ?_
      (lintegral_mono' Measure.restrict_le_self le_rfl))
    rw [lintegral_fSkel P hπ d hf]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) hπf
  obtain ⟨C₀, hC₀, hψC₀, hpet, b₀, hb₀, hdrift, heq, -, -⟩ :=
    exists_fRegular_driftV3 hphK.2 hapK hσinv hf' hf'1 hσf
  set W := gKernelFn K C₀ f' with hWdef
  have hWm : Measurable W := measurable_gKernelFn hC₀.1 hf'
  -- `W < ∞` on `D₀`
  have hWfin : ∀ y ∈ D₀, W y ≠ ∞ := fun y hy => by
    have h1 : y ∈ {x | IsFRegularState K (ψ.restrict D₀) f' x} :=
      hD.isFRegularState_absorbKernel hd hf hreg σ₀ 0 hy
    rw [heq] at h1
    exact h1
  -- a part of `D₀` where `W` is bounded
  have hψD₀ : 0 < ψ D₀ := hD.measure_pos hψ hd 0
  have hcov : D₀ = ⋃ L : ℕ, D₀ ∩ {y | W y ≤ L} := by
    ext y
    refine ⟨fun hy => mem_iUnion.2 ?_, fun hy => (mem_iUnion.1 hy).choose_spec.1⟩
    obtain ⟨L, hL⟩ := ENNReal.exists_nat_gt (hWfin y hy)
    exact ⟨L, hy, hL.le⟩
  obtain ⟨L, hL⟩ := exists_measure_pos_of_iUnion (hcov ▸ hψD₀ : 0 < ψ (⋃ L : ℕ,
    D₀ ∩ {y | W y ≤ L}))
  set B := D₀ ∩ {y | W y ≤ L} with hBdef
  have hBm : MeasurableSet B := hD₀m.inter (measurableSet_le hWm measurable_const)
  obtain ⟨z₀, hz₀⟩ := nonempty_of_measure_ne_zero hL.ne'
  have hWz₀ : W z₀ ≠ ∞ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top L) hz₀.2
  obtain ⟨A, M, hA, hM, hbound⟩ := exists_mixture_bound hphK.2 hapK hσinv hWm hf' hf'1 hb₀ hpet
    hdrift hσf hWz₀
  -- `f ≤ f^{(d)} ≤ W ≤ L` on `B`
  have hfW : ∀ y, f y ≤ W y := fun y => by
    refine (le_fSkel P hd hf y).trans ?_
    rw [hWdef, gKernelFn_eq K hC₀.1 hf' y]
    exact le_self_add
  refine ⟨B, hBm, hL, inter_subset_left, L, ENNReal.natCast_ne_top L,
    fun y hy => (hfW y).trans hy.2, A * L + M, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA
      (ENNReal.natCast_ne_top L), hM⟩, fun ν _ hν => ?_⟩
  -- probabilities carried by `B`
  have hprob : ∀ (μ : Measure X) [IsProbabilityMeasure μ], μ Bᶜ = 0 →
      (∀ k : ℕ, fNorm f ((P ^ k : Kernel X X) ∘ₘ μ) (cycleInv π D (k : ZMod d)) ≤ A * L + M) ∧
      Tendsto (fun k : ℕ => fNorm f ((P ^ k : Kernel X X) ∘ₘ μ)
        (cycleInv π D (k : ZMod d))) atTop (𝓝 0) := fun μ _ hμ => by
    have hμD : μ D₀ᶜ = 0 := measure_mono_null (compl_subset_compl.2 inter_subset_left) hμ
    have hμW : ∫⁻ y, W y ∂μ ≤ L := by
      calc ∫⁻ y, W y ∂μ ≤ ∫⁻ _, (L : ℝ≥0∞) ∂μ := by
            refine lintegral_mono_ae (ae_iff.2 (measure_mono_null (fun y hy => ?_) hμ))
            intro hyB
            exact hy hyB.2
        _ = L := by rw [lintegral_const, measure_univ, mul_one]
    -- each phase is controlled by the chain on `D₀`
    have hphase : ∀ n r, r < d → fNorm f ((P ^ (d * n + r) : Kernel X X) ∘ₘ μ)
        (cycleInv π D ((d * n + r : ℕ) : ZMod d)) ≤ fNorm f' ((K ^ n : Kernel X X) ∘ₘ μ) σ₀ :=
      fun n r hr => by
        have := isMarkovKernel_pow P r
        have := isMarkovKernel_pow P (d * n)
        have e1 : (P ^ (d * n + r) : Kernel X X) ∘ₘ μ =
            (P ^ r : Kernel X X) ∘ₘ ((P ^ (d * n) : Kernel X X) ∘ₘ μ) := by
          rw [Measure.comp_assoc, add_comm, pow_add]; rfl
        have e2 : ((d * n + r : ℕ) : ZMod d) = 0 + (r : ZMod d) := by
          push_cast
          rw [ZMod.natCast_self, zero_mul]
        have e3 : (K ^ n : Kernel X X) ∘ₘ μ = (P ^ (d * n) : Kernel X X) ∘ₘ μ := by
          rw [hK, comp_absorbKernel_pow hD₀m (hD.pow_d_compl_eq_zero 0) n hμD, ← pow_mul]
        rw [e1, e2, ← hD.comp_pow_cycleInv hd hπ r 0, e3]
        exact (fNorm_comp_le (P ^ r) f _ _).trans
          (fNorm_mono (fun y => lintegral_pow_le_fSkel P hr f y) _ _)
    have hkphase : ∀ k : ℕ, fNorm f ((P ^ k : Kernel X X) ∘ₘ μ) (cycleInv π D (k : ZMod d)) ≤
        fNorm f' ((K ^ (k / d) : Kernel X X) ∘ₘ μ) σ₀ := fun k => by
      have h := hphase (k / d) (k % d) (Nat.mod_lt k hd)
      rwa [Nat.div_add_mod] at h
    refine ⟨fun k => (hkphase k).trans ((hbound μ (k / d)).trans
      (add_le_add (mul_le_mul' le_rfl hμW) le_rfl)), ?_⟩
    have hKconv := tendsto_fNorm_of_driftV3 hphK.2 hapK hσinv hWm hf' hf'1 hb₀ hpet hdrift hσf μ
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top L) hμW)
    refine tendsto_of_tendsto_mul_add hd fun r hr => ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKconv (fun _ => zero_le)
      fun n => hphase n r hr
  -- normalise `ν`
  by_cases h0 : ν univ = 0
  · have hν0 : ν = 0 := Measure.measure_univ_eq_zero.1 h0
    subst hν0
    refine ⟨fun k => ?_, ?_⟩
    · rw [comp_zero_measure, Measure.coe_zero, Pi.zero_apply, zero_smul, fNorm_self]
      exact zero_le
    · simp_rw [comp_zero_measure, Measure.coe_zero, Pi.zero_apply, zero_smul, fNorm_self]
      exact tendsto_const_nhds
  · have hνt : ν univ ≠ ∞ := measure_ne_top ν univ
    set μ := (ν univ)⁻¹ • ν with hμdef
    have hμp : IsProbabilityMeasure μ := ⟨by
      rw [hμdef, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hνt]⟩
    have hμB : μ Bᶜ = 0 := by
      rw [hμdef, Measure.smul_apply, hν, smul_eq_mul, mul_zero]
    have hνμ : ν = ν univ • μ := by
      rw [hμdef, smul_smul, ENNReal.mul_inv_cancel h0 hνt, one_smul]
    obtain ⟨hb, hc⟩ := hprob μ hμB
    have hle : ∀ k : ℕ, fNorm f ((P ^ k : Kernel X X) ∘ₘ ν) (ν univ • cycleInv π D (k : ZMod d))
        ≤ ν univ * fNorm f ((P ^ k : Kernel X X) ∘ₘ μ) (cycleInv π D (k : ZMod d)) := fun k => by
      have e1 : (P ^ k : Kernel X X) ∘ₘ ν = ν univ • ((P ^ k : Kernel X X) ∘ₘ μ) := by
        conv_lhs => rw [hνμ]
        exact Measure.comp_smul _
      rw [e1]
      exact fNorm_smul_le f _ _ hνt
    refine ⟨fun k => (hle k).trans (mul_le_mul' le_rfl (hb k)), ?_⟩
    have h := ENNReal.Tendsto.const_mul hc (Or.inr hνt)
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hle

/-! ### Theorem 14.3.6 (ii) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.6 (ii)** for every initial state (MT p. 351), (14.27): if the chain is
`f`-regular (`f ≥ 1`) with period `d`, `d`-cycle `{Dᵢ}` and invariant probability `π`, then
`‖d⁻¹ Σ_{r<d} P^{nd+r}(x, ·) − π‖_f → 0` for **every** `x`. -/
theorem theorem_14_3_6_ii_all {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hreg : IsFRegularChain P ψ f) {d : ℕ} (hper : IsPeriod P ψ d) {D : ZMod d → Set X}
    (hD : IsCycle P ψ d D) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (x : X) :
    Tendsto (fun n => fNorm f ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * n + r) : Kernel X X) x) π)
      atTop (𝓝 0) := by
  have hd := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hph : IsPositiveHarris P ψ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    exact IsRegularChain.isPositiveHarris hψ ⟨Cs, fun n => (hCs n).isRegularSet hf1, hcov⟩
  have hrec := proposition_10_1_1 hph.2
  have hπf := hreg.lintegral_ne_top hrec hf hf1 hπ
  have hσp := hD.isProbabilityMeasure_cycleInv hd hrec hπ
  set σ := cycleInv π D with hσdef
  obtain ⟨B, hBm, hψB, -, L, hL, hfL, M, hM, hmix⟩ :=
    hD.exists_mixture_set hψ hper hπ hf hf1 hreg
  -- the first-entrance laws into `B`
  set T : ℕ → Measure X := fun j => tabooKernel P hBm j x with hT
  set ν : ℕ → Measure X := fun j => (T j).restrict B with hν
  have hνfin : ∀ j, IsFiniteMeasure (ν j) := fun j => by
    refine ⟨lt_of_le_of_lt ?_ ENNReal.one_lt_top⟩
    rw [hν, Measure.restrict_apply_univ]
    have := isMarkovKernel_pow P (j + 1)
    exact (tabooKernel_le_pow P hBm j x hBm).trans prob_le_one
  have hνB : ∀ j, ν j Bᶜ = 0 := fun j => by
    rw [hν, Measure.restrict_apply hBm.compl, compl_inter_self, measure_empty]
  set c : ℕ → ℝ≥0∞ := fun j => ν j univ with hc
  have hc1 : ∑' j, c j = 1 := by
    have h := IsHarris.hitProb_eq_one hph.1 hBm hψB x
    rw [hitProb_eq_tsum P hBm x] at h
    rw [← h]
    exact tsum_congr fun j => Measure.restrict_apply_univ _
  -- the `f`-mass before the entrance is summable
  have hfx : fSumReturn P B f x ≠ ∞ := by
    obtain ⟨Cs, hCs, hcov⟩ := hreg
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
    exact (hCs m).isFRegularState hm B hBm hψB
  have hTf : ∑' m, ∫⁻ y, f y ∂T m ≠ ∞ := by
    have e : ∑' m, ∫⁻ y, f y ∂T m = tabooPotFn P B f x := by
      rw [← lintegral_tabooPotKernel P hBm hf x, tabooPotKernel, Kernel.sum_apply,
        lintegral_sum_measure]
    rw [e]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfx, hL⟩) (tabooPotFn_le hBm hf hfL x)
  have hTm := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hTf
  -- the comparison laws
  set ρ : ℕ → Measure X := fun m => ∑ j ∈ range m, c j • σ ((m - j : ℕ) : ZMod d) with hρ
  have he : Tendsto (fun m => fNorm f ((P ^ (m + 1) : Kernel X X) x) (ρ m)) atTop (𝓝 0) := by
    set a : ℕ → ℕ → ℝ≥0∞ := fun m j => if j < m then
      fNorm f ((P ^ (m - j) : Kernel X X) ∘ₘ ν j) (c j • σ ((m - j : ℕ) : ZMod d)) else 0
      with ha
    have hle : ∀ m, fNorm f ((P ^ (m + 1) : Kernel X X) x) (ρ m) ≤
        ∫⁻ y, f y ∂T m + ∑' j, a m j := fun m => by
      rw [pow_succ_eq_firstEntrance P hBm m x]
      refine (fNorm_add_left_le f _ _ _).trans (add_le_add le_rfl ?_)
      refine (fNorm_finsetSum_le (range m) f _ _).trans (le_of_eq ?_)
      rw [tsum_eq_sum (s := range m) fun j hj => by
        simp only [ha, show ¬ j < m from fun h => hj (Finset.mem_range.2 h), ↓reduceIte]]
      exact Finset.sum_congr rfl fun j hj => by
        simp only [ha, Finset.mem_range.1 hj, ↓reduceIte]
        rfl
    have hab : ∀ m j, a m j ≤ c j * M := fun m j => by
      simp only [ha]
      split_ifs
      · exact (hmix (ν j) (hνB j)).1 (m - j)
      · exact zero_le
    have hb : ∑' j, c j * M ≠ ∞ := by
      rw [ENNReal.tsum_mul_right, hc1, one_mul]; exact hM
    have hconv : ∀ j, Tendsto (fun m => a m j) atTop (𝓝 0) := fun j => by
      have h := ((hmix (ν j) (hνB j)).2).comp (tendsto_sub_atTop_nat j)
      refine h.congr' (eventually_atTop.2 ⟨j + 1, fun m hm => ?_⟩)
      simp only [ha, Function.comp_apply, show j < m by omega, ↓reduceIte]
      rfl
    have hsum := hTm.add (tendsto_tsum_of_le hab hb hconv)
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) hle
  -- the phase averages
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  have hdne : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdt : (d : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top d
  have hdi : (d : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hdne
  set N : ℕ → ℕ := fun n => d * n + (d - 1) with hN
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_mul_of_pos_left n hd).trans le_self_add) tendsto_id
  have htime : ∀ n r, d * (n + 1) + r = N n + r + 1 := fun n r => by
    have h1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
    change d * (n + 1) + r = d * n + (d - 1) + r + 1
    rw [mul_add, mul_one]
    generalize d * n = k
    omega
  set ρbar : ℕ → Measure X := fun n => (d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, ρ (N n + r) with hρbar
  -- the chain against the comparison laws
  have hfirst : Tendsto (fun n => fNorm f ((d : ℝ≥0∞)⁻¹ •
      ∑ r ∈ range d, (P ^ (d * (n + 1) + r) : Kernel X X) x) (ρbar n)) atTop (𝓝 0) := by
    have hb : ∀ n, fNorm f ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, (P ^ (d * (n + 1) + r) : Kernel X X) x)
        (ρbar n) ≤ (d : ℝ≥0∞)⁻¹ * ∑ r ∈ range d,
          fNorm f ((P ^ (N n + r + 1) : Kernel X X) x) (ρ (N n + r)) := fun n => by
      have e : ∑ r ∈ range d, (P ^ (d * (n + 1) + r) : Kernel X X) x =
          ∑ r ∈ range d, (P ^ (N n + r + 1) : Kernel X X) x :=
        Finset.sum_congr rfl fun r _ => by rw [htime n r]
      rw [e]
      exact fNorm_smul_sum_le (range d) f _ _ hdi
    have hlim := ENNReal.Tendsto.const_mul (tendsto_finsetSum (range d) fun r _ =>
      he.comp (tendsto_atTop_mono (fun n => Nat.le_add_right (N n) r) hNt))
      (a := (d : ℝ≥0∞)⁻¹) (Or.inr hdi)
    rw [Finset.sum_const_zero, mul_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb
  -- the comparison laws against `π`
  have hσf : ∀ s, ∫⁻ y, f y ∂σ s ≤ d * ∫⁻ y, f y ∂π := fun s => by
    rw [hσdef, cycleInv, lintegral_smul_measure]
    exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
  have hcsum : ∑' j, c j ≠ ∞ := by rw [hc1]; exact ENNReal.one_ne_top
  set t : ℕ → ℝ≥0∞ := fun n => ∑' k, c (k + N n) with ht
  have htlim : Tendsto t atTop (𝓝 0) := (ENNReal.tendsto_sum_nat_add c hcsum).comp hNt
  have hSt : ∀ n, ∑ j ∈ range (N n), c j + t n = 1 := fun n => by
    rw [ht, ← hc1]
    exact ENNReal.summable.sum_add_tsum_nat_add' (k := N n)
  have hdπ : ∀ i : ZMod d, ∑ r ∈ range d, σ (i + r) = (d : ℝ≥0∞) • π := fun i => by
    have h := hD.eq_smul_sum_cycleInv hd hrec hπ i
    rw [h, smul_smul, ENNReal.mul_inv_cancel hdne hdt, one_smul]
  -- `ρ̄ₙ = (Σ_{j<N} cⱼ) π + Eₙ`
  set E : ℕ → Measure X := fun n => (d : ℝ≥0∞)⁻¹ • ∑ r ∈ range d, ∑ k ∈ range r,
    c (N n + k) • σ ((N n + r - (N n + k) : ℕ) : ZMod d) with hE
  have hdec : ∀ n, ρbar n = (∑ j ∈ range (N n), c j) • π + E n := fun n => by
    have h1 : ∀ r, ρ (N n + r) = ∑ j ∈ range (N n), c j • σ ((N n + r - j : ℕ) : ZMod d) +
        ∑ k ∈ range r, c (N n + k) • σ ((N n + r - (N n + k) : ℕ) : ZMod d) := fun r => by
      change ∑ j ∈ range (N n + r), c j • σ ((N n + r - j : ℕ) : ZMod d) = _
      rw [Finset.sum_range_add]
    have h2 : ∑ r ∈ range d, ∑ j ∈ range (N n), c j • σ ((N n + r - j : ℕ) : ZMod d) =
        ((d : ℝ≥0∞) * ∑ j ∈ range (N n), c j) • π := by
      rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N n := (Finset.mem_range.1 hj).le
      have e : ∀ r, ((N n + r - j : ℕ) : ZMod d) = ((N n - j : ℕ) : ZMod d) + (r : ZMod d) :=
        fun r => by rw [Nat.sub_add_comm hjN, Nat.cast_add]
      simp_rw [e]
      rw [← Finset.smul_sum, hdπ, smul_smul, mul_comm]
    rw [hρbar]
    simp only [h1]
    rw [Finset.sum_add_distrib, h2, smul_add, smul_smul, ← mul_assoc,
      ENNReal.inv_mul_cancel hdne hdt, one_mul]
  have hπdec : ∀ n, π = (∑ j ∈ range (N n), c j) • π + t n • π := fun n => by
    rw [← add_smul, hSt n, one_smul]
  have hEf : ∀ n, ∫⁻ y, f y ∂E n ≤ t n * (d * ∫⁻ y, f y ∂π) := fun n => by
    have hk : ∀ r ∈ range d, ∑ k ∈ range r, c (N n + k) ≤ t n := fun r hr => by
      calc ∑ k ∈ range r, c (N n + k) ≤ ∑ k ∈ range r, c (k + N n) :=
            le_of_eq (Finset.sum_congr rfl fun k _ => by rw [add_comm])
        _ ≤ t n := ENNReal.sum_le_tsum _
    rw [hE, lintegral_smul_measure, lintegral_finsetSum_measure]
    calc (d : ℝ≥0∞)⁻¹ * ∑ r ∈ range d, ∫⁻ y, f y ∂∑ k ∈ range r,
          c (N n + k) • σ ((N n + r - (N n + k) : ℕ) : ZMod d)
        ≤ (d : ℝ≥0∞)⁻¹ * ∑ r ∈ range d, t n * (d * ∫⁻ y, f y ∂π) := by
          refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r hr => ?_)
          rw [lintegral_finsetSum_measure]
          calc ∑ k ∈ range r, ∫⁻ y, f y ∂(c (N n + k) •
                σ ((N n + r - (N n + k) : ℕ) : ZMod d))
              ≤ ∑ k ∈ range r, c (N n + k) * (d * ∫⁻ y, f y ∂π) := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [lintegral_smul_measure]
                exact mul_le_mul' le_rfl (hσf _)
            _ = (∑ k ∈ range r, c (N n + k)) * (d * ∫⁻ y, f y ∂π) := by rw [Finset.sum_mul]
            _ ≤ t n * (d * ∫⁻ y, f y ∂π) := mul_le_mul' (hk r hr) le_rfl
      _ = t n * (d * ∫⁻ y, f y ∂π) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hdne hdt, one_mul]
  have hsecond : ∀ n, fNorm f (ρbar n) π ≤ t n * (d * ∫⁻ y, f y ∂π) + t n * ∫⁻ y, f y ∂π :=
    fun n => by
      have heq : ρbar n + t n • π = π + E n := by
        conv_rhs => rw [hπdec n]
        rw [hdec n, add_right_comm]
      refine (fNorm_le_of_add_eq heq).trans (add_le_add (hEf n) (le_of_eq ?_))
      rw [lintegral_smul_measure, smul_eq_mul]
  have htle : ∀ n, t n ≤ 1 := fun n => by rw [← hSt n]; exact le_add_self
  have hmid : ∀ n, ∫⁻ y, f y ∂ρbar n ≠ ∞ := fun n => by
    rw [hdec n, lintegral_add_measure, lintegral_smul_measure]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
      (by rw [← hSt n]; exact le_self_add)) hπf, ne_top_of_le_ne_top ?_ (hEf n)⟩
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (htle n))
      (ENNReal.mul_ne_top hdt hπf)
  have hlim2 : Tendsto (fun n => t n * (d * ∫⁻ y, f y ∂π) + t n * ∫⁻ y, f y ∂π) atTop
      (𝓝 0) := by
    have h := (ENNReal.Tendsto.mul_const htlim (Or.inr (ENNReal.mul_ne_top hdt hπf))).add
      (ENNReal.Tendsto.mul_const htlim (Or.inr hπf))
    rwa [zero_mul, zero_mul, add_zero] at h
  have hsum := hfirst.add hlim2
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (fNorm_triangle _ _ π (hmid n)).trans (add_le_add le_rfl (hsecond n))

end MeynTweedie.FErgodicity
