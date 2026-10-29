/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.DriftExamples

/-!
# Non-positivity of the SETAR model on all its margins (MT §11.5.2)

Copied for Chapter 19 from the Chapter 11 project
(`DriftRegularity/SetarNullMargins.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, §11.5.1–§11.5.2, pp. 278–284. The book states Proposition 11.5.5 for all
five margins (11.45)–(11.49) of the SETAR parameter space but proves only (11.49) (formalised as
`proposition_11_5_5` in `DriftExamples`); this module proves the other four.

**Theorems 11.5.1 and 11.5.2 with (11.43) off `C`.** `theorem_11_5_1_off`, `theorem_11_5_2_off`:
the bound on the mean increments, `∫ P(x, dy) |V(y) − V(x)| ≤ B`, is needed only for `x ∉ C`
(before `σ_C` the chain is off `C`). The proofs are those of `theorem_11_5_1` and
`theorem_11_5_2` (copied from `NonPositivity`, with `integrable_of_increment_le` for one
state). This matters for the margins: with `V(x) = x⁺` the increments are bounded at `+∞` but not
at `−∞` when the bottom regime jumps (`θ(1) < 0`).

**A unit-slope end.**
* `setar_null_of_top_unit`: under (SETAR1)–(SETAR2), if `θ(M) = 1` and `φ(M) ≥ 0` the SETAR
  model is non-positive, whatever the other parameters: `V(x) = x⁺`, `C = (−∞, R]`,
  `C⁺ = (R, ∞)`, and above `R` the chain is the random walk `x + φ(M) + W(M)`.
* `setar_null_of_bot_unit`: the mirror statement, `θ(1) = 1`, `φ(1) ≤ 0`, `V(x) = x⁻`.

**Proposition 11.5.5 on the margins.**
* `proposition_11_5_5_margins` (p. 283): the SETAR model is non-positive on (11.45)–(11.48);
  (11.45) and (11.47) have `θ(M) = 1, φ(M) = 0`, (11.46) and (11.48) have `θ(1) = 1, φ(1) = 0`.
* `proposition_11_5_5_all`: non-positivity on all five margins (11.45)–(11.49).

**Hypotheses.** Only (SETAR1)–(SETAR2) with integrable, mean-zero noise are used; the finite
variances of (SETAR3) are not needed for non-positivity.

**Corrections.** None: the statement for (11.45)–(11.48), which the book gives without proof, is
true. (The correction to the book's proof for (11.49) is recorded in `DriftExamples`.)
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-- One mean increment bound at `x` makes `V` integrable under `P(x, ·)`. -/
theorem integrable_of_increment_le {V : X → ℝ} (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞)
    [IsMarkovKernel P] {x : X} (hinc : ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) :
    Integrable V (P x) := by
  refine ⟨hV.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ y, ‖V y‖ₑ ∂P x ≤ ∫⁻ y, (‖V y - V x‖ₑ + ‖V x‖ₑ) ∂P x := lintegral_mono fun y => by
        calc ‖V y‖ₑ = ‖(V y - V x) + V x‖ₑ := by rw [sub_add_cancel]
          _ ≤ _ := enorm_add_le _ _
    _ = ∫⁻ y, ‖V y - V x‖ₑ ∂P x + ‖V x‖ₑ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hinc.trans_lt hB.lt_top, enorm_lt_top⟩

/-- **Theorem 11.5.1** (MT p. 278), with (11.43) required only off `C`: if `ΔV ≥ 0` off `C`
(11.42), `sup_{x ∉ C} ∫ P(x, dy) |V(y) − V(x)| < ∞`, and `V(x₀) > V(x)` for every `x ∈ C`
(11.44), then `E_{x₀}[τ_C] = ∞`. The proof is that of `theorem_11_5_1`: before `σ_C` the chain
is off `C`. -/
theorem theorem_11_5_1_off [IsMarkovKernel P] {V : X → ℝ} (hV : Measurable V)
    {C : Set X} (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂P x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x ∉ C, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    {x₀ : X} (hx₀ : ∀ x ∈ C, V x < V x₀) : meanReturnTime P C x₀ = ∞ := by
  have hx₀C : x₀ ∉ C := fun h => lt_irrefl _ (hx₀ x₀ h)
  have := isMarkovKernel_pathKernel P
  by_contra hfin
  set μ := pathKernel P x₀ with hμ
  have hσ := (proposition_3_4_4 hC).2
  have hGk := measurableSet_lt_of_isStoppingTime hσ
  have hG : ∀ k : ℕ, MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstHit C ω} :=
    fun k => (natFilt (X := X)).le k _ (hGk k)
  have hEσ : ∫⁻ ω, ENat.toENNReal (firstHit C ω) ∂μ ≠ ∞ := by
    change meanHitTime P C x₀ ≠ ∞; rwa [meanHitTime_of_notMem P hC hx₀C]
  -- the increments before `σ_C`
  set F : ℕ → (ℕ → X) → ℝ := fun k => {ω | (k : WithTop ℕ) < firstHit C ω}.indicator
    fun ω => V (ω (k + 1)) - V (ω k) with hFdef
  have hDm : ∀ k, Measurable fun ω : ℕ → X => V (ω (k + 1)) - V (ω k) := fun k =>
    (hV.comp (measurable_pi_apply (k + 1))).sub (hV.comp (measurable_pi_apply k))
  have hFm : ∀ k, Measurable (F k) := fun k => (hDm k).indicator (hG k)
  have hpairm : Measurable fun p : X × X => ‖V p.2 - V p.1‖ₑ :=
    ((hV.comp measurable_snd).sub (hV.comp measurable_fst)).enorm
  have hDnorm : ∀ k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstHit C ω},
      ‖V (ω (k + 1)) - V (ω k)‖ₑ ∂μ ≤ B * μ {ω | (k : WithTop ℕ) < firstHit C ω} := fun k => by
    have hpair := setLIntegral_pair P (Measure.dirac x₀) (hGk k) hpairm
    rw [pathMeasure_dirac] at hpair
    rw [hpair, ← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun ω hω => hinc (ω k) (notMem_of_lt_firstHit hω)
  have hFnorm : ∀ k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≤ B * μ {ω | (k : WithTop ℕ) < firstHit C ω} :=
    fun k => by
      simp_rw [hFdef, enorm_indicator_eq_indicator_enorm]
      rw [lintegral_indicator (hG k)]
      exact hDnorm k
  have hsum : ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hB hEσ) ?_
    calc ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≤ ∑' k : ℕ, B * μ {ω | (k : WithTop ℕ) < firstHit C ω} :=
          ENNReal.tsum_le_tsum hFnorm
      _ = B * ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstHit C ω}, 1 ∂μ := by
          rw [ENNReal.tsum_mul_left]; simp
      _ = B * ∫⁻ ω, ENat.toENNReal (firstHit C ω) ∂μ := by
          simp_rw [toENNReal_eq_sumBefore_one (firstHit C)]
          rw [lintegral_sumBefore μ hG fun _ => measurable_const]
  -- each increment has nonnegative mean, by (11.42)
  have hFpos : ∀ k, 0 ≤ ∫ ω, F k ω ∂μ := fun k => by
    have hint : IntegrableOn (fun ω : ℕ → X => V (ω (k + 1)) - V (ω k))
        {ω | (k : WithTop ℕ) < firstHit C ω} (pathMeasure P (Measure.dirac x₀)) := by
      rw [pathMeasure_dirac]
      exact ⟨(hDm k).aestronglyMeasurable, (hDnorm k).trans_lt
        (ENNReal.mul_lt_top hB.lt_top (measure_lt_top _ _))⟩
    rw [hFdef, integral_indicator (hG k), hμ, ← pathMeasure_dirac,
      setIntegral_pair P (Measure.dirac x₀) (hGk k)
        (h := fun p : X × X => V p.2 - V p.1)
        ((hV.comp measurable_snd).sub (hV.comp measurable_fst)) hint]
    refine setIntegral_nonneg (hG k) fun ω hω => ?_
    have hωk : ω k ∉ C := notMem_of_lt_firstHit hω
    have hVi := integrable_of_increment_le hV hB (hinc (ω k) hωk)
    change 0 ≤ ∫ z, (V z - V (ω k)) ∂P (ω k)
    rw [integral_sub hVi (integrable_const _), integral_const, smul_eq_mul, probReal_univ,
      one_mul]
    linarith [hdrift (ω k) hωk]
  -- `σ_C < ∞` and `Φ₀ = x₀`, almost surely
  have hae_fin : ∀ᵐ ω ∂μ, firstHit C ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_toENNReal_firstHit hC) hEσ] with ω hω
    intro h
    rw [h, show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top] at hω
    exact lt_irrefl _ hω
  have hae0 : ∀ᵐ ω ∂μ, V (ω 0) = V x₀ := by
    have hm : MeasurableSet {y | V y ≠ V x₀} := (measurableSet_singleton _).compl.preimage hV
    have h0 : μ {ω | ω 0 ∈ {y | V y ≠ V x₀}} = 0 := by
      rw [hμ, pathKernel_zero_mem P x₀ hm, indicator_of_notMem (by simp)]
    exact measure_mono_null (fun ω hω => hω) h0
  set Vs : (ℕ → X) → ℝ := fun ω => V (stoppedState (firstHit C) ω) with hVsdef
  have hVs : Measurable Vs := hV.comp (measurable_stoppedState hσ)
  -- pathwise, the increments telescope
  have hsupp : ∀ ω (t : ℕ), firstHit C ω = WithTop.some t → ∀ k ∉ Finset.range t, F k ω = 0 :=
    fun ω t ht k hk => by
      refine indicator_of_notMem (fun h => hk (Finset.mem_range.2 ?_)) _
      have h' : (k : WithTop ℕ) < WithTop.some t := ht ▸ h
      rw [Nat.cast_withTop] at h'
      exact WithTop.coe_lt_coe.1 h'
  have htel : ∀ᵐ ω ∂μ, ∑' k, F k ω = Vs ω - V x₀ := by
    filter_upwards [hae_fin, hae0] with ω hω h0
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    have hF : ∀ k ∈ Finset.range t, F k ω = V (ω (k + 1)) - V (ω k) := fun k hk => by
      refine indicator_of_mem (s := {ω | (k : WithTop ℕ) < firstHit C ω})
        (show (k : WithTop ℕ) < firstHit C ω by
        rw [← ht, Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 (Finset.mem_range.1 hk)) _
    rw [Finset.sum_congr rfl hF, Finset.sum_range_sub (fun k => V (ω k)), ← h0, hVsdef]
    simp only [stoppedState_of_eq ht.symm]
  have hnorm : ∀ᵐ ω ∂μ, ‖∑' k, F k ω‖ₑ ≤ ∑' k, ‖F k ω‖ₑ := by
    filter_upwards [hae_fin] with ω hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  -- `V(x₀) − V(Φ_σ)` is integrable, has integral `−Σ E[F_k] ≤ 0`, and is positive a.s.
  have hDint : Integrable (fun ω => V x₀ - Vs ω) μ := by
    refine ⟨(measurable_const.sub hVs).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ ω, ‖V x₀ - Vs ω‖ₑ ∂μ = ∫⁻ ω, ‖∑' k, F k ω‖ₑ ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [htel] with ω hω
          rw [hω, ← enorm_neg, neg_sub]
      _ ≤ ∫⁻ ω, ∑' k, ‖F k ω‖ₑ ∂μ := lintegral_mono_ae hnorm
      _ = ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ := lintegral_tsum fun k => (hFm k).enorm.aemeasurable
      _ < ∞ := hsum.lt_top
  have hle : ∫ ω, (V x₀ - Vs ω) ∂μ ≤ 0 := by
    calc ∫ ω, (V x₀ - Vs ω) ∂μ = ∫ ω, -∑' k, F k ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [htel] with ω hω
          rw [hω, neg_sub]
      _ = -∑' k, ∫ ω, F k ω ∂μ := by
          rw [integral_neg, integral_tsum (fun k => (hFm k).aestronglyMeasurable) hsum]
      _ ≤ 0 := neg_nonpos.2 (tsum_nonneg hFpos)
  have hpos_ae : ∀ᵐ ω ∂μ, 0 < V x₀ - Vs ω := by
    filter_upwards [hae_fin] with ω hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    have hmem : ω t ∈ C := mem_of_firstHit_eq ht.symm
    simp only [hVsdef, stoppedState_of_eq ht.symm, sub_pos]
    exact hx₀ _ hmem
  have hgt : 0 < ∫ ω, (V x₀ - Vs ω) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg_ae (hpos_ae.mono fun ω h => h.le) hDint).2 ?_
    have hc : μ (Function.support fun ω => V x₀ - Vs ω)ᶜ = 0 :=
      ae_iff.1 (hpos_ae.mono fun ω h => h.ne')
    by_contra h0
    have h0' : μ (Function.support fun ω => V x₀ - Vs ω) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have := measure_union_le (μ := μ) (Function.support fun ω => V x₀ - Vs ω)
      (Function.support fun ω => V x₀ - Vs ω)ᶜ
    rw [union_compl_self, measure_univ, h0', hc, add_zero] at this
    exact absurd this (by simp)
  linarith

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.5.2** (MT p. 279), with (11.43) required only off `C`: for a `ψ`-irreducible
chain, if `V` satisfies (11.42) off a set `C ∈ B⁺(X)`, its increments are bounded in mean off
`C`, and the set `C⁺` of states where `V` exceeds every value on `C` is in `B⁺(X)`, then the
chain is non-positive (null). -/
theorem theorem_11_5_2_off [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {V : X → ℝ} (hV : Measurable V) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C)
    (hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂P x) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ x ∉ C, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) (hψCp : 0 < ψ {x | ∀ y ∈ C, V y < V x}) :
    IsNull P ψ := by
  refine ⟨hψ, fun hex => ?_⟩
  obtain ⟨S, -, hfull, -, Cs, hCs, hcov⟩ := (theorem_11_1_4 hψ).1 ⟨hψ, hex⟩
  set Cp := {x | ∀ y ∈ C, V y < V x}
  obtain ⟨n, hn⟩ : ∃ n, 0 < ψ (Cp ∩ Cs n) := by
    by_contra hc
    push Not at hc
    have h1 : Cp ⊆ (⋃ n, Cp ∩ Cs n) ∪ Sᶜ := fun x hx => by
      by_cases hS : x ∈ S
      · rw [← hcov] at hS
        obtain ⟨n, hn⟩ := mem_iUnion.1 hS
        exact Or.inl (mem_iUnion.2 ⟨n, hx, hn⟩)
      · exact Or.inr hS
    have h2 : ψ Cp = 0 := measure_mono_null h1 (measure_union_null
      (measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)) hfull)
    exact hψCp.ne' h2
  obtain ⟨x, hxp, hxn⟩ := nonempty_of_measure_ne_zero hn.ne'
  obtain ⟨M, hM, hbound⟩ := (hCs n).2 C hC hψC
  have hinf := theorem_11_5_1_off hV hC hdrift hB hinc hxp
  exact hM (top_le_iff.1 (hinf ▸ hbound x hxn))

/-! ### The SETAR model with a unit-slope end -/

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **A unit-slope top end with nonnegative intercept makes the SETAR model null.** Under
(SETAR1)–(SETAR2), if `θ(M) = 1` and `φ(M) ≥ 0`, the chain is non-positive, whatever the other
parameters. The test function is `V(x) = x⁺` with `C = (−∞, R]`: above `R` the chain moves as
`x + φ(M) + W(M)`, so `PV(x) ≥ x + φ(M) ≥ V(x)` and `|V(y) − V(x)| ≤ |φ(M)| + |W(M)|`. -/
theorem setar_null_of_top_unit (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hθ : θ (Fin.last m) = 1) (hφ : 0 ≤ φ (Fin.last m)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsNull (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, -, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set M := Fin.last m
  set T := ∑ i, |r i| with hTdef
  have hTr : ∀ i, |r i| ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R := T + 1 with hRdef
  have hR0 : 0 < R := by linarith
  have hregM : ∀ x, R < x → setarRegime r x = M := fun x hx =>
    setarRegime_of_gt r fun i => by linarith [le_abs_self (r i), hTr i]
  set V : ℝ → ℝ := fun y => max y 0 with hVdef
  have hVm : Measurable V := measurable_id.max measurable_const
  have hmap := setarKernel_eq_map Γ φ θ r
  set C := Iic R with hCdef
  have hnotC : ∀ x ∉ C, R < x := fun x hx => not_le.1 hx
  have hVi : ∀ j (c0 : ℝ), Integrable (fun w => V (c0 + w)) (Γ j) := fun j c0 =>
    Integrable.mono' ((integrable_const |c0|).add (hW j).abs)
      (hVm.comp (measurable_const_add c0)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        simp only [hVdef, Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [abs_add_le c0 w, le_abs_self (c0 + w)])
          (by positivity))
  have hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂setarKernel Γ φ θ r x := fun x hx => by
    have hxR := hnotC x hx
    rw [hmap, integral_map (measurable_const_add _).aemeasurable hVm.aestronglyMeasurable,
      hregM x hxR, hθ, one_mul]
    calc V x = φ M + x + 1 * 0 - φ M := by
          simp only [hVdef, max_eq_left (by linarith : (0 : ℝ) ≤ x)]; ring
      _ ≤ φ M + x + 1 * 0 := by linarith
      _ = ∫ w, (φ M + x + 1 * w) ∂Γ M := by
          rw [integral_affine_zeroMean (Γ M) (hW M) (hW0 M)]; ring
      _ ≤ _ := integral_mono ((integrable_const _).add ((hW M).const_mul _)) (hVi M _)
          fun w => by simp only [hVdef, one_mul]; exact le_max_left _ _
  have hinc : ∀ x ∉ C, ∫⁻ y, ‖V y - V x‖ₑ ∂setarKernel Γ φ θ r x ≤
      ENNReal.ofReal (|φ M| + ∫ w, |w| ∂Γ M) := fun x hx => by
    have hxR := hnotC x hx
    have hm : Measurable fun y => ‖V y - V x‖ₑ := (hVm.sub measurable_const).enorm
    rw [hmap, lintegral_map hm (measurable_const_add _), hregM x hxR, hθ]
    have hint : Integrable (fun w : ℝ => |φ M| + |w|) (Γ M) :=
      (integrable_const _).add (hW M).abs
    calc ∫⁻ w, ‖V (φ M + 1 * x + w) - V x‖ₑ ∂Γ M
        ≤ ∫⁻ w, ENNReal.ofReal (|φ M| + |w|) ∂Γ M := lintegral_mono fun w => by
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ((abs_max_sub_max_le_abs _ _ _).trans ?_)
          rw [show φ M + 1 * x + w - x = φ M + w by ring]
          exact abs_add_le _ _
      _ = ENNReal.ofReal (∫ w, (|φ M| + |w|) ∂Γ M) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun w => by positivity)).symm
      _ = ENNReal.ofReal (|φ M| + ∫ w, |w| ∂Γ M) := by
          rw [integral_add (integrable_const _) (hW M).abs, integral_const]
          simp only [probReal_univ, smul_eq_mul, one_mul]
  have hψC : 0 < volume C := by rw [hCdef, Real.volume_Iic]; exact ENNReal.zero_lt_top
  have hCp : Ioi R ⊆ {x | ∀ y ∈ C, V y < V x} := fun x hx y hy => by
    have hxR : R < x := hx
    have hyR : y ≤ R := hy
    simp only [hVdef, max_eq_left (by linarith : (0 : ℝ) ≤ x)]
    exact max_lt (by linarith) (by linarith)
  have hψCp : 0 < volume {x | ∀ y ∈ C, V y < V x} :=
    lt_of_lt_of_le (by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top) (measure_mono hCp)
  exact theorem_11_5_2_off hψ hVm measurableSet_Iic hψC hdrift ENNReal.ofReal_ne_top hinc hψCp

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **A unit-slope bottom end with nonpositive intercept makes the SETAR model null.** Under
(SETAR1)–(SETAR2), if `θ(1) = 1` and `φ(1) ≤ 0`, the chain is non-positive, whatever the other
parameters. The test function is `V(x) = x⁻` with `C = [−R, ∞)`. -/
theorem setar_null_of_bot_unit (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hθ : θ 0 = 1) (hφ : φ 0 ≤ 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsNull (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, -, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set T := ∑ i, |r i| with hTdef
  have hTr : ∀ i, |r i| ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R := T + 1 with hRdef
  have hR0 : 0 < R := by linarith
  have hreg0 : ∀ x, x < -R → setarRegime r x = 0 := fun x hx =>
    setarRegime_of_le r fun i => by linarith [neg_abs_le (r i), hTr i]
  set V : ℝ → ℝ := fun y => max (-y) 0 with hVdef
  have hVm : Measurable V := measurable_neg.max measurable_const
  have hmap := setarKernel_eq_map Γ φ θ r
  set C := Ici (-R) with hCdef
  have hnotC : ∀ x ∉ C, x < -R := fun x hx => not_le.1 hx
  have hVi : ∀ j (c0 : ℝ), Integrable (fun w => V (c0 + w)) (Γ j) := fun j c0 =>
    Integrable.mono' ((integrable_const |c0|).add (hW j).abs)
      (hVm.comp (measurable_const_add c0)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        simp only [hVdef, Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [abs_add_le c0 w, neg_abs_le (c0 + w)])
          (by positivity))
  have hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂setarKernel Γ φ θ r x := fun x hx => by
    have hxR := hnotC x hx
    rw [hmap, integral_map (measurable_const_add _).aemeasurable hVm.aestronglyMeasurable,
      hreg0 x hxR, hθ, one_mul]
    calc V x = -(φ 0 + x) + -1 * 0 + φ 0 := by
          simp only [hVdef, max_eq_left (by linarith : (0 : ℝ) ≤ -x)]; ring
      _ ≤ -(φ 0 + x) + -1 * 0 := by linarith
      _ = ∫ w, (-(φ 0 + x) + -1 * w) ∂Γ 0 := by
          rw [integral_affine_zeroMean (Γ 0) (hW 0) (hW0 0)]; ring
      _ ≤ _ := integral_mono ((integrable_const _).add ((hW 0).const_mul _)) (hVi 0 _)
          fun w => by simp only [hVdef]; exact le_max_of_le_left (by linarith)
  have hinc : ∀ x ∉ C, ∫⁻ y, ‖V y - V x‖ₑ ∂setarKernel Γ φ θ r x ≤
      ENNReal.ofReal (|φ 0| + ∫ w, |w| ∂Γ 0) := fun x hx => by
    have hxR := hnotC x hx
    have hm : Measurable fun y => ‖V y - V x‖ₑ := (hVm.sub measurable_const).enorm
    rw [hmap, lintegral_map hm (measurable_const_add _), hreg0 x hxR, hθ]
    have hint : Integrable (fun w : ℝ => |φ 0| + |w|) (Γ 0) :=
      (integrable_const _).add (hW 0).abs
    calc ∫⁻ w, ‖V (φ 0 + 1 * x + w) - V x‖ₑ ∂Γ 0
        ≤ ∫⁻ w, ENNReal.ofReal (|φ 0| + |w|) ∂Γ 0 := lintegral_mono fun w => by
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ((abs_max_sub_max_le_abs _ _ _).trans ?_)
          rw [show -(φ 0 + 1 * x + w) - -x = -(φ 0 + w) by ring, abs_neg]
          exact abs_add_le _ _
      _ = ENNReal.ofReal (∫ w, (|φ 0| + |w|) ∂Γ 0) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun w => by positivity)).symm
      _ = ENNReal.ofReal (|φ 0| + ∫ w, |w| ∂Γ 0) := by
          rw [integral_add (integrable_const _) (hW 0).abs, integral_const]
          simp only [probReal_univ, smul_eq_mul, one_mul]
  have hψC : 0 < volume C := by rw [hCdef, Real.volume_Ici]; exact ENNReal.zero_lt_top
  have hCp : Iio (-R) ⊆ {x | ∀ y ∈ C, V y < V x} := fun x hx y hy => by
    have hxR : x < -R := hx
    have hyR : -R ≤ y := hy
    simp only [hVdef, max_eq_left (by linarith : (0 : ℝ) ≤ -x)]
    exact max_lt (by linarith) (by linarith)
  have hψCp : 0 < volume {x | ∀ y ∈ C, V y < V x} :=
    lt_of_lt_of_le (by rw [Real.volume_Iio]; exact ENNReal.zero_lt_top) (measure_mono hCp)
  exact theorem_11_5_2_off hψ hVm measurableSet_Ici hψC hdrift ENNReal.ofReal_ne_top hinc hψCp

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.5.5 on the margins (11.45)–(11.48)** (MT p. 283), which the book states
without proof: under (SETAR1)–(SETAR2) the SETAR model is non-positive (null) in each of the
regions (11.45) `θ(1) < 1, θ(M) = 1, φ(M) = 0`; (11.46) `θ(1) = 1, θ(M) < 1, φ(1) = 0`;
(11.47) `θ(1) = θ(M) = 1, φ(M) = 0, φ(1) ≥ 0`; (11.48) `θ(1) = θ(M) = 1, φ(M) < 0, φ(1) = 0`.
(11.45) and (11.47) are cases of `setar_null_of_top_unit`, (11.46) and (11.48) of
`setar_null_of_bot_unit`. -/
theorem proposition_11_5_5_margins (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hreg : (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ φ 0 = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0 ∧ 0 ≤ φ 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ φ 0 = 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsNull (setarKernel Γ φ θ r) volume := by
  rcases hreg with ⟨-, hθ, hφ⟩ | ⟨hθ, -, hφ⟩ | ⟨-, hθ, hφ, -⟩ | ⟨hθ, -, -, hφ⟩
  · exact setar_null_of_top_unit Γ φ θ r h1 h2 hW hW0 hθ hφ.ge
  · exact setar_null_of_bot_unit Γ φ θ r h1 h2 hW hW0 hθ hφ.le
  · exact setar_null_of_top_unit Γ φ θ r h1 h2 hW hW0 hθ hφ.ge
  · exact setar_null_of_bot_unit Γ φ θ r h1 h2 hW hW0 hθ hφ.le

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.5.5** (MT p. 283) on all five margins (11.45)–(11.49): under
(SETAR1)–(SETAR2) the SETAR model is non-positive (null). The region (11.49),
`θ(1) < 0, θ(1)θ(M) = 1, φ(M) + θ(M)φ(1) = 0`, is `proposition_11_5_5`. -/
theorem proposition_11_5_5_all (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hreg : (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ φ 0 = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0 ∧ 0 ≤ φ 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ φ 0 = 0) ∨
      (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ φ (Fin.last m) + θ (Fin.last m) * φ 0 = 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsNull (setarKernel Γ φ θ r) volume := by
  rcases hreg with h | h | h | h | ⟨hθ1, hθ, hφ⟩
  · exact proposition_11_5_5_margins Γ φ θ r h1 h2 hW hW0 (Or.inl h)
  · exact proposition_11_5_5_margins Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inl h))
  · exact proposition_11_5_5_margins Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inr (Or.inl h)))
  · exact proposition_11_5_5_margins Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inr (Or.inr h)))
  · exact proposition_11_5_5 Γ φ θ r h1 h2 hW hW0 hθ1 hθ hφ.le

end MeynTweedie.GeneralizedDrift
