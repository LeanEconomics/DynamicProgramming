/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.UniformModels
import VUniformErgodicity.NSSPeriodicity

/-!
# Uniform ergodicity of Lagrange stable nonlinear state space models (MT §16.2.3)

Meyn and Tweedie, Lemma 16.2.6 and Theorem 16.2.7, pp. 406–407, for the NSS(F) model
`Φₖ₊₁ = F(Φₖ, Wₖ₊₁)` (`nssKernel Γ F`) under (NSS1)–(NSS3): `F` is `C¹`, the disturbance law `Γ`
has a lower semicontinuous density `γ` (`IsLSCDensity`), and the control model CM(F) has the rank
condition (forward accessibility, `RankCondition`), is M-irreducible (`IsMIrreducible`) and has an
aperiodic minimal set (`IsPeriodOf F O M 1`). The model is **Lagrange stable** when every
`A₊(x) = closure` of the states reachable from `x` is compact. `UniformModels` proves the abstract
form `theorem_16_2_7_restrict`, for a `ψ`-irreducible aperiodic T-chain and a compact absorbing
set; here these hypotheses are derived from Theorem 7.3.5 (ii) (`theorem_7_3_5_ii`, from the
Chapter 7 project) and Proposition 7.2.2 (i).

* `isAbsorbing_closure_reach`: `A₊(x)` is closed and absorbing (Proposition 7.2.2 (i)).
* **`lemma_16_2_6`** (p. 406): for every `x`, `A₊(x)` is closed, absorbing and small.
* `eq_of_isInvariant_of_isPositive`: a positive chain has at most one invariant probability
  (Proposition 10.1.1 and Theorem 10.4.4).
* `isInvariant_map_val`, `map_val_restrictKernel_pow`: invariant laws and `n`-step laws of a
  restricted chain, carried to the ambient space.
* **`theorem_16_2_7`** (p. 407): there is a unique invariant probability `π`; for every `x` the
  chain restricted to `A₊(x)` is uniformly ergodic, with invariant law the restriction of `π`;
  and for every measurable `f` bounded on compact sets and every initial state `y`,
  `|E_y[f(Φₙ)] − ∫ f dπ| ≤ R ρ^{⌊n/m⌋}` with `ρ < 1`.

**Hypotheses.** The book's "M-irreducible and aperiodic" is M-irreducibility together with a
minimal set of period one, the setting of Theorem 7.3.5 (ii).
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Restricted chains on the ambient space -/

/-- The `n`-step law of a restricted chain, seen on the ambient space, is the `n`-step law of the
chain: `P_Aⁿ(x, ·) ∘ val⁻¹ = Pⁿ(x, ·)`. -/
theorem map_val_restrictKernel_pow {Y : Type*} [MeasurableSpace Y] (P : Kernel Y Y)
    [IsMarkovKernel P] {A : Set Y} (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (n : ℕ)
    (x : A) : ((restrictKernel P hA ^ n) x).map Subtype.val = (P ^ n) x.1 := by
  ext B hB
  have hB' : MeasurableSet (Subtype.val ⁻¹' B : Set A) := measurable_subtype_coe hB
  rw [Measure.map_apply measurable_subtype_coe hB, restrictKernel_pow_apply P hA hAbs n x hB',
    Subtype.image_preimage_coe, inter_comm]
  exact measure_inter_conull (hAbs.pow_compl hA n x.2)

/-- An invariant law of a restricted chain is, on the ambient space, invariant for the chain. -/
theorem isInvariant_map_val {Y : Type*} [MeasurableSpace Y] (P : Kernel Y Y) [IsMarkovKernel P]
    {A : Set Y} (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) {μ : Measure A}
    (hμ : IsInvariant (restrictKernel P hA) μ) : IsInvariant P (μ.map Subtype.val) := by
  have hM := isMarkovKernel_restrictKernel P hA hAbs
  ext B hB
  rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) measurable_subtype_coe,
    Measure.map_apply measurable_subtype_coe hB]
  conv_rhs => rw [← hμ]
  rw [Measure.bind_apply (measurable_subtype_coe hB) (Kernel.measurable _).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [restrictKernel_apply P hA x (measurable_subtype_coe hB), Subtype.image_preimage_coe,
    inter_comm]
  exact (measure_inter_conull (prob_compl_eq_zero_iff hA |>.2 (hAbs x x.2))).symm

/-- **A positive chain has at most one invariant probability** (Proposition 10.1.1 and
Theorem 10.4.4). -/
theorem eq_of_isInvariant_of_isPositive {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] {P : Kernel Y Y} [IsMarkovKernel P] {ψ : Measure Y}
    (hpos : IsPositive P ψ) {μ ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsInvariant P μ) (hν : IsInvariant P ν) : μ = ν := by
  have hrec := proposition_10_1_1 hpos
  obtain ⟨c, -, h⟩ := hrec.exists_eq_smul ⟨inferInstance, hμ.le⟩ ⟨inferInstance, hν.le⟩
    (IsProbabilityMeasure.ne_zero ν)
  have h1 : μ univ = (c • ν) univ := by rw [← h]
  rw [Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul, mul_one] at h1
  rw [h, ← h1, one_smul]

/-! ### The NSS(F) model -/

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- **`A₊(x)` is closed and absorbing** (MT p. 406, Proposition 7.2.2 (i)): the closure of the
states reachable from `x` is a closed invariant set of CM(F), hence absorbing for NSS(F). -/
theorem isAbsorbing_closure_reach {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) (x : X) :
    IsAbsorbing (nssKernel Γ F) (closure (reach F (controlSet γ) x)) := by
  have hFx : ∀ w ∈ controlSet γ, Continuous fun x => F (x, w) := fun w _ =>
    hF.comp (continuous_id.prodMk continuous_const)
  exact (proposition_7_2_2_i hΓ hF isClosed_closure).2 (isCMInvariant_closure_reach hFx x)

/-- **Lemma 16.2.6** (MT p. 406): if CM(F) is forward accessible, M-irreducible and aperiodic
and NSS(F) satisfies (NSS1)–(NSS3), then for a Lagrange stable model every `A₊(x)` is closed,
absorbing and small. -/
theorem lemma_16_2_6 {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) (hirr : IsMIrreducible F (controlSet γ))
    {M : Set X} (hM : IsMinimal F (controlSet γ) M) (hap : IsPeriodOf F (controlSet γ) M 1)
    (hlag : ∀ x, IsCompact (closure (reach F (controlSet γ) x))) (x : X) :
    have := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
    IsClosed (closure (reach F (controlSet γ) x)) ∧
      IsAbsorbing (nssKernel Γ F) (closure (reach F (controlSet γ) x)) ∧
      IsSmall (nssKernel Γ F) (closure (reach F (controlSet γ) x)) := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  obtain ⟨ψ, hψ, hap', hT⟩ := theorem_7_3_5_ii hΓ hF hrank hirr hM hap
  exact ⟨isClosed_closure, isAbsorbing_closure_reach hΓ hF.continuous x,
    isSmall_of_isCompact_tChain hψ hap' hT (hlag x)⟩

/-- **Theorem 16.2.7** (MT p. 407): suppose NSS(F) satisfies (NSS1)–(NSS3) and CM(F) is forward
accessible, Lagrange stable, M-irreducible and aperiodic. Then there is a unique invariant
probability `π`; for every `x` the chain restricted to the absorbing set `A₊(x)` is uniformly
ergodic, with invariant law the restriction of `π`; and for every measurable `f` bounded on
compact sets and every initial state `y`, `E_y[f(Φₙ)] → ∫ f dπ` at a geometric rate,
`|E_y[f(Φₙ)] − ∫ f dπ| ≤ R ρ^{⌊n/m⌋}` with `ρ < 1`. -/
theorem theorem_16_2_7 {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) (hirr : IsMIrreducible F (controlSet γ))
    {M : Set X} (hM : IsMinimal F (controlSet γ) M) (hap : IsPeriodOf F (controlSet γ) M 1)
    (hlag : ∀ x, IsCompact (closure (reach F (controlSet γ) x))) :
    have := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant (nssKernel Γ F) π ∧
      (∀ ν : Measure X, IsProbabilityMeasure ν → IsInvariant (nssKernel Γ F) ν → ν = π) ∧
      (∀ x, ∃ μ : Measure (closure (reach F (controlSet γ) x)), IsProbabilityMeasure μ ∧
        IsUniformlyErgodic (restrictKernel (nssKernel Γ F) isClosed_closure.measurableSet) μ ∧
        μ.map Subtype.val = π) ∧
      ∀ f : X → ℝ, Measurable f → (∀ K : Set X, IsCompact K → ∃ c, ∀ y ∈ K, |f y| ≤ c) →
        ∀ y, ∃ R ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ m : ℕ, ∀ n,
          |∫ z, f z ∂(nssKernel Γ F ^ n) y - ∫ z, f z ∂π| ≤ R * ρ ^ (n / m) := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  obtain ⟨ψ, hψ, hap', hT⟩ := theorem_7_3_5_ii hΓ hF hrank hirr hM hap
  set A : X → Set X := fun x => closure (reach F (controlSet γ) x) with hAdef
  have hAm : ∀ x, MeasurableSet (A x) := fun x => isClosed_closure.measurableSet
  have hAbs : ∀ x, IsAbsorbing (nssKernel Γ F) (A x) := fun x =>
    isAbsorbing_closure_reach hΓ hF.continuous x
  have hne : ∀ x, (A x).Nonempty := fun x =>
    ⟨x, subset_closure (self_mem_reach F (controlSet γ) x)⟩
  have hres := fun x => theorem_16_2_7_restrict hψ hap' hT (hlag x) (hAm x) (hAbs x) (hne x)
  -- the invariant probability, from the restriction to `A₊(0)`
  obtain ⟨μ₀, hμ₀P, hμ₀U, -⟩ := hres 0
  have hπinv : IsInvariant (nssKernel Γ F) (μ₀.map Subtype.val) :=
    isInvariant_map_val _ (hAm 0) (hAbs 0) hμ₀U.1
  have hpos : IsPositive (nssKernel Γ F) ψ := ⟨hψ, _, inferInstance, hπinv⟩
  have huniq : ∀ ν : Measure X, IsProbabilityMeasure ν → IsInvariant (nssKernel Γ F) ν →
      ν = μ₀.map Subtype.val := fun ν _ hν => eq_of_isInvariant_of_isPositive hpos hν hπinv
  have hmapx : ∀ x (μ : Measure (A x)), IsProbabilityMeasure μ →
      IsUniformlyErgodic (restrictKernel (nssKernel Γ F) (hAm x)) μ →
      μ.map Subtype.val = μ₀.map Subtype.val := fun x μ _ hU =>
    huniq _ inferInstance (isInvariant_map_val _ (hAm x) (hAbs x) hU.1)
  refine ⟨μ₀.map Subtype.val, inferInstance, hπinv, huniq, fun x => ?_, fun f hf hfK y => ?_⟩
  · obtain ⟨μ, hμP, hμU, -⟩ := hres x
    exact ⟨μ, hμP, hμU, hmapx x μ hμP hμU⟩
  · obtain ⟨μ, hμP, hμU, m, ρ, hρ0, hρ1, -, hbd⟩ := hres y
    obtain ⟨c, hc⟩ := hfK (A y) (hlag y)
    have hM' := isMarkovKernel_restrictKernel (nssKernel Γ F) (hAm y) (hAbs y)
    set c' := max c 1 with hc'
    have hc'pos : 0 < c' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hfA : ∀ z : A y, |f z.1| ≤ c' := fun z => (hc z.1 z.2).trans (le_max_left _ _)
    refine ⟨c' * 2, ρ, hρ0, hρ1, m, fun n => ?_⟩
    have h := hbd (fun z => f z.1) (hf.comp measurable_subtype_coe) c' hc'pos hfA
      ⟨y, subset_closure (self_mem_reach F (controlSet γ) y)⟩ n
    have := isMarkovKernel_pow (restrictKernel (nssKernel Γ F) (hAm y)) n
    rw [← integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
      ← integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
      map_val_restrictKernel_pow _ (hAm y) (hAbs y), hmapx y μ hμP hμU] at h
    calc |∫ z, f z ∂(nssKernel Γ F ^ n) y - ∫ z, f z ∂μ₀.map Subtype.val|
        ≤ c' * (2 * ρ ^ (n / m)) := h
      _ = c' * 2 * ρ ^ (n / m) := by ring

end MeynTweedie.VUniformErgodicity
