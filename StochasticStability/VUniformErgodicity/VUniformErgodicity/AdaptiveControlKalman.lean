/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.AdaptiveControl
import VUniformErgodicity.AdaptiveControlStability

/-!
# Proposition 16.5.2 for the Gaussian adaptive control model (MT §16.5.2)

Meyn and Tweedie, §16.5.2, pp. 416–417, for the Gaussian model (SAC1)–(SAC2),
`sacGaussianKernel`, on its state space `X = [σ_z², σ_z²/(1 − α²)] × ℝ²` (`sacSpace`). The module
`AdaptiveControl` proves Proposition 16.5.2 for general disturbances, assuming that the
restricted chain is `ψ`-irreducible and aperiodic and that compact sets are petite. Here these
hypotheses are derived for Gaussian disturbances from Proposition 7.4.3 (`proposition_7_4_3`, the
restricted chain is a `ψ`-irreducible aperiodic T-chain) and Theorem 6.2.5 (ii) (compact sets of a
`ψ`-irreducible T-chain are petite).

* `sacQ`: the chain restricted to `X`.
* `proposition_16_5_2_of_eq`: Proposition 16.5.2 of `AdaptiveControl`, for Gaussian
  disturbances, carried from `sacSet` to the equal set `sacSpace`.
* **`proposition_16_5_2_gaussian`** (p. 417): for `|α| < 1`, `α ≠ 0`, `σ_z, σ_w ≠ 0` and
  `σ_z² < 1`, the restricted chain is a positive, aperiodic T-chain, `V`-uniformly ergodic for
  `V = θ̃⁴ + ε₀θ̃²y² + ε₀²y² + 1` (16.44), and `E_x[Yₖ²] → ∫ y² dπ` geometrically fast (16.48).

**The steady state and (16.49).** The book obtains (16.49) from the identities
`θ̃ₖ = θₖ − E[θₖ | Y₀, …, Yₖ]` and `Σₖ = E[θ̃ₖ² | Y₀, …, Yₖ]` "in steady state". Here the steady
state is shown to be a Kalman law, and (16.49) follows with no further hypothesis.
* `lintegral_map_val_of_isInvariant`, `map_val_restrictKernel_pow_comp`: invariance and `n`-step
  laws of a restricted chain, seen on the ambient space.
* `ofReal_tvNorm_pow_comp_le`: `‖μQⁿ − π‖ ≤ |||Qⁿ − 1 ⊗ π|||_V (μ(V) + π(V))`.
* `isKalmanLaw_of_tendsto`: total variation limits of Kalman laws are Kalman laws (the Kalman
  property is the measure identity `ν = (ν ⊗ N(0, 1)) ∘ T⁻¹`, `T(φ, ξ) = (Σ, √Σ ξ, Y)`).
* **`isKalmanLaw_of_isInvariant`**: every invariant probability `π` is a Kalman law, `θ̃ ~ N(0, Σ)`
  given `(Σ, Y)`, as the total variation limit of the Kalman laws `μ₀Pⁿ` from `sacKalmanInit`
  (Proposition 12.5.2's filter); also `π(V) < ∞`.
* `lintegral_sacGaussian_Ysq` (16.45), `lintegral_sacGaussian_SYsq`: one-step moments.
* `sac_steady_state_identities` (p. 417): `E_π[Y²] = E_π[ΣY²] + σ_w²`,
  `E_π[ΣY²] = σ_z² E_π[Y²] + α²σ_w² E_π[Σ]` and `E_π[θ̃²] = E_π[Σ]`. The second comes from the
  stationarity of `ΣY²`, as `Σₖ₊₁` is a function of `(Σₖ, Yₖ)`.
* **`eq_16_49_gaussian`**: (16.49), `E_π[Y²] = σ_w²/(1 − σ_z²) (1 + α² E_π[θ̃²])`, and the bounds
  on the steady state performance, for every invariant probability.

**Hypotheses.** Proposition 7.4.3 needs `α ≠ 0` and `σ_z ≠ 0` (see `NSSAdaptiveControl`).
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- The Gaussian adaptive control chain restricted to its state space `sacSpace α σz`. -/
noncomputable def sacQ (α σz σw : ℝ) : Kernel (sacSpace α σz) (sacSpace α σz) :=
  restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet

/-- The restricted chain is a Markov kernel. -/
theorem isMarkovKernel_sacQ {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) :
    IsMarkovKernel (sacQ α σz σw) :=
  have := isMarkovKernel_sacGaussianKernel α σz σw
  isMarkovKernel_restrictKernel _ _ (isAbsorbing_sacSpace _ hα hσw)

/-- The two descriptions of the state space agree: `sacSpace α σz = sacSet α σz`. -/
theorem sacSpace_eq_sacSet (α σz : ℝ) : sacSpace α σz = sacSet α σz := by
  ext p
  simp only [sacSpace, sacSet, mem_prod, mem_univ, and_true, mem_ofPred_eq]

/-- The Gaussian moments used by `proposition_16_5_2`: `E Z² = σ_z²`, `E W = 0`, `E W² = σ_w²`, and
second and fourth moments finite. -/
theorem sacGaussian_moments (σz σw : ℝ) :
    Integrable (fun z => z ^ 2) (gaussianReal 0 (σz ^ 2).toNNReal) ∧
      ∫ z, z ^ 2 ∂gaussianReal 0 (σz ^ 2).toNNReal = σz ^ 2 ∧
      Integrable (fun z => z ^ 4) (gaussianReal 0 (σz ^ 2).toNNReal) ∧
      Integrable (fun w => w) (gaussianReal 0 (σw ^ 2).toNNReal) ∧
      ∫ w, w ∂gaussianReal 0 (σw ^ 2).toNNReal = 0 ∧
      Integrable (fun w => w ^ 2) (gaussianReal 0 (σw ^ 2).toNNReal) ∧
      ∫ w, w ^ 2 ∂gaussianReal 0 (σw ^ 2).toNNReal = σw ^ 2 ∧
      Integrable (fun w => w ^ 4) (gaussianReal 0 (σw ^ 2).toNNReal) := by
  have h4 : ∀ v : ℝ≥0, Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 v) := fun v => by
    have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((4 : ℕ) : ℝ≥0∞)
      (ENNReal.natCast_ne_top 4)).integrable_norm_pow (by norm_num)
    refine h.congr (ae_of_all _ fun z => ?_)
    change ‖z‖ ^ 4 = z ^ 4
    rw [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩]
  refine ⟨(memLp_id_gaussianReal 2).integrable_sq, ?_, h4 _,
    (memLp_id_gaussianReal 1).integrable le_rfl, integral_id_gaussianReal,
    (memLp_id_gaussianReal 2).integrable_sq, ?_, h4 _⟩
  · rw [integral_sq_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
  · rw [integral_sq_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]

/-- **Proposition 16.5.2 on an equal state space**: the conclusion of `proposition_16_5_2` for
Gaussian disturbances, for the chain restricted to any set `S = sacSet α σz`. -/
theorem proposition_16_5_2_of_eq {α σz σw : ℝ} (hα : |α| < 1) (hσz : σz ≠ 0) (hσw : σw ≠ 0)
    (hσz1 : σz ^ 2 < 1) {S : Set (ℝ × ℝ × ℝ)} (hS : S = sacSet α σz) (hSm : MeasurableSet S)
    (hSabs : IsAbsorbing (sacGaussianKernel α σz σw) S) {ψ : Measure S}
    (hψ : haveI := isMarkovKernel_restrictKernel _ hSm hSabs
      IsMaximalIrreducibility (restrictKernel (sacGaussianKernel α σz σw) hSm) ψ)
    (hap : IsAperiodic (restrictKernel (sacGaussianKernel α σz σw) hSm) ψ)
    (hcpt : ∀ K : Set S, IsCompact K →
      IsPetite (restrictKernel (sacGaussianKernel α σz σw) hSm) K) :
    haveI := isMarkovKernel_restrictKernel _ hSm hSabs
    ∃ ε : ℝ, 0 < ε ∧ IsPositive (restrictKernel (sacGaussianKernel α σz σw) hSm) ψ ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        IsInvariant (restrictKernel (sacGaussianKernel α σz σw) hSm) μ →
        IsVUniformlyErgodic (fun x : S => ENNReal.ofReal (sacV ε x.1 + 1))
          (restrictKernel (sacGaussianKernel α σz σw) hSm) μ ∧
        (∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun x : S => ENNReal.ofReal (sacV ε x.1 + 1))
          (restrictKernel (sacGaussianKernel α σz σw) hSm) μ n ≠ ∞) ∧
        ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∀ (x : S) (k : ℕ),
          ENNReal.ofReal |∫ z, z.1.2.2 ^ 2 ∂(restrictKernel (sacGaussianKernel α σz σw) hSm ^ k) x
            - ∫ z, z.1.2.2 ^ 2 ∂μ| ≤ R * r⁻¹ ^ k * ENNReal.ofReal (sacV ε x.1 + 1) := by
  subst hS
  obtain ⟨hZ2, hZ2', hZ4, hW1, hW1', hW2, hW2', hW4⟩ := sacGaussian_moments σz σw
  exact proposition_16_5_2 hα hσz hσw hσz1 _ _ hZ2 hZ2' hZ4 hW1 hW1' hW2 hW2' hW4 hψ hap hcpt

/-- **Proposition 16.5.2 for the Gaussian adaptive control model** (MT p. 417), with the
irreducibility, aperiodicity and petiteness hypotheses derived (Proposition 7.4.3,
Theorem 6.2.5 (ii)): for `|α| < 1`, `α ≠ 0`, `σ_z, σ_w ≠ 0` and `σ_z² < 1`, the chain restricted
to its state space is an aperiodic T-chain, positive for a maximal irreducibility measure `ψ`, and
for some `ε₀ > 0` and every invariant probability `π` it is `V`-uniformly ergodic for
`V = θ̃⁴ + ε₀θ̃²y² + ε₀²y² + 1`, with `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞` and
`|E_x[Yₖ²] − ∫ y² dπ| ≤ R r⁻ᵏ V(x)` (16.48). -/
theorem proposition_16_5_2_gaussian {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) (hσz1 : σz ^ 2 < 1) :
    haveI := isMarkovKernel_sacQ (σz := σz) hα hσw
    IsTChain (sacQ α σz σw) ∧ ∃ ψ : Measure (sacSpace α σz), IsAperiodic (sacQ α σz σw) ψ ∧
      ∃ ε : ℝ, 0 < ε ∧ IsPositive (sacQ α σz σw) ψ ∧
      ∀ (μ : Measure (sacSpace α σz)) [IsProbabilityMeasure μ], IsInvariant (sacQ α σz σw) μ →
        IsVUniformlyErgodic (fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1))
          (sacQ α σz σw) μ ∧
        (∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1)) (sacQ α σz σw) μ n ≠ ∞) ∧
        ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∀ (x : sacSpace α σz) (k : ℕ),
          ENNReal.ofReal |∫ z, z.1.2.2 ^ 2 ∂(sacQ α σz σw ^ k) x - ∫ z, z.1.2.2 ^ 2 ∂μ| ≤
            R * r⁻¹ ^ k * ENNReal.ofReal (sacV ε x.1 + 1) := by
  have hPM := isMarkovKernel_sacGaussianKernel α σz σw
  have hM := isMarkovKernel_sacQ (σz := σz) hα hσw
  have hM' : IsMarkovKernel
      (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) := hM
  obtain ⟨hT, ψ, hψ, hap⟩ := proposition_7_4_3 hα hα0 hσz hσw
  have hcpt : ∀ K : Set (sacSpace α σz), IsCompact K → IsPetite (sacQ α σz σw) K :=
    fun K hK => theorem_6_2_5_ii hψ.2.1 hψ.1 hT hK
  refine ⟨hT, ψ, hap, ?_⟩
  exact proposition_16_5_2_of_eq hα hσz hσw hσz1 (sacSpace_eq_sacSet α σz)
    (isClosed_sacSpace α σz).measurableSet (isAbsorbing_sacSpace _ hα hσw) hψ hap hcpt

/-! ### Restricted chains and their laws on the ambient space -/

/-- **Invariance on the ambient space**: if `π` is invariant for `P` restricted to an absorbing
set `A`, its image `π̄` on `X` satisfies `∫ g dπ̄ = ∫ Pg dπ̄`. -/
theorem lintegral_map_val_of_isInvariant {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) (hAbs : IsAbsorbing P A)
    {π : Measure A} (hπ : IsInvariant (restrictKernel P hA) π) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z, g z ∂(π.map Subtype.val) = ∫⁻ z, ∫⁻ y, g y ∂P z ∂(π.map Subtype.val) := by
  have hM := isMarkovKernel_restrictKernel P hA hAbs
  have hG : Measurable fun z => ∫⁻ y, g y ∂P z := hg.lintegral_kernel
  rw [lintegral_map hg measurable_subtype_coe, lintegral_map hG measurable_subtype_coe]
  conv_lhs => rw [← hπ]
  rw [Measure.lintegral_bind (f := fun a : A => g a) (Kernel.measurable _).aemeasurable
    (hg.comp measurable_subtype_coe).aemeasurable]
  exact lintegral_congr fun x => lintegral_restrictKernel P hA hAbs x hg

/-- The `n`-step law of a restricted chain, seen on the ambient space, is the `n`-step law of the
chain: `(μ P_Aⁿ) ∘ val⁻¹ = (μ ∘ val⁻¹) Pⁿ`. -/
theorem map_val_restrictKernel_pow_comp {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (n : ℕ)
    (μ : Measure A) :
    ((restrictKernel P hA ^ n) ∘ₘ μ).map Subtype.val = (P ^ n) ∘ₘ (μ.map Subtype.val) := by
  ext B hB
  have hB' : MeasurableSet (Subtype.val ⁻¹' B : Set A) := measurable_subtype_coe hB
  rw [Measure.map_apply measurable_subtype_coe hB, Measure.bind_apply hB'
    (Kernel.measurable _).aemeasurable, Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) measurable_subtype_coe]
  refine lintegral_congr fun x => ?_
  rw [restrictKernel_pow_apply P hA hAbs n x hB', Subtype.image_preimage_coe, inter_comm]
  exact measure_inter_conull (hAbs.pow_compl hA n x.2)

/-- **Total variation from an initial law**: for `V ≥ 1` and an invariant probability `π`,
`‖μQⁿ − π‖ ≤ |||Qⁿ − 1 ⊗ π|||_V (μ(V) + π(V))`. -/
theorem ofReal_tvNorm_pow_comp_le {X : Type*} [MeasurableSpace X] (Q : Kernel X X)
    [IsMarkovKernel Q] {V : X → ℝ≥0∞} (hVm : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : IsInvariant Q π) (n : ℕ) :
    ENNReal.ofReal (tvNorm ((Q ^ n : Kernel X X) ∘ₘ μ) π) ≤
      vErgDist V Q π n * (∫⁻ x, V x ∂μ + ∫⁻ x, V x ∂π) := by
  have := isMarkovKernel_pow Q n
  set c := vErgDist V Q π n with hc
  have hb : ∀ x, ENNReal.ofReal (tvNorm ((Q ^ n : Kernel X X) x) π) ≤ c * V x := fun x => by
    rw [← fNorm_one]
    exact (fNorm_mono (fun y => hV1 y) _ _).trans
      (fNorm_pow_le_vErgDist_mul Q π n (zero_lt_one.trans_le (hV1 x)).ne' (hVt x))
  have hπn : (Q ^ n : Kernel X X) ∘ₘ π = π := hπ.pow n
  calc ENNReal.ofReal (tvNorm ((Q ^ n : Kernel X X) ∘ₘ μ) π)
      = fNorm 1 ((Q ^ n : Kernel X X) ∘ₘ μ) ((Q ^ n : Kernel X X) ∘ₘ π) := by
        rw [hπn, fNorm_one]
    _ ≤ ∫⁻ x, ∫⁻ y, fNorm 1 ((Q ^ n : Kernel X X) x) ((Q ^ n : Kernel X X) y) ∂π ∂μ :=
        fNorm_comp_le_lintegral _ 1 μ π
    _ ≤ ∫⁻ x, ∫⁻ y, (c * V x + c * V y) ∂π ∂μ := by
        refine lintegral_mono fun x => lintegral_mono fun y => ?_
        rw [fNorm_one]
        calc ENNReal.ofReal (tvNorm ((Q ^ n : Kernel X X) x) ((Q ^ n : Kernel X X) y))
            ≤ ENNReal.ofReal (tvNorm ((Q ^ n : Kernel X X) x) π) +
                ENNReal.ofReal (tvNorm π ((Q ^ n : Kernel X X) y)) := by
              rw [← ENNReal.ofReal_add (tvNorm_nonneg _ _) (tvNorm_nonneg _ _)]
              exact ENNReal.ofReal_le_ofReal (tvNorm_triangle _ _ _)
          _ ≤ c * V x + c * V y := add_le_add (hb x) (by rw [tvNorm_comm]; exact hb y)
    _ = c * (∫⁻ x, V x ∂μ + ∫⁻ x, V x ∂π) := by
        have hin : ∀ x, ∫⁻ y, (c * V x + c * V y) ∂π = c * V x + c * ∫⁻ y, V y ∂π := fun x => by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ hVm]
        simp_rw [hin]
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm, lintegral_const,
          measure_univ, mul_one, mul_add]

/-! ### The Kalman law in steady state -/

/-- **Kalman laws are closed under total variation limits**: if every `μₙ` is a Kalman law
(`θ̃ ~ N(0, Σ)` given `(Σ, Y)`) and `‖μₙ − ν‖ → 0`, then `ν` is a Kalman law. -/
theorem isKalmanLaw_of_tendsto {ν : Measure (ℝ × ℝ × ℝ)} [IsProbabilityMeasure ν]
    {μs : ℕ → Measure (ℝ × ℝ × ℝ)} (hμs : ∀ n, IsProbabilityMeasure (μs n))
    (hK : ∀ n, IsKalmanLaw (μs n))
    (hlim : Tendsto (fun n => ENNReal.ofReal (tvNorm (μs n) ν)) atTop (𝓝 0)) : IsKalmanLaw ν := by
  set N := gaussianReal 0 1 with hN
  set T : (ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ × ℝ := fun p => (p.1.1, √p.1.1 * p.2, p.1.2.2) with hT
  have hTm : Measurable T := by fun_prop
  have hset : ∀ B, MeasurableSet B → ν B = ∫⁻ φ, N (Prod.mk φ ⁻¹' (T ⁻¹' B)) ∂ν := by
    intro B hB
    have hS : MeasurableSet (T ⁻¹' B) := hTm hB
    have hk : Measurable fun φ => N (Prod.mk φ ⁻¹' (T ⁻¹' B)) := measurable_measure_prodMk_left hS
    set k : ℝ × ℝ × ℝ → ℝ := fun φ => (N (Prod.mk φ ⁻¹' (T ⁻¹' B))).toReal with hkdef
    have hkm : Measurable k := hk.ennreal_toReal
    have hk1 : ∀ φ, |k φ| ≤ 1 := fun φ => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have hi1 : ∀ φ, |B.indicator (1 : ℝ × ℝ × ℝ → ℝ) φ| ≤ 1 := fun φ => by
      by_cases hφ : φ ∈ B
      · rw [indicator_of_mem hφ, Pi.one_apply, abs_one]
      · rw [indicator_of_notMem hφ, abs_zero]
        exact zero_le_one
    have hfin : ∀ (ρ : Measure (ℝ × ℝ × ℝ)), ∀ᵐ φ ∂ρ, N (Prod.mk φ ⁻¹' (T ⁻¹' B)) < ∞ := fun ρ =>
      ae_of_all _ fun φ => measure_lt_top _ _
    -- the set form of the Kalman property at time `n`
    have hKn : ∀ n, (μs n).real B = ∫ φ, k φ ∂μs n := fun n => by
      have h := hK n (B.indicator 1) (measurable_one.indicator hB)
      rw [lintegral_indicator_one hB] at h
      have h' : (μs n) B = ∫⁻ φ, N (Prod.mk φ ⁻¹' (T ⁻¹' B)) ∂μs n := by
        rw [h]
        refine lintegral_congr fun φ => ?_
        exact (lintegral_indicator_const_comp (hTm.comp measurable_prodMk_left) hB 1).trans
          (one_mul _)
      rw [measureReal_def, h', integral_toReal hk.aemeasurable (hfin _)]
    have hbd : ∀ n, ENNReal.ofReal |ν.real B - ∫ φ, k φ ∂ν| ≤
        2 * ENNReal.ofReal (tvNorm (μs n) ν) := fun n => by
      have := hμs n
      have h1 := abs_integral_sub_le_tvNorm (μs n) ν (measurable_one.indicator hB) hi1
      rw [integral_indicator_one hB, integral_indicator_one hB] at h1
      have h2 := abs_integral_sub_le_tvNorm (μs n) ν hkm hk1
      rw [hKn n] at h1
      rw [two_mul, ← ENNReal.ofReal_add (tvNorm_nonneg _ _) (tvNorm_nonneg _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |ν.real B - ∫ φ, k φ ∂ν|
          = |(∫ φ, k φ ∂μs n - ∫ φ, k φ ∂ν) - (∫ φ, k φ ∂μs n - ν.real B)| := by ring_nf
        _ ≤ |∫ φ, k φ ∂μs n - ∫ φ, k φ ∂ν| + |∫ φ, k φ ∂μs n - ν.real B| := abs_sub _ _
        _ ≤ tvNorm (μs n) ν + tvNorm (μs n) ν := add_le_add h2 h1
    have hlim2 : Tendsto (fun n => 2 * ENNReal.ofReal (tvNorm (μs n) ν)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := 2) hlim (Or.inr (by norm_num))
      rwa [mul_zero] at h
    have h0 : ENNReal.ofReal |ν.real B - ∫ φ, k φ ∂ν| ≤ 0 :=
      ge_of_tendsto hlim2 (Eventually.of_forall hbd)
    have heq : ν.real B = ∫ φ, k φ ∂ν := by
      have h00 := ENNReal.ofReal_eq_zero.1 (le_antisymm h0 zero_le)
      have := abs_nonpos_iff.1 h00
      linarith
    rw [← ofReal_measureReal (measure_ne_top ν B), heq,
      integral_toReal hk.aemeasurable (hfin _), ENNReal.ofReal_toReal]
    exact (lt_of_le_of_lt (lintegral_mono fun φ => prob_le_one)
      (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.one_lt_top)).ne
  have hEq : ν = (ν.prod N).map T := by
    ext B hB
    rw [Measure.map_apply hTm hB, Measure.prod_apply (hTm hB)]
    exact hset B hB
  intro g hg
  calc ∫⁻ φ, g φ ∂ν = ∫⁻ φ, g φ ∂((ν.prod N).map T) := by rw [← hEq]
    _ = ∫⁻ p, g (T p) ∂(ν.prod N) := lintegral_map hg hTm
    _ = ∫⁻ φ, ∫⁻ ξ, g (T (φ, ξ)) ∂N ∂ν := lintegral_prod _ (hg.comp hTm).aemeasurable

/-- `V = sacV ε + 1` is measurable on the state space. -/
theorem measurable_sacV_add_one (α σz ε : ℝ) :
    Measurable fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1) := by
  have h : Measurable (sacV ε) := by unfold sacV; fun_prop
  exact ENNReal.measurable_ofReal.comp ((h.comp measurable_subtype_coe).add_const 1)

/-- **The steady state is a Kalman law** (MT p. 417, "in steady state `Σₖ = E[θ̃ₖ² | Y₀, …, Yₖ]`"):
for every invariant probability `π` of the restricted Gaussian adaptive control chain, `θ̃` is
`N(0, Σ)` given `(Σ, Y)` under `π`. The laws `μ₀Pⁿ` from the Kalman initial law `sacKalmanInit`
are Kalman laws (`isKalmanLaw_sacGaussian_pow`) and converge to `π` in total variation, since
`‖μ₀Pⁿ − π‖ ≤ |||Pⁿ − 1 ⊗ π|||_V (μ₀(V) + π(V)) → 0` (Proposition 16.5.2). Also `π(V) < ∞`. -/
theorem isKalmanLaw_of_isInvariant {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) (hσz1 : σz ^ 2 < 1) (π : Measure (sacSpace α σz)) [IsProbabilityMeasure π]
    (hπ : IsInvariant (sacQ α σz σw) π) :
    IsKalmanLaw (π.map Subtype.val) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1) ∂π ≠ ∞ := by
  have hPM := isMarkovKernel_sacGaussianKernel α σz σw
  have hM := isMarkovKernel_sacQ (σz := σz) hα hσw
  have hXm := (isClosed_sacSpace α σz).measurableSet
  have hAbs : IsAbsorbing (sacGaussianKernel α σz σw) (sacSpace α σz) :=
    isAbsorbing_sacSpace _ hα hσw
  have hM' : IsMarkovKernel (restrictKernel (sacGaussianKernel α σz σw) hXm) := hM
  obtain ⟨-, ψ, -, ε, hε, -, hall⟩ := proposition_16_5_2_gaussian hα hα0 hσz hσw hσz1
  obtain ⟨⟨-, hlim⟩, ⟨r, -, -, hsum⟩, -⟩ := hall π hπ
  have hVm := measurable_sacV_add_one α σz ε
  have hV1 : ∀ x : sacSpace α σz, 1 ≤ ENNReal.ofReal (sacV ε x.1 + 1) := fun x => by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (sacV_nonneg hε.le _))
  have hVt : ∀ x : sacSpace α σz, ENNReal.ofReal (sacV ε x.1 + 1) ≠ ∞ :=
    fun _ => ENNReal.ofReal_ne_top
  have h0 : vErgDist (fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1))
      (sacQ α σz σw) π 0 ≠ ∞ := by
    refine ne_top_of_le_ne_top hsum ?_
    have h := ENNReal.le_tsum (f := fun n => r ^ n * vErgDist
      (fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1)) (sacQ α σz σw) π n) 0
    rwa [pow_zero, one_mul] at h
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure π
  have hπV := lintegral_ne_top_of_vErgDist_zero hVm hV1 (hVt x₀) _ π h0
  refine ⟨?_, ε, hε, hπV⟩
  -- the Kalman initial law, carried to the state space
  obtain ⟨hμP, hμX, -, hμK⟩ := sacKalmanInit_spec hα σz
  have hμX' : sacKalmanInit σz (sacSpace α σz)ᶜ = 0 := by
    rw [sacSpace_eq_sacSet]
    exact hμX
  have hmap : ((sacKalmanInit σz).comap (Subtype.val : sacSpace α σz → ℝ × ℝ × ℝ)).map
      Subtype.val = sacKalmanInit σz := by
    rw [map_comap_subtype_coe hXm, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 hμX'
  have hμ₀P : IsProbabilityMeasure ((sacKalmanInit σz).comap (Subtype.val :
      sacSpace α σz → ℝ × ℝ × ℝ)) := by
    constructor
    rw [(MeasurableEmbedding.subtype_coe hXm).comap_apply, image_univ, Subtype.range_coe]
    exact (prob_compl_eq_zero_iff hXm).1 hμX'
  have hm4 : Measurable fun z : ℝ × ℝ × ℝ => ENNReal.ofReal (sacV ε z + 1) := by
    unfold sacV; fun_prop
  have hμV : ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1)
      ∂((sacKalmanInit σz).comap (Subtype.val : sacSpace α σz → ℝ × ℝ × ℝ)) ≠ ∞ := by
    have e : ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1)
        ∂((sacKalmanInit σz).comap (Subtype.val : sacSpace α σz → ℝ × ℝ × ℝ)) =
        ∫⁻ z, ENNReal.ofReal (sacV ε z + 1) ∂sacKalmanInit σz := by
      conv_rhs => rw [← hmap]
      rw [lintegral_map hm4 measurable_subtype_coe]
    rw [e, sacKalmanInit, lintegral_map hm4 (by fun_prop)]
    have hpt : ∀ t : ℝ, ENNReal.ofReal (sacV ε ((σz ^ 2, t, 0) : ℝ × ℝ × ℝ) + 1) =
        ENNReal.ofReal (t ^ 4 + 1) := fun t => by
      congr 1
      unfold sacV
      ring
    rw [lintegral_congr hpt]
    exact (((sacGaussian_moments σz σw).2.2.1.add (integrable_const 1)).lintegral_lt_top).ne
  -- total variation convergence of the Kalman laws
  have hμs : ∀ n, IsProbabilityMeasure
      ((sacGaussianKernel α σz σw ^ n : Kernel _ _) ∘ₘ sacKalmanInit σz) := fun n => by
    have := isMarkovKernel_pow (sacGaussianKernel α σz σw) n
    infer_instance
  have hK : ∀ n, IsKalmanLaw ((sacGaussianKernel α σz σw ^ n : Kernel _ _) ∘ₘ sacKalmanInit σz) :=
    isKalmanLaw_sacGaussian_pow hα hσw hμX hμK
  have hC : ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1)
      ∂((sacKalmanInit σz).comap (Subtype.val : sacSpace α σz → ℝ × ℝ × ℝ)) +
      ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1) ∂π ≠ ∞ := ENNReal.add_ne_top.2 ⟨hμV, hπV⟩
  have hb : ∀ n, ENNReal.ofReal (tvNorm
      ((sacGaussianKernel α σz σw ^ n : Kernel _ _) ∘ₘ sacKalmanInit σz) (π.map Subtype.val)) ≤
      vErgDist (fun x : sacSpace α σz => ENNReal.ofReal (sacV ε x.1 + 1)) (sacQ α σz σw) π n *
        (∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1)
          ∂((sacKalmanInit σz).comap (Subtype.val : sacSpace α σz → ℝ × ℝ × ℝ)) +
        ∫⁻ x, ENNReal.ofReal (sacV ε x.1 + 1) ∂π) := fun n => by
    have hq := map_val_restrictKernel_pow_comp (sacGaussianKernel α σz σw) hXm hAbs n
      ((sacKalmanInit σz).comap Subtype.val)
    rw [hmap] at hq
    have := isMarkovKernel_pow (restrictKernel (sacGaussianKernel α σz σw) hXm) n
    rw [← hq]
    exact (ENNReal.ofReal_le_ofReal (tvNorm_map_le measurable_subtype_coe _ _)).trans
      (ofReal_tvNorm_pow_comp_le (sacQ α σz σw) hVm hV1 hVt _ π hπ n)
  have hl := ENNReal.Tendsto.mul_const hlim (Or.inr hC)
  rw [zero_mul] at hl
  have hlimtv := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => zero_le) hb
  exact isKalmanLaw_of_tendsto hμs hK hlimtv

/-! ### The steady state identities and (16.49) -/

/-- `E[(a + W)²] = a² + σ_w²` for the disturbance `W ~ N(0, σ_w²)` of (SAC2). -/
theorem lintegral_sq_add_noise (a σz σw : ℝ) :
    ∫⁻ q, ENNReal.ofReal ((a + q.2) ^ 2)
      ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) =
      ENNReal.ofReal (a ^ 2 + σw ^ 2) := by
  obtain ⟨hW1, hW2, hm, hv⟩ := sacGaussian_noise_moments σz σw
  have hexp : (fun q : ℝ × ℝ => (a + q.2) ^ 2) = fun q => (a ^ 2 + 2 * a * q.2) + q.2 ^ 2 :=
    funext fun q => by ring
  have hint1 : Integrable (fun q : ℝ × ℝ => a ^ 2 + 2 * a * q.2)
      ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) :=
    (integrable_const _).add (hW1.const_mul _)
  have hint : Integrable (fun q : ℝ × ℝ => (a + q.2) ^ 2)
      ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) := by
    rw [hexp]
    exact hint1.add hW2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun q => sq_nonneg _), hexp,
    integral_add hint1 hW2, integral_add (integrable_const _) (hW1.const_mul _), integral_const,
    integral_const_mul, hm, hv, probReal_univ, one_smul]
  congr 1
  ring

/-- **(16.45)**, `PY² = θ̃²Y² + σ_w²` for the Gaussian chain. -/
theorem lintegral_sacGaussian_Ysq (α σz σw : ℝ) (φ : ℝ × ℝ × ℝ) :
    ∫⁻ y, ENNReal.ofReal (y.2.2 ^ 2) ∂sacGaussianKernel α σz σw φ =
      ENNReal.ofReal (φ.2.1 ^ 2 * φ.2.2 ^ 2 + σw ^ 2) := by
  have hF := measurable_sacStep α σz σw
  have hm : Measurable fun y : ℝ × ℝ × ℝ => ENNReal.ofReal (y.2.2 ^ 2) := by fun_prop
  rw [sacGaussianKernel, sacKernel, recursionKernel_apply _ hF φ,
    lintegral_map (g := fun w => sacStep α σz σw (φ, w)) hm (hF.comp measurable_prodMk_left)]
  calc ∫⁻ q, ENNReal.ofReal ((sacStep α σz σw (φ, q)).2.2 ^ 2)
        ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal))
      = ∫⁻ q, ENNReal.ofReal ((φ.2.1 * φ.2.2 + q.2) ^ 2)
        ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) := rfl
    _ = ENNReal.ofReal (φ.2.1 ^ 2 * φ.2.2 ^ 2 + σw ^ 2) := by
        rw [lintegral_sq_add_noise, mul_pow]

/-- `P(ΣY²) = Σ' (θ̃²Y² + σ_w²)` with `Σ' = σ_z² + α²σ_w²Σ/(ΣY² + σ_w²)`: the next `Σ` is a
function of the present state. -/
theorem lintegral_sacGaussian_SYsq (α σz σw : ℝ) {φ : ℝ × ℝ × ℝ} (hφ : 0 ≤ φ.1) :
    ∫⁻ y, ENNReal.ofReal (y.1 * y.2.2 ^ 2) ∂sacGaussianKernel α σz σw φ =
      ENNReal.ofReal (σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2)) *
        ENNReal.ofReal (φ.2.1 ^ 2 * φ.2.2 ^ 2 + σw ^ 2) := by
  have hF := measurable_sacStep α σz σw
  have hm : Measurable fun y : ℝ × ℝ × ℝ => ENNReal.ofReal (y.1 * y.2.2 ^ 2) := by fun_prop
  have hs : 0 ≤ σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2) := by positivity
  rw [sacGaussianKernel, sacKernel, recursionKernel_apply _ hF φ,
    lintegral_map (g := fun w => sacStep α σz σw (φ, w)) hm (hF.comp measurable_prodMk_left)]
  calc ∫⁻ q, ENNReal.ofReal ((sacStep α σz σw (φ, q)).1 * (sacStep α σz σw (φ, q)).2.2 ^ 2)
        ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal))
      = ∫⁻ q, ENNReal.ofReal (σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2)) *
          ENNReal.ofReal ((φ.2.1 * φ.2.2 + q.2) ^ 2)
        ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) :=
        lintegral_congr fun q => ENNReal.ofReal_mul hs
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sq_add_noise, mul_pow]

/-- **The steady state identities** of p. 417, under any invariant probability `π` of the
restricted Gaussian chain (written for its image `π̄` on `ℝ³`): taking expectations in (2.23) and
(2.24), `E_π[Y²] = E_π[ΣY²] + σ_w²` and `E_π[ΣY²] = σ_z² E_π[Y²] + α²σ_w² E_π[Σ]`, and
`E_π[θ̃²] = E_π[Σ]`. The Kalman law of the steady state (`isKalmanLaw_of_isInvariant`) replaces
`θ̃²` by `Σ` in the first two, and gives the third. -/
theorem sac_steady_state_identities {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) (hσz1 : σz ^ 2 < 1) (π : Measure (sacSpace α σz)) [IsProbabilityMeasure π]
    (hπ : IsInvariant (sacQ α σz σw) π) :
    ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂(π.map Subtype.val) =
        ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂(π.map Subtype.val) + ENNReal.ofReal (σw ^ 2) ∧
      ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂(π.map Subtype.val) =
        ENNReal.ofReal (σz ^ 2) * ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂(π.map Subtype.val) +
          ENNReal.ofReal (α ^ 2 * σw ^ 2) * ∫⁻ φ, ENNReal.ofReal φ.1 ∂(π.map Subtype.val) ∧
      ∫⁻ φ, ENNReal.ofReal (φ.2.1 ^ 2) ∂(π.map Subtype.val) =
        ∫⁻ φ, ENNReal.ofReal φ.1 ∂(π.map Subtype.val) := by
  have hPM := isMarkovKernel_sacGaussianKernel α σz σw
  have hXm := (isClosed_sacSpace α σz).measurableSet
  have hAbs : IsAbsorbing (sacGaussianKernel α σz σw) (sacSpace α σz) :=
    isAbsorbing_sacSpace _ hα hσw
  have hKal := (isKalmanLaw_of_isInvariant hα hα0 hσz hσw hσz1 π hπ).1
  have hinv : ∀ g : ℝ × ℝ × ℝ → ℝ≥0∞, Measurable g → ∫⁻ z, g z ∂(π.map Subtype.val) =
      ∫⁻ z, ∫⁻ y, g y ∂sacGaussianKernel α σz σw z ∂(π.map Subtype.val) := fun g hg =>
    lintegral_map_val_of_isInvariant _ hXm hAbs hπ hg
  obtain ⟨ν, hν⟩ : ∃ ν, ν = π.map Subtype.val := ⟨_, rfl⟩
  rw [← hν] at hinv hKal ⊢
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hmem : ∀ᵐ φ ∂ν, φ ∈ sacSpace α σz := by
    rw [hν]
    exact (ae_map_iff measurable_subtype_coe.aemeasurable hXm).2 (ae_of_all _ fun x => x.2)
  have hS0 : ∀ᵐ φ ∂ν, 0 ≤ φ.1 := hmem.mono fun φ hφ => (sq_nonneg σz).trans hφ.1
  have hσw2 : 0 < σw ^ 2 := by positivity
  -- (a)
  have ha : ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂ν =
      ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν + ENNReal.ofReal (σw ^ 2) := by
    have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2) := by fun_prop
    have hK := hKal.lintegral_sq hS0 hg
    calc ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂ν
        = ∫⁻ z, ∫⁻ y, ENNReal.ofReal (y.2.2 ^ 2) ∂sacGaussianKernel α σz σw z ∂ν :=
          hinv _ (by fun_prop)
      _ = ∫⁻ z, (ENNReal.ofReal (z.2.2 ^ 2) * ENNReal.ofReal (z.2.1 ^ 2) +
            ENNReal.ofReal (σw ^ 2)) ∂ν := by
          refine lintegral_congr fun z => ?_
          rw [lintegral_sacGaussian_Ysq, ENNReal.ofReal_add (by positivity) hσw2.le,
            ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
      _ = ∫⁻ z, ENNReal.ofReal (z.2.2 ^ 2) * ENNReal.ofReal (z.2.1 ^ 2) ∂ν +
            ENNReal.ofReal (σw ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ z, ENNReal.ofReal (z.2.2 ^ 2) * ENNReal.ofReal z.1 ∂ν + ENNReal.ofReal (σw ^ 2) := by
          rw [hK]
      _ = ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν + ENNReal.ofReal (σw ^ 2) := by
          congr 1
          refine lintegral_congr_ae (hS0.mono fun z hz => ?_)
          beta_reduce
          rw [ENNReal.ofReal_mul hz, mul_comm]
  refine ⟨ha, ?_, ?_⟩
  · -- (b)
    set s : ℝ × ℝ → ℝ := fun p => σz ^ 2 + α ^ 2 * σw ^ 2 * p.1 / (p.1 * p.2 ^ 2 + σw ^ 2)
      with hsdef
    have hsm : Measurable s := by rw [hsdef]; fun_prop
    have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (s p) * ENNReal.ofReal (p.2 ^ 2) :=
      (ENNReal.measurable_ofReal.comp hsm).mul (by fun_prop)
    have hK := hKal.lintegral_sq hS0 hg
    have hm2 : Measurable fun z : ℝ × ℝ × ℝ => ENNReal.ofReal (s (z.1, z.2.2)) *
        ENNReal.ofReal (σw ^ 2) :=
      (ENNReal.measurable_ofReal.comp (hsm.comp (by fun_prop))).mul measurable_const
    calc ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν
        = ∫⁻ z, ∫⁻ y, ENNReal.ofReal (y.1 * y.2.2 ^ 2) ∂sacGaussianKernel α σz σw z ∂ν :=
          hinv _ (by fun_prop)
      _ = ∫⁻ z, (ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (z.2.2 ^ 2) *
            ENNReal.ofReal (z.2.1 ^ 2) + ENNReal.ofReal (s (z.1, z.2.2)) *
              ENNReal.ofReal (σw ^ 2)) ∂ν := by
          refine lintegral_congr_ae (hS0.mono fun z hz => ?_)
          beta_reduce
          rw [lintegral_sacGaussian_SYsq α σz σw hz, ENNReal.ofReal_add (by positivity)
            hσw2.le, mul_add, ENNReal.ofReal_mul (sq_nonneg _),
            mul_comm (ENNReal.ofReal (z.2.1 ^ 2)), ← mul_assoc]
      _ = ∫⁻ z, ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (z.2.2 ^ 2) *
            ENNReal.ofReal (z.2.1 ^ 2) ∂ν +
          ∫⁻ z, ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (σw ^ 2) ∂ν :=
          lintegral_add_right _ hm2
      _ = ∫⁻ z, ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (z.2.2 ^ 2) *
            ENNReal.ofReal z.1 ∂ν +
          ∫⁻ z, ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (σw ^ 2) ∂ν := by
          rw [hK]
      _ = ∫⁻ z, (ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (z.1 * z.2.2 ^ 2) +
            ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2) +
            ENNReal.ofReal (α ^ 2 * σw ^ 2) * ENNReal.ofReal z.1) ∂ν := by
          rw [← lintegral_add_right _ hm2]
          refine lintegral_congr_ae (hS0.mono fun z hz => ?_)
          beta_reduce
          have hD : 0 < z.1 * z.2.2 ^ 2 + σw ^ 2 := by positivity
          have hs0 : 0 ≤ s (z.1, z.2.2) := by rw [hsdef]; positivity
          have hY : 0 ≤ z.2.2 ^ 2 := sq_nonneg _
          have hSY : 0 ≤ z.1 * z.2.2 ^ 2 := mul_nonneg hz hY
          have hσz2 : 0 ≤ σz ^ 2 := sq_nonneg _
          have hασ : 0 ≤ α ^ 2 * σw ^ 2 := by positivity
          have hreal : s (z.1, z.2.2) * z.2.2 ^ 2 * z.1 + s (z.1, z.2.2) * σw ^ 2 =
              σz ^ 2 * (z.1 * z.2.2 ^ 2) + σz ^ 2 * σw ^ 2 + α ^ 2 * σw ^ 2 * z.1 := by
            rw [hsdef]
            field_simp
          have hL : ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (z.2.2 ^ 2) *
              ENNReal.ofReal z.1 + ENNReal.ofReal (s (z.1, z.2.2)) * ENNReal.ofReal (σw ^ 2) =
              ENNReal.ofReal (s (z.1, z.2.2) * z.2.2 ^ 2 * z.1 + s (z.1, z.2.2) * σw ^ 2) := by
            rw [← ENNReal.ofReal_mul hs0, ← ENNReal.ofReal_mul (mul_nonneg hs0 hY),
              ← ENNReal.ofReal_mul hs0, ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hs0 hY) hz)
                (mul_nonneg hs0 hσw2.le)]
          have hR : ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (z.1 * z.2.2 ^ 2) +
              ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2) +
              ENNReal.ofReal (α ^ 2 * σw ^ 2) * ENNReal.ofReal z.1 =
              ENNReal.ofReal (σz ^ 2 * (z.1 * z.2.2 ^ 2) + σz ^ 2 * σw ^ 2 +
                α ^ 2 * σw ^ 2 * z.1) := by
            rw [← ENNReal.ofReal_mul hσz2, ← ENNReal.ofReal_mul hσz2, ← ENNReal.ofReal_mul hασ,
              ← ENNReal.ofReal_add (mul_nonneg hσz2 hSY) (mul_nonneg hσz2 hσw2.le),
              ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hσz2 hSY) (mul_nonneg hσz2 hσw2.le))
                (mul_nonneg hασ hz)]
          rw [hL, hR, hreal]
      _ = ENNReal.ofReal (σz ^ 2) * (∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν +
            ENNReal.ofReal (σw ^ 2)) +
          ENNReal.ofReal (α ^ 2 * σw ^ 2) * ∫⁻ φ, ENNReal.ofReal φ.1 ∂ν := by
          have e1 : ∫⁻ z, (ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (z.1 * z.2.2 ^ 2) +
              ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2) +
              ENNReal.ofReal (α ^ 2 * σw ^ 2) * ENNReal.ofReal z.1) ∂ν =
              ∫⁻ z, (ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (z.1 * z.2.2 ^ 2) +
                ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2)) ∂ν +
              ∫⁻ z, ENNReal.ofReal (α ^ 2 * σw ^ 2) * ENNReal.ofReal z.1 ∂ν :=
            lintegral_add_left (f := fun z : ℝ × ℝ × ℝ => ENNReal.ofReal (σz ^ 2) *
              ENNReal.ofReal (z.1 * z.2.2 ^ 2) + ENNReal.ofReal (σz ^ 2) *
                ENNReal.ofReal (σw ^ 2)) (by fun_prop) _
          have e2 : ∫⁻ z, (ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (z.1 * z.2.2 ^ 2) +
              ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2)) ∂ν =
              ENNReal.ofReal (σz ^ 2) * ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν +
                ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (σw ^ 2) := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_const_mul _ (by fun_prop)]
          rw [e1, e2, lintegral_const_mul _ (by fun_prop), mul_add]
      _ = _ := by rw [← ha]
  · -- (c)
    have hK := hKal.lintegral_sq hS0 (g := fun _ => 1) measurable_const
    calc ∫⁻ φ, ENNReal.ofReal (φ.2.1 ^ 2) ∂ν = ∫⁻ φ, 1 * ENNReal.ofReal (φ.2.1 ^ 2) ∂ν :=
          lintegral_congr fun φ => (one_mul _).symm
      _ = ∫⁻ φ, 1 * ENNReal.ofReal φ.1 ∂ν := hK
      _ = ∫⁻ φ, ENNReal.ofReal φ.1 ∂ν := lintegral_congr fun φ => one_mul _

/-- **(16.49) for the Gaussian adaptive control model** (MT p. 417), with no hypothesis on the
steady state: for `|α| < 1`, `α ≠ 0`, `σ_z, σ_w ≠ 0`, `σ_z² < 1` and every invariant probability
`π` of the restricted chain,
* `E_π[Y²] = E_π[ΣY²] + σ_w²` and `σ_z² E_π[Y²] = E_π[ΣY²] − α²σ_w² E_π[Σ]`;
* `E_π[θ̃²] = E_π[Σ]`;
* `E_π[Y²] = σ_w²/(1 − σ_z²) (1 + α² E_π[θ̃²])` (16.49); and
* `σ_w²/(1 − σ_z²) (1 + α²σ_z²) ≤ E_π[Y²] ≤ σ_w²/(1 − σ_z²) (1 + α²σ_z²/(1 − α²))`. -/
theorem eq_16_49_gaussian {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) (hσz1 : σz ^ 2 < 1) (π : Measure (sacSpace α σz)) [IsProbabilityMeasure π]
    (hπ : IsInvariant (sacQ α σz σw) π) :
    ∫ x, x.1.2.2 ^ 2 ∂π = ∫ x, x.1.1 * x.1.2.2 ^ 2 ∂π + σw ^ 2 ∧
      σz ^ 2 * ∫ x, x.1.2.2 ^ 2 ∂π =
        ∫ x, x.1.1 * x.1.2.2 ^ 2 ∂π - α ^ 2 * σw ^ 2 * ∫ x, x.1.1 ∂π ∧
      ∫ x, x.1.2.1 ^ 2 ∂π = ∫ x, x.1.1 ∂π ∧
      ∫ x, x.1.2.2 ^ 2 ∂π = σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * ∫ x, x.1.2.1 ^ 2 ∂π) ∧
      σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * σz ^ 2) ≤ ∫ x, x.1.2.2 ^ 2 ∂π ∧
      ∫ x, x.1.2.2 ^ 2 ∂π ≤ σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * (σz ^ 2 / (1 - α ^ 2))) := by
  obtain ⟨ha, hb, hc⟩ := sac_steady_state_identities hα hα0 hσz hσw hσz1 π hπ
  obtain ⟨-, ε, hε, hπV⟩ := isKalmanLaw_of_isInvariant hα hα0 hσz hσw hσz1 π hπ
  have hα2 : α ^ 2 < 1 := by
    have h1 : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [h1]
    nlinarith [abs_nonneg α]
  have hσw2 : 0 < σw ^ 2 := by positivity
  have hS0 : ∀ x : sacSpace α σz, 0 ≤ x.1.1 := fun x => (sq_nonneg σz).trans x.2.1
  -- integrals over `π` as lintegrals over its image
  have hconv : ∀ F : ℝ × ℝ × ℝ → ℝ, Measurable F → (∀ x : sacSpace α σz, 0 ≤ F x.1) →
      ∫ x, F x.1 ∂π = (∫⁻ φ, ENNReal.ofReal (F φ) ∂(π.map Subtype.val)).toReal :=
    fun F hF h0 => by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0)
        (hF.comp measurable_subtype_coe).aestronglyMeasurable,
        lintegral_map (f := fun φ => ENNReal.ofReal (F φ)) (ENNReal.measurable_ofReal.comp hF)
          measurable_subtype_coe]
  have eY := hconv (fun φ => φ.2.2 ^ 2) (by fun_prop) fun x => sq_nonneg _
  have eSY := hconv (fun φ => φ.1 * φ.2.2 ^ 2) (by fun_prop)
    fun x => mul_nonneg (hS0 x) (sq_nonneg _)
  have eS := hconv (fun φ => φ.1) (by fun_prop) hS0
  have eT := hconv (fun φ => φ.2.1 ^ 2) (by fun_prop) fun x => sq_nonneg _
  -- finiteness
  have hmY : ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂(π.map Subtype.val) ≠ ∞ := by
    rw [lintegral_map (f := fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (φ.2.2 ^ 2)) (by fun_prop)
      measurable_subtype_coe]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (ε ^ 2)⁻¹))
      hπV) ?_
    rw [← lintegral_const_mul _ (measurable_sacV_add_one α σz ε)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 ≤ x.1.2.1 ^ 4 := by positivity
    have h2 : 0 ≤ ε * x.1.2.1 ^ 2 * x.1.2.2 ^ 2 := by positivity
    have h3 : ε ^ 2 * x.1.2.2 ^ 2 ≤ sacV ε x.1 + 1 := by unfold sacV; linarith
    calc x.1.2.2 ^ 2 = (ε ^ 2)⁻¹ * (ε ^ 2 * x.1.2.2 ^ 2) := by field_simp
      _ ≤ (ε ^ 2)⁻¹ * (sacV ε x.1 + 1) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hmSY : ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂(π.map Subtype.val) ≠ ∞ :=
    ne_top_of_le_ne_top hmY (ha ▸ le_self_add)
  have hbS : ∀ x : sacSpace α σz, σz ^ 2 ≤ x.1.1 ∧ x.1.1 ≤ σz ^ 2 / (1 - α ^ 2) := fun x => x.2
  have hmS_le : ∫⁻ φ, ENNReal.ofReal φ.1 ∂(π.map Subtype.val) ≤
      ENNReal.ofReal (σz ^ 2 / (1 - α ^ 2)) := by
    rw [lintegral_map (f := fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal φ.1) (by fun_prop)
      measurable_subtype_coe]
    calc ∫⁻ x, ENNReal.ofReal x.1.1 ∂π ≤ ∫⁻ _, ENNReal.ofReal (σz ^ 2 / (1 - α ^ 2)) ∂π :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hbS x).2
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hmS_ge : ENNReal.ofReal (σz ^ 2) ≤ ∫⁻ φ, ENNReal.ofReal φ.1 ∂(π.map Subtype.val) := by
    rw [lintegral_map (f := fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal φ.1) (by fun_prop)
      measurable_subtype_coe]
    calc ENNReal.ofReal (σz ^ 2) = ∫⁻ _, ENNReal.ofReal (σz ^ 2) ∂π := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, ENNReal.ofReal x.1.1 ∂π :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hbS x).1
  have hmS : ∫⁻ φ, ENNReal.ofReal φ.1 ∂(π.map Subtype.val) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmS_le
  -- the real identities
  have h1 := congrArg ENNReal.toReal ha
  rw [ENNReal.toReal_add hmSY ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hσw2.le] at h1
  have h2 := congrArg ENNReal.toReal hb
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmY)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmS), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (by positivity)] at h2
  have h3 := congrArg ENNReal.toReal hc
  rw [← eY, ← eSY] at h1
  rw [← eY, ← eSY, ← eS] at h2
  rw [← eT, ← eS] at h3
  have hcmem : ∫ x, x.1.1 ∂π ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) := by
    rw [eS]
    exact ⟨(ENNReal.ofReal_le_iff_le_toReal hmS).1 hmS_ge,
      ENNReal.toReal_le_of_le_ofReal (div_nonneg (sq_nonneg _) (by linarith)) hmS_le⟩
  have h2' : σz ^ 2 * ∫ x, x.1.2.2 ^ 2 ∂π =
      ∫ x, x.1.1 * x.1.2.2 ^ 2 ∂π - α ^ 2 * σw ^ 2 * ∫ x, x.1.1 ∂π := by linarith
  have h49 := eq_16_49 (ne_of_lt hσz1) h1 h2'
  refine ⟨h1, h2', h3, by rw [h3]; exact h49, (sac_performance_bounds hσz1 h49 hcmem).1,
    (sac_performance_bounds hσz1 h49 hcmem).2⟩

end MeynTweedie.VUniformErgodicity
