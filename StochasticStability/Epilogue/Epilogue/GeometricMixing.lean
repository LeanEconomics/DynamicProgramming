/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.VUniformErgodic

/-!
# `V`-geometric mixing (MT §16.1.2, Theorem 16.1.5)

Meyn and Tweedie, §16.1.2, pp. 397–398. `ψ` is a maximal irreducibility measure, the state space
is countably generated, `V ≥ 1` is measurable and everywhere finite, and `μ` is an invariant
probability.

* `pathKernel_map_pair`: under `P_x` the pair `(Φₖ, Φₖ₊ₙ)` has law `Pᵏ(x, ·) ⊗ Pⁿ`, and
  `integral_pair_eq`: `E_x[g(Φₖ) h(Φₖ₊ₙ)] = ∫ Pᵏ(x, dy) g(y) Pⁿh(y)` (the Markov property used in
  the proof).
* `exists_vErgDist_sqrt_le`: `V`-uniform ergodicity in the form (16.3) passes to `√V` (by
  Theorem 16.0.1 and Lemma 15.2.9, as in the book's appeal to Lemma 15.2.9).
* **Theorem 16.1.5** (`theorem_16_1_5`, p. 398): for a `V`-uniformly ergodic chain there are
  `R < ∞` and `ρ < 1` such that for all `g² ≤ V`, `h² ≤ V` and `k, n`,
  `|E_x[g(Φₖ) h(Φₖ₊ₙ)] − E_x[g(Φₖ)] E_x[h(Φₖ₊ₙ)]| ≤ R ρⁿ (1 + ρᵏ V(x))`;
  `IsVGeomMixing` and `theorem_16_1_5_mixing`: the chain is `V`-geometrically mixing (p. 398).
* `eq_16_17` ((16.17), p. 398): the stationary version is geometrically mixing,
  `|E_π[g(Φₖ) h(Φₖ₊ₙ)] − π(g) π(h)| ≤ R ρⁿ`; `IsStrongMixing` (p. 397) and
  `isStrongMixing_of_vUniformlyErgodic`: the stationary chain is strong mixing.

The proof splits the covariance as `∫ Pᵏ(x, dy) g(y) (Pⁿh(y) − μ(h)) + Pᵏg(x) (μ(h) − Pᵏ⁺ⁿh(x))`
and bounds the two terms with `|||Pⁿ − 1 ⊗ μ|||_{√V}`; this replaces the book's centring of both
`g` and `h`, and gives the same bound.

**Correction.** As in Theorem 16.0.1, `V`-uniform ergodicity is taken with every
`|||Pⁿ − 1 ⊗ μ|||_V` finite (`theorem_16_0_1_counterexample`).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The law of a pair of coordinates -/

/-- **The two-dimensional distributions**: under `P_x` the pair `(Φₖ, Φₖ₊ₙ)` has law
`Pᵏ(x, ·) ⊗ Pⁿ`, i.e. `P_x(Φₖ ∈ A, Φₖ₊ₙ ∈ B) = ∫_A Pᵏ(x, dy) Pⁿ(y, B)`. -/
theorem pathKernel_map_pair (P : Kernel X X) [IsMarkovKernel P] (x : X) (k n : ℕ) :
    (pathKernel P x).map (fun ω => (ω k, ω (k + n))) = (P ^ k) x ⊗ₘ (P ^ n) := by
  have := isMarkovKernel_pathKernel P
  have := isMarkovKernel_pow P k
  have := isMarkovKernel_pow P n
  have hm : Measurable fun ω : ℕ → X => (ω k, ω (k + n)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply (k + n))
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [Measure.map_apply hm (hA.prod hB), Measure.compProd_apply_prod hA hB]
    have hG : MeasurableSet[natFilt k] {ω : ℕ → X | ω k ∈ A} :=
      measurableSet_coord_natFilt le_rfl hA
    have hEm : MeasurableSet {ω : ℕ → X | ω n ∈ B} := measurable_pi_apply n hB
    have hEm' : MeasurableSet {ω : ℕ → X | ω (k + n) ∈ B} := measurable_pi_apply (k + n) hB
    have key := markov_lintegral P (Measure.dirac x) hG
      (measurable_one.indicator hEm : Measurable
        ({ω : ℕ → X | ω n ∈ B}.indicator (1 : (ℕ → X) → ℝ≥0∞)))
    rw [pathMeasure_dirac] at key
    have hl : ∀ ω : ℕ → X, {ω' : ℕ → X | ω' n ∈ B}.indicator 1 (shift k ω) =
        {ω : ℕ → X | ω (k + n) ∈ B}.indicator (1 : (ℕ → X) → ℝ≥0∞) ω := fun ω => rfl
    have hr : ∀ y, ∫⁻ ω', {ω' : ℕ → X | ω' n ∈ B}.indicator 1 ω' ∂pathKernel P y =
        (P ^ n) y B := fun y => by
      rw [lintegral_indicator_one hEm, pathKernel_coord_mem P y n hB]
    simp_rw [hl, hr] at key
    rw [lintegral_indicator_one hEm', Measure.restrict_apply hEm'] at key
    have hrhs : ∫⁻ ω in {ω : ℕ → X | ω k ∈ A}, (P ^ n) (ω k) B ∂pathKernel P x =
        ∫⁻ y in A, (P ^ n) y B ∂(P ^ k) x := by
      rw [← pathKernel_map_coord P x k,
        setLIntegral_map hA (Kernel.measurable_coe _ hB) (measurable_pi_apply k)]
      rfl
    have hset : (fun ω : ℕ → X => (ω k, ω (k + n))) ⁻¹' (A ×ˢ B) =
        {ω | ω (k + n) ∈ B} ∩ {ω | ω k ∈ A} := by
      ext ω; simp [and_comm]
    rw [hset, key, hrhs]
  · rw [measure_univ, measure_univ]

/-- `E_x[g(Φₖ)] = Pᵏg(x)`. -/
theorem integral_coord_eq (P : Kernel X X) [IsMarkovKernel P] (x : X) (k : ℕ) {g : X → ℝ}
    (hg : Measurable g) : ∫ ω, g (ω k) ∂pathKernel P x = ∫ y, g y ∂(P ^ k) x := by
  rw [← pathKernel_map_coord P x k,
    integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable]

/-- **The Markov property for a product of two coordinates**:
`E_x[g(Φₖ) h(Φₖ₊ₙ)] = ∫ Pᵏ(x, dy) g(y) Pⁿh(y)` when `g(y) h(z)` is integrable for the joint law. -/
theorem integral_pair_eq (P : Kernel X X) [IsMarkovKernel P] (x : X) (k n : ℕ) {g h : X → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hint : Integrable (fun p : X × X => g p.1 * h p.2) ((P ^ k) x ⊗ₘ (P ^ n))) :
    ∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x =
      ∫ y, g y * ∫ z, h z ∂(P ^ n) y ∂(P ^ k) x := by
  have := isMarkovKernel_pow P k
  have := isMarkovKernel_pow P n
  have hm : Measurable fun ω : ℕ → X => (ω k, ω (k + n)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply (k + n))
  have hF : Measurable fun p : X × X => g p.1 * h p.2 :=
    (hg.comp measurable_fst).mul (hh.comp measurable_snd)
  calc ∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x
      = ∫ p, g p.1 * h p.2 ∂(pathKernel P x).map (fun ω => (ω k, ω (k + n))) :=
        (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, g p.1 * h p.2 ∂((P ^ k) x ⊗ₘ (P ^ n)) := by rw [pathKernel_map_pair]
    _ = ∫ y, ∫ z, g y * h z ∂(P ^ n) y ∂(P ^ k) x := Measure.integral_compProd hint
    _ = ∫ y, g y * ∫ z, h z ∂(P ^ n) y ∂(P ^ k) x := by simp_rw [integral_const_mul]

/-! ### Passing to `√V` -/

omit [MeasurableSpace X] in
/-- `√V · √V = V`. -/
theorem rpow_half_mul_self (V : X → ℝ≥0∞) (x : X) :
    V x ^ (1 / 2 : ℝ) * V x ^ (1 / 2 : ℝ) = V x := by
  rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

variable [MeasurableSpace.CountablyGenerated X] in
/-- **`√V`-uniform ergodicity** (MT p. 398, via Lemma 15.2.9): the bound (16.3) for `V` gives the
bound (16.3) for `√V`. -/
theorem exists_vErgDist_sqrt_le {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (h : ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ n, vErgDist V P μ n ≤ R * r⁻¹ ^ n) :
    ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
      ∀ n, vErgDist (fun x => V x ^ (1 / 2 : ℝ)) P μ n ≤ R * r⁻¹ ^ n := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    have := ENNReal.rpow_le_rpow (hV1 x) hhalf.le
    rwa [ENNReal.one_rpow] at this
  have hWt : ∀ x, V x ^ (1 / 2 : ℝ) ≠ ∞ := fun x => ENNReal.rpow_ne_top_of_nonneg hhalf.le (hVt x)
  obtain ⟨V₀, hV₀m, hV₀1, c, hc, hequiv, ρ, b, hρ, hb, C, hC, hd⟩ :=
    ((theorem_16_0_1 hψ hap hV hV1 hVt μ hμ).out 2 4).1 h
  obtain ⟨ρ', b', hρ', hb', C', hC', hd'⟩ := lemma_15_2_9 hV₀m hV₀1 hρ hb hC hd
  have key := (theorem_16_0_1 hψ hap (hV.pow_const (1 / 2 : ℝ)) hW1 hWt μ hμ).out 2 4
  refine key.2 ⟨fun x => V₀ x ^ (1 / 2 : ℝ), hV₀m.pow_const _, fun x => by
      have := ENNReal.rpow_le_rpow (hV₀1 x) hhalf.le
      rwa [ENNReal.one_rpow] at this, c ^ (1 / 2 : ℝ),
      ENNReal.rpow_ne_top_of_nonneg hhalf.le hc, fun x => ⟨?_, ?_⟩, ρ', b', hρ', hb', C', hC', hd'⟩
  · rw [← ENNReal.mul_rpow_of_nonneg _ _ hhalf.le]
    exact ENNReal.rpow_le_rpow (hequiv x).1 hhalf.le
  · rw [← ENNReal.mul_rpow_of_nonneg _ _ hhalf.le]
    exact ENNReal.rpow_le_rpow (hequiv x).2 hhalf.le

/-! ### Theorem 16.1.5 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.1.5** (MT p. 398): if `Φ` is `V`-uniformly ergodic (with every distance finite),
there are `R < ∞` and `ρ < 1` such that for all measurable `g, h` with `g² ≤ V`, `h² ≤ V`, all
`x` and all `k, n`,
`|E_x[g(Φₖ) h(Φₖ₊ₙ)] − E_x[g(Φₖ)] E_x[h(Φₖ₊ₙ)]| ≤ R ρⁿ (1 + ρᵏ V(x))`. -/
theorem theorem_16_1_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (hU : (∀ n, vErgDist V P μ n ≠ ∞) ∧ IsVUniformlyErgodic V P μ) :
    ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ ρ : ℝ≥0∞, ρ < 1 ∧ ∀ g h : X → ℝ, Measurable g → Measurable h →
      (∀ y, ENNReal.ofReal (g y ^ 2) ≤ V y) → (∀ y, ENNReal.ofReal (h y ^ 2) ≤ V y) →
        ∀ x k n, ENNReal.ofReal |∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x -
          (∫ ω, g (ω k) ∂pathKernel P x) * ∫ ω, h (ω (k + n)) ∂pathKernel P x| ≤
            R * ρ ^ n * (1 + ρ ^ k * V x) := by
  have := nonempty_of_isProbabilityMeasure μ
  inhabit X
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  set W : X → ℝ≥0∞ := fun x => V x ^ (1 / 2 : ℝ) with hWdef
  have hWm : Measurable W := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ W x := fun x => by
    have := ENNReal.rpow_le_rpow (hV1 x) hhalf.le
    rwa [ENNReal.one_rpow] at this
  have hWt : ∀ x, W x ≠ ∞ := fun x => ENNReal.rpow_ne_top_of_nonneg hhalf.le (hVt x)
  have hW0 : ∀ x, W x ≠ 0 := fun x => (zero_lt_one.trans_le (hW1 x)).ne'
  have hV0 : ∀ x, V x ≠ 0 := fun x => (zero_lt_one.trans_le (hV1 x)).ne'
  have hWW : ∀ x, W x * W x = V x := rpow_half_mul_self V
  have hWV : ∀ x, W x ≤ V x := fun x => by
    calc W x = W x * 1 := (mul_one _).symm
      _ ≤ W x * W x := mul_le_mul' le_rfl (hW1 x)
      _ = V x := hWW x
  obtain ⟨r, hr, R, hR, hA⟩ := ((theorem_16_0_1 hψ hap hV hV1 hVt μ hμ).out 1 2).1 hU
  obtain ⟨r₁, hr₁, R₁, hR₁, hA₁⟩ :=
    exists_vErgDist_sqrt_le hψ hap hV hV1 hVt μ hμ ⟨r, hr, R, hR, hA⟩
  have hμV : ∫⁻ y, V y ∂μ ≠ ∞ :=
    lintegral_ne_top_of_vErgDist_zero hV hV1 (hVt default) P μ (hU.1 0)
  set m := ∫⁻ y, V y ∂μ with hm
  set mW := ∫⁻ y, W y ∂μ with hmW
  have hmW : mW ≠ ∞ := ne_top_of_le_ne_top hμV (lintegral_mono hWV)
  set ρ := max r⁻¹ r₁⁻¹ with hρ
  have hρ1 : ρ < 1 := max_lt (ENNReal.inv_lt_one.2 hr) (ENNReal.inv_lt_one.2 hr₁)
  have hrρ : r⁻¹ ≤ ρ := le_max_left _ _
  have hr₁ρ : r₁⁻¹ ≤ ρ := le_max_right _ _
  have hA₁le : ∀ j, vErgDist W P μ j ≤ R₁ := fun j => (hA₁ j).trans
    (mul_le_of_le_one_right' (pow_le_one₀ zero_le (ENNReal.inv_le_one.2 hr₁.le)))
  refine ⟨R₁ * m + R₁ * R + (R₁ + mW) * R₁, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top hR₁ hμV, ENNReal.mul_ne_top hR₁ hR⟩, ENNReal.mul_ne_top
      (ENNReal.add_ne_top.2 ⟨hR₁, hmW⟩) hR₁⟩, ρ, hρ1, fun g h hg hh hg2 hh2 x k n => ?_⟩
  have hgW : ∀ y, ENNReal.ofReal |g y| ≤ W y := fun y => by
    rw [hWdef]
    simp only
    have : ENNReal.ofReal |g y| = ENNReal.ofReal (g y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hhalf.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs]
    rw [this]
    exact ENNReal.rpow_le_rpow (hg2 y) hhalf.le
  have hhW : ∀ y, ENNReal.ofReal |h y| ≤ W y := fun y => by
    rw [hWdef]
    simp only
    have : ENNReal.ofReal |h y| = ENNReal.ofReal (h y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hhalf.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs]
    rw [this]
    exact ENNReal.rpow_le_rpow (hh2 y) hhalf.le
  -- moments
  have hPV : ∀ j y, ∫⁻ z, V z ∂(P ^ j) y ≤ R * r⁻¹ ^ j * V y + m := fun j y =>
    (lintegral_pow_le_vErgDist hV P μ j (hV0 y) (hVt y)).trans
      (add_le_add (mul_le_mul' (hA j) le_rfl) le_rfl)
  have hPVt : ∀ j y, ∫⁻ z, V z ∂(P ^ j) y ≠ ∞ := fun j y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hR
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne'))) (hVt y), hμV⟩)
      (hPV j y)
  have hPW : ∀ j y, ∫⁻ z, W z ∂(P ^ j) y ≤ (R₁ + mW) * W y := fun j y => by
    calc ∫⁻ z, W z ∂(P ^ j) y ≤ vErgDist W P μ j * W y + mW :=
          lintegral_pow_le_vErgDist hWm P μ j (hW0 y) (hWt y)
      _ ≤ R₁ * W y + mW * W y := add_le_add (mul_le_mul' (hA₁le j) le_rfl)
          (le_mul_of_one_le_right' (hW1 y))
      _ = (R₁ + mW) * W y := (add_mul _ _ _).symm
  have hintW : ∀ (ν : Measure X), ∫⁻ z, V z ∂ν ≠ ∞ → ∀ f : X → ℝ, Measurable f →
      (∀ y, ENNReal.ofReal |f y| ≤ W y) → Integrable f ν := fun ν hν f hf hfW =>
    integrable_of_ofReal_abs_le hf hfW (ne_top_of_le_ne_top hν (lintegral_mono hWV))
  have hhP : ∀ j y, Integrable h ((P ^ j) y) := fun j y => hintW _ (hPVt j y) h hh hhW
  have hhμ : Integrable h μ := hintW μ hμV h hh hhW
  have hgP : Integrable g ((P ^ k) x) := hintW _ (hPVt k x) g hg hgW
  -- the inner function `Pⁿh` and its centring
  set Hn : X → ℝ := fun y => ∫ z, h z ∂(P ^ n) y with hHn
  set cH := ∫ z, h z ∂μ with hcH
  have hHnm : Measurable Hn :=
    (StronglyMeasurable.integral_kernel (κ := P ^ n) hh.stronglyMeasurable).measurable
  have hHnb : ∀ y, ENNReal.ofReal |Hn y - cH| ≤ R₁ * ρ ^ n * W y := fun y => by
    have := isMarkovKernel_pow P n
    calc ENNReal.ofReal |Hn y - cH| ≤ fNorm W ((P ^ n) y) μ :=
          ofReal_abs_integral_sub_le_fNorm ⟨hh, hhW, hhP n y, hhμ⟩
      _ ≤ vErgDist W P μ n * W y := fNorm_pow_le_vErgDist_mul P μ n (hW0 y) (hWt y)
      _ ≤ R₁ * r₁⁻¹ ^ n * W y := mul_le_mul' (hA₁ n) le_rfl
      _ ≤ R₁ * ρ ^ n * W y := mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hr₁ρ n))
          le_rfl
  have hHnabs : ∀ y, ENNReal.ofReal |Hn y| ≤ (R₁ + mW) * W y := fun y => by
    calc ENNReal.ofReal |Hn y| = ‖Hn y‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ z, ‖h z‖ₑ ∂(P ^ n) y := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z, W z ∂(P ^ n) y := lintegral_mono fun z => by
          rw [Real.enorm_eq_ofReal_abs]; exact hhW z
      _ ≤ (R₁ + mW) * W y := hPW n y
  have hc1 : R₁ + mW ≠ ∞ := ENNReal.add_ne_top.2 ⟨hR₁, hmW⟩
  -- integrability for `Pᵏ(x, ·)`
  have hint_gHn : Integrable (fun y => g y * Hn y) ((P ^ k) x) := by
    refine integrable_of_ofReal_abs_le (f := fun y => (R₁ + mW) * V y) (hg.mul hHnm)
      (fun y => ?_) ?_
    · rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← hWW y]
      calc ENNReal.ofReal |g y| * ENNReal.ofReal |Hn y| ≤ W y * ((R₁ + mW) * W y) :=
            mul_le_mul' (hgW y) (hHnabs y)
        _ = (R₁ + mW) * (W y * W y) := by ring
    · rw [lintegral_const_mul' _ _ hc1]; exact ENNReal.mul_ne_top hc1 (hPVt k x)
  have hint_Hn : Integrable Hn ((P ^ k) x) :=
    integrable_of_ofReal_abs_le (f := fun y => (R₁ + mW) * W y) hHnm hHnabs (by
      rw [lintegral_const_mul' _ _ hc1]
      exact ENNReal.mul_ne_top hc1 (ne_top_of_le_ne_top (hPVt k x) (lintegral_mono hWV)))
  have hint_pair : Integrable (fun p : X × X => g p.1 * h p.2) ((P ^ k) x ⊗ₘ (P ^ n)) := by
    have := isMarkovKernel_pow P k
    have := isMarkovKernel_pow P n
    refine integrable_of_ofReal_abs_le (f := fun p : X × X => W p.1 * W p.2)
      ((hg.comp measurable_fst).mul (hh.comp measurable_snd)) (fun p => ?_) ?_
    · rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul' (hgW p.1) (hhW p.2)
    · rw [Measure.lintegral_compProd (f := fun p : X × X => W p.1 * W p.2)
        ((hWm.comp measurable_fst).mul (hWm.comp measurable_snd))]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hc1 (hPVt k x)) ?_
      calc ∫⁻ y, ∫⁻ z, W (y, z).1 * W (y, z).2 ∂(P ^ n) y ∂(P ^ k) x
          = ∫⁻ y, W y * ∫⁻ z, W z ∂(P ^ n) y ∂(P ^ k) x := by
            refine lintegral_congr fun y => ?_
            exact lintegral_const_mul (W y) hWm
        _ ≤ ∫⁻ y, W y * ((R₁ + mW) * W y) ∂(P ^ k) x :=
            lintegral_mono fun y => mul_le_mul' le_rfl (hPW n y)
        _ = ∫⁻ y, (R₁ + mW) * V y ∂(P ^ k) x := lintegral_congr fun y => by
            rw [← hWW y]; ring
        _ = (R₁ + mW) * ∫⁻ y, V y ∂(P ^ k) x := lintegral_const_mul _ hV
  -- the three expectations
  have hE1 : ∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x = ∫ y, g y * Hn y ∂(P ^ k) x :=
    integral_pair_eq P x k n hg hh hint_pair
  have hEG : ∫ ω, g (ω k) ∂pathKernel P x = ∫ y, g y ∂(P ^ k) x := integral_coord_eq P x k hg
  have hEH : ∫ ω, h (ω (k + n)) ∂pathKernel P x = ∫ y, Hn y ∂(P ^ k) x := by
    rw [integral_coord_eq P x (k + n) hh, pow_add_eq]
    have := isMarkovKernel_pow P (k + n)
    have hi : Integrable h (((P ^ n) ∘ₖ (P ^ k)) x) := by rw [← pow_add_eq]; exact hhP (k + n) x
    exact Kernel.integral_comp hi
  set EG := ∫ y, g y ∂(P ^ k) x with hEGdef
  set EH := ∫ y, Hn y ∂(P ^ k) x with hEHdef
  -- the decomposition
  have hdec : ∫ y, g y * Hn y ∂(P ^ k) x - EG * EH =
      ∫ y, g y * (Hn y - cH) ∂(P ^ k) x + EG * (cH - EH) := by
    have e : ∫ y, g y * (Hn y - cH) ∂(P ^ k) x = ∫ y, g y * Hn y ∂(P ^ k) x - EG * cH := by
      simp_rw [mul_sub]
      rw [integral_sub hint_gHn (hgP.mul_const cH), integral_mul_const]
    rw [e]; ring
  rw [hE1, hEG, hEH, hdec]
  -- the first term
  have hT1 : ENNReal.ofReal |∫ y, g y * (Hn y - cH) ∂(P ^ k) x| ≤
      R₁ * ρ ^ n * (R * ρ ^ k * V x + m) := by
    calc ENNReal.ofReal |∫ y, g y * (Hn y - cH) ∂(P ^ k) x|
        = ‖∫ y, g y * (Hn y - cH) ∂(P ^ k) x‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ y, ‖g y * (Hn y - cH)‖ₑ ∂(P ^ k) x := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, R₁ * ρ ^ n * V y ∂(P ^ k) x := lintegral_mono fun y => by
          rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← hWW y]
          calc ENNReal.ofReal |g y| * ENNReal.ofReal |Hn y - cH|
              ≤ W y * (R₁ * ρ ^ n * W y) := mul_le_mul' (hgW y) (hHnb y)
            _ = R₁ * ρ ^ n * (W y * W y) := by ring
      _ = R₁ * ρ ^ n * ∫⁻ y, V y ∂(P ^ k) x := lintegral_const_mul _ hV
      _ ≤ R₁ * ρ ^ n * (R * r⁻¹ ^ k * V x + m) := mul_le_mul' le_rfl (hPV k x)
      _ ≤ R₁ * ρ ^ n * (R * ρ ^ k * V x + m) := mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hrρ k)) le_rfl) le_rfl)
  -- the second term
  have hEGb : ENNReal.ofReal |EG| ≤ (R₁ + mW) * W x := by
    calc ENNReal.ofReal |EG| = ‖EG‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ z, ‖g z‖ₑ ∂(P ^ k) x := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z, W z ∂(P ^ k) x := lintegral_mono fun z => by
          rw [Real.enorm_eq_ofReal_abs]; exact hgW z
      _ ≤ (R₁ + mW) * W x := hPW k x
  have hEHb : ENNReal.ofReal |cH - EH| ≤ R₁ * ρ ^ (k + n) * W x := by
    have := isMarkovKernel_pow P (k + n)
    have hEH' : EH = ∫ z, h z ∂(P ^ (k + n)) x := by
      rw [← hEH, integral_coord_eq P x (k + n) hh]
    rw [abs_sub_comm, hEH']
    calc ENNReal.ofReal |∫ z, h z ∂(P ^ (k + n)) x - cH| ≤ fNorm W ((P ^ (k + n)) x) μ :=
          ofReal_abs_integral_sub_le_fNorm ⟨hh, hhW, hhP (k + n) x, hhμ⟩
      _ ≤ vErgDist W P μ (k + n) * W x := fNorm_pow_le_vErgDist_mul P μ _ (hW0 x) (hWt x)
      _ ≤ R₁ * r₁⁻¹ ^ (k + n) * W x := mul_le_mul' (hA₁ _) le_rfl
      _ ≤ R₁ * ρ ^ (k + n) * W x := mul_le_mul' (mul_le_mul' le_rfl
          (pow_le_pow_left₀ zero_le hr₁ρ _)) le_rfl
  have hT2 : ENNReal.ofReal |EG * (cH - EH)| ≤ (R₁ + mW) * R₁ * ρ ^ n * (ρ ^ k * V x) := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    calc ENNReal.ofReal |EG| * ENNReal.ofReal |cH - EH|
        ≤ (R₁ + mW) * W x * (R₁ * ρ ^ (k + n) * W x) := mul_le_mul' hEGb hEHb
      _ = (R₁ + mW) * R₁ * ρ ^ n * (ρ ^ k * (W x * W x)) := by rw [pow_add]; ring
      _ = (R₁ + mW) * R₁ * ρ ^ n * (ρ ^ k * V x) := by rw [hWW x]
  calc ENNReal.ofReal |∫ y, g y * (Hn y - cH) ∂(P ^ k) x + EG * (cH - EH)|
      ≤ ENNReal.ofReal (|∫ y, g y * (Hn y - cH) ∂(P ^ k) x| + |EG * (cH - EH)|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |∫ y, g y * (Hn y - cH) ∂(P ^ k) x| + ENNReal.ofReal |EG * (cH - EH)| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ R₁ * ρ ^ n * (R * ρ ^ k * V x + m) + (R₁ + mW) * R₁ * ρ ^ n * (ρ ^ k * V x) :=
        add_le_add hT1 hT2
    _ = R₁ * m * ρ ^ n + (R₁ * R + (R₁ + mW) * R₁) * ρ ^ n * (ρ ^ k * V x) := by ring
    _ ≤ (R₁ * m + R₁ * R + (R₁ + mW) * R₁) * ρ ^ n +
          (R₁ * m + R₁ * R + (R₁ + mW) * R₁) * ρ ^ n * (ρ ^ k * V x) := by
        refine add_le_add (mul_le_mul' ?_ le_rfl) (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl)
        · rw [add_assoc]; exact le_self_add
        · rw [add_assoc]; exact le_add_self
    _ = (R₁ * m + R₁ * R + (R₁ + mW) * R₁) * ρ ^ n * (1 + ρ ^ k * V x) := by ring

/-- **`V`-geometric mixing** (MT p. 398): `|E_x[g(Φₖ) h(Φₖ₊ₙ)] − E_x[g(Φₖ)] E_x[h(Φₖ₊ₙ)]| ≤
R V(x) ρⁿ` for all `k`, all `x` and all `g² ≤ V`, `h² ≤ V`, with `R < ∞`, `ρ < 1`. -/
def IsVGeomMixing (P : Kernel X X) [IsMarkovKernel P] (V : X → ℝ≥0∞) : Prop :=
  ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ ρ : ℝ≥0∞, ρ < 1 ∧ ∀ g h : X → ℝ, Measurable g → Measurable h →
    (∀ y, ENNReal.ofReal (g y ^ 2) ≤ V y) → (∀ y, ENNReal.ofReal (h y ^ 2) ≤ V y) →
      ∀ x k n, ENNReal.ofReal |∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x -
        (∫ ω, g (ω k) ∂pathKernel P x) * ∫ ω, h (ω (k + n)) ∂pathKernel P x| ≤ R * V x * ρ ^ n

variable [MeasurableSpace.CountablyGenerated X] in
/-- **A `V`-uniformly ergodic chain is `V`-geometrically mixing** (MT Theorem 16.1.5, p. 398):
`1 + ρᵏ V(x) ≤ 2 V(x)`. -/
theorem theorem_16_1_5_mixing {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (hU : (∀ n, vErgDist V P μ n ≠ ∞) ∧ IsVUniformlyErgodic V P μ) : IsVGeomMixing P V := by
  obtain ⟨R, hR, ρ, hρ, hb⟩ := theorem_16_1_5 hψ hap hV hV1 hVt μ hμ hU
  refine ⟨2 * R, ENNReal.mul_ne_top ENNReal.ofNat_ne_top hR, ρ, hρ,
    fun g h hg hh hg2 hh2 x k n => (hb g h hg hh hg2 hh2 x k n).trans ?_⟩
  have hk : ρ ^ k ≤ 1 := pow_le_one₀ zero_le hρ.le
  calc R * ρ ^ n * (1 + ρ ^ k * V x) ≤ R * ρ ^ n * (V x + 1 * V x) :=
        mul_le_mul' le_rfl (add_le_add (hV1 x) (mul_le_mul' hk le_rfl))
    _ = 2 * R * V x * ρ ^ n := by ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The stationary version is geometrically mixing** (16.17), MT p. 398: for a `V`-uniformly
ergodic chain started from its invariant probability `π`, there are `R < ∞` and `ρ < 1` with
`|E_π[g(Φₖ) h(Φₖ₊ₙ)] − π(g) π(h)| ≤ R ρⁿ` for all `g² ≤ V`, `h² ≤ V` and `k, n` (here `π(V) < ∞`,
Theorem 14.3.7). -/
theorem eq_16_17 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (hU : (∀ n, vErgDist V P μ n ≠ ∞) ∧ IsVUniformlyErgodic V P μ) :
    ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ ρ : ℝ≥0∞, ρ < 1 ∧ ∀ g h : X → ℝ, Measurable g → Measurable h →
      (∀ y, ENNReal.ofReal (g y ^ 2) ≤ V y) → (∀ y, ENNReal.ofReal (h y ^ 2) ≤ V y) →
        ∀ k n, ENNReal.ofReal |∫ ω, g (ω k) * h (ω (k + n)) ∂pathMeasure P μ -
          (∫ y, g y ∂μ) * ∫ y, h y ∂μ| ≤ R * ρ ^ n := by
  have := nonempty_of_isProbabilityMeasure μ
  inhabit X
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  set W : X → ℝ≥0∞ := fun x => V x ^ (1 / 2 : ℝ) with hWdef
  have hWm : Measurable W := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ W x := fun x => by
    have := ENNReal.rpow_le_rpow (hV1 x) hhalf.le
    rwa [ENNReal.one_rpow] at this
  have hWt : ∀ x, W x ≠ ∞ := fun x => ENNReal.rpow_ne_top_of_nonneg hhalf.le (hVt x)
  have hW0 : ∀ x, W x ≠ 0 := fun x => (zero_lt_one.trans_le (hW1 x)).ne'
  have hV0 : ∀ x, V x ≠ 0 := fun x => (zero_lt_one.trans_le (hV1 x)).ne'
  have hWW : ∀ x, W x * W x = V x := rpow_half_mul_self V
  have hWV : ∀ x, W x ≤ V x := fun x => by
    calc W x = W x * 1 := (mul_one _).symm
      _ ≤ W x * W x := mul_le_mul' le_rfl (hW1 x)
      _ = V x := hWW x
  obtain ⟨r, hr, R, hR, hA⟩ := ((theorem_16_0_1 hψ hap hV hV1 hVt μ hμ).out 1 2).1 hU
  obtain ⟨r₁, hr₁, R₁, hR₁, hA₁⟩ :=
    exists_vErgDist_sqrt_le hψ hap hV hV1 hVt μ hμ ⟨r, hr, R, hR, hA⟩
  have hμV : ∫⁻ y, V y ∂μ ≠ ∞ :=
    lintegral_ne_top_of_vErgDist_zero hV hV1 (hVt default) P μ (hU.1 0)
  set m := ∫⁻ y, V y ∂μ with hm
  set mW := ∫⁻ y, W y ∂μ with hmW
  have hmW : mW ≠ ∞ := ne_top_of_le_ne_top hμV (lintegral_mono hWV)
  have hA₁le : ∀ j, vErgDist W P μ j ≤ R₁ := fun j => (hA₁ j).trans
    (mul_le_of_le_one_right' (pow_le_one₀ zero_le (ENNReal.inv_le_one.2 hr₁.le)))
  have hc1 : R₁ + mW ≠ ∞ := ENNReal.add_ne_top.2 ⟨hR₁, hmW⟩
  refine ⟨R₁ * m, ENNReal.mul_ne_top hR₁ hμV, r₁⁻¹, ENNReal.inv_lt_one.2 hr₁,
    fun g h hg hh hg2 hh2 k n => ?_⟩
  have hgW : ∀ y, ENNReal.ofReal |g y| ≤ W y := fun y => by
    rw [hWdef]
    have : ENNReal.ofReal |g y| = ENNReal.ofReal (g y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hhalf.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs]
    rw [this]
    exact ENNReal.rpow_le_rpow (hg2 y) hhalf.le
  have hhW : ∀ y, ENNReal.ofReal |h y| ≤ W y := fun y => by
    rw [hWdef]
    have : ENNReal.ofReal |h y| = ENNReal.ofReal (h y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hhalf.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs]
    rw [this]
    exact ENNReal.rpow_le_rpow (hh2 y) hhalf.le
  have hPV : ∀ j y, ∫⁻ z, V z ∂(P ^ j) y ≠ ∞ := fun j y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (hU.1 j) (hVt y), hμV⟩)
      (lintegral_pow_le_vErgDist hV P μ j (hV0 y) (hVt y))
  have hPW : ∀ j y, ∫⁻ z, W z ∂(P ^ j) y ≤ (R₁ + mW) * W y := fun j y => by
    calc ∫⁻ z, W z ∂(P ^ j) y ≤ vErgDist W P μ j * W y + mW :=
          lintegral_pow_le_vErgDist hWm P μ j (hW0 y) (hWt y)
      _ ≤ R₁ * W y + mW * W y := add_le_add (mul_le_mul' (hA₁le j) le_rfl)
          (le_mul_of_one_le_right' (hW1 y))
      _ = (R₁ + mW) * W y := (add_mul _ _ _).symm
  have hintW : ∀ (ν : Measure X), ∫⁻ z, V z ∂ν ≠ ∞ → ∀ f : X → ℝ, Measurable f →
      (∀ y, ENNReal.ofReal |f y| ≤ W y) → Integrable f ν := fun ν hν f hf hfW =>
    integrable_of_ofReal_abs_le hf hfW (ne_top_of_le_ne_top hν (lintegral_mono hWV))
  have hhP : ∀ j y, Integrable h ((P ^ j) y) := fun j y => hintW _ (hPV j y) h hh hhW
  have hhμ : Integrable h μ := hintW μ hμV h hh hhW
  have hgμ : Integrable g μ := hintW μ hμV g hg hgW
  set Hn : X → ℝ := fun y => ∫ z, h z ∂(P ^ n) y with hHn
  set cH := ∫ z, h z ∂μ with hcH
  have hHnm : Measurable Hn :=
    (StronglyMeasurable.integral_kernel (κ := P ^ n) hh.stronglyMeasurable).measurable
  have hHnb : ∀ y, ENNReal.ofReal |Hn y - cH| ≤ R₁ * r₁⁻¹ ^ n * W y := fun y => by
    have := isMarkovKernel_pow P n
    calc ENNReal.ofReal |Hn y - cH| ≤ fNorm W ((P ^ n) y) μ :=
          ofReal_abs_integral_sub_le_fNorm ⟨hh, hhW, hhP n y, hhμ⟩
      _ ≤ vErgDist W P μ n * W y := fNorm_pow_le_vErgDist_mul P μ n (hW0 y) (hWt y)
      _ ≤ R₁ * r₁⁻¹ ^ n * W y := mul_le_mul' (hA₁ n) le_rfl
  have hHnabs : ∀ y, ENNReal.ofReal |Hn y| ≤ (R₁ + mW) * W y := fun y => by
    calc ENNReal.ofReal |Hn y| = ‖Hn y‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ z, ‖h z‖ₑ ∂(P ^ n) y := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z, W z ∂(P ^ n) y := lintegral_mono fun z => by
          rw [Real.enorm_eq_ofReal_abs]; exact hhW z
      _ ≤ (R₁ + mW) * W y := hPW n y
  have hgHb : ∀ y, ENNReal.ofReal |g y * Hn y| ≤ (R₁ + mW) * V y := fun y => by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← hWW y]
    calc ENNReal.ofReal |g y| * ENNReal.ofReal |Hn y| ≤ W y * ((R₁ + mW) * W y) :=
          mul_le_mul' (hgW y) (hHnabs y)
      _ = (R₁ + mW) * (W y * W y) := by ring
  have hint_gHn : ∀ (ν : Measure X), ∫⁻ z, V z ∂ν ≠ ∞ →
      Integrable (fun y => g y * Hn y) ν := fun ν hν =>
    integrable_of_ofReal_abs_le (f := fun y => (R₁ + mW) * V y) (hg.mul hHnm) hgHb (by
      rw [lintegral_const_mul' _ _ hc1]; exact ENNReal.mul_ne_top hc1 hν)
  -- the path expectations under `P_π`
  have := isMarkovKernel_pathKernel P
  have := isMarkovKernel_pow P k
  have := isMarkovKernel_pow P n
  have hWWm : Measurable fun p : X × X => W p.1 * W p.2 :=
    (hWm.comp measurable_fst).mul (hWm.comp measurable_snd)
  have hpb : ∀ x, ∫⁻ p, W p.1 * W p.2 ∂((P ^ k) x ⊗ₘ (P ^ n)) ≤
      (R₁ + mW) * ∫⁻ y, V y ∂(P ^ k) x := fun x => by
    rw [Measure.lintegral_compProd (f := fun p : X × X => W p.1 * W p.2) hWWm]
    calc ∫⁻ y, ∫⁻ z, W (y, z).1 * W (y, z).2 ∂(P ^ n) y ∂(P ^ k) x
        = ∫⁻ y, W y * ∫⁻ z, W z ∂(P ^ n) y ∂(P ^ k) x :=
          lintegral_congr fun y => lintegral_const_mul (W y) hWm
      _ ≤ ∫⁻ y, W y * ((R₁ + mW) * W y) ∂(P ^ k) x :=
          lintegral_mono fun y => mul_le_mul' le_rfl (hPW n y)
      _ = ∫⁻ y, (R₁ + mW) * V y ∂(P ^ k) x := lintegral_congr fun y => by
          rw [← hWW y]; ring
      _ = (R₁ + mW) * ∫⁻ y, V y ∂(P ^ k) x := lintegral_const_mul _ hV
  have hgh : ∀ p : X × X, ‖g p.1 * h p.2‖ₑ ≤ W p.1 * W p.2 := fun p => by
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul' (hgW p.1) (hhW p.2)
  have hpair : ∀ x, ∫ ω, g (ω k) * h (ω (k + n)) ∂pathKernel P x =
      ∫ y, g y * Hn y ∂(P ^ k) x := fun x =>
    integral_pair_eq P x k n hg hh ⟨((hg.comp measurable_fst).mul
      (hh.comp measurable_snd)).aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono hgh)
        (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (ENNReal.mul_ne_top hc1 (hPV k x)) (hpb x)))⟩
  have hk : (P ^ k : Kernel X X) ∘ₘ μ = μ := hμ.pow k
  have hpm : Measurable fun ω : ℕ → X => (ω k, ω (k + n)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply (k + n))
  have hFm : Measurable fun ω : ℕ → X => g (ω k) * h (ω (k + n)) :=
    (hg.comp (measurable_pi_apply k)).mul (hh.comp (measurable_pi_apply (k + n)))
  have hinner : ∀ x, ∫⁻ ω, ‖g (ω k) * h (ω (k + n))‖ₑ ∂pathKernel P x ≤
      (R₁ + mW) * ∫⁻ y, V y ∂(P ^ k) x := fun x => by
    have e : ∫⁻ ω, ‖g (ω k) * h (ω (k + n))‖ₑ ∂pathKernel P x =
        ∫⁻ p, ‖g p.1 * h p.2‖ₑ ∂((pathKernel P x).map fun ω => (ω k, ω (k + n))) := by
      rw [lintegral_map (f := fun p : X × X => ‖g p.1 * h p.2‖ₑ)
        (((hg.comp measurable_fst).mul (hh.comp measurable_snd)).enorm) hpm]
    rw [e, pathKernel_map_pair]
    exact (lintegral_mono hgh).trans (hpb x)
  have hFint : Integrable (fun ω : ℕ → X => g (ω k) * h (ω (k + n)))
      (pathKernel P ∘ₘ μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    change ∫⁻ ω, ‖g (ω k) * h (ω (k + n))‖ₑ ∂(pathKernel P ∘ₘ μ) < ∞
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hFm.enorm.aemeasurable]
    calc ∫⁻ x, ∫⁻ ω, ‖g (ω k) * h (ω (k + n))‖ₑ ∂pathKernel P x ∂μ
        ≤ ∫⁻ x, (R₁ + mW) * ∫⁻ y, V y ∂(P ^ k) x ∂μ := lintegral_mono hinner
      _ = (R₁ + mW) * ∫⁻ y, V y ∂((P ^ k : Kernel X X) ∘ₘ μ) := by
          rw [lintegral_const_mul _ hV.lintegral_kernel]
          congr 1
          exact lintegral_kfun μ (P ^ k) hV
      _ = (R₁ + mW) * m := by rw [hk]
      _ < ∞ := lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hc1 hμV)
  have hE1 : ∫ ω, g (ω k) * h (ω (k + n)) ∂pathMeasure P μ = ∫ y, g y * Hn y ∂μ := by
    rw [pathMeasure_eq_comp, integral_measure_comp _ _ hFint]
    simp_rw [hpair]
    rw [← integral_measure_comp _ _ (by rw [hk]; exact hint_gHn μ hμV), hk]
  rw [hE1]
  have hdec : ∫ y, g y * Hn y ∂μ - (∫ y, g y ∂μ) * cH = ∫ y, g y * (Hn y - cH) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub (hint_gHn μ hμV) (hgμ.mul_const cH), integral_mul_const]
  rw [hdec]
  calc ENNReal.ofReal |∫ y, g y * (Hn y - cH) ∂μ| = ‖∫ y, g y * (Hn y - cH) ∂μ‖ₑ :=
        (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ y, ‖g y * (Hn y - cH)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, R₁ * r₁⁻¹ ^ n * V y ∂μ := lintegral_mono fun y => by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← hWW y]
        calc ENNReal.ofReal |g y| * ENNReal.ofReal |Hn y - cH|
            ≤ W y * (R₁ * r₁⁻¹ ^ n * W y) := mul_le_mul' (hgW y) (hHnb y)
          _ = R₁ * r₁⁻¹ ^ n * (W y * W y) := by ring
    _ = R₁ * r₁⁻¹ ^ n * m := lintegral_const_mul _ hV
    _ = R₁ * m * r₁⁻¹ ^ n := by ring

/-- **Strong mixing** of the chain started from `μ` (MT p. 397): some `δ(n) → 0` bounds
`|E_μ[g(Φₖ) h(Φₖ₊ₙ)] − E_μ[g(Φₖ)] E_μ[h(Φₖ₊ₙ)]|` uniformly in `k` and in `|g|, |h| ≤ 1`. -/
def IsStrongMixing (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) : Prop :=
  ∃ δ : ℕ → ℝ≥0∞, Tendsto δ atTop (𝓝 0) ∧ ∀ g h : X → ℝ, Measurable g → Measurable h →
    (∀ y, |g y| ≤ 1) → (∀ y, |h y| ≤ 1) → ∀ k n,
      ENNReal.ofReal |∫ ω, g (ω k) * h (ω (k + n)) ∂pathMeasure P μ -
        (∫ ω, g (ω k) ∂pathMeasure P μ) * ∫ ω, h (ω (k + n)) ∂pathMeasure P μ| ≤ δ n

/-- Under an invariant probability, `E_μ[g(Φₖ)] = μ(g)`. -/
theorem integral_coord_pathMeasure (P : Kernel X X) [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) (k : ℕ) {g : X → ℝ} (hg : Measurable g) :
    ∫ ω, g (ω k) ∂pathMeasure P μ = ∫ y, g y ∂μ := by
  rw [← integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable,
    pathMeasure_map_coord, hμ.pow k]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The stationary version of a `V`-uniformly ergodic chain is strong mixing**, with geometric
`δ(n) = Rρⁿ` (MT p. 398, from (16.17); bounded `g`, `h` have `g², h² ≤ 1 ≤ V`). -/
theorem isStrongMixing_of_vUniformlyErgodic {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (hU : (∀ n, vErgDist V P μ n ≠ ∞) ∧ IsVUniformlyErgodic V P μ) : IsStrongMixing P μ := by
  obtain ⟨R, hR, ρ, hρ, hb⟩ := eq_16_17 hψ hap hV hV1 hVt μ hμ hU
  refine ⟨fun n => R * ρ ^ n, ?_, fun g h hg hh hg1 hh1 k n => ?_⟩
  · simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ)
      (Or.inr hR)
  have hsq : ∀ (f : X → ℝ), (∀ y, |f y| ≤ 1) → ∀ y, ENNReal.ofReal (f y ^ 2) ≤ V y :=
    fun f hf y => by
      refine le_trans ?_ (hV1 y)
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hf y
      nlinarith [abs_nonneg (f y), sq_abs (f y)]
  rw [integral_coord_pathMeasure P hμ k hg, integral_coord_pathMeasure P hμ (k + n) hh]
  exact hb g h hg hh (hsq g hg1) (hsq h hh1) k n

end MeynTweedie.Epilogue
