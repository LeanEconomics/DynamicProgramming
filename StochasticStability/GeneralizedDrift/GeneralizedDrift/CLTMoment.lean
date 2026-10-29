/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.CLTCriteria
import GeneralizedDrift.GeometricErgodicTheorem

/-!
# Criteria for the CLT (MT §17.5, Theorem 17.0.1)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/CLTMoment.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Lemmas 17.5.1–17.5.2, Theorems 17.5.3–17.5.4 (pp. 450–454) and
Theorem 17.0.1 (p. 422). The CLT moment condition: (V3) holds with `f ≥ 1`, `V` everywhere
finite and `C` petite, and the invariant probability has `π(V²) < ∞`.

**Degenerate variance.**
* `tendsto_inv_sqrt_mul_succ_iff`, `tendsto_inv_sqrt_natCast`, `isShiftInvariant_sqrt_pathSum`:
  the event `{n^{−1/2} Sₙ(g) → 0}` is shift invariant.
* `tendsto_zero_of_poissonVariance_eq_zero`: for a Harris chain with a solution `ĝ` of Poisson's
  equation with `ĝ, Pĝ ∈ L²(π)` and `γ_g² = π(ĝ² − (Pĝ)²) = 0`, `n^{−1/2} Sₙ(g − c) → 0`
  `P_x`-a.s. for every `x` (the martingale increments vanish `P_π`-a.s., and Proposition 17.1.6).

**Autocovariances and moments.**
* `integral_coord_zero_mul`: `E_μ[h₁(Φ₀) h₂(Φₖ)] = ∫ μ(dx) h₁(x) Pᵏh₂(x)`.
* `memLp_toReal_of_lintegral_sq`, `lintegral_ne_top_of_sq`: `π(V²) < ∞` gives `V ∈ L²(π)` and
  `π(V) < ∞`.
* `poissonSeries`: `ĝ = Σₙ (Pⁿg − π(g))` (17.39); `asymptoticVariance`: the series (17.3);
  `poissonSeries_abs_bound`: `Σₙ |Pⁿg(x) − π(g)| ≤ R (V(x) + 1)`.

**Results.**
* **Lemma 17.5.1** (`lemma_17_5_1`, p. 450): (V4) for `V ≥ 1` and a petite set gives the CLT
  moment condition with `f = √V`, `V' = (1 − ρ')⁻¹√V`.
* **Lemma 17.5.2 (i)** (`lemma_17_5_2_i`, p. 451): `ĝ` solves Poisson's equation with
  `|ĝ| ≤ R (V + 1)`, and `g, ĝ, Pĝ ∈ L²(π)`.
* **Theorem 17.5.3** (`theorem_17_5_3`, p. 452): `γ_g² = π(ĝ² − (Pĝ)²) ≥ 0`,
  `(1/n) E_π[Sₙ(ḡ)²] → γ_g²`, and `γ_g² = E_π[ḡ(Φ₀)²] + 2 Σ_{k≥1} E_π[ḡ(Φ₀)ḡ(Φₖ)]` with
  absolutely summable autocovariances (17.56); `theorem_17_5_3_clt`: the CLT under every `P_x`;
  `theorem_17_5_3_degenerate`: if `γ_g² = 0`, `n^{−1/2} Sₙ(ḡ) → 0` a.s. from every state (the book
  leaves convergence in distribution to the reader).
* **Theorem 17.5.4** (`theorem_17_5_4`, `theorem_17_5_4_clt`, p. 453), with (V4) for a petite set
  in place of `V`-uniform ergodicity (equivalent by Theorem 16.0.1) and `ofReal_abs_le_sqrt`.
* **Theorem 17.0.1** (`theorem_17_0_1`, `theorem_17_0_1_iv`, p. 422): (i) the LLN from every
  state; (ii) `γ_g²` of (17.3) is finite, non-negative and the limit (17.4); (iii) `γ_g² = 0` gives
  `n^{−1/2} Sₙ(ḡ) → 0` a.s.; (iv) the CLT.

**Hypotheses.** "Ergodic" (MT p. 316) is taken as positive Harris and aperiodic; the variance
statements of Theorem 17.5.3 use only `ψ`-irreducibility and aperiodicity. `V`-uniform ergodicity
(Chapter 16, not in this project) is replaced by its drift characterisation (V4) for a petite set.

**Elsewhere.** Here the CLT comes from the martingale route of §17.4 and needs no cycle moments.
Lemma 17.5.2 (ii), the moment bound (17.53) for the split `m`-skeleton, and through it (Theorem
17.3.6) the LIL parts of Theorems 17.5.3, 17.5.4 and 17.0.1 (iv) are in `SkeletonMoment`
(`lemma_17_5_2_ii`, `theorem_17_5_3_lil_skeleton`, `theorem_17_5_4_lil_skeleton`,
`theorem_17_0_1_iv_lil_skeleton`).
-/
namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The event `{n^{−1/2} Sₙ(g) → 0}` -/

/-- For a real sequence, `n^{−1/2} u(n + 1) → 0` iff `n^{−1/2} u(n) → 0`. -/
theorem tendsto_inv_sqrt_mul_succ_iff (u : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * u (n + 1)) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * u n) atTop (𝓝 0) := by
  have key : ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ, |(√((n : ℝ) + 1))⁻¹ * y| ≤ |(√(n : ℝ))⁻¹ * y| ∧
      |(√(n : ℝ))⁻¹ * y| ≤ √2 * |(√((n : ℝ) + 1))⁻¹ * y| := by
    intro n hn y
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hst : √(n : ℝ) ≤ √((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have ht : 0 < √((n : ℝ) + 1) := hs.trans_le hst
    have hts : √((n : ℝ) + 1) ≤ √2 * √(n : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hs), abs_of_pos (inv_pos.2 ht)]
    constructor
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ hs hst) (abs_nonneg y)
    · rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg y)
      rw [← div_eq_mul_inv, le_div_iff₀ ht, inv_mul_eq_div, div_le_iff₀ hs]
      exact hts
  constructor
  · intro h
    rw [← tendsto_add_atTop_iff_nat 1]
    refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      (by simpa only [norm_zero] using h.norm)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.cast_succ]
    exact (key n hn _).1
  · intro h
    have h1 := (tendsto_add_atTop_iff_nat 1).2 h
    have h2 : Tendsto (fun n : ℕ => √2 * |(√((n : ℝ) + 1))⁻¹ * u (n + 1)|) atTop (𝓝 0) := by
      have := (h1.abs).const_mul √2
      simp only [abs_zero, mul_zero] at this
      refine this.congr fun n => ?_
      simp only [Nat.cast_succ]
    refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) h2
    rw [Real.norm_eq_abs]
    exact (key n hn _).2

/-- `n^{−1/2} → 0`. -/
theorem tendsto_inv_sqrt_natCast : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

omit [MeasurableSpace X] in
/-- The event `{n^{−1/2} Sₙ(g) → 0}` is shift invariant. -/
theorem isShiftInvariant_sqrt_pathSum (g : X → ℝ) :
    IsShiftInvariant {ω : ℕ → X |
      Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop (𝓝 0)} := by
  have hone : ∀ ω : ℕ → X, (Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * pathSum g n (shift 1 ω))
      atTop (𝓝 0) ↔ Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop (𝓝 0)) := by
    intro ω
    have hsplit : ∀ n : ℕ, pathSum g n (shift 1 ω) = pathSum g (n + 1) ω - g (ω 1) := by
      intro n
      have h := pathSum_split g (m := 1) (n := n + 1) (by omega) ω
      rw [Nat.add_sub_cancel] at h
      have h1 : pathSum g 1 ω = g (ω 1) := by simp [pathSum]
      rw [h, h1]; ring
    have hc : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * g (ω 1)) atTop (𝓝 0) := by
      have := tendsto_inv_sqrt_natCast.mul_const (g (ω 1))
      rwa [zero_mul] at this
    rw [← tendsto_inv_sqrt_mul_succ_iff (fun n => pathSum g n ω)]
    simp_rw [hsplit, mul_sub]
    constructor
    · intro h
      have := h.add hc
      rw [zero_add] at this
      exact this.congr fun n => by ring
    · intro h
      have := h.sub hc
      rwa [sub_zero] at this
  intro m ω
  induction m generalizing ω with
  | zero => rw [shift_zero]
  | succ m ih =>
    rw [← shift_shift 1 m]
    have h := ih ω
    simp only [mem_ofPred_eq] at h ⊢
    rw [← h]
    exact hone (shift m ω)

/-! ### Degenerate asymptotic variance -/

/-- If `γ_g² = π(ĝ² − (Pĝ)²) = 0` for a Harris chain and a solution `ĝ` of Poisson's equation with
`ĝ, Pĝ ∈ L²(π)`, then `n^{−1/2} Sₙ(g − c) → 0` almost surely from every initial state. Under
`P_π` the increments `ĝ(Φₖ₊₁) − Pĝ(Φₖ)` have zero second moment, so `Sₙ(g − c) = Pĝ(Φ₀) − Pĝ(Φₙ)`;
the LLN for `(Pĝ)²` gives `Pĝ(Φₙ)²/n → 0`; and the event is shift invariant
(Proposition 17.1.6). -/
theorem tendsto_zero_of_poissonVariance_eq_zero [MeasurableSpace.CountablyGenerated X]
    {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgm : Measurable g)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    (h0 : ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π = 0) (x : X) :
    ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * pathSum (fun y => g y - c) n ω) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hPm := measurable_kernelInt P hghm
  set E : Set (ℕ → X) := {ω | Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
    pathSum (fun y => g y - c) n ω) atTop (𝓝 0)} with hE
  have hEm : MeasurableSet E := measurableSet_tendsto (𝓝 0) fun n =>
    measurable_const.mul (measurable_pathSum (hgm.sub measurable_const) n)
  obtain ⟨-, hL2, -, hsq⟩ := poisson_increment_props P hπ hghm hgh2 hPgh2
  -- the increments vanish `P_π`-a.s.
  have hD0 : ∀ k, ∀ᵐ ω ∂pathMeasure P π, gh (ω (k + 1)) - kernelInt P gh (ω k) = 0 := by
    intro k
    have hint : ∫ ω, (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2 ∂pathMeasure P π = 0 := by
      rw [hsq k, h0]
    have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) (hL2 k).integrable_sq).1 hint
    filter_upwards [h] with ω hω
    exact pow_eq_zero_iff two_ne_zero |>.1 hω
  have hall := ae_all_iff.2 hD0
  have hlln := lln_of_harris_measure hH hπ (hPm.pow_const 2) hPgh2.integrable_sq π
  have hπE : ∀ᵐ ω ∂pathMeasure P π, ω ∈ E := by
    filter_upwards [hall, hlln] with ω hω hl
    have hS : ∀ n : ℕ, (√(n : ℝ))⁻¹ * pathSum (fun y => g y - c) n ω =
        (√(n : ℝ))⁻¹ * kernelInt P gh (ω 0) - (√(n : ℝ))⁻¹ * kernelInt P gh (ω n) := by
      intro n
      rw [pathSum_eq_poissonMart hsol n ω, poissonMart,
        Finset.sum_eq_zero fun k _ => hω k]
      ring
    have h1 : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * kernelInt P gh (ω 0)) atTop (𝓝 0) := by
      have := tendsto_inv_sqrt_natCast.mul_const (kernelInt P gh (ω 0))
      rwa [zero_mul] at this
    -- `Pĝ(Φₙ)²/n → 0`
    have h2 : Tendsto (fun n : ℕ => kernelInt P gh (ω n) ^ 2 / n) atTop (𝓝 0) := by
      have h := tendsto_term_div_of_tendsto_average (a := fun j => kernelInt P gh (ω (j + 1)) ^ 2)
        hl
      rw [← tendsto_add_atTop_iff_nat 1]
      refine h.congr fun n => ?_
      simp only [Nat.cast_succ]
    have h3 : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * kernelInt P gh (ω n)) atTop (𝓝 0) := by
      have hs : Tendsto (fun n : ℕ => √(kernelInt P gh (ω n) ^ 2 / n)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp h2
        rwa [Real.sqrt_zero] at this
      refine squeeze_zero_norm (fun n => le_of_eq ?_) hs
      rw [Real.norm_eq_abs, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
        abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), div_eq_inv_mul]
    have := h1.sub h3
    rw [sub_zero] at this
    exact this.congr fun n => (hS n).symm
  have hπE1 : pathMeasure P π E = 1 := by
    rw [ae_iff] at hπE
    exact (prob_compl_eq_zero_iff hEm).1 hπE
  have hx := proposition_17_1_6 hH hEm (isShiftInvariant_sqrt_pathSum _) π hπE1 x
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff hEm).2 hx

/-! ### Autocovariances -/

/-- `E_μ[h₁(Φ₀) h₂(Φₖ)] = ∫ μ(dx) h₁(x) Pᵏh₂(x)`. -/
theorem integral_coord_zero_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {h₁ h₂ : X → ℝ} (h₁m : Measurable h₁) (h₂m : Measurable h₂) (k : ℕ)
    (hi : Integrable (fun ω : ℕ → X => h₁ (ω 0) * h₂ (ω k)) (pathMeasure P μ))
    (hi2 : Integrable (fun ω : ℕ → X => h₂ (ω k)) (pathMeasure P μ)) :
    ∫ ω, h₁ (ω 0) * h₂ (ω k) ∂pathMeasure P μ =
      ∫ x, h₁ x * ∫ y, h₂ y ∂(P ^ k : Kernel X X) x ∂μ := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hmk := markov_property P μ 0 (H := fun ω => h₂ (ω k)) (h₂m.comp (measurable_pi_apply k))
    (by simpa only [shift_zero] using hi2)
  simp only [shift_zero] at hmk
  have hf : StronglyMeasurable[natFilt 0] fun ω : ℕ → X => h₁ (ω 0) :=
    (h₁m.comp (measurable_coord_natFilt 0)).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hf hi hi2
  have hPk : Measurable fun x => ∫ y, h₂ y ∂(P ^ k : Kernel X X) x := by
    have := isMarkovKernel_pow P k
    exact (StronglyMeasurable.integral_kernel h₂m.stronglyMeasurable).measurable
  calc ∫ ω, h₁ (ω 0) * h₂ (ω k) ∂pathMeasure P μ
      = ∫ ω, ((pathMeasure P μ)[(fun ω : ℕ → X => h₁ (ω 0)) * (fun ω => h₂ (ω k)) |
          natFilt 0]) ω ∂pathMeasure P μ := (integral_condExp ((natFilt (X := X)).le 0)).symm
    _ = ∫ ω, h₁ (ω 0) * ∫ ω', h₂ (ω' k) ∂pathKernel P (ω 0) ∂pathMeasure P μ := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hmk] with ω e1 e2
        rw [e1, Pi.mul_apply, e2]
    _ = ∫ ω, h₁ (ω 0) * ∫ y, h₂ y ∂(P ^ k : Kernel X X) (ω 0) ∂pathMeasure P μ := by
        simp_rw [integral_coord_eq P h₂m]
    _ = ∫ x, h₁ x * ∫ y, h₂ y ∂(P ^ k : Kernel X X) x ∂μ := by
        have h := integral_map (μ := pathMeasure P μ) (measurable_pi_apply 0).aemeasurable
          (f := fun x => h₁ x * ∫ y, h₂ y ∂(P ^ k : Kernel X X) x)
          (h₁m.mul hPk).aestronglyMeasurable
        rw [pathMeasure_map_zero] at h
        exact h.symm

/-! ### Square-integrability of `V` -/

/-- `π(V²) < ∞` gives `V ∈ L²(π)` (as a real function). -/
theorem memLp_toReal_of_lintegral_sq {μ : Measure X} {V : X → ℝ≥0∞} (hV : Measurable V)
    (h : ∫⁻ x, V x ^ 2 ∂μ ≠ ∞) : MemLp (fun x => (V x).toReal) 2 μ := by
  refine (memLp_two_iff_integrable_sq hV.ennreal_toReal.aestronglyMeasurable).2 ?_
  have := integrable_toReal_of_lintegral_ne_top (hV.pow_const 2).aemeasurable h
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_pow]

/-- `π(V²) < ∞` gives `π(V) < ∞` for a finite measure. -/
theorem lintegral_ne_top_of_sq {μ : Measure X} [IsFiniteMeasure μ] {V : X → ℝ≥0∞}
    (h : ∫⁻ x, V x ^ 2 ∂μ ≠ ∞) : ∫⁻ x, V x ∂μ ≠ ∞ := by
  have hle : ∀ x, V x ≤ 1 + V x ^ 2 := fun x => by
    by_cases hx : V x ≤ 1
    · exact hx.trans le_self_add
    · push Not at hx
      calc V x = V x * 1 := (mul_one _).symm
        _ ≤ V x * V x := by gcongr
        _ = V x ^ 2 := (sq _).symm
        _ ≤ 1 + V x ^ 2 := le_add_self
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_add_left measurable_const, lintegral_const]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.one_ne_top (measure_ne_top _ _), h⟩

/-! ### Lemma 17.5.2 (i): Poisson's equation under the CLT moment condition -/

/-- The solution `ĝ = Σₙ (Pⁿg − π(g))` (17.39) of Poisson's equation. -/
noncomputable def poissonSeries (P : Kernel X X) (π : Measure X) (g : X → ℝ) (x : X) : ℝ :=
  ∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π)

/-- The asymptotic variance (17.3): `γ_g² = E_π[ḡ(Φ₀)²] + 2 Σ_{k ≥ 1} E_π[ḡ(Φ₀) ḡ(Φₖ)]`,
`ḡ = g − π(g)`. -/
noncomputable def asymptoticVariance (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (g : X → ℝ) : ℝ :=
  ∫ ω, (g (ω 0) - ∫ y, g y ∂π) ^ 2 ∂pathMeasure P π + 2 * ∑' k : ℕ,
    ∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω (k + 1)) - ∫ y, g y ∂π) ∂pathMeasure P π

variable [MeasurableSpace.CountablyGenerated X]

/-- Under (V3) with `π(V) < ∞`, the series (17.39) converges absolutely, with
`Σₙ |Pⁿg(x) − π(g)| ≤ R (V(x) + 1)` for every `|g| ≤ f`, and its sum of absolute values is
measurable. -/
theorem poissonSeries_abs_bound {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (hπV : ∫⁻ x, V x ∂π ≠ ∞) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      (∀ n x, Integrable g ((P ^ n : Kernel X X) x)) ∧ Integrable g π ∧
      (∀ x, Summable fun n => |∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π|) ∧
      (∀ x, ∑' n, |∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π| ≤
        R * ((V x).toReal + 1)) ∧
      Measurable fun x => ∑' n, |∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π| := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨-, -, -, -, hsum⟩ := theorem_14_0_1_consequences hψ hap hf hf1 hpet hV hb
    (hVfin x₀) hdrift hπ
  obtain ⟨B, hB, hBbd⟩ := hsum hπV
  refine ⟨B.toReal, ENNReal.toReal_nonneg, fun g hgm hgf => ?_⟩
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := by
    obtain ⟨_, hfin⟩ := isPositive_of_driftV3 hψ hf hf1 hpet hV hb (hVfin x₀) hdrift
    exact hfin π inferInstance hπ
  have hPf : ∀ n x, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hVfin x, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hb⟩)
      (lintegral_pow_le_of_driftV3 hf hV hCm hdrift x n)
  have hgPn : ∀ n x, Integrable g ((P ^ n : Kernel X X) x) := fun n x =>
    integrable_of_ofReal_abs_le hgm hgf (hPf n x)
  have hgπ : Integrable g π := integrable_of_ofReal_abs_le hgm hgf hπf
  set a : ℕ → X → ℝ := fun n x => ∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π with ha
  have habs : ∀ n x, ENNReal.ofReal |a n x| ≤ fNorm f ((P ^ n : Kernel X X) x) π :=
    fun n x => ofReal_abs_integral_sub_le_fNorm ⟨hgm, hgf, hgPn n x, hgπ⟩
  have hbound : ∀ x, ∑' n, ENNReal.ofReal |a n x| ≤ B * (V x + 1) := fun x =>
    (ENNReal.tsum_le_tsum fun n => habs n x).trans (hBbd x)
  have hne : ∀ x, ∑' n, ENNReal.ofReal |a n x| ≠ ∞ := fun x =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
      ⟨hVfin x, ENNReal.one_ne_top⟩)) (hbound x)
  have hsumm : ∀ x, Summable fun n => |a n x| := fun x =>
    (ENNReal.summable_toReal (hne x)).congr fun n => by rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  have htsum : ∀ x, ∑' n, |a n x| = (∑' n, ENNReal.ofReal |a n x|).toReal := fun x => by
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  refine ⟨hgPn, hgπ, hsumm, fun x => ?_, ?_⟩
  · rw [htsum x]
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
      ⟨hVfin x, ENNReal.one_ne_top⟩)) (hbound x)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add (hVfin x) ENNReal.one_ne_top,
      ENNReal.toReal_one] at h3
  · have ham : ∀ n, Measurable (a n) := fun n => by
      have := isMarkovKernel_pow P n
      exact ((StronglyMeasurable.integral_kernel hgm.stronglyMeasurable).measurable).sub
        measurable_const
    refine measurable_of_tendsto_metrizable (f := fun N x => ∑ n ∈ Finset.range N, |a n x|)
      (fun N => Finset.measurable_sum _ fun n _ => measurable_abs_of_measurable (ham n)) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact (hsumm x).hasSum.tendsto_sum_nat

/-- **Lemma 17.5.2 (i)** (MT p. 451): under the CLT moment condition ((V3) with `f ≥ 1`, `V`
finite, `C` petite, `π(V²) < ∞`), there is `R < ∞` such that for every `|g| ≤ f` the series
`ĝ = Σₙ (Pⁿg − π(g))` solves Poisson's equation with `|ĝ| ≤ R (V + 1)`; in particular
`g, ĝ, Pĝ ∈ L²(π)`. -/
theorem lemma_17_5_2_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      IsPoissonSolution P g (poissonSeries P π g) (∫ y, g y ∂π) ∧
      Measurable (poissonSeries P π g) ∧
      (∀ x, |poissonSeries P π g x| ≤ R * ((V x).toReal + 1)) ∧
      MemLp g 2 π ∧ MemLp (poissonSeries P π g) 2 π ∧
      MemLp (kernelInt P (poissonSeries P π g)) 2 π := by
  have hπV := lintegral_ne_top_of_sq hπV2
  obtain ⟨R, hR, hsol⟩ := theorem_17_4_2 hψ hap hf hf1 hpet hV hVfin hb hdrift hπ hπV
  refine ⟨R, hR, fun g hgm hgf => ?_⟩
  obtain ⟨hs, hm, hbd⟩ := hsol g hgm hgf
  have hVL2 : MemLp (fun x => (V x).toReal) 2 π := memLp_toReal_of_lintegral_sq hV hπV2
  have hfle : ∀ x, ENNReal.ofReal |g x| ≤ V x + b := fun x => by
    refine (hgf x).trans ?_
    calc f x ≤ ∫⁻ y, V y ∂P x + f x := le_add_self
      _ ≤ V x + C.indicator (fun _ => b) x := hdrift x
      _ ≤ V x + b := add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x)
  have hg2 : MemLp g 2 π := by
    refine MemLp.of_le (hVL2.add (memLp_const b.toReal)) hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hVfin x, hb⟩) (hfle x)
    rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_add (hVfin x) hb] at this
  have hgh2 : MemLp (poissonSeries P π g) 2 π := by
    refine MemLp.of_le ((hVL2.add (memLp_const 1)).const_mul R) hm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hR (add_nonneg ENNReal.toReal_nonneg zero_le_one))]
    exact hbd x
  have hPeq : kernelInt P (poissonSeries P π g) =
      fun x => poissonSeries P π g x - (g x - ∫ y, g y ∂π) := funext fun x => by
    have h2 : poissonSeries P π g x - kernelInt P (poissonSeries P π g) x =
        g x - ∫ y, g y ∂π := (hs x).2
    linarith
  refine ⟨hs, hm, hbd, hg2, hgh2, ?_⟩
  rw [hPeq]
  exact hgh2.sub (hg2.sub (memLp_const _))

/-! ### Theorem 17.5.3 -/

/-- **Theorem 17.5.3** (MT p. 452), the asymptotic variance: under the CLT moment condition, for
`|g| ≤ f`, `ḡ = g − π(g)` and `ĝ = Σₙ (Pⁿg − π(g))`, the constant `γ_g² = π(ĝ² − (Pĝ)²)` is well
defined (`ĝ, Pĝ ∈ L²(π)`) and non-negative, `(1/n) E_π[Sₙ(ḡ)²] → γ_g²`, the autocovariances
`E_π[ḡ(Φ₀) ḡ(Φₖ)]` are absolutely summable, and
`γ_g² = E_π[ḡ(Φ₀)²] + 2 Σ_{k ≥ 1} E_π[ḡ(Φ₀) ḡ(Φₖ)]` (17.56). Only the ergodicity used in the
proof is assumed: `ψ`-irreducibility and aperiodicity. -/
theorem theorem_17_5_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x) :
    MemLp (poissonSeries P π g) 2 π ∧ MemLp (kernelInt P (poissonSeries P π g)) 2 π ∧
    0 ≤ ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π ∧
    Tendsto (fun n : ℕ =>
      (∫ ω, pathSum (fun x => g x - ∫ y, g y ∂π) n ω ^ 2 ∂pathMeasure P π) / n) atTop
      (𝓝 (∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) ∧
    Summable (fun k : ℕ => |∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω k) - ∫ y, g y ∂π)
      ∂pathMeasure P π|) ∧
    ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π =
      ∫ ω, (g (ω 0) - ∫ y, g y ∂π) ^ 2 ∂pathMeasure P π + 2 * ∑' k : ℕ,
        ∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω (k + 1)) - ∫ y, g y ∂π) ∂pathMeasure P π := by
  have := isProbabilityMeasure_pathMeasure P π
  obtain ⟨R, -, hL⟩ := lemma_17_5_2_i hψ hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2
  obtain ⟨hsol, hghm, -, hg2, hgh2, hPgh2⟩ := hL g hgm hgf
  obtain ⟨R', hR', hS⟩ := poissonSeries_abs_bound hψ hap hf hf1 hpet hV hVfin hb hdrift hπ
    (lintegral_ne_top_of_sq hπV2)
  obtain ⟨hgPn, -, hsumm, hsbd, hsm⟩ := hS g hgm hgf
  have hσ := (poisson_increment_props P hπ hghm hgh2 hPgh2).2.2.2 0
  refine ⟨hgh2, hPgh2, by rw [← hσ]; exact integral_nonneg fun ω => sq_nonneg _,
    tendsto_variance_poisson P hπ hsol hghm hgh2 hPgh2, ?_⟩
  set c := ∫ y, g y ∂π with hc
  set gh := poissonSeries P π g with hgh
  set a : ℕ → X → ℝ := fun n x => ∫ y, g y ∂(P ^ n : Kernel X X) x - c with ha
  have hgbm : Measurable fun x => g x - c := hgm.sub measurable_const
  have hgb2 : MemLp (fun x => g x - c) 2 π := hg2.sub (memLp_const c)
  have hlaw : ∀ j, (pathMeasure P π).map (fun ω => ω j) = π := fun j => hπ.map_coord j
  have hcL2 : ∀ j, MemLp (fun ω : ℕ → X => g (ω j) - c) 2 (pathMeasure P π) := fun j => by
    have : MemLp (fun x => g x - c) 2 ((pathMeasure P π).map fun ω => ω j) := by
      rw [hlaw j]; exact hgb2
    exact this.comp_of_map (measurable_pi_apply j).aemeasurable
  have hs1 : ∀ k x, ∫ y, (g y - c) ∂(P ^ k : Kernel X X) x = a k x := fun k x => by
    have := isMarkovKernel_pow P k
    rw [integral_sub (hgPn k x) (integrable_const c), integral_const, probReal_univ, one_smul]
  have hs2 : ∀ k, ∫ ω, (g (ω 0) - c) * (g (ω k) - c) ∂pathMeasure P π =
      ∫ x, (g x - c) * a k x ∂π := fun k => by
    rw [integral_coord_zero_mul P π hgbm hgbm k ((hcL2 0).integrable_mul (hcL2 k))
      ((hcL2 k).integrable one_le_two)]
    simp_rw [hs1]
  have ham : ∀ n, Measurable (a n) := fun n => by
    have := isMarkovKernel_pow P n
    exact ((StronglyMeasurable.integral_kernel hgm.stronglyMeasurable).measurable).sub
      measurable_const
  have hVL2 : MemLp (fun x => (V x).toReal) 2 π := memLp_toReal_of_lintegral_sq hV hπV2
  have habs2 : MemLp (fun x => |g x - c|) 2 π := hgb2.norm
  have hdomI : Integrable (fun x => |g x - c| * (R' * ((V x).toReal + 1))) π := by
    have h1 : MemLp (fun x => R' * ((V x).toReal + 1)) 2 π :=
      (hVL2.add (memLp_const 1)).const_mul R'
    exact habs2.integrable_mul h1
  have htm : (fun x => ∑' n, |g x - c| * |a n x|) = fun x => |g x - c| * ∑' n, |a n x| :=
    funext fun x => tsum_mul_left
  have hbI : Integrable (fun x => ∑' n, |g x - c| * |a n x|) π := by
    rw [htm]
    refine hdomI.mono' ((measurable_abs_of_measurable hgbm).mul hsm).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (tsum_nonneg fun n => abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hsbd x) (abs_nonneg _)
  have hbS : ∀ x, Summable fun n => |g x - c| * |a n x| := fun x => (hsumm x).mul_left _
  have hasum : ∀ x, Summable fun n => a n x := fun x =>
    Summable.of_norm ((hsumm x).congr fun n => (Real.norm_eq_abs _).symm)
  have hhas : HasSum (fun k => ∫ x, (g x - c) * a k x ∂π) (∫ x, (g x - c) * gh x ∂π) :=
    hasSum_integral_of_dominated_convergence (fun n x => |g x - c| * |a n x|)
      (fun n => (hgbm.mul (ham n)).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_mul])
      (Eventually.of_forall hbS) hbI
      (Eventually.of_forall fun x => (hasum x).hasSum.mul_left (g x - c))
  have hhasB : HasSum (fun k => ∫ x, |g x - c| * |a k x| ∂π)
      (∫ x, ∑' n, |g x - c| * |a n x| ∂π) :=
    hasSum_integral_of_dominated_convergence (fun n x => |g x - c| * |a n x|)
      (fun n => ((measurable_abs_of_measurable hgbm).mul
        (measurable_abs_of_measurable (ham n))).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))])
      (Eventually.of_forall hbS) hbI (Eventually.of_forall fun x => (hbS x).hasSum)
  refine ⟨Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hhasB.summable, ?_⟩
  · calc |∫ ω, (g (ω 0) - c) * (g (ω k) - c) ∂pathMeasure P π|
        = |∫ x, (g x - c) * a k x ∂π| := by rw [hs2 k]
      _ ≤ ∫ x, |(g x - c) * a k x| ∂π := abs_integral_le_integral_abs
      _ = ∫ x, |g x - c| * |a k x| ∂π := by simp_rw [abs_mul]
  -- `γ² = 2 π(ḡ ĝ) − π(ḡ²)`
  have hv := poisson_variance_eq (π := π) hsol
  have hI : Integrable (fun x => 2 * ((g x - c) * gh x)) π :=
    (hgb2.integrable_mul hgh2).const_mul 2
  have hint2 : Integrable (fun x => (g x - c) ^ 2) π := hgb2.integrable_sq
  have e : (fun x => 2 * gh x * (g x - c) - (g x - c) ^ 2) =
      fun x => 2 * ((g x - c) * gh x) - (g x - c) ^ 2 := funext fun x => by ring
  have hv2 : ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π =
      2 * ∫ x, (g x - c) * gh x ∂π - ∫ x, (g x - c) ^ 2 ∂π := by
    rw [hv, e, integral_sub hI hint2, integral_const_mul]
  -- `π(ḡ ĝ) = Σₖ π(ḡ Pᵏḡ)`
  have htsum := hhas.tsum_eq
  rw [hhas.summable.tsum_eq_zero_add] at htsum
  have ha0 : ∀ x, a 0 x = g x - c := fun x => by
    simp only [ha, pow_zero_apply, integral_dirac' _ _ hgm.stronglyMeasurable]
  have h0 : ∫ x, (g x - c) * a 0 x ∂π = ∫ x, (g x - c) ^ 2 ∂π := by
    simp_rw [ha0, sq]
  have hp0 : ∫ ω, (g (ω 0) - c) ^ 2 ∂pathMeasure P π = ∫ x, (g x - c) * a 0 x ∂π := by
    rw [← hs2 0]; simp_rw [sq]
  rw [hv2, hp0]
  simp_rw [hs2]
  rw [← htsum, h0]
  ring

/-- **Theorem 17.5.3** (MT p. 452), the CLT: for an ergodic (positive Harris, aperiodic) chain
under the CLT moment condition and `|g| ≤ f`, `n^{−1/2} Sₙ(ḡ) ⇒ N(0, γ_g²)` under every `P_x`.
The book asks `γ_g² > 0`; with the degenerate normal `N(0, 0) = δ₀` no positivity is needed. -/
theorem theorem_17_5_3_clt {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (poissonSeries P π g x ^ 2 -
      kernelInt P (poissonSeries P π g) x ^ 2) ∂π).toNNReal) P') (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      atTop Z (fun _ => pathKernel P x) P' := by
  obtain ⟨R, -, hL⟩ := lemma_17_5_2_i hph.1.1 hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2
  obtain ⟨hsol, hghm, -, -, hgh2, hPgh2⟩ := hL g hgm hgf
  exact theorem_17_4_5_clt hph hap hπ hsol hghm hgm hgh2 hPgh2 hZ x

/-- **Theorem 17.5.3**, the degenerate case (MT p. 453): under the CLT moment condition, for a
Harris chain and `|g| ≤ f`, if `γ_g² = 0` then `n^{−1/2} Sₙ(ḡ) → 0` almost surely from every
initial state. The book states (and leaves to the reader) only convergence in distribution, and
proves almost sure convergence for `V`-uniformly ergodic chains (Theorem 17.5.4). -/
theorem theorem_17_5_3_degenerate {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x)
    (h0 : ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π = 0)
    (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n : ℕ =>
      (√(n : ℝ))⁻¹ * pathSum (fun y => g y - ∫ z, g z ∂π) n ω) atTop (𝓝 0) := by
  obtain ⟨R, -, hL⟩ := lemma_17_5_2_i hH.1 hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2
  obtain ⟨hsol, hghm, -, -, hgh2, hPgh2⟩ := hL g hgm hgf
  exact tendsto_zero_of_poissonVariance_eq_zero hH hπ hsol hghm hgm hgh2 hPgh2 h0 x

/-! ### Lemma 17.5.1 and Theorem 17.5.4: `V`-uniformly ergodic chains -/

/-- **Lemma 17.5.1** (MT p. 450): if (V4) holds for `V ≥ 1` and a petite set (equivalently, by
Theorem 16.0.1, the aperiodic chain is `V`-uniformly ergodic), then the CLT moment condition holds
with `f = √V` and `V' = (1 − ρ')⁻¹ √V`: (V3) holds for some petite `C'`, and
`π(V'²) = (1 − ρ')⁻² π(V) < ∞`. -/
theorem lemma_17_5_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ ρ' b' : ℝ≥0∞, ∃ C' : Set X, ρ' < 1 ∧ b' ≠ ∞ ∧ IsPetite P C' ∧
      DriftV3 P (fun x => (1 - ρ')⁻¹ * V x ^ (1 / 2 : ℝ)) (fun x => V x ^ (1 / 2 : ℝ))
        ((1 - ρ')⁻¹ * b') C' ∧
      ∫⁻ x, ((1 - ρ')⁻¹ * V x ^ (1 / 2 : ℝ)) ^ 2 ∂π ≠ ∞ := by
  obtain ⟨ρ', b', hρ', hb', C', hC', h4⟩ := lemma_15_2_9 hV hV1 hρ hb hC h
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h (hVfin x₀)
  have hπV := (hgeo π hπ).1
  have hct : (1 - ρ')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne'
  refine ⟨ρ', b', C', hρ', hb', hC', h4.driftV3_scaled hWm hρ', ?_⟩
  have hsq : ∀ x, (V x ^ (1 / 2 : ℝ)) ^ 2 = V x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  simp_rw [mul_pow, hsq]
  rw [lintegral_const_mul _ hV]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hct) hπV

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `g² ≤ V` gives `|g| ≤ √V`. -/
theorem ofReal_abs_le_sqrt {g : X → ℝ} {V : X → ℝ≥0∞} (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x)
    (x : X) : ENNReal.ofReal |g x| ≤ V x ^ (1 / 2 : ℝ) := by
  have h1 : ENNReal.ofReal |g x| ^ (2 : ℝ) ≤ V x := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]; exact hg x
  calc ENNReal.ofReal |g x| = (ENNReal.ofReal |g x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ V x ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)

/-- **Theorem 17.5.4** (MT p. 453): for a positive Harris, aperiodic chain satisfying (V4) for
`V ≥ 1` finite and a petite set (that is, a `V`-uniformly ergodic chain, Theorem 16.0.1), and
`g² ≤ V`, the conclusions of Theorem 17.5.3 hold, and if `γ_g² = 0` then `n^{−1/2} Sₙ(ḡ) → 0`
almost surely from every initial state. -/
theorem theorem_17_5_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) :
    MemLp (poissonSeries P π g) 2 π ∧ MemLp (kernelInt P (poissonSeries P π g)) 2 π ∧
    0 ≤ ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π ∧
    Tendsto (fun n : ℕ =>
      (∫ ω, pathSum (fun x => g x - ∫ y, g y ∂π) n ω ^ 2 ∂pathMeasure P π) / n) atTop
      (𝓝 (∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) ∧
    Summable (fun k : ℕ => |∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω k) - ∫ y, g y ∂π)
      ∂pathMeasure P π|) ∧
    ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π =
      ∫ ω, (g (ω 0) - ∫ y, g y ∂π) ^ 2 ∂pathMeasure P π + 2 * ∑' k : ℕ,
        ∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω (k + 1)) - ∫ y, g y ∂π) ∂pathMeasure P π ∧
    (∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π = 0 →
      ∀ x, ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n : ℕ =>
        (√(n : ℝ))⁻¹ * pathSum (fun y => g y - ∫ z, g z ∂π) n ω) atTop (𝓝 0)) := by
  obtain ⟨ρ', b', C', hρ', hb', hC', h3, hπV2⟩ := lemma_17_5_1 hph.1.1 hap hV hV1 hVfin hρ hb
    hC h hπ
  have hct : (1 - ρ')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne'
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    simpa using ENNReal.rpow_le_rpow (hV1 x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hV'm : Measurable fun x => (1 - ρ')⁻¹ * V x ^ (1 / 2 : ℝ) := hWm.const_mul _
  have hV'fin : ∀ x, (1 - ρ')⁻¹ * V x ^ (1 / 2 : ℝ) ≠ ∞ := fun x =>
    ENNReal.mul_ne_top hct (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hVfin x))
  have hgf := ofReal_abs_le_sqrt hg
  obtain ⟨h1, h2, h3', h4, h5, h6⟩ := theorem_17_5_3 hph.1.1 hap hWm hW1 hC' hV'm hV'fin
    (ENNReal.mul_ne_top hct hb') h3 hπ hπV2 hgm hgf
  exact ⟨h1, h2, h3', h4, h5, h6, fun h0 x => theorem_17_5_3_degenerate hph.1 hap hWm hW1 hC'
    hV'm hV'fin (ENNReal.mul_ne_top hct hb') h3 hπ hπV2 hgm hgf h0 x⟩

/-- **Theorem 17.5.4**, the CLT: under the hypotheses of `theorem_17_5_4`,
`n^{−1/2} Sₙ(ḡ) ⇒ N(0, γ_g²)` under every `P_x`. -/
theorem theorem_17_5_4_clt {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (poissonSeries P π g x ^ 2 -
      kernelInt P (poissonSeries P π g) x ^ 2) ∂π).toNNReal) P') (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      atTop Z (fun _ => pathKernel P x) P' := by
  obtain ⟨ρ', b', C', hρ', hb', hC', h3, hπV2⟩ := lemma_17_5_1 hph.1.1 hap hV hV1 hVfin hρ hb
    hC h hπ
  have hct : (1 - ρ')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne'
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    simpa using ENNReal.rpow_le_rpow (hV1 x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact theorem_17_5_3_clt hph hap hWm hW1 hC' (hWm.const_mul _) (fun x =>
    ENNReal.mul_ne_top hct (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hVfin x)))
    (ENNReal.mul_ne_top hct hb') h3 hπ hπV2 hgm (ofReal_abs_le_sqrt hg) hZ x

/-! ### Theorem 17.0.1 -/

/-- **Theorem 17.0.1** (i)–(iii) (MT p. 422), for a positive Harris chain with invariant
probability `π`: (i) the LLN holds from every initial state for every `g ∈ L¹(π)`; and when the
chain is aperiodic and (V4) holds for `V ≥ 1` finite and a petite set (`V`-uniform ergodicity),
for every `g² ≤ V`: (ii) the series (17.3) defining `γ_g²` converges absolutely, `γ_g² ≥ 0`, and
`(1/n) E_π[Sₙ(ḡ)²] → γ_g²` (17.4); (iii) if `γ_g² = 0` then `n^{−1/2} Sₙ(ḡ) → 0` almost surely
from every initial state. -/
theorem theorem_17_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) :
    (∀ g : X → ℝ, Measurable g → Integrable g π → ∀ x, ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun n => pathSum g n ω / n) atTop (𝓝 (∫ y, g y ∂π))) ∧
    (IsAperiodic P ψ → ∀ {V : X → ℝ≥0∞}, Measurable V → (∀ x, 1 ≤ V x) → (∀ x, V x ≠ ∞) →
      ∀ {ρ b : ℝ≥0∞}, ρ < 1 → b ≠ ∞ → ∀ {C : Set X}, IsPetite P C → DriftV4 P V ρ b C →
      ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) →
        Summable (fun k : ℕ => |∫ ω, (g (ω 0) - ∫ y, g y ∂π) * (g (ω k) - ∫ y, g y ∂π)
          ∂pathMeasure P π|) ∧
        0 ≤ asymptoticVariance P π g ∧
        Tendsto (fun n : ℕ =>
          (∫ ω, pathSum (fun x => g x - ∫ y, g y ∂π) n ω ^ 2 ∂pathMeasure P π) / n) atTop
          (𝓝 (asymptoticVariance P π g)) ∧
        (asymptoticVariance P π g = 0 → ∀ x, ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n : ℕ =>
          (√(n : ℝ))⁻¹ * pathSum (fun y => g y - ∫ z, g z ∂π) n ω) atTop (𝓝 0))) := by
  refine ⟨fun g hgm hgi x => lln_of_harris hph.1 hπ hgm hgi x, ?_⟩
  intro hap V hV hV1 hVfin ρ b hρ hb C hC h g hgm hg
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := theorem_17_5_4 hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg
  have heq : asymptoticVariance P π g =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := h6.symm
  rw [heq]
  exact ⟨h5, h3, h4, h7⟩

/-- **Theorem 17.0.1** (iv), the CLT part (MT p. 422): under the hypotheses of (ii),
`n^{−1/2} Sₙ(ḡ) ⇒ N(0, γ_g²)` under every `P_x`, with `γ_g²` the series (17.3). The LIL is
`theorem_17_0_1_iv_lil_skeleton` (`SkeletonMoment`). -/
theorem theorem_17_0_1_iv {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (asymptoticVariance P π g).toNNReal) P') (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
      atTop Z (fun _ => pathKernel P x) P' := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := theorem_17_5_4 hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg
  have heq : asymptoticVariance P π g =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := h6.symm
  rw [heq] at hZ
  exact theorem_17_5_4_clt hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg hZ x

end MeynTweedie.GeneralizedDrift
