/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.HarrisLLN
import GeneralizedDrift.FNormErgodicTheorem

/-!
# Poisson's equation (MT §17.4.1, §17.4.3)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/PoissonEquation.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, pp. 443–450. For a forcing function `g` and a constant `c` (in the book
`c = π(g)`), `ĝ` solves **Poisson's equation** (17.37) if `ĝ − Pĝ = g − c`; `kernelInt P h x =
Ph(x) = ∫ P(x, dy) h(y)`.

**Definitions.** `kernelInt`, `IsPoissonSolution P g ĝ c` (with `ĝ` integrable for each `P(x, ·)`),
`poissonMart P ĝ n = Mₙ(g) = Σ_{k=1}^n [ĝ(Φₖ) − Pĝ(Φₖ₋₁)]` (17.43).

**Results.**
* **Proposition 17.4.1** (`proposition_17_4_1`, p. 443): for a positive Harris chain, two
  `π`-integrable solutions differ by a constant `π`-a.e. The book refers to Theorem 14.3.6; the
  proof here uses that the difference `h` is harmonic: `h(Φₖ)` is a stationary martingale bounded
  in `L¹(P_π)`, so it converges almost surely, the LLN identifies the limit as `π(h)`, and
  stationarity forces `h(Φ₀) = π(h)`.
* **Theorem 17.4.2** (`theorem_17_4_2`, p. 445), for aperiodic chains: under (V3) with `V` finite,
  `f ≥ 1`, `C` petite and `π(V) < ∞`, there is `R` with a solution `|ĝ| ≤ R(V + 1)` for every
  `|g| ≤ f`, namely `ĝ = Σₖ (Pᵏg − π(g))` (17.39).
* **Theorem 17.4.3** (`theorem_17_4_3`, p. 446), (17.44): `Sₙ(g − c) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)`,
  and `(Mₙ(g), 𝓕ₙ^Φ)` is a `P_π`-martingale.
* (17.46), (17.49) (`poisson_variance_eq`): `π(ĝ² − (Pĝ)²) = π(2ĝḡ − ḡ²)`, `ḡ = g − c`;
  `integral_sq_poissonMart_increment`: `E_π[(ĝ(Φₖ₊₁) − Pĝ(Φₖ))²] = π(ĝ² − (Pĝ)²)`.

**Hypotheses.** Theorem 17.4.2 is proved for aperiodic chains (the case the book proves first,
from the absolute convergence of (17.39)); the periodic case, through the resolvent `K_{a_ε}`, is
now proved in `PeriodicPoisson` (`theorem_17_4_2_periodic`). All uses in §17.5 are for ergodic,
hence aperiodic, chains.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Poisson's equation -/

/-- `Ph(x) = ∫ P(x, dy) h(y)` for a real function `h`. -/
noncomputable def kernelInt (P : Kernel X X) (h : X → ℝ) (x : X) : ℝ := ∫ y, h y ∂P x

/-- `Ph` is measurable. -/
theorem measurable_kernelInt (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ}
    (hh : Measurable h) : Measurable (kernelInt P h) :=
  (StronglyMeasurable.integral_kernel hh.stronglyMeasurable).measurable

/-- **Poisson's equation** (17.37), MT p. 443: `ĝ − Pĝ = g − c`, with `ĝ` integrable for every
`P(x, ·)`. -/
def IsPoissonSolution (P : Kernel X X) (g gh : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, Integrable gh (P x) ∧ gh x - kernelInt P gh x = g x - c

/-- `∫ π(dx) |Ph(x)| ≤ ∫ π |h|`, so `Ph ∈ L¹(π)` for invariant `π` and `h ∈ L¹(π)`. -/
theorem integrable_kernelInt (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariant P π) {h : X → ℝ} (hhm : Measurable h) (hhi : Integrable h π) :
    Integrable (kernelInt P h) π := by
  refine ⟨(measurable_kernelInt P hhm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖kernelInt P h x‖ₑ ∂π ≤ ∫⁻ x, ∫⁻ y, ‖h y‖ₑ ∂P x ∂π :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖h y‖ₑ ∂(P ∘ₘ π) := (Measure.lintegral_bind (Kernel.aemeasurable _)
        hhm.enorm.aemeasurable).symm
    _ = ∫⁻ y, ‖h y‖ₑ ∂π := by rw [hπ]
    _ < ∞ := hhi.2

/-! ### Proposition 17.4.1 -/

/-- For a harmonic `h ∈ L¹(π)` (integrable for each `P(x, ·)`), `E_μ[h(Φₖ₊₁) | 𝓕ₖ] = h(Φₖ)`. -/
theorem condExp_coord_succ_of_harmonic (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {h : X → ℝ} (hhm : Measurable h)
    (hhi : Integrable h π) (hharm : ∀ x, ∫ y, h y ∂P x = h x) (k : ℕ) :
    (pathMeasure P π)[fun ω => h (ω (k + 1)) | natFilt k] =ᵐ[pathMeasure P π]
      fun ω => h (ω k) := by
  have hlaw : (pathMeasure P π).map (fun ω => ω (k + 1)) = π := hπ.map_coord (k + 1)
  have hint : Integrable (fun ω => h ((shift k ω) 1)) (pathMeasure P π) := by
    have : Integrable h ((pathMeasure P π).map fun ω => ω (k + 1)) := by rwa [hlaw]
    exact this.comp_measurable (measurable_pi_apply (k + 1))
  have h1 := markov_property P π k (H := fun ω => h (ω 1)) (hhm.comp (measurable_pi_apply 1))
    hint
  refine h1.trans (Eventually.of_forall fun ω => ?_)
  change ∫ ω', h (ω' 1) ∂pathKernel P (ω k) = h (ω k)
  rw [integral_coord_eq P hhm (ω k) 1, pow_one]
  exact hharm (ω k)

/-- **Proposition 17.4.1** (MT p. 443): for a positive Harris chain with invariant probability
`π`, two `π`-integrable solutions of Poisson's equation differ by a constant, `π`-a.e. -/
theorem proposition_17_4_1 [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh gh' : X → ℝ} {c : ℝ}
    (h1 : IsPoissonSolution P g gh c) (h2 : IsPoissonSolution P g gh' c) (hm : Measurable gh)
    (hm' : Measurable gh') (hi : Integrable gh π) (hi' : Integrable gh' π) :
    ∃ k : ℝ, gh =ᵐ[π] fun x => k + gh' x := by
  have := isProbabilityMeasure_pathMeasure P π
  set h : X → ℝ := fun x => gh x - gh' x with hhdef
  have hhm : Measurable h := hm.sub hm'
  have hhi : Integrable h π := hi.sub hi'
  -- `h` is harmonic
  have hharm : ∀ x, ∫ y, h y ∂P x = h x := by
    intro x
    obtain ⟨ha, hb⟩ := h1 x
    obtain ⟨ha', hb'⟩ := h2 x
    rw [hhdef, integral_sub ha ha']
    simp only [kernelInt] at hb hb'
    linarith
  -- `h(Φₖ)` is a `P_π`-martingale bounded in `L¹`
  have hlaw : ∀ k, (pathMeasure P π).map (fun ω => ω k) = π := fun k => hπ.map_coord k
  have hik : ∀ k, Integrable (fun ω => h (ω k)) (pathMeasure P π) := fun k => by
    have : Integrable h ((pathMeasure P π).map fun ω => ω k) := by rw [hlaw]; exact hhi
    exact this.comp_measurable (measurable_pi_apply k)
  have hmart : Martingale (fun k ω => h (ω k)) natFilt (pathMeasure P π) :=
    martingale_nat (fun k => (hhm.comp (measurable_coord_natFilt k)).stronglyMeasurable) hik
      (fun k => (condExp_coord_succ_of_harmonic P hπ hhm hhi hharm k).symm)
  have hbdd : ∀ k, eLpNorm (fun ω => h (ω k)) 1 (pathMeasure P π) ≤
      (eLpNorm h 1 π).toNNReal := by
    intro k
    rw [ENNReal.coe_toNNReal (MemLp.eLpNorm_ne_top (memLp_one_iff_integrable.2 hhi))]
    have : eLpNorm h 1 π = eLpNorm h 1 ((pathMeasure P π).map fun ω => ω k) := by
      rw [hlaw k]
    rw [this, eLpNorm_map_measure hhm.aestronglyMeasurable
      (measurable_pi_apply k).aemeasurable]
    rfl
  have hconv := hmart.submartingale.ae_tendsto_limitProcess hbdd
  -- the LLN identifies the limit
  have hlln := lln_of_harris_measure hH hπ hhm hhi π
  have hlim : ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun k => h (ω k)) atTop
      (𝓝 (∫ y, h y ∂π)) := by
    filter_upwards [hconv, hlln] with ω h3 h4
    have h5 := (h3.comp (tendsto_add_atTop_nat 1)).cesaro
    have h6 : Tendsto (fun n : ℕ => pathSum h n ω / n) atTop
        (𝓝 (natFilt.limitProcess (fun k ω => h (ω k)) (pathMeasure P π) ω)) :=
      h5.congr fun n => by rw [pathSum, div_eq_inv_mul]; rfl
    rwa [tendsto_nhds_unique h6 h4] at h3
  -- stationarity: `π(|h − π(h)| ≥ ε) = 0`
  set m := ∫ y, h y ∂π with hmdef
  have hmeas : TendstoInMeasure (pathMeasure P π) (fun k ω => h (ω k)) atTop fun _ => m :=
    tendstoInMeasure_of_tendsto_ae
      (fun k => (hhm.comp (measurable_pi_apply k)).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_dist] at hmeas
  have hzero : ∀ ε : ℝ, 0 < ε → π {x | ε ≤ dist (h x) m} = 0 := by
    intro ε hε
    have hset : MeasurableSet {x | ε ≤ dist (h x) m} :=
      measurableSet_le measurable_const (hhm.dist measurable_const)
    have hk : ∀ k, pathMeasure P π {ω | ε ≤ dist (h (ω k)) m} = π {x | ε ≤ dist (h x) m} := by
      intro k
      rw [show π {x | ε ≤ dist (h x) m} =
          ((pathMeasure P π).map fun ω => ω k) {x | ε ≤ dist (h x) m} by rw [hlaw k],
        Measure.map_apply (measurable_pi_apply k) hset]
      rfl
    have := hmeas ε hε
    simp_rw [hk] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  refine ⟨m, ?_⟩
  have hae : ∀ᵐ x ∂π, h x = m := by
    have hall : ∀ n : ℕ, ∀ᵐ x ∂π, dist (h x) m < 1 / ((n : ℝ) + 1) := by
      intro n
      have := hzero (1 / ((n : ℝ) + 1)) (by positivity)
      rw [measure_eq_zero_iff_ae_notMem] at this
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [ae_all_iff.2 hall] with x hx
    by_contra hne
    have hpos : 0 < dist (h x) m := dist_pos.2 hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact absurd (hx n) (not_lt.2 hn.le)
  filter_upwards [hae] with x hx
  simp only [hhdef] at hx
  linarith

/-! ### Theorem 17.4.2 (aperiodic case) -/

/-- Under (V3), `Pᵏf(x) ≤ V(x) + (k + 1) b` (the Comparison Theorem 14.2.2). -/
theorem lintegral_pow_le_of_driftV3 {P : Kernel X X} [IsMarkovKernel P] {f V : X → ℝ≥0∞}
    {b : ℝ≥0∞} {C : Set X} (hf : Measurable f) (hV : Measurable V) (hC : MeasurableSet C)
    (hdrift : DriftV3 P V f b C) (x : X) (k : ℕ) :
    ∫⁻ y, f y ∂(P ^ k : Kernel X X) x ≤ V x + (k + 1) * b := by
  have hs : Measurable (C.indicator fun _ => b) := measurable_const.indicator hC
  have h := (theorem_14_2_2 P hV hf hs hdrift x).1 k
  have hle1 : ∫⁻ y, f y ∂(P ^ k : Kernel X X) x ≤
      ∑ j ∈ Finset.range (k + 1), ∫⁻ y, f y ∂(P ^ j : Kernel X X) x :=
    Finset.single_le_sum (f := fun j => ∫⁻ y, f y ∂(P ^ j : Kernel X X) x)
      (fun j _ => zero_le) (Finset.self_mem_range_succ k)
  have hle2 : ∑ j ∈ Finset.range (k + 1), ∫⁻ y, C.indicator (fun _ => b) y ∂(P ^ j : Kernel X X) x
      ≤ (k + 1) * b := by
    have := isMarkovKernel_pow P
    calc ∑ j ∈ Finset.range (k + 1), ∫⁻ y, C.indicator (fun _ => b) y ∂(P ^ j : Kernel X X) x
        ≤ ∑ _j ∈ Finset.range (k + 1), b := Finset.sum_le_sum fun j _ => by
          calc ∫⁻ y, C.indicator (fun _ => b) y ∂(P ^ j : Kernel X X) x
              ≤ ∫⁻ _y, b ∂(P ^ j : Kernel X X) x :=
                lintegral_mono fun y => indicator_le_self' (fun _ _ => zero_le) y
            _ = b := by
                have := isMarkovKernel_pow P j
                rw [lintegral_const, measure_univ, mul_one]
      _ = (k + 1) * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
  calc ∫⁻ y, f y ∂(P ^ k : Kernel X X) x ≤ _ := hle1
    _ ≤ _ := h
    _ ≤ V x + (k + 1) * b := add_le_add le_rfl hle2

/-- **Theorem 17.4.2** (MT p. 445), aperiodic case: for an aperiodic `ψ`-irreducible chain with
(V3) for an everywhere finite `V`, `f ≥ 1`, a petite `C`, and `π(V) < ∞`, there is `R < ∞` such
that for every `|g| ≤ f` Poisson's equation has the solution `ĝ = Σₖ (Pᵏg − π(g))` (17.39)
with `|ĝ| ≤ R (V + 1)`. -/
theorem theorem_17_4_2 [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (hπV : ∫⁻ x, V x ∂π ≠ ∞) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      IsPoissonSolution P g
        (fun x => ∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π)) (∫ y, g y ∂π) ∧
      Measurable (fun x => ∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π)) ∧
      ∀ x, |∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π)| ≤ R * ((V x).toReal + 1) := by
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
  -- `Pⁿf(x) < ∞`, so `g` is a test function for `Pⁿ(x, ·)` and `π`
  have hPf : ∀ n x, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hVfin x, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hb⟩)
      (lintegral_pow_le_of_driftV3 hf hV hCm hdrift x n)
  have htest : ∀ n x, IsFTest f ((P ^ n : Kernel X X) x) π g := fun n x =>
    ⟨hgm, hgf, integrable_of_ofReal_abs_le hgm hgf (hPf n x),
      integrable_of_ofReal_abs_le hgm hgf hπf⟩
  set a : ℕ → X → ℝ := fun n x => ∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂π with ha
  have habs : ∀ n x, ENNReal.ofReal |a n x| ≤ fNorm f ((P ^ n : Kernel X X) x) π :=
    fun n x => ofReal_abs_integral_sub_le_fNorm (htest n x)
  -- summability and the bound
  have hsumm : ∀ x, Summable fun n => a n x := by
    intro x
    refine Summable.of_norm ?_
    have hne : ∑' n, ENNReal.ofReal |a n x| ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
        ⟨hVfin x, ENNReal.one_ne_top⟩))
        ((ENNReal.tsum_le_tsum fun n => habs n x).trans (hBbd x))
    refine (ENNReal.summable_toReal hne).congr fun n => ?_
    rw [ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  have hbound : ∀ x, ∑' n, ENNReal.ofReal |a n x| ≤ B * (V x + 1) := fun x =>
    (ENNReal.tsum_le_tsum fun n => habs n x).trans (hBbd x)
  have hbound' : ∀ x, |∑' n, a n x| ≤ B.toReal * ((V x).toReal + 1) := by
    intro x
    have h1 : |∑' n, a n x| ≤ ∑' n, |a n x| := by
      have := norm_tsum_le_tsum_norm (hsumm x).norm
      simpa [Real.norm_eq_abs] using this
    have h2 : ∑' n, |a n x| = (∑' n, ENNReal.ofReal |a n x|).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
      simp_rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    rw [h2] at h1
    refine h1.trans ?_
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
      ⟨hVfin x, ENNReal.one_ne_top⟩)) (hbound x)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add (hVfin x) ENNReal.one_ne_top,
      ENNReal.toReal_one] at h3
  -- measurability
  have ham : ∀ n, Measurable (a n) := fun n => by
    have := isMarkovKernel_pow P n
    exact ((StronglyMeasurable.integral_kernel hgm.stronglyMeasurable).measurable).sub
      measurable_const
  have hghm : Measurable fun x => ∑' n, a n x := by
    refine measurable_of_tendsto_metrizable (f := fun N x => ∑ n ∈ Finset.range N, a n x)
      (fun N => Finset.measurable_sum _ fun n _ => ham n) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact (hsumm x).hasSum.tendsto_sum_nat
  -- each term is bounded by `B (V + 1)`
  have habs1 : ∀ n y, |a n y| ≤ B.toReal * ((V y).toReal + 1) := by
    intro n y
    have h1 : ENNReal.ofReal |a n y| ≤ B * (V y + 1) :=
      (ENNReal.le_tsum n).trans (hbound y)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
      ⟨hVfin y, ENNReal.one_ne_top⟩)) h1
    rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_add (hVfin y) ENNReal.one_ne_top, ENNReal.toReal_one] at h2
  refine ⟨fun x => ?_, hghm, hbound'⟩
  have hPV : ∫⁻ y, V y ∂P x ≠ ∞ := by
    have h := hdrift x
    have hrhs : V x + C.indicator (fun _ => b) x ≠ ∞ := ENNReal.add_ne_top.2 ⟨hVfin x, by
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx]; exact hb
      · rw [indicator_of_notMem hx]; exact ENNReal.zero_ne_top⟩
    exact ne_top_of_le_ne_top hrhs (le_trans le_self_add h)
  have hdom : Integrable (fun y => B.toReal * ((V y).toReal + 1)) (P x) :=
    ((integrable_toReal_of_lintegral_ne_top hV.aemeasurable hPV).add
      (integrable_const 1)).const_mul _
  have hai : ∀ n, Integrable (a n) (P x) := fun n =>
    hdom.mono' (ham n).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact habs1 n y)
  have hint : Integrable (fun y => ∑' n, a n y) (P x) :=
    hdom.mono' hghm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hbound' y)
  refine ⟨hint, ?_⟩
  -- `∫ ĝ dP(x) = Σₙ a (n + 1) x`
  have hstep : ∀ n, ∫ y, a n y ∂P x = a (n + 1) x := by
    intro n
    have := isMarkovKernel_pow P n
    have hi1 : Integrable (fun y => ∫ z, g z ∂(P ^ n : Kernel X X) y) (P x) :=
      ((hai n).add (integrable_const (∫ y, g y ∂π))).congr
        (Eventually.of_forall fun y => by simp [ha])
    rw [ha]
    simp only
    rw [integral_sub hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    congr 1
    rw [pow_succ]
    change _ = ∫ z, g z ∂((P ^ n : Kernel X X) ∘ₖ P) x
    rw [Kernel.integral_comp]
    have := (htest (n + 1) x).2.2.1
    rw [pow_succ] at this
    exact this
  have htsum : ∫ y, ∑' n, a n y ∂P x = ∑' n, a (n + 1) x := by
    rw [MeasureTheory.integral_tsum (fun n => (ham n).aestronglyMeasurable)]
    · simp_rw [hstep]
    · rw [← lintegral_tsum fun n => (ham n).enorm.aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
        ⟨hPV, ENNReal.one_ne_top⟩)) ?_
      calc ∫⁻ y, ∑' n, ‖a n y‖ₑ ∂P x ≤ ∫⁻ y, B * (V y + 1) ∂P x := by
            refine lintegral_mono fun y => ?_
            simp_rw [Real.enorm_eq_ofReal_abs]
            exact hbound y
        _ = B * (∫⁻ y, V y ∂P x + 1) := by
            rw [lintegral_const_mul B (f := fun y => V y + 1) (hV.add measurable_const),
              lintegral_add_right (fun y => V y) measurable_const, lintegral_const,
              measure_univ, mul_one]
  have ha0 : a 0 x = g x - ∫ y, g y ∂π := by
    rw [ha]
    simp only
    rw [pow_zero_apply, integral_dirac' _ _ hgm.stronglyMeasurable]
  change (∑' n, a n x) - ∫ y, (∑' n, a n y) ∂P x = g x - ∫ y, g y ∂π
  rw [htsum, (hsumm x).tsum_eq_zero_add, ha0]
  ring

/-! ### Theorem 17.4.3: the martingale decomposition -/

/-- The martingale (17.43): `Mₙ(g) = Σ_{k=1}^n [ĝ(Φₖ) − Pĝ(Φₖ₋₁)]`. -/
noncomputable def poissonMart (P : Kernel X X) (gh : X → ℝ) (n : ℕ) (ω : ℕ → X) : ℝ :=
  ∑ k ∈ Finset.range n, (gh (ω (k + 1)) - kernelInt P gh (ω k))

/-- (17.44), pathwise: `Sₙ(g − c) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)`. -/
theorem pathSum_eq_poissonMart {P : Kernel X X} {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (n : ℕ) (ω : ℕ → X) :
    pathSum (fun x => g x - c) n ω =
      poissonMart P gh n ω + kernelInt P gh (ω 0) - kernelInt P gh (ω n) := by
  have hterm : ∀ k, g (ω (k + 1)) - c = (gh (ω (k + 1)) - kernelInt P gh (ω k)) +
      (kernelInt P gh (ω k) - kernelInt P gh (ω (k + 1))) := fun k => by
    have := (hsol (ω (k + 1))).2; linarith
  rw [pathSum, poissonMart]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun k => kernelInt P gh (ω k))]
  ring

/-- Under `P_π`, `ĝ(Φₖ₊₁) − Pĝ(Φₖ)` has conditional mean zero given `𝓕ₖ^Φ`. -/
theorem condExp_poisson_increment (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {gh : X → ℝ} (hghm : Measurable gh)
    (hghi : Integrable gh π) (k : ℕ) :
    (pathMeasure P π)[fun ω => gh (ω (k + 1)) | natFilt k] =ᵐ[pathMeasure P π]
      fun ω => kernelInt P gh (ω k) := by
  have hlaw : (pathMeasure P π).map (fun ω => ω (k + 1)) = π := hπ.map_coord (k + 1)
  have hint : Integrable (fun ω => gh ((shift k ω) 1)) (pathMeasure P π) := by
    have : Integrable gh ((pathMeasure P π).map fun ω => ω (k + 1)) := by rwa [hlaw]
    exact this.comp_measurable (measurable_pi_apply (k + 1))
  have h1 := markov_property P π k (H := fun ω => gh (ω 1)) (hghm.comp (measurable_pi_apply 1))
    hint
  refine h1.trans (Eventually.of_forall fun ω => ?_)
  change ∫ ω', gh (ω' 1) ∂pathKernel P (ω k) = kernelInt P gh (ω k)
  rw [integral_coord_eq P hghm (ω k) 1, pow_one]
  rfl

/-- Integrability of `h(Φₖ)` under `P_π` for `h ∈ L¹(π)`. -/
theorem integrable_coord_of_invariant (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {h : X → ℝ} (hhi : Integrable h π)
    (k : ℕ) : Integrable (fun ω => h (ω k)) (pathMeasure P π) := by
  have : Integrable h ((pathMeasure P π).map fun ω => ω k) := by rw [hπ.map_coord k]; exact hhi
  exact this.comp_measurable (measurable_pi_apply k)

/-- **Theorem 17.4.3** (MT p. 446): if `π` is an invariant probability and `ĝ ∈ L¹(π)` solves
Poisson's equation, then `Sₙ(g − c) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)` and `(Mₙ(g), 𝓕ₙ^Φ)` is a
`P_π`-martingale. -/
theorem theorem_17_4_3 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hghi : Integrable gh π) :
    (∀ n ω, pathSum (fun x => g x - c) n ω =
      poissonMart P gh n ω + kernelInt P gh (ω 0) - kernelInt P gh (ω n)) ∧
      Martingale (poissonMart P gh) natFilt (pathMeasure P π) := by
  have := isProbabilityMeasure_pathMeasure P π
  refine ⟨pathSum_eq_poissonMart hsol, ?_⟩
  have hPm := measurable_kernelInt P hghm
  have hPi := integrable_kernelInt P hπ hghm hghi
  have hinc : ∀ k, Integrable (fun ω => gh (ω (k + 1)) - kernelInt P gh (ω k))
      (pathMeasure P π) := fun k =>
    (integrable_coord_of_invariant P hπ hghi (k + 1)).sub
      (integrable_coord_of_invariant P hπ hPi k)
  have hadapt : ∀ n, StronglyMeasurable[natFilt n] (poissonMart P gh n) := by
    intro n
    refine (Finset.measurable_sum _ fun k hk => ?_).stronglyMeasurable
    have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
    exact ((hghm.comp (measurable_coord_natFilt (k + 1))).mono ((natFilt (X := X)).mono hk')
      le_rfl).sub ((hPm.comp (measurable_coord_natFilt k)).mono
        ((natFilt (X := X)).mono (by omega)) le_rfl)
  have hint : ∀ n, Integrable (poissonMart P gh n) (pathMeasure P π) := fun n =>
    integrable_finsetSum _ fun k _ => hinc k
  refine martingale_nat hadapt hint fun n => ?_
  -- `E[M_{n+1} | 𝓕ₙ] = Mₙ`
  have hsplit : poissonMart P gh (n + 1) = fun ω => poissonMart P gh n ω +
      (gh (ω (n + 1)) - kernelInt P gh (ω n)) := by
    ext ω; rw [poissonMart, poissonMart, Finset.sum_range_succ]
  rw [hsplit]
  have h1 : (pathMeasure P π)[fun ω => poissonMart P gh n ω +
      (gh (ω (n + 1)) - kernelInt P gh (ω n)) | natFilt n] =ᵐ[pathMeasure P π]
      (pathMeasure P π)[poissonMart P gh n | natFilt n] +
        (pathMeasure P π)[fun ω => gh (ω (n + 1)) - kernelInt P gh (ω n) | natFilt n] :=
    condExp_add (hint n) (hinc n) _
  have h2 : (pathMeasure P π)[poissonMart P gh n | natFilt n] = poissonMart P gh n :=
    condExp_of_stronglyMeasurable ((natFilt (X := X)).le n) (hadapt n) (hint n)
  have h3 : (pathMeasure P π)[fun ω => gh (ω (n + 1)) - kernelInt P gh (ω n) | natFilt n]
      =ᵐ[pathMeasure P π] (pathMeasure P π)[fun ω => gh (ω (n + 1)) | natFilt n] -
        (pathMeasure P π)[fun ω => kernelInt P gh (ω n) | natFilt n] :=
    condExp_sub (integrable_coord_of_invariant P hπ hghi (n + 1))
      (integrable_coord_of_invariant P hπ hPi n) _
  have h4 : (pathMeasure P π)[fun ω => kernelInt P gh (ω n) | natFilt n] =
      fun ω => kernelInt P gh (ω n) :=
    condExp_of_stronglyMeasurable ((natFilt (X := X)).le n)
      (hPm.comp (measurable_coord_natFilt n)).stronglyMeasurable
      (integrable_coord_of_invariant P hπ hPi n)
  have h5 := condExp_poisson_increment P hπ hghm hghi n
  filter_upwards [h1, h3, h5] with ω e1 e3 e5
  rw [e1, Pi.add_apply, h2, e3, Pi.sub_apply, h4, e5, sub_self, add_zero]

/-! ### The variance identities (17.46), (17.49) -/

/-- (17.49): `π(ĝ² − (Pĝ)²) = π(2ĝḡ − ḡ²)` for `ḡ = g − c`, when `ĝ, ḡ ∈ L²(π)`. -/
theorem poisson_variance_eq {P : Kernel X X} {π : Measure X} {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) :
    ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π =
      ∫ x, (2 * gh x * (g x - c) - (g x - c) ^ 2) ∂π := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h := (hsol x).2
  have : kernelInt P gh x = gh x - (g x - c) := by linarith
  simp only [this]
  ring

/-- `E_π[(ĝ(Φₖ₊₁) − Pĝ(Φₖ))²] = π(ĝ² − (Pĝ)²)` for `ĝ, Pĝ ∈ L²(π)`. -/
theorem integral_sq_poissonMart_increment (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {gh : X → ℝ} (hghm : Measurable gh)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π) (k : ℕ) :
    ∫ ω, (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2 ∂pathMeasure P π =
      ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  have hlaw : ∀ j, (pathMeasure P π).map (fun ω => ω j) = π := fun j => hπ.map_coord j
  have hL2 : ∀ (h : X → ℝ), Measurable h → MemLp h 2 π → ∀ j,
      MemLp (fun ω => h (ω j)) 2 (pathMeasure P π) := fun h hm h2 j => by
    have : MemLp h 2 ((pathMeasure P π).map fun ω => ω j) := by rw [hlaw j]; exact h2
    exact this.comp_of_map (measurable_pi_apply j).aemeasurable
  have hA := hL2 gh hghm hgh2 (k + 1)
  have hB := hL2 _ hPm hPgh2 k
  have hint_sq : ∀ (h : X → ℝ), Measurable h → MemLp h 2 π → ∀ j,
      ∫ ω, h (ω j) ^ 2 ∂pathMeasure P π = ∫ x, h x ^ 2 ∂π := fun h hm h2 j => by
    rw [show ∫ x, h x ^ 2 ∂π = ∫ x, h x ^ 2 ∂((pathMeasure P π).map fun ω => ω j) by
      rw [hlaw j], integral_map (measurable_pi_apply j).aemeasurable
        (hm.pow_const 2).aestronglyMeasurable]
  -- the cross term: `E[ĝ(Φₖ₊₁) Pĝ(Φₖ)] = π((Pĝ)²)`
  have hcross : ∫ ω, kernelInt P gh (ω k) * gh (ω (k + 1)) ∂pathMeasure P π =
      ∫ x, kernelInt P gh x ^ 2 ∂π := by
    have hFm : StronglyMeasurable[natFilt k] fun ω => kernelInt P gh (ω k) :=
      (hPm.comp (measurable_coord_natFilt k)).stronglyMeasurable
    have hprod := hB.integrable_mul hA
    have h1 : (pathMeasure P π)[fun ω => kernelInt P gh (ω k) * gh (ω (k + 1)) | natFilt k]
        =ᵐ[pathMeasure P π] fun ω => kernelInt P gh (ω k) *
          (pathMeasure P π)[fun ω => gh (ω (k + 1)) | natFilt k] ω :=
      condExp_mul_of_stronglyMeasurable_left hFm hprod (hA.integrable one_le_two)
    have h2 := condExp_poisson_increment P hπ hghm (hgh2.integrable one_le_two) k
    rw [← integral_condExp ((natFilt (X := X)).le k), ← hint_sq _ hPm hPgh2 k]
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]; ring
  have hexp : (fun ω : ℕ → X => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2) = fun ω =>
      gh (ω (k + 1)) ^ 2 - 2 * (kernelInt P gh (ω k) * gh (ω (k + 1))) +
        kernelInt P gh (ω k) ^ 2 := by
    ext ω; ring
  have i1 : Integrable (fun ω => gh (ω (k + 1)) ^ 2) (pathMeasure P π) := hA.integrable_sq
  have i2 : Integrable (fun ω => 2 * (kernelInt P gh (ω k) * gh (ω (k + 1))))
      (pathMeasure P π) := (hB.integrable_mul hA).const_mul 2
  have i3 : Integrable (fun ω => kernelInt P gh (ω k) ^ 2) (pathMeasure P π) := hB.integrable_sq
  have e1 := integral_add (i1.sub i2) i3
  have e2 := integral_sub i1 i2
  simp only [Pi.sub_apply] at e1 e2
  rw [hexp, e1, e2, integral_const_mul, hcross, hint_sq gh hghm hgh2, hint_sq _ hPm hPgh2,
    integral_sub hgh2.integrable_sq hPgh2.integrable_sq]
  ring

end MeynTweedie.GeneralizedDrift
