/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.HarrisDecomposition
import Ergodicity.ModelRandomWalk
import Ergodicity.ModelLinearModels
import Ergodicity.NonEvanescence
import Ergodicity.RandomWalkHalfLine
import Ergodicity.DriftHarris
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# Stochastic comparison and transience of random walks (MT §9.1.1, §9.5)

Meyn and Tweedie, Proposition 9.1.2 (p. 202) and §9.5, pp. 218–227.

**The path law of a random recursion.**
* `pathKernel_recursion`: for the recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` driven by i.i.d. `Wₙ ∼ Γ`, the
  law of the whole sample path `(orbit F x ω)ₙ` under `Γ^{⊗ℕ}` is `P_x`: the recursion realizes
  the chain on path space (Theorem 3.4.1 with Mathlib's independence of the coordinates of
  `Measure.infinitePi`).
* `ae_tendsto_partialSum`: the strong law of large numbers for `Σ_{i ≤ n} c(Wᵢ)`
  (`ProbabilityTheory.strong_law_ae`).
* `harrisQ_recursion`: `Q(x, A) = Γ^{⊗ℕ}{ω : orbit F x ω ∈ A i.o.}`.

**Results.**
* **Proposition 9.1.2** (`proposition_9_1_2`, p. 202): a random walk on `ℤ` whose increment has
  mean `β ≠ 0` has every state transient (`Q(x, {x}) = 0`, `U(x, {x}) < ∞`);
  `proposition_9_1_2_chain`: if it is irreducible, it is a transient chain.
* `isTransientChain_of_harrisQ_lt_one`: a `ψ`-irreducible chain with a set `A ∈ B⁺(X)` such that
  `Q(x, A) < 1` for every `x` is transient (Theorems 9.1.5 and 8.3.4).
* **The stochastic comparison principle** (9.44), p. 219: if `P_x(τ_C ≥ n) ≤ P'_x(τ_C ≥ n)`,
  then `L'(x, C) ≤ L(x, C)` (`hitProb_le_of_comparison`); `comparison_harris`: if `Φ'` reaches
  `C` almost surely from `Cᶜ` and `C` is petite for `Φ`, then `Φ` is Harris;
  `comparison_transient`: if `L(x, C) < 1` on `D ⊆ Cᶜ` with `C, D ∈ B⁺(X)` for `Φ'`, then `Φ'`
  is transient.
* **Proposition 9.5.1** (`proposition_9_5_1`, p. 219): random walk on `ℝ₊` with `β > 0` visits
  every bounded set finitely often from every starting point; if it is `ψ`-irreducible it is
  transient.
* **Proposition 9.5.2** (`proposition_9_5_2`, p. 220): for the scalar linear model with bounded
  mean-zero noise which is a `ψ`-irreducible T-chain, Harris recurrence holds iff `|α| ≤ 1`;
  `proposition_9_5_2_necessity` (Harris forces `|α| ≤ 1`, for bounded noise, with no further
  hypothesis) and `proposition_9_5_2_sufficiency` (mean zero, finite variance).
* **Proposition 9.5.3** (`proposition_9_5_3`, p. 221): an irreducible random walk on `ℝ` with
  non-zero mean is transient; `randomWalk_real_evanescent`: indeed `P_x{Φ → ∞} = 1`.
* **Theorem 9.5.5** (p. 225), for a chain on `ℝ₊` with bounded increments (9.58), mean drift
  `m(x)` (`meanDrift`) and second moment `v(x)` (`incrementVar`): (i) `theorem_9_5_5_i`,
  `m(x) ≤ θ v(x)/2x` with `θ < 1` gives Harris recurrence (test function `log(1 + x)`);
  (ii) `theorem_9_5_5_ii`, `m(x) ≥ θ v(x)/2x` with `θ > 1` gives transience (test function
  `1 − (1 + x)^{−α}`). The Taylor expansions (9.63), (9.67) are `integral_log_le` and
  `integral_rpow_neg_le`, from the second-order bound `le_quadratic_of_deriv2_le`.

**Hypotheses.** In Theorem 9.5.5 the book's informal standing assumption ("enough weight on the
negative half line to make the chain a `δ₀`-irreducible T-chain with `v` bounded from zero") is
replaced by what the proofs use: (i) the sets `[0, c]` are petite; (ii) every tail `(c, ∞)` is
in `B⁺(X)`. In Proposition 9.5.2 the irreducibility and T-chain property, asserted by the book,
are hypotheses (see the correction below).

**Corrections.**
* Proposition 9.1.2 holds for every `β ≠ 0` (the book states `β > 0`; the proof uses only
  `β ≠ 0`). The proofs of Propositions 9.1.2, 9.5.1 and 9.5.3 here all use the strong law of
  large numbers on the path: the book's discretisation argument for Proposition 9.5.1 (with
  the unproved claim that the discretised walk is stochastically smaller) is replaced by the
  pathwise bound `Φₙ ≥ x + W₁ + ⋯ + Wₙ` (Lindley's representation).
* Proposition 9.5.1: random walk on `ℝ₊` with `β > 0` need not be `ψ`-irreducible (if
  `Γ(−∞, 0] = 0` the walk only moves up), so "transient" in the sense of §8 needs
  `ψ`-irreducibility as a hypothesis; the pathwise conclusion holds without it.
* Proposition 9.5.2: the proof's claim that the model with noise supported on `[−R, R]` is
  `μ^Leb`-irreducible on `ℝ` is false for `|α| < 1` (`proposition_9_5_2_not_leb_irreducible`:
  the path from `0` stays in `[−R/(1 − |α|), R/(1 − |α|)]`) and also for `|α| > 1` (far from
  `0` the path moves monotonically away). The book's comparison arguments for `|α| ≤ 1` are
  replaced by the drift `log(1 + |x|)` and Theorem 9.4.1.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The path law of a random recursion -/

variable {W : Type*} [MeasurableSpace W] in
/-- **The recursion realizes the chain on path space**: driven by i.i.d. `Wₙ ∼ Γ`, the sample path
`(orbit F x ω)ₙ` has law `P_x` for the kernel `P(x, A) = Γ{w : F(x, w) ∈ A}`. -/
theorem pathKernel_recursion (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : Measurable F) (x : X) :
    haveI := isMarkovKernel_recursionKernel Γ hF
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun ω n => orbit F x ω n) =
      pathKernel (recursionKernel Γ F) x := by
  have := isMarkovKernel_recursionKernel Γ hF
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  -- `Φₙ` as a function of `(W₀, …, Wₙ)`
  set h : (n : ℕ) → (Π _ : Finset.Iic n, W) → X := fun n r =>
    controlMap F n x (fun i : Fin n => r ⟨i + 1, Finset.mem_Iic.2 (by omega)⟩)
  have hh : ∀ n, Measurable (h n) := fun n =>
    (measurable_controlMap_right hF n x).comp (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  have horbit : ∀ n ω, orbit F x ω n = h n (Preorder.frestrictLe n ω) := fun n ω => by
    rw [orbit_eq_controlMap]; rfl
  have hR : ∀ n, Measurable[natFilt (X := W) n] (Preorder.frestrictLe (π := fun _ : ℕ => W) n) := by
    intro n
    rw [natFilt, Filtration.piLE_eq_comap_frestrictLe]
    exact Measurable.of_comap_le le_rfl
  have hΨ : ∀ n, Measurable[natFilt (X := W) n] fun ω => orbit F x ω n := fun n => by
    simp_rw [horbit n]
    exact (hh n).comp (hR n)
  have h0 : μ.map (fun ω => orbit F x ω 0) = Measure.dirac x := by
    simp only [orbit_zero]
    rw [Measure.map_const, measure_univ, one_smul]
  -- independence of the past and the next increment
  have hiid : iIndepFun (fun i (ω : ℕ → W) => ω i) μ :=
    iIndepFun_infinitePi (P := fun _ => Γ) (X := fun _ w => w) fun _ => measurable_id
  have hstep : ∀ n (G : Set (ℕ → W)), MeasurableSet[natFilt n] G → ∀ f : X → ℝ≥0∞,
      Measurable f → ∫⁻ ω in G, f (orbit F x ω (n + 1)) ∂μ =
        ∫⁻ ω in G, ∫⁻ y, f y ∂recursionKernel Γ F (orbit F x ω n) ∂μ := by
    intro n G hG f hf
    have hG' := hG
    rw [natFilt, Filtration.piLE_eq_comap_frestrictLe] at hG'
    obtain ⟨T, hT, rfl⟩ := hG'
    set R := Preorder.frestrictLe (π := fun _ : ℕ => W) n
    have hRm : Measurable R := Preorder.measurable_frestrictLe n
    have hev : Measurable fun ω : ℕ → W => ω (n + 1) := measurable_pi_apply _
    have hST : Disjoint (Finset.Iic n) {n + 1} :=
      Finset.disjoint_singleton_right.2 (by simp)
    have hind0 := hiid.indepFun_finset (Finset.Iic n) {n + 1} hST fun i => measurable_pi_apply i
    have hind : IndepFun R (fun ω : ℕ → W => ω (n + 1)) μ := by
      have := hind0.comp measurable_id (measurable_pi_apply
        (⟨n + 1, Finset.mem_singleton_self _⟩ : ({n + 1} : Finset ℕ)))
      exact this
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map hRm.aemeasurable hev.aemeasurable).1 hind
    rw [Measure.infinitePi_map_eval] at hprod
    set φ : (Π _ : Finset.Iic n, W) × W → ℝ≥0∞ :=
      (T ×ˢ univ).indicator fun p => f (F (h n p.1, p.2))
    have hφ : Measurable φ :=
      (hf.comp (hF.comp (((hh n).comp measurable_fst).prodMk measurable_snd))).indicator
        (hT.prod MeasurableSet.univ)
    have hk : ∀ z, ∫⁻ y, f y ∂recursionKernel Γ F z = ∫⁻ w, f (F (z, w)) ∂Γ := fun z => by
      have hm : Measurable fun w => F (z, w) := hF.comp measurable_prodMk_left
      rw [recursionKernel_apply Γ hF z, lintegral_map hf hm]
    have hpre : MeasurableSet (R ⁻¹' T) := hRm hT
    calc ∫⁻ ω in R ⁻¹' T, f (orbit F x ω (n + 1)) ∂μ
        = ∫⁻ ω, φ (R ω, ω (n + 1)) ∂μ := by
          rw [← lintegral_indicator hpre]
          refine lintegral_congr fun ω => ?_
          by_cases hω : R ω ∈ T
          · rw [indicator_of_mem (show ω ∈ R ⁻¹' T from hω)]
            simp only [φ]
            rw [indicator_of_mem (show (R ω, ω (n + 1)) ∈ T ×ˢ univ from ⟨hω, trivial⟩),
              orbit_succ, horbit]
          · rw [indicator_of_notMem (show ω ∉ R ⁻¹' T from hω)]
            simp only [φ]
            rw [indicator_of_notMem (show (R ω, ω (n + 1)) ∉ T ×ˢ univ from fun h => hω h.1)]
      _ = ∫⁻ p, φ p ∂(μ.map fun ω => (R ω, ω (n + 1))) :=
          (lintegral_map hφ (hRm.prodMk hev)).symm
      _ = ∫⁻ r, ∫⁻ w, φ (r, w) ∂Γ ∂(μ.map R) := by rw [hprod, lintegral_prod _ hφ.aemeasurable]
      _ = ∫⁻ r, T.indicator (fun r => ∫⁻ w, f (F (h n r, w)) ∂Γ) r ∂(μ.map R) := by
          refine lintegral_congr fun r => ?_
          by_cases hr : r ∈ T
          · simp [φ, hr]
          · simp [φ, hr]
      _ = ∫⁻ ω, T.indicator (fun r => ∫⁻ w, f (F (h n r, w)) ∂Γ) (R ω) ∂μ := by
          refine lintegral_map ?_ hRm
          exact (Measurable.lintegral_prod_right' (f := fun p : (Π _ : Finset.Iic n, W) × W =>
            f (F (h n p.1, p.2))) (hf.comp (hF.comp (((hh n).comp measurable_fst).prodMk
              measurable_snd)))).indicator hT
      _ = ∫⁻ ω in R ⁻¹' T, ∫⁻ y, f y ∂recursionKernel Γ F (orbit F x ω n) ∂μ := by
          rw [← lintegral_indicator hpre]
          refine lintegral_congr fun ω => ?_
          by_cases hω : R ω ∈ T
          · rw [indicator_of_mem (show ω ∈ R ⁻¹' T from hω), indicator_of_mem hω, hk, horbit]
          · rw [indicator_of_notMem (show ω ∉ R ⁻¹' T from hω), indicator_of_notMem hω]
  have hmc := isMarkovChain_of_step (recursionKernel Γ F) (Measure.dirac x) hΨ h0 hstep
  have h := law_eq_pathMeasure (recursionKernel Γ F) (Measure.dirac x) hmc
  rw [pathMeasure_dirac] at h
  exact h

variable {W : Type*} [MeasurableSpace W] in
/-- `Q(x, A) = Γ^{⊗ℕ}{ω : the orbit from x is in A infinitely often}`. -/
theorem harrisQ_recursion (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : Measurable F) (x : X) {A : Set X} (hA : MeasurableSet A) :
    haveI := isMarkovKernel_recursionKernel Γ hF
    harrisQ (recursionKernel Γ F) A x =
      (Measure.infinitePi fun _ : ℕ => Γ) {ω | (fun n => orbit F x ω n) ∈ ioSet A} := by
  have := isMarkovKernel_recursionKernel Γ hF
  have hmeas : Measurable fun (ω : ℕ → W) (n : ℕ) => orbit F x ω n :=
    measurable_pi_iff.2 fun n => by
      simp_rw [orbit_eq_controlMap]
      exact (measurable_controlMap_right hF n x).comp
        (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  rw [harrisQ, ← pathKernel_recursion Γ hF x, Measure.map_apply hmeas (measurableSet_ioSet hA)]
  rfl

/-! ### The strong law along the path -/

variable {W : Type*} [MeasurableSpace W] in
/-- **The strong law of large numbers** for `c(W₁) + ⋯ + c(Wₙ)` under `Γ^{⊗ℕ}`. -/
theorem ae_tendsto_partialSum (Γ : Measure W) [IsProbabilityMeasure Γ] {c : W → ℝ}
    (hc : Measurable c) (hint : Integrable c Γ) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, c (ω (i + 1))) / n) atTop
        (𝓝 (∫ w, c w ∂Γ)) := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  set Y : ℕ → (ℕ → W) → ℝ := fun i ω => c (ω i)
  set Z : ℕ → (ℕ → W) → ℝ := fun i ω => Y (i + 1) ω
  have hYm : ∀ i, Measurable (Y i) := fun i => hc.comp (measurable_pi_apply i)
  have hind : iIndepFun Y μ := iIndepFun_infinitePi (P := fun _ => Γ) (X := fun _ => c) fun _ => hc
  have hmap : ∀ i, μ.map (Y i) = Γ.map c := fun i => by
    change μ.map (c ∘ fun ω => ω i) = _
    rw [← Measure.map_map hc (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := fun i =>
    ⟨(hYm _).aemeasurable, (hYm _).aemeasurable, by rw [hmap, hmap]⟩
  have hZ0 : Integrable (Z 0) μ := by
    have h1 : Integrable c (μ.map fun ω => ω 1) := by rw [Measure.infinitePi_map_eval]; exact hint
    exact (integrable_map_measure hc.aestronglyMeasurable
      (measurable_pi_apply 1).aemeasurable).1 h1
  have hE : ∫ ω, Z 0 ω ∂μ = ∫ w, c w ∂Γ := by
    change ∫ ω, c (ω 1) ∂μ = _
    rw [← integral_map (measurable_pi_apply 1).aemeasurable hc.aestronglyMeasurable,
      Measure.infinitePi_map_eval]
  have hslln := strong_law_ae Z hZ0 (fun i j hij => hind.indepFun (by omega)) hident
  rw [hE] at hslln
  filter_upwards [hslln] with ω hω
  refine hω.congr fun n => ?_
  simp only [smul_eq_mul, Z, Y]
  rw [div_eq_inv_mul]

/-- If `aₙ/n → β ≠ 0`, then `|aₙ| ≤ R` holds for only finitely many `n`. -/
theorem eventually_abs_gt_of_tendsto_div {a : ℕ → ℝ} {β : ℝ} (hβ : β ≠ 0)
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 β)) (R : ℝ) :
    ∀ᶠ n in atTop, R < |a n| := by
  have h1 : ∀ᶠ n : ℕ in atTop, |β| / 2 < |a n / n| :=
    (continuous_abs.tendsto β |>.comp h).eventually (lt_mem_nhds (half_lt_self (abs_pos.2 hβ)))
  have h2 : ∀ᶠ n : ℕ in atTop, 2 * (|R| + 1) / |β| < n :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [abs_div, abs_of_pos hnpos, lt_div_iff₀ hnpos] at hn1
  have hβpos : 0 < |β| := abs_pos.2 hβ
  rw [div_lt_iff₀ hβpos] at hn2
  nlinarith [abs_nonneg R, le_abs_self R]

/-! ### Proposition 9.1.2: random walk on `ℤ` -/

/-- `Q(x, {y}) = 0` for random walk on `ℤ` with non-zero mean: by the strong law,
`|Φₙ| → ∞` almost surely. -/
theorem randomWalk_int_harrisQ_eq_zero (Γ : Measure ℤ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) Γ)
    (hβ : ∫ z, (z : ℝ) ∂Γ ≠ 0) (x y : ℤ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    harrisQ (randomWalkKernel Γ) {y} x = 0 := by
  have := isMarkovKernel_randomWalkKernel Γ
  have : IsMarkovKernel (recursionKernel Γ fun p : ℤ × ℤ => p.1 + p.2) :=
    isMarkovKernel_recursionKernel Γ (measurable_add_step (G := ℤ))
  change harrisQ (recursionKernel Γ fun p : ℤ × ℤ => p.1 + p.2) {y} x = 0
  rw [harrisQ_recursion Γ (measurable_add_step (G := ℤ)) x
    (measurableSet_singleton y), measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_tendsto_partialSum Γ (c := fun z : ℤ => (z : ℝ)) (measurable_of_countable _)
    hint] with ω hω hio
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_abs_gt_of_tendsto_div hβ hω |(y : ℝ) - x|)
  obtain ⟨n, hn, hny⟩ := hio N
  simp only [mem_singleton_iff, orbit_randomWalk] at hny
  have : (∑ i ∈ Finset.range n, (ω (i + 1) : ℝ)) = (y : ℝ) - x := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hny
    push_cast at this
    linarith
  have h := hN n hn
  rw [this] at h
  exact lt_irrefl _ h

/-- **Proposition 9.1.2** (MT p. 202): for random walk on `ℤ` whose increment has a finite mean
`β ≠ 0`, every state is transient: `Q(x, {x}) = 0`, hence `L(x, {x}) < 1` and
`U(x, {x}) < ∞`. -/
theorem proposition_9_1_2 (Γ : Measure ℤ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) Γ)
    (hβ : ∫ z, (z : ℝ) ∂Γ ≠ 0) (x : ℤ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    harrisQ (randomWalkKernel Γ) {x} x = 0 ∧ hitProb (randomWalkKernel Γ) {x} x < 1 ∧
      IsTransientState (randomWalkKernel Γ) x := by
  have := isMarkovKernel_randomWalkKernel Γ
  set P := randomWalkKernel Γ
  have hQ := randomWalk_int_harrisQ_eq_zero Γ hint hβ x x
  have hL : hitProb P {x} x < 1 := by
    refine lt_of_le_of_ne (hitProb_le_one P {x} x) fun h1 => ?_
    have := (proposition_9_1_1 P (measurableSet_singleton x) fun y hy => by
      rw [mem_singleton_iff.1 hy]; exact h1).2 x rfl
    rw [hQ] at this
    exact zero_ne_one this
  refine ⟨hQ, hL, ?_⟩
  have hb := proposition_8_3_1_iii P (measurableSet_singleton x) hL
    (fun y hy => by rw [mem_singleton_iff.1 hy]) x
  exact ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hL).ne') hb

/-- **Proposition 9.1.2**, chain form: an irreducible random walk on `ℤ` with non-zero mean is a
transient chain. -/
theorem proposition_9_1_2_chain (Γ : Measure ℤ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) Γ)
    (hβ : ∫ z, (z : ℝ) ∂Γ ≠ 0)
    (hirr : haveI := isMarkovKernel_randomWalkKernel Γ; IsIrreducibleChain (randomWalkKernel Γ)) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    IsTransientChain (randomWalkKernel Γ) Measure.count := by
  have := isMarkovKernel_randomWalkKernel Γ
  exact (isTransientChain_count_iff _ hirr).2 fun x => (proposition_9_1_2 Γ hint hβ x).2.2


/-! ### A transience criterion through `Q` -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- A `ψ`-irreducible chain with a set `A ∈ B⁺(X)` such that `Q(x, A) < 1` for every `x` is
transient: a recurrent chain has a non-empty maximal Harris set (Theorem 9.1.5). -/
theorem isTransientChain_of_harrisQ_lt_one {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hψA : 0 < ψ A)
    (hQ : ∀ x, harrisQ P A x < 1) : IsTransientChain P ψ := by
  rcases theorem_8_3_4 P hψ with hrec | htr
  · obtain ⟨H, ⟨-, ⟨x, hx⟩, -, -, hQH⟩, -, -⟩ := theorem_9_1_5 hrec
    exact absurd (hQH A hA hψA x hx) (hQ x).ne
  · exact htr

/-- If `aₙ/n → β > 0`, then `aₙ > R` for all large `n`. -/
theorem eventually_gt_of_tendsto_div_pos {a : ℕ → ℝ} {β : ℝ} (hβ : 0 < β)
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 β)) (R : ℝ) : ∀ᶠ n in atTop, R < a n := by
  have h1 : ∀ᶠ n : ℕ in atTop, β / 2 < a n / n := h.eventually (lt_mem_nhds (half_lt_self hβ))
  have h2 : ∀ᶠ n : ℕ in atTop, 2 * (|R| + 1) / β < n :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ hnpos] at hn1
  rw [div_lt_iff₀ hβ] at hn2
  nlinarith [abs_nonneg R, le_abs_self R]

/-! ### Proposition 9.5.3: random walk on `ℝ` -/

/-- For random walk on `ℝ` with non-zero mean, every bounded interval is visited only finitely
often: `Q(x, [−R, R]) = 0`. -/
theorem randomWalk_real_harrisQ_eq_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun w : ℝ => w) Γ)
    (hβ : ∫ w, w ∂Γ ≠ 0) (x R : ℝ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    harrisQ (randomWalkKernel Γ) (Icc (-R) R) x = 0 := by
  have : IsMarkovKernel (recursionKernel Γ fun p : ℝ × ℝ => p.1 + p.2) :=
    isMarkovKernel_recursionKernel Γ (measurable_add_step (G := ℝ))
  change harrisQ (recursionKernel Γ fun p : ℝ × ℝ => p.1 + p.2) (Icc (-R) R) x = 0
  rw [harrisQ_recursion Γ (measurable_add_step (G := ℝ)) x measurableSet_Icc,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_tendsto_partialSum Γ (c := fun w : ℝ => w) measurable_id hint] with ω hω hio
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_abs_gt_of_tendsto_div hβ hω (|x| + R))
  obtain ⟨n, hn, hnR⟩ := hio N
  simp only [mem_Icc, orbit_randomWalk] at hnR
  have h := hN n hn
  have : |∑ i ∈ Finset.range n, ω (i + 1)| ≤ |x| + R := by
    rw [abs_le]; constructor <;> linarith [abs_le.1 (le_refl |x|), neg_abs_le x, le_abs_self x]
  linarith

/-- **Random walk on `ℝ` with non-zero mean is evanescent**: `P_x{Φ → ∞} = 1`. -/
theorem randomWalk_real_evanescent (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun w : ℝ => w) Γ)
    (hβ : ∫ w, w ∂Γ ≠ 0) (x : ℝ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    pathKernel (randomWalkKernel Γ) x tendsToInfty = 1 := by
  have := isMarkovKernel_randomWalkKernel Γ
  have := isMarkovKernel_pathKernel (randomWalkKernel Γ)
  refine (prob_compl_eq_zero_iff measurableSet_tendsToInfty).1 ?_
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun R : ℕ =>
    randomWalk_real_harrisQ_eq_zero Γ hint hβ x R)
  simp only [tendsToInfty, mem_compl_iff, mem_ofPred_eq, not_forall, not_not] at hω
  obtain ⟨K, hK, hωK⟩ := hω
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R, hR⟩ := exists_nat_ge r
  refine mem_iUnion.2 ⟨R, ioSet_mono (fun y hy => ?_) hωK⟩
  have := hr hy
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact abs_le.1 (this.trans hR)

/-- **Proposition 9.5.3** (MT p. 221): an irreducible random walk on `ℝ` whose increment has a
non-zero mean is transient. -/
theorem proposition_9_5_3 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun w : ℝ => w) Γ) (hβ : ∫ w, w ∂Γ ≠ 0)
    {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_randomWalkKernel Γ
      IsMaximalIrreducibility (randomWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    IsTransientChain (randomWalkKernel Γ) ψ := by
  have := isMarkovKernel_randomWalkKernel Γ
  have hU : (⋃ R : ℕ, Icc (-(R : ℝ)) R) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨R, hR⟩ := exists_nat_ge |y|
    exact ⟨R, abs_le.1 hR⟩
  have hpos : 0 < ψ (⋃ R : ℕ, Icc (-(R : ℝ)) R) := by
    rw [hU]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨R, hR⟩ := exists_measure_pos_of_iUnion hpos
  refine isTransientChain_of_harrisQ_lt_one hψ measurableSet_Icc hR fun x => ?_
  rw [randomWalk_real_harrisQ_eq_zero Γ hint hβ x R]
  exact one_pos


/-! ### Proposition 9.5.1: random walk on `ℝ₊` -/

/-- For random walk on `ℝ₊` with `β > 0`, every bounded set `[0, c]` is visited only finitely
often: `Q(x, [0, c]) = 0`. The path is bounded below by `x + W₁ + ⋯ + Wₙ` (Lindley). -/
theorem halfLine_harrisQ_eq_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun w : ℝ => w) Γ)
    (hβ : 0 < ∫ w, w ∂Γ) (x c : ℝ≥0) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    harrisQ (halfLineWalkKernel Γ) (Iic c) x = 0 := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  have : IsMarkovKernel (recursionKernel Γ halfLineStep) :=
    isMarkovKernel_recursionKernel Γ measurable_halfLineStep
  change harrisQ (recursionKernel Γ halfLineStep) (Iic c) x = 0
  rw [harrisQ_recursion Γ measurable_halfLineStep x measurableSet_Iic,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_tendsto_partialSum Γ (c := fun w : ℝ => w) measurable_id hint] with ω hω hio
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_gt_of_tendsto_div_pos hβ hω (c : ℝ))
  obtain ⟨n, hn, hnc⟩ := hio N
  simp only [mem_Iic] at hnc
  have hl := halfLineOrbit_eq_lindley x ω n
  have hge : (x : ℝ) + partialSum ω n ≤ ((orbit halfLineStep x ω n : ℝ≥0) : ℝ) := by
    change (x : ℝ) + partialSum ω n ≤ (halfLineOrbit x ω n : ℝ)
    rw [hl]; exact le_max_left _ _
  have hc : ((orbit halfLineStep x ω n : ℝ≥0) : ℝ) ≤ c := by exact_mod_cast hnc
  have h := hN n hn
  have hx : (0 : ℝ) ≤ x := x.2
  simp only [partialSum] at hge
  linarith

/-- **Proposition 9.5.1** (MT p. 219): random walk on `ℝ₊` with `β > 0` visits every bounded set
only finitely often, from every starting point; if it is `ψ`-irreducible, it is transient. -/
theorem proposition_9_5_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hint : Integrable (fun w : ℝ => w) Γ) (hβ : 0 < ∫ w, w ∂Γ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    (∀ x c : ℝ≥0, harrisQ (halfLineWalkKernel Γ) (Iic c) x = 0) ∧
      ∀ ψ : Measure ℝ≥0, IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ →
        IsTransientChain (halfLineWalkKernel Γ) ψ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨halfLine_harrisQ_eq_zero Γ hint hβ, fun ψ hψ => ?_⟩
  have hU : (⋃ c : ℕ, Iic (c : ℝ≥0)) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨c, hc⟩ := exists_nat_ge y
    exact ⟨c, hc⟩
  have hpos : 0 < ψ (⋃ c : ℕ, Iic (c : ℝ≥0)) := by
    rw [hU]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨c, hc⟩ := exists_measure_pos_of_iUnion hpos
  refine isTransientChain_of_harrisQ_lt_one hψ measurableSet_Iic hc fun x => ?_
  rw [halfLine_harrisQ_eq_zero Γ hint hβ x c]
  exact one_pos


/-! ### Proposition 9.5.2: the scalar linear model -/

/-- **Proposition 9.5.2**, necessity (MT p. 220): if the noise of the scalar linear model
`Xₙ = αXₙ₋₁ + Wₙ` is bounded, `|W| ≤ R`, and the model is Harris recurrent (for some `ψ`),
then `|α| ≤ 1`. For `|α| > 1` and `|x| ≥ R/(|α| − 1)` the path satisfies `|Xₙ| ≥ |x|` for every
`n`, so bounded sets are not visited from far away, against Theorem 9.1.4. -/
theorem proposition_9_5_2_necessity (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α R : ℝ}
    (hR : Γ (Icc (-R) R)ᶜ = 0) {ψ : Measure ℝ}
    (hH : haveI := isMarkovKernel_ar1Kernel Γ α; IsHarris (ar1Kernel Γ α) ψ) : |α| ≤ 1 := by
  have := isMarkovKernel_ar1Kernel Γ α
  by_contra hα
  push Not at hα
  -- a bounded interval charged by `ψ`
  have hU : (⋃ c : ℕ, Icc (-(c : ℝ)) c) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨c, hc⟩ := exists_nat_ge |y|
    exact ⟨c, abs_le.1 hc⟩
  have hpos : 0 < ψ (⋃ c : ℕ, Icc (-(c : ℝ)) c) := by
    rw [hU]; exact pos_iff_ne_zero.2 fun h => hH.1.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨c, hc⟩ := exists_measure_pos_of_iUnion hpos
  -- a starting point far away
  set x : ℝ := max ((c : ℝ) + 1) (|R| / (|α| - 1))
  have hα1 : 0 < |α| - 1 := by linarith
  have hx1 : (c : ℝ) + 1 ≤ x := le_max_left _ _
  have hx2 : |R| / (|α| - 1) ≤ x := le_max_right _ _
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx1
  have hQ1 := theorem_9_1_4 hH measurableSet_Icc hc x
  -- the path never returns to `[−c, c]`
  have hQ0 : harrisQ (ar1Kernel Γ α) (Icc (-(c : ℝ)) c) x = 0 := by
    have : IsMarkovKernel (recursionKernel Γ fun p : ℝ × ℝ => α * p.1 + p.2) :=
      isMarkovKernel_recursionKernel Γ (measurable_ar1Step α)
    change harrisQ (recursionKernel Γ fun p : ℝ × ℝ => α * p.1 + p.2) (Icc (-(c : ℝ)) c) x = 0
    rw [harrisQ_recursion Γ (measurable_ar1Step α) x measurableSet_Icc,
      measure_eq_zero_iff_ae_notMem]
    have hae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ), ∀ i, ω i ∈ Icc (-R) R := by
      refine ae_all_iff.2 fun i => ?_
      rw [ae_iff]
      have : (Measure.infinitePi fun _ : ℕ => Γ) {ω | ω i ∉ Icc (-R) R} =
          Γ (Icc (-R) R)ᶜ := by
        calc (Measure.infinitePi fun _ : ℕ => Γ) {ω | ω i ∉ Icc (-R) R}
            = (Measure.infinitePi fun _ : ℕ => Γ) ((fun f : ℕ → ℝ => f i) ⁻¹' (Icc (-R) R)ᶜ) :=
              rfl
          _ = ((Measure.infinitePi fun _ : ℕ => Γ).map fun f => f i) (Icc (-R) R)ᶜ :=
              (Measure.map_apply (measurable_pi_apply i) measurableSet_Icc.compl).symm
          _ = Γ (Icc (-R) R)ᶜ := by rw [Measure.infinitePi_map_eval]
      rw [this, hR]
    filter_upwards [hae] with ω hω hio
    have hgrow : ∀ n, x ≤ |orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n| := by
      intro n
      induction n with
      | zero => simp [abs_of_pos hxpos]
      | succ n ih =>
        rw [orbit_succ]
        have hw : |ω (n + 1)| ≤ |R| := by
          have := hω (n + 1)
          rw [mem_Icc] at this
          exact (abs_le.2 this).trans (le_abs_self R) |>.trans_eq rfl
        calc x ≤ |α| * x - |R| := by
              have : |R| ≤ (|α| - 1) * x := by
                rw [div_le_iff₀ hα1] at hx2; linarith
              nlinarith
          _ ≤ |α| * |orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n| - |ω (n + 1)| := by
              gcongr
          _ = |α * orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n| - |ω (n + 1)| := by
              rw [abs_mul]
          _ ≤ _ := by
              have := abs_sub_abs_le_abs_sub (α * orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n)
                (-ω (n + 1))
              rw [abs_neg, sub_neg_eq_add] at this
              exact this
    obtain ⟨n, -, hn⟩ := hio 0
    have h1 := hgrow n
    rw [mem_Icc] at hn
    have : |orbit (fun p : ℝ × ℝ => α * p.1 + p.2) x ω n| ≤ c := abs_le.2 hn
    linarith
  rw [hQ0] at hQ1
  exact zero_ne_one hQ1

/-! ### The stochastic comparison principle (9.44) -/

/-- `P_x(τ_C = ∞) = inf_n P_x(τ_C ≥ n)`. -/
theorem pathKernel_firstReturn_top_eq_iInf (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (x : X) :
    pathKernel P x {ω | firstReturn C ω = ⊤} =
      ⨅ n : ℕ, pathKernel P x {ω | WithTop.some n ≤ firstReturn C ω} := by
  have := isMarkovKernel_pathKernel P
  have hset : {ω : ℕ → X | firstReturn C ω = ⊤} =
      ⋂ n : ℕ, {ω | WithTop.some n ≤ firstReturn C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n; rw [h]; exact le_top
    · intro h
      by_contra hne
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      have := h (m + 1)
      rw [← hm] at this
      exact absurd (WithTop.coe_le_coe.1 this) (by omega)
  rw [hset]
  refine Antitone.measure_iInter (fun a b hab ω hω => le_trans (WithTop.coe_le_coe.2 hab) hω)
    (fun n => (measurableSet_le_firstReturn hC n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩

/-- **Stochastic comparison** (9.44), MT p. 219: if `P_x(τ_C ≥ n) ≤ P'_x(τ_C ≥ n)` for every
`n`, then `L'(x, C) ≤ L(x, C)`. -/
theorem hitProb_le_of_comparison (P P' : Kernel X X) [IsMarkovKernel P] [IsMarkovKernel P']
    {C : Set X} (hC : MeasurableSet C) {x : X}
    (h : ∀ n : ℕ, pathKernel P x {ω | WithTop.some n ≤ firstReturn C ω} ≤
      pathKernel P' x {ω | WithTop.some n ≤ firstReturn C ω}) :
    hitProb P' C x ≤ hitProb P C x := by
  have := isMarkovKernel_pathKernel P
  have := isMarkovKernel_pathKernel P'
  have hT := measurableSet_firstReturn_ne_top (X := X) hC
  have hc : ∀ (Q : Kernel X X) [IsMarkovKernel Q],
      hitProb Q C x = 1 - pathKernel Q x {ω | firstReturn C ω = ⊤} := by
    intro Q _
    have := isMarkovKernel_pathKernel Q
    have e : {ω : ℕ → X | firstReturn C ω = ⊤} = {ω | firstReturn C ω ≠ ⊤}ᶜ := by ext; simp
    rw [e, prob_compl_eq_one_sub hT, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rfl
  rw [hc P', hc P, pathKernel_firstReturn_top_eq_iInf P hC,
    pathKernel_firstReturn_top_eq_iInf P' hC]
  exact tsub_le_tsub_left (iInf_mono h) 1

/-- **Stochastic comparison, recurrence** (MT p. 219): if (9.44) holds off `C`, the second chain
`Φ'` reaches `C` almost surely from every point off `C`, and `C` is petite for the
`ψ`-irreducible chain `Φ`, then `Φ` is Harris recurrent. -/
theorem comparison_harris {P P' : Kernel X X} [IsMarkovKernel P] [IsMarkovKernel P']
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C)
    (hcomp : ∀ x ∉ C, ∀ n : ℕ, pathKernel P x {ω | WithTop.some n ≤ firstReturn C ω} ≤
      pathKernel P' x {ω | WithTop.some n ≤ firstReturn C ω})
    (hL' : ∀ x ∉ C, hitProb P' C x = 1) : IsHarris P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hoff : ∀ x ∉ C, hitProb P C x = 1 := fun x hx =>
    le_antisymm (hitProb_le_one P C x) ((hL' x hx).symm.le.trans
      (hitProb_le_of_comparison P P' hCm (hcomp x hx)))
  refine proposition_9_1_7_ii hψ hC fun x => ?_
  by_cases hx : x ∈ C
  · rw [hitProb_first_step P hCm x, setLIntegral_congr_fun hCm.compl fun y hy => hoff y hy,
      setLIntegral_const, one_mul, measure_add_measure_compl hCm, measure_univ]
  · exact hoff x hx

/-- **Stochastic comparison, transience** (MT p. 219): if (9.44) holds on a set `D ⊆ Cᶜ` with
`C, D ∈ B⁺(X)` for the `ψ'`-irreducible chain `Φ'`, and the first chain `Φ` has `L(x, C) < 1`
for `x ∈ D`, then `Φ'` is transient. -/
theorem comparison_transient {P P' : Kernel X X} [IsMarkovKernel P] [IsMarkovKernel P']
    {ψ' : Measure X} (hψ' : IsMaximalIrreducibility P' ψ') {C D : Set X} (hC : MeasurableSet C)
    (hD : MeasurableSet D) (hψC : 0 < ψ' C) (hψD : 0 < ψ' D)
    (hcomp : ∀ x ∈ D, ∀ n : ℕ, pathKernel P x {ω | WithTop.some n ≤ firstReturn C ω} ≤
      pathKernel P' x {ω | WithTop.some n ≤ firstReturn C ω})
    (hL : ∀ x ∈ D, hitProb P C x < 1) : IsTransientChain P' ψ' :=
  (theorem_8_3_6_ii P' hψ').2 ⟨C, D, hC, hD, hψC, hψD, fun x hx =>
    (hitProb_le_of_comparison P P' hC (hcomp x hx)).trans_lt (hL x hx)⟩

/-! ### Theorem 9.5.5: increment analysis on `ℝ₊` -/


/-- **A second-order Taylor bound**: if `f'' ≤ M` on `[−δ, δ]`, then
`f(u) ≤ f(0) + f'(0)u + Mu²/2` there. -/
theorem le_quadratic_of_deriv2_le {f f' f'' : ℝ → ℝ} {δ M : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ u ∈ Icc (-δ) δ, HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ Icc (-δ) δ, HasDerivAt f' (f'' u) u)
    (hM : ∀ u ∈ Icc (-δ) δ, f'' u ≤ M) {u : ℝ} (hu : u ∈ Icc (-δ) δ) :
    f u ≤ f 0 + f' 0 * u + M / 2 * u ^ 2 := by
  set g : ℝ → ℝ := fun u => f 0 + f' 0 * u + M / 2 * u ^ 2 - f u
  set g' : ℝ → ℝ := fun u => f' 0 + M * u - f' u
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ⟩
  have hg : ∀ u ∈ Icc (-δ) δ, HasDerivAt g (g' u) u := fun u hu => by
    have h1 : HasDerivAt (fun v => f 0 + f' 0 * v + M / 2 * v ^ 2 - f v)
        (0 + f' 0 * 1 + M / 2 * (↑2 * u ^ (2 - 1)) - f' u) u :=
      ((((hasDerivAt_const u (f 0)).add ((hasDerivAt_id u).const_mul (f' 0)))).add
        ((hasDerivAt_pow 2 u).const_mul (M / 2))).sub (hf u hu)
    exact h1.congr_deriv (by simp [g']; ring)
  have hg' : ∀ u ∈ Icc (-δ) δ, HasDerivAt g' (M - f'' u) u := fun u hu => by
    have h1 : HasDerivAt (fun v => f' 0 + M * v - f' v) (0 + M * 1 - f'' u) u :=
      ((hasDerivAt_const u (f' 0)).add ((hasDerivAt_id u).const_mul M)).sub (hf' u hu)
    exact h1.congr_deriv (by ring)
  have hint : interior (Icc (-δ) δ) ⊆ Icc (-δ) δ := interior_subset
  -- `g'` is monotone
  have hmono : MonotoneOn g' (Icc (-δ) δ) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u hu => (hg' u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hg' u (hint hu)).differentiableAt.differentiableWithinAt)
      (fun u hu => by rw [(hg' u (hint hu)).deriv]; linarith [hM u (hint hu)])
  have hg'0 : g' 0 = 0 := by simp [g']
  rcases le_total 0 u with hu0 | hu0
  · have hmg : MonotoneOn g (Icc 0 δ) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun v hv => (hg v ⟨by linarith [hv.1], hv.2⟩).continuousAt.continuousWithinAt)
        (fun v hv => (hg v ⟨by linarith [(interior_subset hv : v ∈ Icc 0 δ).1],
          (interior_subset hv : v ∈ Icc 0 δ).2⟩).differentiableAt.differentiableWithinAt)
        (fun v hv => by
          have hv' : v ∈ Icc 0 δ := interior_subset hv
          have hvI : v ∈ Icc (-δ) δ := ⟨by linarith [hv'.1], hv'.2⟩
          rw [(hg v hvI).deriv, ← hg'0]
          exact hmono h0 hvI hv'.1)
    have := hmg ⟨le_rfl, hδ⟩ ⟨hu0, hu.2⟩ hu0
    simp only [g, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_self] at this
    linarith
  · have hag : AntitoneOn g (Icc (-δ) 0) :=
      antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun v hv => (hg v ⟨hv.1, by linarith [hv.2]⟩).continuousAt.continuousWithinAt)
        (fun v hv => by
          have hv' : v ∈ Icc (-δ) 0 := interior_subset hv
          exact (hg v ⟨hv'.1, by linarith [hv'.2]⟩).differentiableAt.differentiableWithinAt)
        (fun v hv => by
          have hv' : v ∈ Icc (-δ) 0 := interior_subset hv
          have hvI : v ∈ Icc (-δ) δ := ⟨hv'.1, by linarith [hv'.2]⟩
          rw [(hg v hvI).deriv, ← hg'0]
          exact hmono hvI h0 hv'.2)
    have := hag ⟨hu.1, hu0⟩ ⟨by linarith, le_rfl⟩ hu0
    simp only [g, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_self] at this
    linarith

/-- `log(1 + u) ≤ u − u²/(2(1 + δ)²)` for `|u| ≤ δ < 1`. -/
theorem log_one_add_le_quadratic {δ u : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hu : u ∈ Icc (-δ) δ) :
    Real.log (1 + u) ≤ u - u ^ 2 / (2 * (1 + δ) ^ 2) := by
  have hpos : ∀ v ∈ Icc (-δ) δ, 0 < 1 + v := fun v hv => by linarith [hv.1]
  have h := le_quadratic_of_deriv2_le (f := fun v => Real.log (1 + v)) (f' := fun v => 1 / (1 + v))
    (f'' := fun v => -1 / (1 + v) ^ 2) (M := -1 / (1 + δ) ^ 2) hδ
    (fun v hv => by
      have := ((hasDerivAt_id v).const_add 1).log (hpos v hv).ne'
      simpa using this)
    (fun v hv => by
      have := ((hasDerivAt_id v).const_add 1).inv (hpos v hv).ne'
      convert this using 1
      · ext w; simp
      · simp)
    (fun v hv => by
      have h1 : (1 + v) ^ 2 ≤ (1 + δ) ^ 2 := by
        have := hpos v hv
        nlinarith [hv.2]
      have h2 : 0 < (1 + v) ^ 2 := pow_pos (hpos v hv) 2
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact one_div_le_one_div_of_le h2 h1)
    hu
  simp only [add_zero, Real.log_one, div_one, one_mul, zero_add] at h
  have e : -1 / (1 + δ) ^ 2 / 2 * u ^ 2 = -(u ^ 2 / (2 * (1 + δ) ^ 2)) := by
    field_simp
  linarith

/-- `(1 + u)^{−α} ≤ 1 − αu + α(α + 1)(1 − δ)^{−α−2} u²/2` for `|u| ≤ δ < 1`. -/
theorem rpow_neg_le_quadratic {α δ u : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hu : u ∈ Icc (-δ) δ) :
    (1 + u) ^ (-α) ≤ 1 - α * u + α * (α + 1) * (1 - δ) ^ (-α - 2) / 2 * u ^ 2 := by
  have hpos : ∀ v ∈ Icc (-δ) δ, 0 < 1 + v := fun v hv => by linarith [hv.1]
  have h := le_quadratic_of_deriv2_le (f := fun v => (1 + v) ^ (-α))
    (f' := fun v => -α * (1 + v) ^ (-α - 1))
    (f'' := fun v => α * (α + 1) * (1 + v) ^ (-α - 2))
    (M := α * (α + 1) * (1 - δ) ^ (-α - 2)) hδ
    (fun v hv => by
      have := ((hasDerivAt_id' v).const_add 1).rpow_const (p := -α) (Or.inl (hpos v hv).ne')
      exact this.congr_deriv (by ring))
    (fun v hv => by
      have := (((hasDerivAt_id' v).const_add 1).rpow_const (p := -α - 1)
        (Or.inl (hpos v hv).ne')).const_mul (-α)
      refine this.congr_deriv ?_
      rw [show -α - 1 - 1 = -α - 2 by ring]
      ring)
    (fun v hv => by
      have h1 : 1 - δ ≤ 1 + v := by linarith [hv.1]
      have h2 : 0 < 1 - δ := by linarith
      have : (1 + v) ^ (-α - 2) ≤ (1 - δ) ^ (-α - 2) :=
        Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
      have hc : 0 ≤ α * (α + 1) := by positivity
      exact mul_le_mul_of_nonneg_left this hc)
    hu
  simp only [add_zero, Real.one_rpow, mul_one] at h
  linarith

/-- The **mean drift** `m(x) = E_x[Φ₁ − x]` of a chain on `ℝ₊` (MT p. 224). -/
noncomputable def meanDrift (P : Kernel ℝ≥0 ℝ≥0) (x : ℝ≥0) : ℝ := ∫ y, ((y : ℝ) - x) ∂P x

/-- The **second moment of the increment** `v(x) = E_x[(Φ₁ − x)²]` (MT p. 225). -/
noncomputable def incrementVar (P : Kernel ℝ≥0 ℝ≥0) (x : ℝ≥0) : ℝ :=
  ∫ y, ((y : ℝ) - x) ^ 2 ∂P x

/-- **Bounded increments** (9.58), MT p. 225: `|Φ₁ − x| ≤ R`, `P_x`-a.s. -/
def HasBoundedIncrements (P : Kernel ℝ≥0 ℝ≥0) (R : ℝ) : Prop :=
  ∀ x : ℝ≥0, ∀ᵐ y : ℝ≥0 ∂P x, |(y : ℝ) - x| ≤ R

/-- `v(x) ≥ 0`. -/
theorem incrementVar_nonneg (P : Kernel ℝ≥0 ℝ≥0) (x : ℝ≥0) : 0 ≤ incrementVar P x :=
  integral_nonneg fun _ => sq_nonneg _

/-- A function of the increment bounded on `[−R, R]` is integrable. -/
theorem integrable_of_boundedIncrement {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {R : ℝ}
    (hR : HasBoundedIncrements P R) (x : ℝ≥0) {g : ℝ≥0 → ℝ} (hg : Measurable g) {K : ℝ}
    (hK : ∀ y : ℝ≥0, |(y : ℝ) - x| ≤ R → |g y| ≤ K) : Integrable g (P x) :=
  Integrable.of_bound hg.aestronglyMeasurable K
    ((hR x).mono fun y hy => by rw [Real.norm_eq_abs]; exact hK y hy)

/-- **The drift of `log(1 + x)`** (9.62)–(9.63): with bounded increments and `δ = R/(1 + x) < 1`,
`E_x[log(1 + Φ₁)] ≤ log(1 + x) + m(x)/(1 + x) − v(x)/(2(1 + x)²(1 + δ)²)`. -/
theorem integral_log_le {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {R : ℝ}
    (hR : HasBoundedIncrements P R) {x : ℝ≥0} (hδ : R / (1 + x) < 1) :
    ∫ y, Real.log (1 + (y : ℝ)) ∂P x ≤ Real.log (1 + x) + meanDrift P x / (1 + x) -
      incrementVar P x / (2 * (1 + x) ^ 2 * (1 + R / (1 + x)) ^ 2) := by
  have hx0 : (0 : ℝ) ≤ x := x.2
  have ha : (0 : ℝ) < 1 + x := by linarith
  set δ := R / (1 + x)
  obtain ⟨y₀, hy₀⟩ := (hR x).exists
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hy₀
  have hδ0 : 0 ≤ δ := div_nonneg hR0 ha.le
  have hm : Measurable fun y : ℝ≥0 => (y : ℝ) - x := measurable_coe_nnreal_real.sub measurable_const
  have i1 : Integrable (fun y : ℝ≥0 => (y : ℝ) - x) (P x) :=
    integrable_of_boundedIncrement hR x hm fun y hy => hy
  have i2 : Integrable (fun y : ℝ≥0 => ((y : ℝ) - x) ^ 2) (P x) :=
    integrable_of_boundedIncrement hR x (hm.pow_const 2) (K := R ^ 2) fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg ((y : ℝ) - x), sq_abs ((y : ℝ) - x)]
  have hlogm : Measurable fun y : ℝ≥0 => Real.log (1 + (y : ℝ)) :=
    Real.measurable_log.comp (measurable_const.add measurable_coe_nnreal_real)
  have ilog : Integrable (fun y : ℝ≥0 => Real.log (1 + (y : ℝ))) (P x) :=
    integrable_of_boundedIncrement hR x hlogm (K := x + R) fun y hy => by
      have hy0 : (0 : ℝ) ≤ y := y.2
      rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (y : ℝ) by linarith)
      have := (abs_le.1 hy).2
      linarith
  set h : ℝ≥0 → ℝ := fun y => Real.log (1 + x) + ((y : ℝ) - x) / (1 + x) -
    ((y : ℝ) - x) ^ 2 / (2 * (1 + x) ^ 2 * (1 + δ) ^ 2)
  have ih : Integrable h (P x) :=
    ((integrable_const _).add (i1.div_const _)).sub (i2.div_const _)
  have hle : ∀ᵐ y : ℝ≥0 ∂P x, Real.log (1 + (y : ℝ)) ≤ h y := by
    filter_upwards [hR x] with y hy
    have hy0 : (0 : ℝ) ≤ y := y.2
    set u := ((y : ℝ) - x) / (1 + x)
    have hu : u ∈ Icc (-δ) δ := by
      have := abs_le.1 hy
      have hδR : δ * (1 + x) = R := div_mul_cancel₀ R ha.ne'
      constructor
      · rw [le_div_iff₀ ha]; linarith
      · rw [div_le_iff₀ ha]; linarith
    have hsplit : Real.log (1 + (y : ℝ)) = Real.log (1 + x) + Real.log (1 + u) := by
      rw [← Real.log_mul ha.ne' (by have := hu.1; linarith)]
      congr 1; simp only [u]; field_simp; ring
    rw [hsplit]
    have := log_one_add_le_quadratic hδ0 hδ hu
    have e : u ^ 2 / (2 * (1 + δ) ^ 2) = ((y : ℝ) - x) ^ 2 / (2 * (1 + x) ^ 2 * (1 + δ) ^ 2) := by
      simp only [u]; field_simp
    simp only [h]
    linarith
  calc ∫ y, Real.log (1 + (y : ℝ)) ∂P x ≤ ∫ y, h y ∂P x := integral_mono_ae ilog ih hle
    _ = _ := by
        have j1 : Integrable (fun y : ℝ≥0 => ((y : ℝ) - x) / (1 + x)) (P x) := i1.div_const _
        have j2 : Integrable (fun y : ℝ≥0 => ((y : ℝ) - x) ^ 2 /
            (2 * (1 + x) ^ 2 * (1 + δ) ^ 2)) (P x) := i2.div_const _
        have j0 : Integrable (fun _ : ℝ≥0 => Real.log (1 + x)) (P x) := integrable_const _
        have j01 : Integrable (fun y : ℝ≥0 => Real.log (1 + x) + ((y : ℝ) - x) / (1 + x))
            (P x) := j0.add j1
        simp only [h]
        rw [integral_sub j01 j2, integral_add j0 j1, integral_const, integral_div,
          integral_div, meanDrift, incrementVar]
        simp

/-- **The drift of `(1 + x)^{−α}`** (9.66)–(9.67): with bounded increments and
`δ = R/(1 + x) < 1`, `E_x[(1 + Φ₁)^{−α}] ≤ (1 + x)^{−α} (1 − α m(x)/(1 + x) +
α(α + 1)(1 − δ)^{−α−2} v(x)/(2(1 + x)²))`. -/
theorem integral_rpow_neg_le {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {R : ℝ}
    (hR : HasBoundedIncrements P R) {x : ℝ≥0} (hδ : R / (1 + x) < 1) {α : ℝ} (hα : 0 < α) :
    ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤ (1 + (x : ℝ)) ^ (-α) * (1 - α * (meanDrift P x / (1 + x)) +
      α * (α + 1) * (1 - R / (1 + x)) ^ (-α - 2) / 2 * (incrementVar P x / (1 + x) ^ 2)) := by
  have hx0 : (0 : ℝ) ≤ x := x.2
  have ha : (0 : ℝ) < 1 + x := by linarith
  set δ := R / (1 + x)
  obtain ⟨y₀, hy₀⟩ := (hR x).exists
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hy₀
  have hδ0 : 0 ≤ δ := div_nonneg hR0 ha.le
  have hm : Measurable fun y : ℝ≥0 => (y : ℝ) - x := measurable_coe_nnreal_real.sub measurable_const
  have i1 : Integrable (fun y : ℝ≥0 => (y : ℝ) - x) (P x) :=
    integrable_of_boundedIncrement hR x hm fun y hy => hy
  have i2 : Integrable (fun y : ℝ≥0 => ((y : ℝ) - x) ^ 2) (P x) :=
    integrable_of_boundedIncrement hR x (hm.pow_const 2) (K := R ^ 2) fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg ((y : ℝ) - x), sq_abs ((y : ℝ) - x)]
  have hpm : Measurable fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α) :=
    (measurable_const.add measurable_coe_nnreal_real).pow_const _
  have ip : Integrable (fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α)) (P x) :=
    integrable_of_boundedIncrement hR x hpm (K := 1) fun y _ => by
      have hy0 : (0 : ℝ) ≤ y := y.2
      rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  set K : ℝ := α * (α + 1) * (1 - δ) ^ (-α - 2)
  set c : ℝ := (1 + (x : ℝ)) ^ (-α)
  have hc0 : 0 ≤ c := Real.rpow_nonneg ha.le _
  set h : ℝ≥0 → ℝ := fun y => c * (1 - α * (((y : ℝ) - x) / (1 + x)) +
    K / 2 * (((y : ℝ) - x) ^ 2 / (1 + x) ^ 2))
  have ih : Integrable h (P x) :=
    (((integrable_const _).sub ((i1.div_const _).const_mul α)).add
      ((i2.div_const _).const_mul (K / 2))).const_mul c
  have hle : ∀ᵐ y : ℝ≥0 ∂P x, (1 + (y : ℝ)) ^ (-α) ≤ h y := by
    filter_upwards [hR x] with y hy
    have hy0 : (0 : ℝ) ≤ y := y.2
    set u := ((y : ℝ) - x) / (1 + x)
    have hu : u ∈ Icc (-δ) δ := by
      have := abs_le.1 hy
      have hδR : δ * (1 + x) = R := div_mul_cancel₀ R ha.ne'
      constructor
      · rw [le_div_iff₀ ha]; linarith
      · rw [div_le_iff₀ ha]; linarith
    have hsplit : (1 + (y : ℝ)) ^ (-α) = c * (1 + u) ^ (-α) := by
      rw [← Real.mul_rpow ha.le (by have := hu.1; linarith)]
      congr 1; simp only [u]; field_simp; ring
    rw [hsplit]
    have := rpow_neg_le_quadratic hα hδ0 hδ hu
    simp only [h]
    have e : u ^ 2 = ((y : ℝ) - x) ^ 2 / (1 + x) ^ 2 := by simp only [u]; rw [div_pow]
    rw [← e]
    exact mul_le_mul_of_nonneg_left this hc0
  calc ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤ ∫ y, h y ∂P x := integral_mono_ae ip ih hle
    _ = _ := by
        have j0 : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) (P x) := integrable_const _
        have j1 : Integrable (fun y : ℝ≥0 => α * (((y : ℝ) - x) / (1 + x))) (P x) :=
          (i1.div_const _).const_mul α
        have j2 : Integrable (fun y : ℝ≥0 => K / 2 * (((y : ℝ) - x) ^ 2 / (1 + x) ^ 2)) (P x) :=
          (i2.div_const _).const_mul (K / 2)
        have j01 : Integrable (fun y : ℝ≥0 => 1 - α * (((y : ℝ) - x) / (1 + x))) (P x) :=
          j0.sub j1
        simp only [h]
        rw [integral_const_mul, integral_add j01 j2, integral_sub j0 j1, integral_const,
          integral_const_mul, integral_const_mul, integral_div, integral_div, meanDrift,
          incrementVar]
        simp [K]

/-- **Theorem 9.5.5 (i)** (MT p. 225): a `ψ`-irreducible chain on `ℝ₊` with bounded increments
(9.58), whose sets `[0, c]` are petite, and with `m(x) ≤ θ v(x)/2x` for `x > x₀` and some
`θ < 1` (9.59), is Harris recurrent (in particular recurrent); the test function is
`V(x) = log(1 + x)` (9.61) and the conclusion comes from Theorem 9.1.8. -/
theorem theorem_9_5_5_i {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ψ : Measure ℝ≥0}
    (hψ : IsMaximalIrreducibility P ψ) (hpet : ∀ c : ℝ≥0, IsPetite P (Iic c)) {R : ℝ}
    (hR : HasBoundedIncrements P R) {θ : ℝ} (hθ : θ < 1) {x₀ : ℝ≥0}
    (hm : ∀ x, x₀ < x → meanDrift P x ≤ θ * incrementVar P x / (2 * x)) : IsHarris P ψ := by
  obtain ⟨y₀, hy₀⟩ := (hR 0).exists
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hy₀
  -- replace `θ` by `θ' = max θ 0 ∈ [0, 1)`
  set θ' := max θ 0
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'1 : θ' < 1 := max_lt hθ (by norm_num)
  set ε := (1 - θ') / 3
  have hε0 : 0 < ε := by simp only [ε]; linarith
  have hε1 : ε ≤ 1 := by simp only [ε]; linarith
  have hθε : θ' * (1 + ε) ^ 2 ≤ 1 := by
    have h1 : θ' * ε ≤ ε := by nlinarith
    have h2 : θ' * ε ^ 2 ≤ ε := by
      have h3 : θ' * ε ^ 2 ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hθ'1.le (sq_nonneg ε)
      have h4 : ε ^ 2 ≤ ε := by nlinarith
      linarith
    have e : θ' * (1 + ε) ^ 2 = θ' + 2 * (θ' * ε) + θ' * ε ^ 2 := by ring
    have e3 : 3 * ε = 1 - θ' := by simp only [ε]; ring
    rw [e]
    linarith
  -- the threshold
  set x₁ : ℝ := max (x₀ : ℝ) (max ((1 + R) / ε) (2 * R))
  have hdrift : ∀ x : ℝ≥0, x₁ < x → ∫ y, Real.log (1 + (y : ℝ)) ∂P x ≤ Real.log (1 + x) := by
    intro x hx
    have hx0 : (x₀ : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hx1 : (1 + R) / ε < x := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx
    have hx2 : 2 * R < x := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx
    have hxpos : (0 : ℝ) < x := lt_of_le_of_lt (by positivity) hx1
    have ha : (0 : ℝ) < 1 + x := by linarith
    have hδ : R / (1 + x) < 1 := by rw [div_lt_one ha]; linarith
    have h1 := integral_log_le hR hδ
    have hv := incrementVar_nonneg P x
    have hmx : meanDrift P x ≤ θ' * incrementVar P x / (2 * x) :=
      (hm x (by exact_mod_cast hx0)).trans (by gcongr; exact le_max_left _ _)
    -- `θ'(1 + x + R)² ≤ x(1 + x)`
    have hkey : θ' * (1 + x + R) ^ 2 ≤ x * (1 + x) := by
      have hxε : 1 + R ≤ ε * x := by rw [div_lt_iff₀ hε0] at hx1; linarith
      have h1 : 1 + x + R ≤ (1 + ε) * x := by linarith
      have h2 : (1 + x + R) ^ 2 ≤ ((1 + ε) * x) ^ 2 := by
        have : 0 ≤ 1 + x + R := by linarith
        exact pow_le_pow_left₀ this h1 2
      calc θ' * (1 + x + R) ^ 2 ≤ θ' * ((1 + ε) * x) ^ 2 := mul_le_mul_of_nonneg_left h2 hθ'0
        _ = θ' * (1 + ε) ^ 2 * x ^ 2 := by ring
        _ ≤ 1 * x ^ 2 := by gcongr
        _ ≤ x * (1 + x) := by nlinarith
    have hgap : meanDrift P x / (1 + x) -
        incrementVar P x / (2 * (1 + x) ^ 2 * (1 + R / (1 + x)) ^ 2) ≤ 0 := by
      have e : (1 + x) ^ 2 * (1 + R / (1 + x)) ^ 2 = (1 + x + R) ^ 2 := by field_simp
      rw [show 2 * (1 + (x : ℝ)) ^ 2 * (1 + R / (1 + x)) ^ 2 = 2 * (1 + x + R) ^ 2 by
        rw [mul_assoc, e]]
      have hb : meanDrift P x / (1 + x) ≤ θ' * incrementVar P x / (2 * x * (1 + x)) := by
        rw [div_le_iff₀ ha]
        calc meanDrift P x ≤ θ' * incrementVar P x / (2 * x) := hmx
          _ = θ' * incrementVar P x / (2 * x * (1 + x)) * (1 + x) := by field_simp
      have hc : θ' * incrementVar P x / (2 * x * (1 + x)) ≤
          incrementVar P x / (2 * (1 + x + R) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hkey hv
        nlinarith
      linarith
    linarith
  -- the test function `V(x) = log(1 + x)` and Theorem 9.1.8
  set V : ℝ≥0 → ℝ≥0 := fun y => Real.toNNReal (Real.log (1 + y))
  have hVm : Measurable V :=
    (Real.measurable_log.comp (measurable_const.add measurable_coe_nnreal_real)).real_toNNReal
  have hVcoe : ∀ y : ℝ≥0, (V y : ℝ) = Real.log (1 + y) := fun y =>
    Real.coe_toNNReal _ (Real.log_nonneg (by linarith [NNReal.coe_nonneg y]))
  have hpetV : ∀ n : ℕ, IsPetite P {y | V y ≤ n} := fun n =>
    isPetite_of_subset (hpet (Real.toNNReal (Real.exp n))) (measurableSet_le hVm measurable_const)
      fun y hy => by
        simp only [mem_ofPred_eq] at hy
        have h1 : Real.log (1 + y) ≤ n := by
          have := NNReal.coe_le_coe.2 hy
          rwa [hVcoe] at this
        have h2 : 1 + (y : ℝ) ≤ Real.exp n := by
          rw [← Real.log_le_iff_le_exp (by linarith [NNReal.coe_nonneg y])]; exact h1
        rw [mem_Iic, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le]
        linarith
  refine theorem_9_1_8 hψ (hpet (Real.toNNReal x₁)) hVm hpetV fun x hx => ?_
  simp only [mem_Iic, not_le] at hx
  have hx' : x₁ < x := by
    have := NNReal.coe_lt_coe.2 hx
    rwa [Real.coe_toNNReal _ ((NNReal.coe_nonneg x₀).trans (le_max_left _ _))] at this
  rw [drift_nonpos_iff]
  have hint : Integrable (fun y : ℝ≥0 => Real.log (1 + (y : ℝ))) (P x) :=
    integrable_of_boundedIncrement hR x
      (Real.measurable_log.comp (measurable_const.add measurable_coe_nnreal_real))
      (K := x + R) fun y hy => by
        have hy0 : (0 : ℝ) ≤ y := y.2
        rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + (y : ℝ) by linarith)
        have := (abs_le.1 hy).2
        linarith
  have heq : ∀ y : ℝ≥0, ((V y : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.log (1 + y)) := fun y => by
    rw [← hVcoe]; exact (ENNReal.ofReal_coe_nnreal).symm
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y =>
    Real.log_nonneg (by linarith [NNReal.coe_nonneg y]))]
  exact ENNReal.ofReal_le_ofReal (hdrift x hx')

/-- **Theorem 9.5.5 (ii)** (MT p. 225): a `ψ`-irreducible chain on `ℝ₊` with bounded increments
(9.58), whose tails `(c, ∞)` are all in `B⁺(X)`, and with `m(x) ≥ θ v(x)/2x` for `x > x₀` and
some `θ > 1` (9.60), is transient; the test function is `V(x) = 1 − (1 + x)^{−α}` (9.65) with
`α = (θ − 1)/2`, and the conclusion comes from Theorem 8.4.2. -/
theorem theorem_9_5_5_ii {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ψ : Measure ℝ≥0}
    (hψ : IsMaximalIrreducibility P ψ) (hψpos : ∀ c : ℝ≥0, 0 < ψ (Ioi c)) {R : ℝ}
    (hR : HasBoundedIncrements P R) {θ : ℝ} (hθ : 1 < θ) {x₀ : ℝ≥0}
    (hm : ∀ x, x₀ < x → θ * incrementVar P x / (2 * x) ≤ meanDrift P x) :
    IsTransientChain P ψ := by
  obtain ⟨y₀, hy₀⟩ := (hR 0).exists
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hy₀
  set α := (θ - 1) / 2
  have hα : 0 < α := by simp only [α]; linarith
  -- a `δ₀ ∈ (0, 1/2]` with `(α + 1)(1 − δ₀)^{−α−2} ≤ θ`
  have hcont : ContinuousAt (fun δ : ℝ => (1 - δ) ^ (-α - 2)) 0 :=
    ((continuous_const.sub continuous_id).continuousAt).rpow_const (Or.inl (by norm_num))
  have hκ : (1 - (0 : ℝ)) ^ (-α - 2) < θ / (α + 1) := by
    rw [sub_zero, Real.one_rpow, lt_div_iff₀ (by linarith)]
    simp only [α]; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hκ))
  set δ₀ := min (ε / 2) (1 / 2)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hδ₀κ : (1 - δ₀) ^ (-α - 2) < θ / (α + 1) := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ₀]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- the threshold
  set x₁ : ℝ := max (x₀ : ℝ) (R / δ₀)
  have hdrift : ∀ x : ℝ≥0, x₁ < x →
      ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤ (1 + (x : ℝ)) ^ (-α) := by
    intro x hx
    have hx0 : (x₀ : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxR : R / δ₀ < x := lt_of_le_of_lt (le_max_right _ _) hx
    have hxpos : (0 : ℝ) < x := lt_of_le_of_lt (div_nonneg hR0 hδ₀.le) hxR
    have ha : (0 : ℝ) < 1 + x := by linarith
    have hδx : R / (1 + x) ≤ δ₀ := by
      rw [div_le_iff₀ ha]
      rw [div_lt_iff₀ hδ₀] at hxR
      nlinarith
    have hδ : R / (1 + x) < 1 := by linarith
    have h1 := integral_rpow_neg_le hR hδ hα
    have hv := incrementVar_nonneg P x
    have hmx := hm x (by exact_mod_cast hx0)
    have hc0 : 0 ≤ (1 + (x : ℝ)) ^ (-α) := Real.rpow_nonneg ha.le _
    -- `(1 − δ)^{−α−2} ≤ θ/(α + 1)`
    have hpow : (1 - R / (1 + x)) ^ (-α - 2) ≤ θ / (α + 1) := by
      refine le_trans ?_ hδ₀κ.le
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hK : α * (α + 1) * (1 - R / (1 + x)) ^ (-α - 2) ≤ α * θ := by
      have : (α + 1) * (1 - R / (1 + x)) ^ (-α - 2) ≤ θ := by
        rw [le_div_iff₀ (by linarith)] at hpow; linarith
      nlinarith
    have hbr : 1 - α * (meanDrift P x / (1 + x)) + α * (α + 1) * (1 - R / (1 + x)) ^ (-α - 2) /
        2 * (incrementVar P x / (1 + x) ^ 2) ≤ 1 := by
      have hq : 0 ≤ incrementVar P x / (1 + x) ^ 2 := by positivity
      have hstep1 : α * (α + 1) * (1 - R / (1 + x)) ^ (-α - 2) / 2 *
          (incrementVar P x / (1 + x) ^ 2) ≤ α * θ / 2 * (incrementVar P x / (1 + x) ^ 2) := by
        gcongr
      have hstep2 : α * θ / 2 * (incrementVar P x / (1 + x) ^ 2) ≤
          α * (meanDrift P x / (1 + x)) := by
        have hmx' : θ * incrementVar P x / (2 * x) / (1 + x) ≤ meanDrift P x / (1 + x) :=
          div_le_div_of_nonneg_right hmx ha.le
        have hcmp : θ / 2 * (incrementVar P x / (1 + x) ^ 2) ≤
            θ * incrementVar P x / (2 * x) / (1 + x) := by
          rw [show θ * incrementVar P x / (2 * x) / (1 + x) =
            θ / 2 * (incrementVar P x / (x * (1 + x))) by field_simp]
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hv (by positivity)
            (by nlinarith)) (by linarith)
        nlinarith
      linarith
    calc ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤ _ := h1
      _ ≤ (1 + (x : ℝ)) ^ (-α) * 1 := mul_le_mul_of_nonneg_left hbr hc0
      _ = _ := mul_one _
  -- the test function `V(x) = 1 − (1 + x)^{−α}` and Theorem 8.4.2
  set V : ℝ≥0 → ℝ := fun y => 1 - (1 + (y : ℝ)) ^ (-α)
  have hVm : Measurable V := measurable_const.sub
    ((measurable_const.add measurable_coe_nnreal_real).pow_const _)
  have hle1 : ∀ y : ℝ≥0, (1 + (y : ℝ)) ^ (-α) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [NNReal.coe_nonneg y]) (by linarith)
  have hV0 : ∀ y, 0 ≤ V y := fun y => by simp only [V]; linarith [hle1 y]
  have hVle : ∀ y, V y ≤ 1 := fun y => by
    simp only [V]; linarith [Real.rpow_nonneg (by linarith [NNReal.coe_nonneg y] :
      (0 : ℝ) ≤ 1 + y) (-α)]
  -- `V` is strictly increasing
  have hVmono : ∀ y z : ℝ≥0, V y ≤ V z ↔ y ≤ z := by
    intro y z
    constructor
    · intro h
      by_contra hyz
      push Not at hyz
      have hlt : (1 + (z : ℝ)) ^ (-α) > (1 + (y : ℝ)) ^ (-α) :=
        Real.rpow_lt_rpow_of_neg (by linarith [NNReal.coe_nonneg z])
          (by have := NNReal.coe_lt_coe.2 hyz; linarith) (by linarith)
      simp only [V] at h
      linarith
    · intro h
      simp only [V]
      have : (1 + (z : ℝ)) ^ (-α) ≤ (1 + (y : ℝ)) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [NNReal.coe_nonneg y])
          (by have := NNReal.coe_le_coe.2 h; linarith) (by linarith)
      linarith
  -- a level `x₂ ≥ x₁` with `ψ[0, x₂] > 0`
  have hU : (⋃ n : ℕ, Iic (Real.toNNReal x₁ + n)) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge y
    exact ⟨n, le_add_left hn⟩
  have hpos : 0 < ψ (⋃ n : ℕ, Iic (Real.toNNReal x₁ + n)) := by
    rw [hU]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hpos
  set x₂ := Real.toNNReal x₁ + n
  have hset : {y : ℝ≥0 | V y ≤ V x₂} = Iic x₂ := by ext y; simp [hVmono]
  refine (theorem_8_4_2 P hψ).2 ⟨V, V x₂, hVm, hV0, ⟨1, hVle⟩, hV0 _, ?_, ?_, fun x hx => ?_⟩
  · rw [hset]; exact hn
  · rw [hset, compl_Iic]; exact hψpos x₂
  · rw [hset, mem_compl_iff, mem_Iic, not_le] at hx
    have hx' : x₁ < x := by
      have h1 : (x₁ : ℝ) ≤ (Real.toNNReal x₁ : ℝ) := Real.le_coe_toNNReal x₁
      have h2 : ((Real.toNNReal x₁ : ℝ≥0) : ℝ) ≤ (x₂ : ℝ) := by
        simp only [x₂, NNReal.coe_add, NNReal.coe_natCast]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have h3 : (x₂ : ℝ) < x := by exact_mod_cast hx
      linarith
    have hint : Integrable (fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α)) (P x) :=
      integrable_of_boundedIncrement hR x
        ((measurable_const.add measurable_coe_nnreal_real).pow_const _) (K := 1) fun y _ => by
          rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [NNReal.coe_nonneg y]) _)]
          exact hle1 y
    simp only [driftR, V]
    rw [integral_sub (integrable_const _) hint, integral_const]
    simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, Measure.real]
    linarith [hdrift x hx']

/-! ### Proposition 9.5.2: sufficiency -/

/-- The drift of `log(1 + |x|)` for the AR(1) model with `|α| < 1`:
`∫ log(1 + |αx + w|) Γ(dw) ≤ log(1 + |x|)` once `|x| ≥ E|W|/(1 − |α|)`. -/
theorem ar1_log_drift_contract (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) {α : ℝ} (hα : |α| < 1) {x : ℝ}
    (hx : (∫ w, |w| ∂Γ) / (1 - |α|) ≤ |x|) :
    ∫ w, Real.log (1 + |α * x + w|) ∂Γ ≤ Real.log (1 + |x|) := by
  have hα1 : 0 < 1 - |α| := by linarith
  have ha : 0 < 1 + |x| := by positivity
  have hint := integrable_log_one_add_abs Γ hW (α * x)
  have hg : Integrable (fun w => Real.log (1 + |x|) + (|w| - (1 - |α|) * |x|) / (1 + |x|)) Γ :=
    (integrable_const _).add ((hW.abs.sub (integrable_const _)).div_const _)
  have hpt : ∀ w, Real.log (1 + |α * x + w|) ≤
      Real.log (1 + |x|) + (|w| - (1 - |α|) * |x|) / (1 + |x|) := by
    intro w
    have hpos : 0 < (1 + |α * x + w|) / (1 + |x|) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) ha.ne'] at h1
    have h2 : (1 + |α * x + w|) / (1 + |x|) - 1 ≤ (|w| - (1 - |α|) * |x|) / (1 + |x|) := by
      rw [div_sub_one ha.ne']
      refine div_le_div_of_nonneg_right ?_ ha.le
      have := abs_add_le (α * x) w
      rw [abs_mul] at this
      linarith
    linarith
  calc ∫ w, Real.log (1 + |α * x + w|) ∂Γ
      ≤ ∫ w, (Real.log (1 + |x|) + (|w| - (1 - |α|) * |x|) / (1 + |x|)) ∂Γ :=
        integral_mono hint hg hpt
    _ = Real.log (1 + |x|) + ((∫ w, |w| ∂Γ) - (1 - |α|) * |x|) / (1 + |x|) := by
        have j2 : Integrable (fun w : ℝ => |w|) Γ := hW.abs
        have j1 : Integrable (fun w : ℝ => (|w| - (1 - |α|) * |x|) / (1 + |x|)) Γ :=
          (j2.sub (integrable_const _)).div_const _
        rw [integral_add (integrable_const _) j1, integral_const, integral_div,
          integral_sub j2 (integrable_const _), integral_const]
        simp
    _ ≤ Real.log (1 + |x|) := by
        have : (∫ w, |w| ∂Γ) - (1 - |α|) * |x| ≤ 0 := by
          rw [div_le_iff₀ hα1] at hx; linarith
        have := div_nonpos_of_nonpos_of_nonneg this ha.le
        linarith

/-- **Proposition 9.5.2**, sufficiency (MT p. 220): if the scalar linear model
`Xₙ = αXₙ₋₁ + Wₙ` has mean-zero noise with `E[W²] < ∞`, is a `ψ`-irreducible T-chain and
`|α| ≤ 1`, then it is Harris recurrent. The book's comparison argument is replaced by the test
function `V(x) = log(1 + |x|)` of Proposition 9.4.5 (for `|α| = 1`) and the contraction bound
(for `|α| < 1`), Theorem 9.4.1 and Theorem 9.2.2 (ii). -/
theorem proposition_9_5_2_sufficiency (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) {α : ℝ} (hα : |α| ≤ 1)
    {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hT : IsTChain (ar1Kernel Γ α)) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    IsHarris (ar1Kernel Γ α) ψ := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hW := integrable_of_integrable_sq Γ hW2
  obtain ⟨R₁, hR₁, hdr⟩ := randomWalk_log_drift_abs Γ hW2 hβ
  -- the real drift bound off a compact interval
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : ℝ, R < |x| →
      ∫ w, Real.log (1 + |α * x + w|) ∂Γ ≤ Real.log (1 + |x|) := by
    rcases hα.lt_or_eq with hlt | heq
    · exact ⟨(∫ w, |w| ∂Γ) / (1 - |α|), fun x hx => ar1_log_drift_contract Γ hW hlt hx.le⟩
    · refine ⟨R₁, fun x hx => ?_⟩
      have hax : |α * x| = |x| := by rw [abs_mul, heq, one_mul]
      have := hdr (α * x) (by rw [hax]; exact hx)
      rwa [hax] at this
  set V : ℝ → ℝ≥0 := fun y => Real.toNNReal (Real.log (1 + |y|))
  have hVm : Measurable V :=
    (Real.measurable_log.comp (measurable_const.add continuous_abs.measurable)).real_toNNReal
  refine (theorem_9_2_2_ii hψ hT).2 (theorem_9_4_1 hVm isCoercive_log_one_add_abs
    (isCompact_Icc (a := -|R|) (b := |R|)) fun x hx => ?_)
  have hxR : R < |x| := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith [abs_nonneg R])]; linarith [le_abs_self R]
    · exact lt_of_le_of_lt (le_abs_self R) (lt_of_lt_of_le hx (le_abs_self x))
  have hVe : Measurable fun y => ((V y : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hVm
  rw [drift_nonpos_iff]
  change ∫⁻ y, ((V y : ℝ≥0) : ℝ≥0∞) ∂(recursionKernel Γ fun p : ℝ × ℝ => α * p.1 + p.2) x ≤ _
  rw [recursionKernel_apply Γ (measurable_ar1Step α) x,
    lintegral_map hVe (measurable_const_add (α * x))]
  exact lintegral_log_one_add_abs_le Γ hW x (hR x hxR)

/-- **Proposition 9.5.2** (MT p. 220): for the scalar linear model with bounded mean-zero noise
that is a `ψ`-irreducible T-chain, the model is Harris recurrent iff `|α| ≤ 1`. -/
theorem proposition_9_5_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {R : ℝ}
    (hR : Γ (Icc (-R) R)ᶜ = 0) (hβ : ∫ w, w ∂Γ = 0) {α : ℝ} {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hT : IsTChain (ar1Kernel Γ α)) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    IsHarris (ar1Kernel Γ α) ψ ↔ |α| ≤ 1 := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hW2 : Integrable (fun w => w ^ 2) Γ := by
    refine Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable (R ^ 2) ?_
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) hR
    simp only [mem_ofPred_eq, Real.norm_eq_abs, not_le] at hw
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]
    by_contra h
    push Not at h
    rw [abs_of_nonneg (sq_nonneg w)] at hw
    nlinarith [abs_le.2 h, sq_abs w, abs_nonneg w]
  exact ⟨proposition_9_5_2_necessity Γ hR,
    fun hα => proposition_9_5_2_sufficiency Γ hW2 hβ hα hψ hT⟩

/-- **Correction to the proof of Proposition 9.5.2** (MT p. 220): the scalar linear model with
noise supported on `[−R, R]` and `|α| < 1` is **not** Lebesgue-irreducible on `ℝ`, as the proof
asserts: from `0` the path stays in `[−K, K]`, `K = R/(1 − |α|)`, so `(K, ∞)` is never
reached. -/
theorem proposition_9_5_2_not_leb_irreducible (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α R : ℝ}
    (hα : |α| < 1) (hR : Γ (Icc (-R) R)ᶜ = 0) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    ¬ IsPhiIrreducible (ar1Kernel Γ α) volume := by
  have := isMarkovKernel_ar1Kernel Γ α
  have : IsMarkovKernel (recursionKernel Γ fun p : ℝ × ℝ => α * p.1 + p.2) :=
    isMarkovKernel_recursionKernel Γ (measurable_ar1Step α)
  intro hirr
  set K := |R| / (1 - |α|)
  have hα1 : 0 < 1 - |α| := by linarith
  have hK0 : 0 ≤ K := div_nonneg (abs_nonneg R) hα1.le
  have hKR : |α| * K + |R| = K := by simp only [K]; field_simp; ring
  have hB : MeasurableSet (Ioi K) := measurableSet_Ioi
  have hpos : 0 < volume (Ioi K) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
  have hL := hirr (Ioi K) hB hpos 0
  -- from `0` the path stays in `[−K, K]`
  have hmeas : Measurable fun (ω : ℕ → ℝ) (n : ℕ) =>
      orbit (fun p : ℝ × ℝ => α * p.1 + p.2) 0 ω n :=
    measurable_pi_iff.2 fun n => by
      simp_rw [orbit_eq_controlMap]
      exact (measurable_controlMap_right (measurable_ar1Step α) n 0).comp
        (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  have hT := measurableSet_firstReturn_ne_top (X := ℝ) hB
  change 0 < hitProb (recursionKernel Γ fun p : ℝ × ℝ => α * p.1 + p.2) (Ioi K) 0 at hL
  rw [hitProb, ← pathKernel_recursion Γ (measurable_ar1Step α) 0,
    Measure.map_apply hmeas hT] at hL
  have hae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ), ∀ i, ω i ∈ Icc (-R) R := by
    refine ae_all_iff.2 fun i => ?_
    rw [ae_iff]
    calc (Measure.infinitePi fun _ : ℕ => Γ) {ω | ω i ∉ Icc (-R) R}
        = (Measure.infinitePi fun _ : ℕ => Γ) ((fun f : ℕ → ℝ => f i) ⁻¹' (Icc (-R) R)ᶜ) := rfl
      _ = ((Measure.infinitePi fun _ : ℕ => Γ).map fun f => f i) (Icc (-R) R)ᶜ :=
          (Measure.map_apply (measurable_pi_apply i) measurableSet_Icc.compl).symm
      _ = 0 := by rw [Measure.infinitePi_map_eval, hR]
  have h0 : (Measure.infinitePi fun _ : ℕ => Γ)
      ((fun ω n => orbit (fun p : ℝ × ℝ => α * p.1 + p.2) 0 ω n) ⁻¹'
        {ω | firstReturn (Ioi K) ω ≠ ⊤}) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω hmem
    have hbound : ∀ n, |orbit (fun p : ℝ × ℝ => α * p.1 + p.2) 0 ω n| ≤ K := by
      intro n
      induction n with
      | zero => simp [hK0]
      | succ n ih =>
        rw [orbit_succ]
        have hw : |ω (n + 1)| ≤ |R| := (abs_le.2 (hω (n + 1))).trans (le_abs_self R)
        calc |α * orbit (fun p : ℝ × ℝ => α * p.1 + p.2) 0 ω n + ω (n + 1)|
            ≤ |α| * |orbit (fun p : ℝ × ℝ => α * p.1 + p.2) 0 ω n| + |ω (n + 1)| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ |α| * K + |R| := by gcongr
          _ = K := hKR
    simp only [mem_preimage, mem_ofPred_eq, firstReturn_ne_top_iff] at hmem
    obtain ⟨n, -, hn⟩ := hmem
    exact absurd ((le_abs_self _).trans (hbound n)) (not_le.2 hn)
  rw [h0] at hL
  exact lt_irrefl 0 hL

end MeynTweedie.Ergodicity
