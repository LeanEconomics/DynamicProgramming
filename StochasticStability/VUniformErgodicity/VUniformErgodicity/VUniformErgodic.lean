/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.OperatorNorm

/-!
# `V`-uniform ergodicity (MT Theorem 16.0.1, Theorem 16.1.4)

Meyn and Tweedie, pp. 392–397. `ψ` is a maximal irreducibility measure, the state space is
countably generated, `V ≥ 1` is measurable and everywhere finite, and `μ` is an invariant
probability.

* `IsVUniformlyErgodic V P μ` (16.2), p. 392: `|||Pⁿ − 1 ⊗ μ|||_V → 0`.
* `measure_le_add_fNorm`: `ν(A) ≤ μ(A) + ‖μ − ν‖_f` for `f ≥ 1`, so that (16.13) gives
  `Pⁿ(x, C) ≥ μ(C) − Rρⁿ V(x)`.
* `isUnboundedOffPetite_of_tendsto`: if `|||Pⁿ − 1 ⊗ μ|||_V → 0`, every sublevel set of `V` is
  petite (the first step of the proof of Theorem 16.1.4, by Proposition 5.5.4 (i)).
* **Theorem 16.1.4** (`theorem_16_1_4`, p. 396): `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ` gives (V4) for
  `V₀ = Σ_{i < n} sⁱ PⁱV`, with `V ≤ V₀ ≤ c V`, and a petite set. The book's weights are
  `sⁱ = e^{i/n}`; any `s > 1` with `R (s/r)ⁿ ≤ 1` works, through the identity
  `s P V₀ + V = V₀ + sⁿ PⁿV`.
* `fNorm_le_const_mul`, `vErgDist_le_of_equiv`: equivalent weights `c⁻¹V ≤ V₀ ≤ cV` give
  equivalent distances, `|||Pⁿ − 1 ⊗ μ|||_V ≤ c² |||Pⁿ − 1 ⊗ μ|||_{V₀}`.
* **Theorem 16.0.1** (`theorem_16_0_1`, p. 393), corrected: for a `ψ`-irreducible aperiodic chain
  the following are equivalent: (i) `V`-uniform ergodicity with all the distances finite;
  (ii) `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ` (16.3); (iii) `|||Pⁱ − 1 ⊗ μ|||_V < ∞` for `i ≤ n` and
  `|||Pⁿ − 1 ⊗ μ|||_V < 1` (16.4); (iv) (V4) for a petite set and some `V₀` with
  `c⁻¹ V ≤ V₀ ≤ c V` (16.5).

* `tsum_fNorm_le_of_tsum_vErgDist` (p. 396): `V`-uniform ergodicity in the form (16.12) is
  `V`-geometric ergodicity, `Σ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)`.

**Correction.** In Theorem 16.0.1, (i) as printed (`|||Pⁿ − 1 ⊗ π|||_V → 0` alone) does not imply
(ii)–(iv): a finite number of the distances may be infinite. `theorem_16_0_1_counterexample` is
the deterministic chain `twoStepKernel` on `ℕ` (`0 ↦ 0`, odd `k ↦ k + 1`, even `k ≥ 2 ↦ 0`) with
`V(k) = 1` for odd `k` and `V(k) = k + 1` otherwise: it is `ψ`-irreducible and aperiodic,
`Pⁿ = 1 ⊗ δ₀` for `n ≥ 2`, but `|||P − 1 ⊗ δ₀|||_V = ∞`. The equivalence holds with (i) read as
"`V`-uniformly ergodic and `|||Pⁿ − 1 ⊗ π|||_V < ∞` for every `n`", which is the form proved; the
proof of (i) ⇒ (iii) in the book (through Proposition 16.1.3) needs exactly this.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The definition -/

/-- **`V`-uniform ergodicity** (16.2), MT p. 392: `μ` is invariant and
`|||Pⁿ − 1 ⊗ μ|||_V → 0`. -/
def IsVUniformlyErgodic (V : X → ℝ≥0∞) (P : Kernel X X) (μ : Measure X) : Prop :=
  IsInvariant P μ ∧ Tendsto (vErgDist V P μ) atTop (𝓝 0)

/-- `ν(A) ≤ μ(A) + ‖μ − ν‖_f` for `f ≥ 1` (test the norm with `1_A`). -/
theorem measure_le_add_fNorm {f : X → ℝ≥0∞} (hf1 : ∀ x, 1 ≤ f x) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) :
    ν A ≤ μ A + fNorm f μ ν := by
  have hgm : Measurable (A.indicator (1 : X → ℝ)) := measurable_one.indicator hA
  have hg1 : ∀ x, |A.indicator (1 : X → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ A <;> simp [hx]
  have htest : IsFTest f μ ν (A.indicator 1) :=
    ⟨hgm, fun x => (ENNReal.ofReal_le_ofReal (hg1 x)).trans
      (by rw [ENNReal.ofReal_one]; exact hf1 x),
      integrable_of_abs_le_one hgm hg1, integrable_of_abs_le_one hgm hg1⟩
  have hkey := ofReal_abs_integral_sub_le_fNorm htest
  rw [integral_indicator_one hA, integral_indicator_one hA] at hkey
  calc ν A = ENNReal.ofReal (ν.real A) := (ofReal_measureReal (measure_ne_top ν A)).symm
    _ ≤ ENNReal.ofReal (μ.real A + |μ.real A - ν.real A|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [neg_abs_le (μ.real A - ν.real A)]
    _ = ENNReal.ofReal (μ.real A) + ENNReal.ofReal |μ.real A - ν.real A| :=
        ENNReal.ofReal_add measureReal_nonneg (abs_nonneg _)
    _ ≤ μ A + fNorm f μ ν := add_le_add (ofReal_measureReal (measure_ne_top μ A)).le hkey

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The sublevel sets of `V` are petite** (MT p. 397): if `|||Pⁿ − 1 ⊗ μ|||_V → 0` for a
`ψ`-irreducible chain, then `Pⁿ(x, C) ≥ μ(C) − |||Pⁿ − 1 ⊗ μ|||_V ℓ` on `{V ≤ ℓ}` for a small
`C ∈ B⁺(X)`, so `{V ≤ ℓ} ⇝ C` and `{V ≤ ℓ}` is petite (Proposition 5.5.4 (i)). -/
theorem isUnboundedOffPetite_of_tendsto {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    (hlim : Tendsto (vErgDist V P μ) atTop (𝓝 0)) : IsUnboundedOffPetite P V := by
  intro ℓ hℓ
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hμC : 0 < μ C :=
    hμ.isSubinvariant.pos_of_pos hψ.2.1 (IsProbabilityMeasure.ne_zero μ) hC.1 hψC
  have hμCt : μ C ≠ ∞ := measure_ne_top μ C
  have hlimℓ : Tendsto (fun n => vErgDist V P μ n * ℓ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hℓ)
  have hpos : (0 : ℝ≥0∞) < μ C / 2 := ENNReal.half_pos hμC.ne'
  obtain ⟨n, hn⟩ := (hlimℓ.eventually (gt_mem_nhds hpos)).exists
  have hacc : SampledAccessible P (diracDist n) {x | V x ≤ ℓ} C := by
    refine ⟨μ C / 2, hpos, fun x hx => ?_⟩
    rw [sampledKernel_diracDist]
    have := isMarkovKernel_pow P n
    have hx' : V x ≤ ℓ := hx
    have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
    have hVt : V x ≠ ∞ := ne_top_of_le_ne_top hℓ hx'
    have h1 := measure_le_add_fNorm hV1 ((P ^ n) x) μ hC.1
    have h2 := fNorm_pow_le_vErgDist_mul (V := V) P μ n hV0 hVt
    have h3 : vErgDist V P μ n * V x ≤ μ C / 2 := (mul_le_mul' le_rfl hx').trans hn.le
    have h4 : μ C ≤ (P ^ n) x C + μ C / 2 := h1.trans (add_le_add le_rfl (h2.trans h3))
    calc μ C / 2 = μ C - μ C / 2 := (ENNReal.sub_half hμCt).symm
      _ ≤ (P ^ n) x C := tsub_le_iff_right.2 h4
  obtain ⟨δ, -, hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC)
    (measurableSet_le hV measurable_const) (isSamplingDist_diracDist n) hacc
  exact ⟨_, _, hpet⟩

/-! ### Theorem 16.1.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.1.4** (MT p. 396): for a `ψ`-irreducible chain with
`|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ` for all `n` (16.13), (V4) holds for a petite set and some `V₀`
with `V ≤ V₀ ≤ c V` (16.14). -/
theorem theorem_16_1_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {μ : Measure X} [IsProbabilityMeasure μ] (hμ : IsInvariant P μ)
    {r R : ℝ≥0∞} (hr : 1 < r) (hR : R ≠ ∞) (h : ∀ n, vErgDist V P μ n ≤ R * r⁻¹ ^ n) :
    ∃ V₀ : X → ℝ≥0∞, Measurable V₀ ∧ (∀ x, 1 ≤ V₀ x) ∧ ∃ c : ℝ≥0∞, c ≠ ∞ ∧
      (∀ x, V x ≤ V₀ x ∧ V₀ x ≤ c * V x) ∧ ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧
        ∃ C, IsPetite P C ∧ DriftV4 P V₀ ρ b C := by
  have := nonempty_of_isProbabilityMeasure μ
  inhabit X
  set t := r⁻¹ with htdef
  have ht : t < 1 := ENNReal.inv_lt_one.2 hr
  have h0 : vErgDist V P μ 0 ≠ ∞ := ne_top_of_le_ne_top (by simpa using hR) (h 0)
  have hμV : ∫⁻ y, V y ∂μ ≠ ∞ := lintegral_ne_top_of_vErgDist_zero hV hV1 (hVt default) P μ h0
  set m := ∫⁻ y, V y ∂μ with hm
  have hgeo : ∀ {q : ℝ≥0∞}, q < 1 → Tendsto (fun n => R * q ^ n) atTop (𝓝 0) := fun hq => by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Or.inr hR)
  have hlim : Tendsto (vErgDist V P μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hgeo ht) (fun _ => zero_le) h
  have hU := isUnboundedOffPetite_of_tendsto hψ hV hV1 hμ hlim
  obtain ⟨s, hs, hst, hts⟩ := exists_one_lt_mul_lt_one ht
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs).ne'
  obtain ⟨n, hn, hn1⟩ := ((hgeo hts).eventually (gt_mem_nhds zero_lt_one)).and
    (eventually_ge_atTop 1) |>.exists
  -- the function `V₀ = Σ_{i < n} sⁱ PⁱV`
  set W : ℕ → X → ℝ≥0∞ := fun i x => ∫⁻ y, V y ∂(P ^ i) x with hW
  have hWm : ∀ i, Measurable (W i) := fun i => hV.lintegral_kernel
  have hW0 : ∀ x, W 0 x = V x := fun x => by
    rw [hW]; simp only; rw [pow_zero_apply, lintegral_dirac' x hV]
  set V₀ : X → ℝ≥0∞ := fun x => ∑ i ∈ Finset.range n, s ^ i * W i x with hV₀
  have hV₀m : Measurable V₀ := Finset.measurable_sum _ fun i _ => (hWm i).const_mul _
  have hVV₀ : ∀ x, V x ≤ V₀ x := fun x => by
    have h0n : 0 ∈ Finset.range n := Finset.mem_range.2 hn1
    calc V x = s ^ 0 * W 0 x := by rw [pow_zero, one_mul, hW0]
      _ ≤ V₀ x := Finset.single_le_sum (f := fun i => s ^ i * W i x) (fun _ _ => zero_le) h0n
  have hWle : ∀ i x, W i x ≤ (R + m) * V x := fun i x => by
    have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
    have hAi : vErgDist V P μ i ≤ R := (h i).trans (mul_le_of_le_one_right' (pow_le_one₀ zero_le
      ht.le))
    calc W i x ≤ vErgDist V P μ i * V x + m := lintegral_pow_le_vErgDist hV P μ i hV0 (hVt x)
      _ ≤ R * V x + m * V x := add_le_add (mul_le_mul' hAi le_rfl)
          (le_mul_of_one_le_right' (hV1 x))
      _ = (R + m) * V x := (add_mul _ _ _).symm
  set c := ∑ i ∈ Finset.range n, s ^ i * (R + m) with hc
  have hct : c ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hst) (ENNReal.add_ne_top.2 ⟨hR, hμV⟩)
  have hV₀c : ∀ x, V₀ x ≤ c * V x := fun x => by
    rw [hc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (hWle i x)
  -- the identity `s P V₀ + V = V₀ + sⁿ PⁿV`
  have hiter : ∀ i x, ∫⁻ y, W i y ∂P x = W (i + 1) x := fun i x => by
    have := congrFun (kfun_pow_succ P i hV) x
    simp only [kfun] at this
    exact this.symm
  have hPV₀ : ∀ x, ∫⁻ y, V₀ y ∂P x = ∑ i ∈ Finset.range n, s ^ i * W (i + 1) x := fun x => by
    rw [hV₀]
    simp only
    rw [lintegral_finsetSum _ fun i _ => (hWm i).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (hWm i), hiter]
  have hident : ∀ x, s * ∫⁻ y, V₀ y ∂P x + V x = V₀ x + s ^ n * W n x := fun x => by
    rw [hPV₀, Finset.mul_sum, hV₀]
    simp only
    have e1 := Finset.sum_range_succ (fun i => s ^ i * W i x) n
    have e2 := Finset.sum_range_succ' (fun i => s ^ i * W i x) n
    rw [← e1, e2, pow_zero, one_mul, hW0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring
  -- the bound `sⁿ PⁿV ≤ V + sⁿ μ(V)`
  have hsn : s ^ n * vErgDist V P μ n ≤ 1 := by
    calc s ^ n * vErgDist V P μ n ≤ s ^ n * (R * t ^ n) := mul_le_mul' le_rfl (h n)
      _ = R * (t * s) ^ n := by rw [mul_pow]; ring
      _ ≤ 1 := hn.le
  have hdrift : ∀ x, ∫⁻ y, V₀ y ∂P x ≤ s⁻¹ * V₀ x + s⁻¹ * (s ^ n * m) := fun x => by
    have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
    have hb : s ^ n * W n x ≤ V x + s ^ n * m := by
      calc s ^ n * W n x ≤ s ^ n * (vErgDist V P μ n * V x + m) :=
            mul_le_mul' le_rfl (lintegral_pow_le_vErgDist hV P μ n hV0 (hVt x))
        _ = s ^ n * vErgDist V P μ n * V x + s ^ n * m := by ring
        _ ≤ 1 * V x + s ^ n * m := add_le_add (mul_le_mul' hsn le_rfl) le_rfl
        _ = V x + s ^ n * m := by rw [one_mul]
    have h1 : s * ∫⁻ y, V₀ y ∂P x + V x ≤ (V₀ x + s ^ n * m) + V x := by
      rw [hident]
      calc V₀ x + s ^ n * W n x ≤ V₀ x + (V x + s ^ n * m) := add_le_add le_rfl hb
        _ = (V₀ x + s ^ n * m) + V x := by ring
    have h2 := (ENNReal.add_le_add_iff_right (hVt x)).1 h1
    calc ∫⁻ y, V₀ y ∂P x = s⁻¹ * (s * ∫⁻ y, V₀ y ∂P x) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hs0 hst, one_mul]
      _ ≤ s⁻¹ * (V₀ x + s ^ n * m) := mul_le_mul' le_rfl h2
      _ = s⁻¹ * V₀ x + s⁻¹ * (s ^ n * m) := mul_add _ _ _
  have hV₀1 : ∀ x, 1 ≤ V₀ x := fun x => (hV1 x).trans (hVV₀ x)
  have hU₀ : IsUnboundedOffPetite P V₀ := fun ℓ hℓ => by
    obtain ⟨a, ν, -, ha, hν, hle⟩ := hU ℓ hℓ
    exact ⟨a, ν, measurableSet_le hV₀m measurable_const, ha, hν, fun x hx =>
      hle x ((hVV₀ x).trans hx)⟩
  obtain ⟨ρ, b, hρ, hb, C, hC, hd⟩ := (lemma_15_2_8 hV₀m hV₀1).2 ⟨hU₀, s⁻¹, s⁻¹ * (s ^ n * m),
    ENNReal.inv_lt_one.2 hs, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hs0)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top hst) hμV), hdrift⟩
  exact ⟨V₀, hV₀m, hV₀1, c, hct, fun x => ⟨hVV₀ x, hV₀c x⟩, ρ, b, hρ, hb, C, hC, hd⟩

/-! ### Equivalent weights -/

/-- `‖μ − ν‖_f ≤ c ‖μ − ν‖_g` when `f ≤ c g`, `c < ∞`. -/
theorem fNorm_le_const_mul {f g : X → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (hfg : ∀ x, f x ≤ c * g x)
    (μ ν : Measure X) : fNorm f μ ν ≤ c * fNorm g μ ν :=
  fNorm_le fun _ hh => ofReal_abs_integral_sub_le_mul_fNorm hc hh.1
    (fun x => (hh.2.1 x).trans (hfg x)) hh.2.2.1 hh.2.2.2

/-- **Equivalent weights give equivalent distances**: if `V ≤ c V₀` and `V₀ ≤ c V`, then
`|||Pⁿ − 1 ⊗ μ|||_V ≤ c² |||Pⁿ − 1 ⊗ μ|||_{V₀}`. -/
theorem vErgDist_le_of_equiv {V V₀ : X → ℝ≥0∞} (hV₀1 : ∀ x, 1 ≤ V₀ x) (hV₀t : ∀ x, V₀ x ≠ ∞)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hequiv : ∀ x, V x ≤ c * V₀ x ∧ V₀ x ≤ c * V x) (P : Kernel X X)
    (μ : Measure X) (n : ℕ) : vErgDist V P μ n ≤ c * c * vErgDist V₀ P μ n := by
  refine vOpNorm_le fun x => ?_
  rw [Kernel.const_apply]
  have hV₀0 : V₀ x ≠ 0 := (zero_lt_one.trans_le (hV₀1 x)).ne'
  calc fNorm V ((P ^ n) x) μ ≤ c * fNorm V₀ ((P ^ n) x) μ :=
        fNorm_le_const_mul hc (fun y => (hequiv y).1) _ _
    _ ≤ c * (vErgDist V₀ P μ n * V₀ x) :=
        mul_le_mul' le_rfl (fNorm_pow_le_vErgDist_mul P μ n hV₀0 (hV₀t x))
    _ ≤ c * (vErgDist V₀ P μ n * (c * V x)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hequiv x).2)
    _ = c * c * vErgDist V₀ P μ n * V x := by ring

/-! ### Theorem 16.0.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.0.1** (MT p. 393), with (i) corrected: for a `ψ`-irreducible aperiodic chain, an
invariant probability `μ` and a measurable, everywhere finite `V ≥ 1`, the following are
equivalent:
(i) `Φ` is `V`-uniformly ergodic and every `|||Pⁿ − 1 ⊗ μ|||_V` is finite;
(ii) `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ` for all `n`, for some `r > 1`, `R < ∞` (16.3);
(iii) `|||Pⁱ − 1 ⊗ μ|||_V < ∞` for `i ≤ n` and `|||Pⁿ − 1 ⊗ μ|||_V < 1`, for some `n > 0` (16.4);
(iv) (V4) holds for a petite set and some `V₀ ≥ 1` with `c⁻¹ V ≤ V₀ ≤ c V` (16.5). -/
theorem theorem_16_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) :
    List.TFAE [
      (∀ n, vErgDist V P μ n ≠ ∞) ∧ IsVUniformlyErgodic V P μ,
      ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ n, vErgDist V P μ n ≤ R * r⁻¹ ^ n,
      ∃ n, 0 < n ∧ (∀ i ≤ n, vErgDist V P μ i ≠ ∞) ∧ vErgDist V P μ n < 1,
      ∃ V₀ : X → ℝ≥0∞, Measurable V₀ ∧ (∀ x, 1 ≤ V₀ x) ∧ ∃ c : ℝ≥0∞, c ≠ ∞ ∧
        (∀ x, V x ≤ c * V₀ x ∧ V₀ x ≤ c * V x) ∧ ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧
          ∃ C, IsPetite P C ∧ DriftV4 P V₀ ρ b C] := by
  have := nonempty_of_isProbabilityMeasure μ
  inhabit X
  tfae_have 1 → 3 := by
    rintro ⟨hfin, -, hlim⟩
    obtain ⟨n, hn, hn1⟩ := ((hlim.eventually (gt_mem_nhds zero_lt_one)).and
      (eventually_ge_atTop 1)).exists
    exact ⟨n, hn1, fun i _ => hfin i, hn⟩
  tfae_have 3 → 2 := by
    rintro ⟨n, hn, hfin, hγ⟩
    have hμV := lintegral_ne_top_of_vErgDist_zero hV hV1 (hVt default) P μ (hfin 0 (zero_le))
    obtain ⟨t, ht1, ht0, K, hK, hb⟩ :=
      vErgDist_le_geometric hV hV1 hVt hμ hμV (hfin 1 hn) hn hγ
    exact ⟨t⁻¹, ENNReal.one_lt_inv.2 ht1, K, hK, fun k => by rw [inv_inv]; exact hb k⟩
  tfae_have 2 → 1 := by
    rintro ⟨r, hr, R, hR, hb⟩
    have hr1 : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr
    refine ⟨fun n => ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne'))) (hb n), hμ, ?_⟩
    have hlim : Tendsto (fun n => R * r⁻¹ ^ n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
        (Or.inr hR)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb
  tfae_have 2 → 4 := by
    rintro ⟨r, hr, R, hR, hb⟩
    obtain ⟨V₀, hV₀m, hV₀1, c, hc, hequiv, ρ, b, hρ, hb', C, hC, hd⟩ :=
      theorem_16_1_4 hψ hV hV1 hVt hμ hr hR hb
    refine ⟨V₀, hV₀m, hV₀1, max c 1, max_ne_top hc ENNReal.one_ne_top, fun x => ⟨?_, ?_⟩, ρ, b,
      hρ, hb', C, hC, hd⟩
    · exact (hequiv x).1.trans (le_mul_of_one_le_left' (le_max_right c 1))
    · exact (hequiv x).2.trans (mul_le_mul' (le_max_left c 1) le_rfl)
  tfae_have 4 → 2 := by
    rintro ⟨V₀, hV₀m, hV₀1, c, hc, hequiv, ρ, b, hρ, hb, C, hC, hd⟩
    have hV₀t : ∀ x, V₀ x ≠ ∞ := fun x =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (hVt x)) (hequiv x).2
    obtain ⟨-, r, hr, -, R, hR, hbd⟩ :=
      vErgDist_le_of_driftV4 hψ hap hV₀m hV₀1 hV₀t hρ hb hC hd μ hμ
    refine ⟨r, hr, c * c * R, ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hc) hR, fun n => ?_⟩
    calc vErgDist V P μ n ≤ c * c * vErgDist V₀ P μ n :=
          vErgDist_le_of_equiv hV₀1 hV₀t hc hequiv P μ n
      _ ≤ c * c * (R * r⁻¹ ^ n) := mul_le_mul' le_rfl (hbd n)
      _ = c * c * R * r⁻¹ ^ n := by ring
  tfae_finish

/-! ### `V`-uniform ergodicity gives `V`-geometric ergodicity -/

/-- **`V`-uniformly ergodic chains are `V`-geometrically ergodic** (MT p. 396): if
`Σₙ rⁿ |||Pⁿ − 1 ⊗ μ|||_V = S < ∞`, then `Σₙ rⁿ ‖Pⁿ(x, ·) − μ‖_V ≤ S V(x)` for every `x`. -/
theorem tsum_fNorm_le_of_tsum_vErgDist {V : X → ℝ≥0∞} (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) (P : Kernel X X) (μ : Measure X) (r : ℝ≥0∞) (x : X) :
    ∑' n, r ^ n * fNorm V ((P ^ n) x) μ ≤ (∑' n, r ^ n * vErgDist V P μ n) * V x := by
  have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (fNorm_pow_le_vErgDist_mul P μ n hV0 (hVt x))

/-! ### The counterexample to Theorem 16.0.1 (i) as printed -/

/-- The step of the counterexample chain on `ℕ`: `0 ↦ 0`, odd `k ↦ k + 1`, even `k ≥ 2 ↦ 0`. -/
def twoStep (k : ℕ) : ℕ := if Odd k then k + 1 else 0

/-- The deterministic counterexample chain `P(k, ·) = δ_{twoStep k}`. -/
noncomputable def twoStepKernel : Kernel ℕ ℕ :=
  Kernel.deterministic twoStep (measurable_of_countable _)

/-- The weight of the counterexample: `V(k) = 1` for odd `k`, `V(k) = k + 1` otherwise. -/
noncomputable def twoStepWeight (k : ℕ) : ℝ≥0∞ := if Odd k then 1 else (k : ℝ≥0∞) + 1

/-- The counterexample chain is a Markov kernel. -/
theorem isMarkovKernel_twoStepKernel : IsMarkovKernel twoStepKernel := by
  unfold twoStepKernel; infer_instance

/-- Two steps of `twoStep` always reach `0`. -/
theorem twoStep_twoStep (k : ℕ) : twoStep (twoStep k) = 0 := by
  unfold twoStep
  by_cases hk : Odd k
  · have : ¬ Odd (k + 1) := by rw [Nat.not_odd_iff_even]; exact hk.add_one
    simp [hk, this]
  · simp [hk]

/-- `Pⁿ⁺²(k, ·) = δ₀` for the counterexample chain. -/
theorem twoStepKernel_pow_add_two (n : ℕ) (k : ℕ) :
    (twoStepKernel ^ (n + 2)) k = Measure.dirac 0 := by
  have hP : ∀ j, twoStepKernel j = Measure.dirac (twoStep j) := fun j =>
    Kernel.deterministic_apply _ j
  induction n generalizing k with
  | zero =>
    rw [pow_two]
    change (twoStepKernel ∘ₖ twoStepKernel) k = _
    rw [Kernel.comp_apply, hP, Measure.dirac_bind twoStepKernel.measurable, hP, twoStep_twoStep]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]
    change ((twoStepKernel ^ (n + 2)) ∘ₖ twoStepKernel) k = _
    rw [Kernel.comp_apply, hP, Measure.dirac_bind (twoStepKernel ^ (n + 2)).measurable, ih]

/-- The weight of the counterexample is at least `1` and finite. -/
theorem twoStepWeight_mem (k : ℕ) : 1 ≤ twoStepWeight k ∧ twoStepWeight k ≠ ∞ := by
  unfold twoStepWeight
  split_ifs
  · exact ⟨le_rfl, ENNReal.one_ne_top⟩
  · exact ⟨le_add_self, ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩⟩

/-- `δ₀` is invariant for the counterexample chain. -/
theorem isInvariant_twoStepKernel : IsInvariant twoStepKernel (Measure.dirac 0) := by
  unfold IsInvariant
  rw [dirac_kernel, twoStepKernel, Kernel.deterministic_apply]
  rfl

/-- `|||Pⁿ − 1 ⊗ δ₀|||_V = 0` for `n ≥ 2`. -/
theorem twoStep_vErgDist_add_two (n : ℕ) :
    vErgDist twoStepWeight twoStepKernel (Measure.dirac 0) (n + 2) = 0 := by
  refine le_antisymm (vOpNorm_le fun x => ?_) zero_le
  rw [twoStepKernel_pow_add_two, Kernel.const_apply, fNorm_self, zero_mul]

/-- `|||P − 1 ⊗ δ₀|||_V = ∞`: from the odd state `k` the chain jumps to `k + 1`, where
`V = k + 2`, while `V(k) = 1`. -/
theorem twoStep_vErgDist_one : vErgDist twoStepWeight twoStepKernel (Measure.dirac 0) 1 = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun N => ?_
  obtain ⟨j, hj⟩ := exists_nat_ge (N : ℝ)
  set k := 2 * j + 1 with hk
  have hkodd : Odd k := ⟨j, rfl⟩
  have hk1 : ¬ Odd (k + 1) := by rw [Nat.not_odd_iff_even]; exact hkodd.add_one
  set g : ℕ → ℝ := fun y => if y = k + 1 then ((k : ℝ) + 2) else 0 with hg
  have hgtest : IsFTest twoStepWeight (Measure.dirac (k + 1)) (Measure.dirac 0) g := by
    refine ⟨measurable_of_countable _, fun y => ?_, integrable_dirac enorm_lt_top,
      integrable_dirac enorm_lt_top⟩
    by_cases hy : y = k + 1
    · subst hy
      simp only [hg, ite_true, twoStepWeight, hk1, ite_false]
      rw [abs_of_nonneg (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num)]
      push_cast
      rw [ENNReal.ofReal_natCast]
      norm_num [add_assoc]
    · simp [hg, hy]
  have hkey := ofReal_abs_integral_sub_le_fNorm hgtest
  rw [integral_dirac, integral_dirac] at hkey
  have hval : g (k + 1) - g 0 = (k : ℝ) + 2 := by simp [hg]
  rw [hval] at hkey
  have hrow : fNorm twoStepWeight (twoStepKernel k) (Measure.dirac 0) / twoStepWeight k ≤
      vErgDist twoStepWeight twoStepKernel (Measure.dirac 0) 1 := by
    have := le_iSup (fun x => fNorm twoStepWeight ((twoStepKernel ^ 1) x)
      ((Kernel.const ℕ (Measure.dirac 0)) x) / twoStepWeight x) k
    unfold vErgDist vOpNorm
    simpa [pow_one, Kernel.const_apply] using this
  have hPk : twoStepKernel k = Measure.dirac (k + 1) := by
    rw [twoStepKernel, Kernel.deterministic_apply, twoStep]; simp [hkodd]
  have hVk : twoStepWeight k = 1 := by simp [twoStepWeight, hkodd]
  rw [hPk, hVk, div_one] at hrow
  refine le_trans ?_ (hkey.trans hrow)
  rw [abs_of_nonneg (by positivity)]
  have : (N : ℝ) ≤ (k : ℝ) + 2 := by rw [hk]; push_cast; linarith
  calc (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by simp
    _ ≤ ENNReal.ofReal ((k : ℝ) + 2) := ENNReal.ofReal_le_ofReal this

/-- **The counterexample to Theorem 16.0.1 as printed** ((i) ⇏ (ii)): the chain `twoStepKernel` is
`ψ`-irreducible and aperiodic, `δ₀` is invariant, `|||Pⁿ − 1 ⊗ δ₀|||_V → 0` (it vanishes for
`n ≥ 2`), but no bound `|||Pⁿ − 1 ⊗ δ₀|||_V ≤ R r⁻ⁿ` holds, since the distance is infinite at
`n = 1`. -/
theorem theorem_16_0_1_counterexample :
    haveI := isMarkovKernel_twoStepKernel
    ∃ ψ : Measure ℕ, IsMaximalIrreducibility twoStepKernel ψ ∧ IsAperiodic twoStepKernel ψ ∧
      IsVUniformlyErgodic twoStepWeight twoStepKernel (Measure.dirac 0) ∧
      ¬ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
        ∀ n, vErgDist twoStepWeight twoStepKernel (Measure.dirac 0) n ≤ R * r⁻¹ ^ n := by
  have := isMarkovKernel_twoStepKernel
  have hP : ∀ j, twoStepKernel j = Measure.dirac (twoStep j) := fun j =>
    Kernel.deterministic_apply _ j
  -- `δ₀` is an irreducibility measure
  have hφ : IsPhiIrreducible twoStepKernel (Measure.dirac 0) := by
    intro A hA hpos x
    have h0A : (0 : ℕ) ∈ A := by
      by_contra h
      rw [Measure.dirac_apply' 0 hA, Set.indicator_of_notMem h] at hpos
      exact lt_irrefl _ hpos
    refine (hitProb_pos_iff twoStepKernel hA x).2 ⟨1, ?_⟩
    rw [twoStepKernel_pow_add_two 0 x, Measure.dirac_apply_of_mem h0A]
    exact zero_lt_one
  set ψ := maxIrrMeasure twoStepKernel (Measure.dirac 0)
  have hψ : IsMaximalIrreducibility twoStepKernel ψ :=
    isMaximalIrreducibility_maxIrrMeasure twoStepKernel hφ (Measure.dirac_ne_zero)
  have hψ0 : 0 < ψ {0} := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := hψ.2.2 _ hφ h0
    simp at this
  let M : Minorization twoStepKernel :=
    { C := {0}
      δ := 2⁻¹
      ν := Measure.dirac 0
      measurableSet_C := measurableSet_singleton 0
      δ_pos := by simp
      δ_lt_one := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
      isProbabilityMeasure_ν := inferInstance
      le := fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hP]
        have : twoStep 0 = 0 := by simp [twoStep]
        rw [this]
        exact Measure.le_intro fun A _ _ => by
          rw [Measure.smul_apply, smul_eq_mul]
          exact mul_le_of_le_one_left' (ENNReal.inv_le_one.2 one_le_two) }
  have hap : IsAperiodic twoStepKernel ψ :=
    isAperiodic_of_minorization hψ M hψ0 (by simp [M])
  refine ⟨ψ, hψ, hap, ⟨isInvariant_twoStepKernel, ?_⟩, ?_⟩
  · refine tendsto_atTop_of_eventually_const (i₀ := 2) fun n hn => ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact twoStep_vErgDist_add_two k
  · rintro ⟨r, hr, R, hR, hb⟩
    have h1 := hb 1
    rw [twoStep_vErgDist_one, top_le_iff] at h1
    exact ENNReal.mul_ne_top hR (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne')) h1

end MeynTweedie.VUniformErgodicity
