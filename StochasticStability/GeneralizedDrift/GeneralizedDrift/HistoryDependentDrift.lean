/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.StateDependentDrift
import GeneralizedDrift.CompactPetite
import GeneralizedDrift.NonPositivity

/-!
# History-dependent drift criteria (MT §19.2)

Meyn and Tweedie, §19.2, pp. 491–498. The test functions are a sequence `Vₖ = Vₖ(Φ₀, …, Φₖ)`,
written here as functions `Vs k : (ℕ → X) → ·` on path space; adaptedness to `𝓕ₖ^Φ` is used only
through the drift hypotheses, which are stated in integrated form: `E[V_{k+1} | 𝓕ₖ^Φ] ≤ Vₖ` on
`{σ_C > k}` is `∫_G V_{k+1} ≤ ∫_G Vₖ` for every `G ∈ 𝓕ₖ^Φ` with `G ⊆ {σ_C > k}`
(`avoidSet C (k + 1)`). "Almost surely `[P_*]`" is "under every `P_x`".

**Results.**
* **Theorem 19.2.1** (`theorem_19_2_1`, p. 492): the generalized negative drift (19.32) gives
  `E_x[τ_C] ≤ ε⁻¹ V₀(x)` off `C` and `≤ 1 + ε⁻¹ PV₀(x)` on `C`; `theorem_19_2_1_regular`: with
  `C` petite and `PV₀` bounded on `C`, the chain is regular.
* **Theorem 19.2.2** (`theorem_19_2_2`, p. 493): the generalized positive drift (19.33) with
  (19.34) and the bounded increments (19.35) gives `E_{x₀}[τ_C] = ∞`.
* **Theorem 19.2.3** (`theorem_19_2_3`, p. 493): for an aperiodic `ψ`-irreducible T-chain, the
  generalized geometric drift (19.37) for a coercive sequence with `V₀` bounded on compacta gives
  positivity and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R (V₀(x) + 1)`, `f = V + 1`. The steps are
  `geomDrift_arith` and `setLIntegral_geomDrift_le` (the drift `ρVₖ − εf(Φₖ)` off
  `C = {V ≤ 2L/(ρ − λ) + 1}`) and `geomSum_le_of_genGeomDrift` (the Dynkin argument for `rᵏVₖ`),
  then Theorem 15.4.1. `theorem_19_2_3_driftV4`: the same set gives, by Theorem 15.2.4 and
  Theorem 11.3.4, an everywhere finite `W ≥ f` solving (V4) for a petite set, and the chain is
  positive Harris (the form used for the limit theorems of Theorem 19.2.6).
* `ae_bdd_of_avoid_seq`: the killed sequence `Vₖ 1{σ_C ≥ k}` of (19.38) is a nonnegative
  supermartingale, so `Vₖ` stays bounded on `{σ_C = ∞}`.
* **Theorem 19.2.4** (`theorem_19_2_4`, p. 494): the generalized non-positive drift (19.38) for
  a coercive sequence and a compact `C` gives non-evanescence; `theorem_19_2_4_harris`: for a
  `ψ`-irreducible T-chain, Harris recurrence.
* **Theorem 19.2.5** (`theorem_19_2_5`, p. 495): the generalized non-negative drift (19.40) for
  `0 ≤ Vₖ ≤ L` with `Vₖ ≤ M` at `σ_A = k` gives `P_x{σ_A = ∞} ≥ (V₀(x) − M)/(L − M)`;
  `theorem_19_2_5_transient`: if `A` and `{V₀ > M}` are in `B⁺(X)`, the chain is transient.

**Hypotheses.**
* Theorem 19.2.1: `ε < ∞` (the book's `ε > 0` is real).
* Theorem 19.2.2: (19.34) is used in its almost sure form under `P_{x₀}`,
  `Vₖ < V₀(x₀)` whenever `Φₖ ∈ C`; the book states it for every path from `x₀`, which implies the
  almost sure form when singletons are measurable. (19.33) and (19.35) are only needed under
  `P_{x₀}`.
* Theorem 19.2.3: `V₀ = v(Φ₀)` with `v` bounded on compact sets (the book's "`V₀` uniformly
  bounded on compact subsets"); `V` is measurable and `X` is countably generated, Hausdorff.
* Theorem 19.2.5: the book's `Vₖ` are non-negative (`Vₖ : X^{k+1} → ℝ₊`), and this is assumed.

**Elsewhere.** Theorem 19.2.6 (the dependent parameter bilinear model, pp. 496–498), with the
three conditional bounds the book takes from [275], is in `BilinearDrift`.

**Corrections.**
* Theorem 19.2.5: the book's proof uses Kolmogorov's inequality; only the submartingale
  inequality `E[M_n] ≥ E[M₀]` and `Mₙ ≤ L 1{σ_A ≥ n} + M 1{σ_A < n}` are needed, and the proof
  here is that argument.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Preliminaries -/

omit [MeasurableSpace X] in
/-- `k < t` iff `k + 1 ≤ t` in `ℕ ∪ {∞}`. -/
theorem coe_lt_iff_succ_le (k : ℕ) (t : WithTop ℕ) :
    (k : WithTop ℕ) < t ↔ WithTop.some (k + 1) ≤ t := by
  cases t with
  | top => exact ⟨fun _ => le_top, fun _ => WithTop.coe_lt_top k⟩
  | coe m => exact ⟨fun h => WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 h),
      fun h => WithTop.coe_lt_coe.2 (WithTop.coe_le_coe.1 h)⟩

omit [MeasurableSpace X] in
/-- `{σ_C > k} = {Φ₀, …, Φₖ ∉ C}`. -/
theorem lt_firstHit_iff_mem_avoidSet (C : Set X) (ω : ℕ → X) (k : ℕ) :
    (k : WithTop ℕ) < firstHit C ω ↔ ω ∈ avoidSet C (k + 1) := by
  rw [coe_lt_iff_succ_le, le_firstHit_iff]
  rfl

omit [MeasurableSpace X] in
/-- `{σ_C = ∞} = ⋂ₖ {σ_C ≥ k}`. -/
theorem firstHit_eq_top_iff (C : Set X) (ω : ℕ → X) :
    firstHit C ω = ⊤ ↔ ∀ k, ω ∈ avoidSet C k := by
  constructor
  · intro h k i _ hi
    have := (le_firstHit_iff C ω (i + 1)).1 (by rw [h]; exact le_top) i (Nat.lt_succ_self i)
    exact this hi
  · intro h
    by_contra hne
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
    have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := C)
      (n := 0) (ω := ω) hne
    rw [← firstHit, ← ht] at hmem
    exact h (t + 1) t (Nat.lt_succ_self t) hmem

/-! ### Theorem 19.2.1 -/

/-- **The generalized negative drift bound** (MT p. 492): if
`E[V_{k+1} | 𝓕ₖ^Φ] ≤ Vₖ − ε` on `{σ_C > k}` under `P_x` (19.32), then
`E_x[σ_C] ≤ ε⁻¹ E_x[V₀]`. -/
theorem meanHitTime_le_of_genNegDrift (P : Kernel X X) [IsMarkovKernel P]
    {Vs : ℕ → (ℕ → X) → ℝ≥0∞} {C : Set X} (hC : MeasurableSet C) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hεt : ε ≠ ∞) (x : X)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P x + ε * pathKernel P x G ≤
        ∫⁻ ω in G, Vs k ω ∂pathKernel P x) :
    meanHitTime P C x ≤ ε⁻¹ * ∫⁻ ω, Vs 0 ω ∂pathKernel P x := by
  have hσ := (proposition_3_4_4 hC).2
  have hτ : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < firstHit C ω} := fun n =>
    (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hσ n)
  have hcomp := comparison_lintegral (pathKernel P x) hτ (Z := Vs) (F := fun _ _ => ε)
    (S := fun _ _ => 0) (fun _ => measurable_const) (fun _ => measurable_const) fun n => by
      have hG := measurableSet_lt_of_isStoppingTime hσ n
      have hsub : {ω : ℕ → X | (n : WithTop ℕ) < firstHit C ω} ⊆ avoidSet C (n + 1) :=
        fun ω hω => (lt_firstHit_iff_mem_avoidSet C ω n).1 hω
      rw [setLIntegral_const, setLIntegral_const, zero_mul, add_zero]
      exact hdrift n _ hG hsub
  have hsum : ∀ ω : ℕ → X, sumBefore (firstHit C) (fun _ _ => ε) ω =
      ε * ENat.toENNReal (firstHit C ω) := fun ω => by
    rw [toENNReal_eq_sumBefore_one, ← sumBefore_const_mul]
    simp only [mul_one]
  simp_rw [hsum] at hcomp
  rw [lintegral_const_mul _ (measurable_toENNReal_firstHit hC)] at hcomp
  have hS : ∫⁻ ω, sumBefore (firstHit C) (fun _ _ => (0 : ℝ≥0∞)) ω ∂pathKernel P x = 0 := by
    simp [sumBefore]
  rw [hS, add_zero] at hcomp
  calc meanHitTime P C x = ε⁻¹ * (ε * meanHitTime P C x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hε hεt, one_mul]
    _ ≤ ε⁻¹ * ∫⁻ ω, Vs 0 ω ∂pathKernel P x := mul_le_mul' le_rfl hcomp

/-- **Theorem 19.2.1** (MT p. 492): if the adapted sequence `Vₖ`, with `V₀ = v(Φ₀)`, satisfies
the generalized negative drift condition (19.32), `E[V_{k+1} | 𝓕ₖ^Φ] ≤ Vₖ − ε` on
`{σ_C > k}` under every `P_y`, then `E_x[τ_C] ≤ ε⁻¹ v(x)` for `x ∉ C` and
`E_x[τ_C] ≤ 1 + ε⁻¹ ∫ P(x, dy) v(y)` for `x ∈ C`. The proof is the book's (Proposition 11.3.3
with `Zₖ = Vₖ`, `εₖ = ε`), the bound on `C` through `τ_C = 1 + σ_C ∘ θ`. -/
theorem theorem_19_2_1 (P : Kernel X X) [IsMarkovKernel P] {Vs : ℕ → (ℕ → X) → ℝ≥0∞}
    {v : X → ℝ≥0∞} (hv : Measurable v) (hV0 : ∀ ω, Vs 0 ω = v (ω 0)) {C : Set X}
    (hC : MeasurableSet C) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεt : ε ≠ ∞)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P y + ε * pathKernel P y G ≤
        ∫⁻ ω in G, Vs k ω ∂pathKernel P y) :
    (∀ x ∉ C, meanReturnTime P C x ≤ ε⁻¹ * v x) ∧
      ∀ x ∈ C, meanReturnTime P C x ≤ 1 + ε⁻¹ * ∫⁻ y, v y ∂P x := by
  have hhit : ∀ y, meanHitTime P C y ≤ ε⁻¹ * v y := fun y => by
    have h := meanHitTime_le_of_genNegDrift P hC hε hεt y (hdrift y)
    simp_rw [hV0] at h
    rwa [lintegral_coord_zero P y hv] at h
  refine ⟨fun x hx => ?_, fun x _ => ?_⟩
  · rw [← meanHitTime_of_notMem P hC hx]; exact hhit x
  · rw [meanReturnTime_eq_one_add P hC x, ← lintegral_const_mul _ hv]
    exact add_le_add le_rfl (lintegral_mono hhit)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.2.1, regularity** (MT p. 492): if moreover `C` is petite, `v` is finite and
`sup_{x ∈ C} E_x[V₀(Φ₁)] < ∞`, the chain is regular (Theorem 11.3.15). -/
theorem theorem_19_2_1_regular {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {Vs : ℕ → (ℕ → X) → ℝ≥0∞} {v : X → ℝ≥0∞}
    (hv : Measurable v) (hvfin : ∀ x, v x ≠ ∞) (hV0 : ∀ ω, Vs 0 ω = v (ω 0)) {C : Set X}
    (hC : IsPetite P C) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεt : ε ≠ ∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hPv : ∀ x ∈ C, ∫⁻ y, v y ∂P x ≤ K)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P y + ε * pathKernel P y G ≤
        ∫⁻ ω in G, Vs k ω ∂pathKernel P y) :
    IsRegularChain P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨hoff, hon⟩ := theorem_19_2_1 P hv hV0 hCm hε hεt hdrift
  have hεi : ε⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hε
  have hon' : ∀ x ∈ C, meanReturnTime P C x ≤ 1 + ε⁻¹ * K := fun x hx =>
    (hon x hx).trans (add_le_add le_rfl (mul_le_mul' le_rfl (hPv x hx)))
  have hM : 1 + ε⁻¹ * K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hεi hK⟩
  refine (theorem_11_3_15 hψ).2.2 ⟨C, hC, fun x => ?_, 1 + ε⁻¹ * K, hM, hon'⟩
  by_cases hx : x ∈ C
  · exact ne_top_of_le_ne_top hM (hon' x hx)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hεi (hvfin x)) (hoff x hx)

/-! ### Theorem 19.2.2 -/

/-- **Theorem 19.2.2** (MT p. 493): suppose that under `P_{x₀}`, `x₀ ∉ C`, the real adapted
sequence `Vₖ` with `V₀ = v(Φ₀)` satisfies the generalized positive drift condition (19.33),
`E[V_{k+1} | 𝓕ₖ^Φ] ≥ Vₖ` on `{σ_C > k}`, has conditional increments bounded in mean (19.35),
`E[|V_{k+1} − Vₖ| | 𝓕ₖ^Φ] ≤ B`, and satisfies (19.34), `Vₖ < v(x₀)` whenever `Φₖ ∈ C`. Then
`E_{x₀}[τ_C] = ∞`. The proof is that of Theorem 11.5.1: if `E_{x₀}[σ_C] < ∞`, the sum
`Σ_{k<σ_C} (V_{k+1} − Vₖ) = V_{σ_C} − V₀` is integrable with non-negative mean, while it is
negative almost surely. -/
theorem theorem_19_2_2 (P : Kernel X X) [IsMarkovKernel P] {Vs : ℕ → (ℕ → X) → ℝ}
    (hVs : ∀ k, Measurable (Vs k)) {v : X → ℝ} (hV0 : ∀ ω, Vs 0 ω = v (ω 0)) {C : Set X}
    (hC : MeasurableSet C) {x₀ : X} (hx₀C : x₀ ∉ C)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫ ω in G, Vs k ω ∂pathKernel P x₀ ≤ ∫ ω in G, Vs (k + 1) ω ∂pathKernel P x₀)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G →
      ∫⁻ ω in G, ‖Vs (k + 1) ω - Vs k ω‖ₑ ∂pathKernel P x₀ ≤ B * pathKernel P x₀ G)
    (h34 : ∀ᵐ ω ∂pathKernel P x₀, ∀ k, ω k ∈ C → Vs k ω < v x₀) :
    meanReturnTime P C x₀ = ∞ := by
  have := isMarkovKernel_pathKernel P
  set μ := pathKernel P x₀ with hμ
  have hv : Measurable v := by
    have : v = fun y => Vs 0 (fun _ => y) := funext fun y => (hV0 fun _ => y).symm
    rw [this]; exact (hVs 0).comp (measurable_pi_iff.2 fun _ => measurable_id)
  by_contra hfin
  have hσ := (proposition_3_4_4 hC).2
  have hGk := measurableSet_lt_of_isStoppingTime hσ
  have hG : ∀ k : ℕ, MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstHit C ω} :=
    fun k => (natFilt (X := X)).le k _ (hGk k)
  have hGsub : ∀ k : ℕ, {ω : ℕ → X | (k : WithTop ℕ) < firstHit C ω} ⊆ avoidSet C (k + 1) :=
    fun k ω hω => (lt_firstHit_iff_mem_avoidSet C ω k).1 hω
  have hEσ : ∫⁻ ω, ENat.toENNReal (firstHit C ω) ∂μ ≠ ∞ := by
    change meanHitTime P C x₀ ≠ ∞; rwa [meanHitTime_of_notMem P hC hx₀C]
  -- each `Vₖ` is integrable
  have hVint : ∀ k, Integrable (Vs k) μ := by
    intro k
    refine ⟨(hVs k).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hb : ∀ k, ∫⁻ ω, ‖Vs k ω‖ₑ ∂μ ≤ ‖v x₀‖ₑ + k * B := by
      intro k
      induction k with
      | zero =>
        simp_rw [hV0]
        rw [lintegral_coord_zero P x₀ hv.enorm]
        simp
      | succ k ih =>
        calc ∫⁻ ω, ‖Vs (k + 1) ω‖ₑ ∂μ ≤ ∫⁻ ω, (‖Vs (k + 1) ω - Vs k ω‖ₑ + ‖Vs k ω‖ₑ) ∂μ :=
              lintegral_mono fun ω => by
                calc ‖Vs (k + 1) ω‖ₑ = ‖(Vs (k + 1) ω - Vs k ω) + Vs k ω‖ₑ := by
                      rw [sub_add_cancel]
                  _ ≤ _ := enorm_add_le _ _
          _ = ∫⁻ ω, ‖Vs (k + 1) ω - Vs k ω‖ₑ ∂μ + ∫⁻ ω, ‖Vs k ω‖ₑ ∂μ :=
              lintegral_add_left ((hVs (k + 1)).sub (hVs k)).enorm _
          _ ≤ B + (‖v x₀‖ₑ + k * B) := by
              refine add_le_add ?_ ih
              have := hinc k univ MeasurableSet.univ
              rwa [Measure.restrict_univ, measure_univ, mul_one] at this
          _ = ‖v x₀‖ₑ + (k + 1 : ℕ) * B := by push_cast; ring
    exact (hb k).trans_lt (ENNReal.add_lt_top.2 ⟨enorm_lt_top,
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top k) hB.lt_top⟩)
  -- the increments before `σ_C`
  set F : ℕ → (ℕ → X) → ℝ := fun k => {ω | (k : WithTop ℕ) < firstHit C ω}.indicator
    fun ω => Vs (k + 1) ω - Vs k ω with hFdef
  have hDm : ∀ k, Measurable fun ω : ℕ → X => Vs (k + 1) ω - Vs k ω := fun k =>
    (hVs (k + 1)).sub (hVs k)
  have hFm : ∀ k, Measurable (F k) := fun k => (hDm k).indicator (hG k)
  have hDnorm : ∀ k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstHit C ω},
      ‖Vs (k + 1) ω - Vs k ω‖ₑ ∂μ ≤ B * μ {ω | (k : WithTop ℕ) < firstHit C ω} := fun k =>
    hinc k _ (hGk k)
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
  -- each increment has non-negative mean, by (19.33)
  have hFpos : ∀ k, 0 ≤ ∫ ω, F k ω ∂μ := fun k => by
    rw [hFdef, integral_indicator (hG k), integral_sub (hVint (k + 1)).integrableOn
      (hVint k).integrableOn, sub_nonneg]
    exact hdrift k _ (hGk k) (hGsub k)
  -- `σ_C < ∞` and `V₀ = v(x₀)`, almost surely
  have hae_fin : ∀ᵐ ω ∂μ, firstHit C ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_toENNReal_firstHit hC) hEσ] with ω hω
    intro h
    rw [h, show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top] at hω
    exact lt_irrefl _ hω
  have hae0 : ∀ᵐ ω ∂μ, v (ω 0) = v x₀ := by
    have hm : MeasurableSet {y | v y ≠ v x₀} := (measurableSet_singleton _).compl.preimage hv
    have h0 : μ {ω | ω 0 ∈ {y | v y ≠ v x₀}} = 0 := by
      rw [hμ, pathKernel_zero_mem P x₀ hm, indicator_of_notMem (by simp)]
    exact measure_mono_null (fun ω hω => hω) h0
  have hsupp : ∀ ω (t : ℕ), firstHit C ω = WithTop.some t → ∀ k ∉ Finset.range t, F k ω = 0 :=
    fun ω t ht k hk => by
      refine indicator_of_notMem (fun h => hk (Finset.mem_range.2 ?_)) _
      have h' : (k : WithTop ℕ) < WithTop.some t := ht ▸ h
      rw [Nat.cast_withTop] at h'
      exact WithTop.coe_lt_coe.1 h'
  -- the telescoped sum is negative almost surely
  have hneg : ∀ᵐ ω ∂μ, ∑' k, F k ω < 0 := by
    filter_upwards [hae_fin, hae0, h34] with ω hω h0 h34ω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    have hF : ∀ k ∈ Finset.range t, F k ω = Vs (k + 1) ω - Vs k ω := fun k hk => by
      refine indicator_of_mem (s := {ω | (k : WithTop ℕ) < firstHit C ω})
        (show (k : WithTop ℕ) < firstHit C ω by
        rw [← ht, Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 (Finset.mem_range.1 hk)) _
    rw [Finset.sum_congr rfl hF, Finset.sum_range_sub (fun k => Vs k ω), hV0, h0, sub_neg]
    exact h34ω t (mem_of_firstHit_eq ht.symm)
  have hnorm : ∀ᵐ ω ∂μ, ‖∑' k, F k ω‖ₑ ≤ ∑' k, ‖F k ω‖ₑ := by
    filter_upwards [hae_fin] with ω hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  have hDint : Integrable (fun ω => -∑' k, F k ω) μ := by
    refine ⟨(Measurable.tsum hFm).neg.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ ω, ‖-∑' k, F k ω‖ₑ ∂μ = ∫⁻ ω, ‖∑' k, F k ω‖ₑ ∂μ := by simp_rw [enorm_neg]
      _ ≤ ∫⁻ ω, ∑' k, ‖F k ω‖ₑ ∂μ := lintegral_mono_ae hnorm
      _ = ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ := lintegral_tsum fun k => (hFm k).enorm.aemeasurable
      _ < ∞ := hsum.lt_top
  have hle : ∫ ω, -∑' k, F k ω ∂μ ≤ 0 := by
    rw [integral_neg, integral_tsum (fun k => (hFm k).aestronglyMeasurable) hsum]
    exact neg_nonpos.2 (tsum_nonneg hFpos)
  have hpos_ae : ∀ᵐ ω ∂μ, 0 < -∑' k, F k ω := hneg.mono fun ω h => neg_pos.2 h
  have hgt : 0 < ∫ ω, -∑' k, F k ω ∂μ := by
    refine (integral_pos_iff_support_of_nonneg_ae (hpos_ae.mono fun ω h => h.le) hDint).2 ?_
    have hc : μ (Function.support fun ω => -∑' k, F k ω)ᶜ = 0 :=
      ae_iff.1 (hpos_ae.mono fun ω h => h.ne')
    by_contra h0
    have h0' : μ (Function.support fun ω => -∑' k, F k ω) = 0 :=
      nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have := measure_union_le (μ := μ) (Function.support fun ω => -∑' k, F k ω)
      (Function.support fun ω => -∑' k, F k ω)ᶜ
    rw [union_compl_self, measure_univ, h0', hc, add_zero] at this
    exact absurd this (by simp)
  linarith

/-! ### The killed sequence and Theorem 19.2.4 -/

/-- The killed sequence `Mₖ = Vₖ 1{σ_C ≥ k}` (MT p. 495), real valued. -/
noncomputable def killedSeq (Vs : ℕ → (ℕ → X) → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) : ℝ :=
  (avoidSet C k).indicator (fun ω => (Vs k ω : ℝ)) ω

/-- The killed sequence `Mₖ = Vₖ 1{σ_C ≥ k}`, `[0, ∞]`-valued. -/
noncomputable def killedSeqE (Vs : ℕ → (ℕ → X) → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) :
    ℝ≥0∞ :=
  (avoidSet C k).indicator (fun ω => (Vs k ω : ℝ≥0∞)) ω

omit [MeasurableSpace X] in
/-- `Mₖ ≥ 0`. -/
theorem killedSeq_nonneg (Vs : ℕ → (ℕ → X) → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) :
    0 ≤ killedSeq Vs C k ω :=
  indicator_nonneg (fun _ _ => NNReal.coe_nonneg _) ω

omit [MeasurableSpace X] in
/-- The two versions of `Mₖ` agree. -/
theorem ofReal_killedSeq (Vs : ℕ → (ℕ → X) → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) :
    ENNReal.ofReal (killedSeq Vs C k ω) = killedSeqE Vs C k ω := by
  unfold killedSeq killedSeqE
  by_cases h : ω ∈ avoidSet C k <;> simp [h]

/-- `Mₖ` is `𝓕ₖ^Φ`-measurable for an adapted sequence. -/
theorem measurable_natFilt_killedSeq {Vs : ℕ → (ℕ → X) → ℝ≥0}
    (hVs : ∀ k, Measurable[natFilt k] (Vs k)) {C : Set X} (hC : MeasurableSet C) (k : ℕ) :
    Measurable[natFilt k] (killedSeq Vs C k) :=
  (measurable_coe_nnreal_real.comp (hVs k)).indicator
    (measurableSet_natFilt_avoidSet hC (Nat.le_succ k))

/-- **The supermartingale inequality for the killed sequence** (MT p. 495): under (19.38),
`∫_G M_{k+1} ≤ ∫_G Mₖ` for `G ∈ 𝓕ₖ^Φ`. -/
theorem setLIntegral_killedSeqE_succ_le (pr : Measure (ℕ → X)) {Vs : ℕ → (ℕ → X) → ℝ≥0}
    {C : Set X} (hC : MeasurableSet C)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, (Vs (k + 1) ω : ℝ≥0∞) ∂pr ≤ ∫⁻ ω in G, (Vs k ω : ℝ≥0∞) ∂pr)
    {k : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, killedSeqE Vs C (k + 1) ω ∂pr ≤ ∫⁻ ω in G, killedSeqE Vs C k ω ∂pr := by
  have hA1 : MeasurableSet[natFilt k] (avoidSet C (k + 1)) :=
    measurableSet_natFilt_avoidSet hC le_rfl
  unfold killedSeqE
  rw [setLIntegral_indicator (measurableSet_avoidSet hC (k + 1)),
    setLIntegral_indicator (measurableSet_avoidSet hC k)]
  calc ∫⁻ ω in avoidSet C (k + 1) ∩ G, (Vs (k + 1) ω : ℝ≥0∞) ∂pr
      ≤ ∫⁻ ω in avoidSet C (k + 1) ∩ G, (Vs k ω : ℝ≥0∞) ∂pr :=
        hdrift k _ (hA1.inter hG) inter_subset_left
    _ ≤ ∫⁻ ω in avoidSet C k ∩ G, (Vs k ω : ℝ≥0∞) ∂pr :=
        lintegral_mono_set (inter_subset_inter_left G (avoidSet_succ_subset C k))

/-- `E[Mₖ] ≤ E[V₀]`. -/
theorem lintegral_killedSeqE_le (pr : Measure (ℕ → X)) {Vs : ℕ → (ℕ → X) → ℝ≥0}
    {C : Set X} (hC : MeasurableSet C)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, (Vs (k + 1) ω : ℝ≥0∞) ∂pr ≤ ∫⁻ ω in G, (Vs k ω : ℝ≥0∞) ∂pr) (k : ℕ) :
    ∫⁻ ω, killedSeqE Vs C k ω ∂pr ≤ ∫⁻ ω, (Vs 0 ω : ℝ≥0∞) ∂pr := by
  induction k with
  | zero =>
    refine le_of_eq (lintegral_congr fun ω => ?_)
    simp [killedSeqE, avoidSet]
  | succ k ih =>
    have h := setLIntegral_killedSeqE_succ_le pr hC hdrift (k := k) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    exact h.trans ih

/-- **Bounded on `{σ_C = ∞}`** (MT p. 495): under the generalized non-positive drift (19.38) and
`E[V₀] < ∞`, the killed sequence `Mₖ = Vₖ 1{σ_C ≥ k}` is a nonnegative supermartingale, so it
converges almost surely; on `{σ_C = ∞}`, `Mₖ = Vₖ`, which therefore stays bounded. -/
theorem ae_bdd_of_avoid_seq (pr : Measure (ℕ → X)) [IsProbabilityMeasure pr]
    {Vs : ℕ → (ℕ → X) → ℝ≥0} (hVs : ∀ k, Measurable[natFilt k] (Vs k)) {C : Set X}
    (hC : MeasurableSet C)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, (Vs (k + 1) ω : ℝ≥0∞) ∂pr ≤ ∫⁻ ω in G, (Vs k ω : ℝ≥0∞) ∂pr)
    (hfin : ∫⁻ ω, (Vs 0 ω : ℝ≥0∞) ∂pr ≠ ∞) :
    ∀ᵐ ω ∂pr, (∀ i, ω i ∉ C) → ∃ r : ℝ, ∀ k, (Vs k ω : ℝ) ≤ r := by
  have hmeas : ∀ k, Measurable (killedSeq Vs C k) := fun k =>
    (measurable_natFilt_killedSeq hVs hC k).mono ((natFilt (X := X)).le k) le_rfl
  have henorm : ∀ k ω, ‖killedSeq Vs C k ω‖ₑ = killedSeqE Vs C k ω := fun k ω => by
    rw [← ofReal_killedSeq, Real.enorm_eq_ofReal (killedSeq_nonneg Vs C k ω)]
  have hint : ∀ k, Integrable (killedSeq Vs C k) pr := fun k => by
    refine ⟨(hmeas k).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [henorm]
    exact (lintegral_killedSeqE_le pr hC hdrift k).trans_lt hfin.lt_top
  have hset : ∀ k G, ∫ ω in G, killedSeq Vs C k ω ∂pr =
      (∫⁻ ω in G, killedSeqE Vs C k ω ∂pr).toReal := fun k G => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (killedSeq_nonneg Vs C k))
      (hmeas k).aestronglyMeasurable]
    simp_rw [ofReal_killedSeq]
  have hsup : Supermartingale (killedSeq Vs C) natFilt pr := by
    refine supermartingale_of_setIntegral_succ_le
      (fun k => (measurable_natFilt_killedSeq hVs hC k).stronglyMeasurable) hint
      fun k G hG => ?_
    rw [hset, hset]
    have hfin' : ∫⁻ ω in G, killedSeqE Vs C k ω ∂pr ≠ ∞ :=
      ne_top_of_le_ne_top hfin ((setLIntegral_le_lintegral _ _).trans
        (lintegral_killedSeqE_le pr hC hdrift k))
    exact ENNReal.toReal_mono hfin' (setLIntegral_killedSeqE_succ_le pr hC hdrift hG)
  have hbdd : ∀ k, eLpNorm ((-killedSeq Vs C) k) 1 pr ≤
      (∫⁻ ω, (Vs 0 ω : ℝ≥0∞) ∂pr).toNNReal := by
    intro k
    rw [ENNReal.coe_toNNReal hfin,
      eLpNorm_one_eq_lintegral_enorm ((hsup.neg.integrable k).aestronglyMeasurable)]
    have : ∀ ω, ‖(-killedSeq Vs C) k ω‖ₑ = killedSeqE Vs C k ω := fun ω => by
      rw [Pi.neg_apply, Pi.neg_apply, enorm_neg, henorm]
    simp_rw [this]
    exact lintegral_killedSeqE_le pr hC hdrift k
  filter_upwards [hsup.neg.exists_ae_tendsto_of_bdd hbdd] with ω ⟨c, hc⟩ hav
  have hc' := hc.neg
  simp only [Pi.neg_apply, neg_neg] at hc'
  have heq : (fun k => killedSeq Vs C k ω) = fun k => (Vs k ω : ℝ) := by
    funext k
    simp only [killedSeq]
    rw [indicator_of_mem (show ω ∈ avoidSet C k from fun i _ => hav i)]
  rw [heq] at hc'
  obtain ⟨r, hr⟩ := hc'.bddAbove_range
  exact ⟨r, fun k => hr (mem_range_self k)⟩

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- **Theorem 19.2.4** (MT p. 494): if an adapted coercive sequence `Vₖ` (`Vₖ ≥ V(Φₖ)` for a
coercive `V`, (19.36)) with `E_y[V₀] < ∞` satisfies the generalized non-positive drift
(19.38), `E[V_{k+1} | 𝓕ₖ^Φ] ≤ Vₖ` on `{σ_C > k}` under every `P_y`, for a compact `C`, then
the chain is non-evanescent. The proof is that of Theorem 9.4.1, with the killed sequence
(`ae_bdd_of_avoid_seq`) in place of `V(Φₖ) 1{σ_C ≥ k}`. -/
theorem theorem_19_2_4 {P : Kernel X X} [IsMarkovKernel P] {Vs : ℕ → (ℕ → X) → ℝ≥0}
    (hVs : ∀ k, Measurable[natFilt k] (Vs k)) {V : X → ℝ≥0} (hV : IsCoercive V)
    (hVV : ∀ k ω, V (ω k) ≤ Vs k ω) (hfin : ∀ y, ∫⁻ ω, (Vs 0 ω : ℝ≥0∞) ∂pathKernel P y ≠ ∞)
    {C : Set X} (hC : IsCompact C)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, (Vs (k + 1) ω : ℝ≥0∞) ∂pathKernel P y ≤
        ∫⁻ ω in G, (Vs k ω : ℝ≥0∞) ∂pathKernel P y) :
    IsNonEvanescent P := by
  have := isMarkovKernel_pathKernel P
  have hCm := hC.measurableSet
  set Av := {ω : ℕ → X | ∀ i, ω i ∉ C}
  have hAv : MeasurableSet Av := by
    have : Av = ⋂ i, {ω : ℕ → X | ω i ∈ Cᶜ} := by ext ω; simp [Av]
    rw [this]; exact MeasurableSet.iInter fun i => measurable_pi_apply i hCm.compl
  have hTm : MeasurableSet (tendsToInfty (X := X)) := measurableSet_tendsToInfty
  have step1 : ∀ y, pathKernel P y (Av ∩ tendsToInfty) = 0 := by
    intro y
    have h := ae_bdd_of_avoid_seq (pathKernel P y) hVs hCm (hdrift y) (hfin y)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω hmem
    obtain ⟨hav, hT⟩ := hmem
    obtain ⟨r, hr⟩ := hω hav
    refine hT _ (hV r.toNNReal) fun N => ⟨N, le_rfl, subset_closure ?_⟩
    change V (ω N) ≤ r.toNNReal
    rw [← Real.toNNReal_coe (r := V (ω N))]
    exact Real.toNNReal_le_toNNReal ((NNReal.coe_le_coe.2 (hVV N ω)).trans (hr N))
  intro x
  have hcov : tendsToInfty (X := X) ⊆ ⋃ M, shift M ⁻¹' (Av ∩ tendsToInfty) := by
    intro ω hω
    have hnio : ω ∉ ioSet C := hω C hC
    simp only [ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at hnio
    obtain ⟨M, hM⟩ := hnio
    refine mem_iUnion.2 ⟨M, ?_, (isShiftInvariant_tendsToInfty M ω).2 hω⟩
    intro i
    simp only [shift_apply]
    exact hM (M + i) (by omega)
  refine measure_mono_null hcov (measure_iUnion_null fun M => ?_)
  rw [pathKernel_shift_preimage P x M (hAv.inter hTm)]
  simp [step1]

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 19.2.4, Harris recurrence** (MT p. 494): for a `ψ`-irreducible T-chain, (19.38)
for a coercive sequence and a compact `C` gives Harris recurrence (Theorem 9.2.2). -/
theorem theorem_19_2_4_harris {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) {Vs : ℕ → (ℕ → X) → ℝ≥0}
    (hVs : ∀ k, Measurable[natFilt k] (Vs k)) {V : X → ℝ≥0} (hV : IsCoercive V)
    (hVV : ∀ k ω, V (ω k) ≤ Vs k ω) (hfin : ∀ y, ∫⁻ ω, (Vs 0 ω : ℝ≥0∞) ∂pathKernel P y ≠ ∞)
    {C : Set X} (hC : IsCompact C)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet C (k + 1) →
      ∫⁻ ω in G, (Vs (k + 1) ω : ℝ≥0∞) ∂pathKernel P y ≤
        ∫⁻ ω in G, (Vs k ω : ℝ≥0∞) ∂pathKernel P y) :
    IsHarris P ψ :=
  (theorem_9_2_2_ii hψ hT).2 (theorem_19_2_4 hVs hV hVV hfin hC hdrift)

/-! ### Theorem 19.2.5 -/

/-- **Theorem 19.2.5** (MT p. 495): suppose the adapted sequence `0 ≤ Vₖ ≤ L` with `V₀ = v(Φ₀)`
satisfies the generalized non-negative drift (19.40), `E[V_{k+1} | 𝓕ₖ^Φ] ≥ Vₖ` on `{σ_A > k}`
under `P_x`, and `Vₖ ≤ M < L` on `{σ_A = k}`. Then `P_x{σ_A = ∞} ≥ (v(x) − M)/(L − M)`.
The process `Mₖ = Vₖ` on `{σ_A ≥ k}` and `M` on `{σ_A < k}` is a submartingale. -/
theorem theorem_19_2_5 (P : Kernel X X) [IsMarkovKernel P] {Vs : ℕ → (ℕ → X) → ℝ}
    (hVs : ∀ k, Measurable (Vs k)) {v : X → ℝ} (hV0 : ∀ ω, Vs 0 ω = v (ω 0)) {A : Set X}
    (hA : MeasurableSet A) {L M : ℝ} (hLM : M < L) (hnn : ∀ k ω, 0 ≤ Vs k ω)
    (hL : ∀ k ω, Vs k ω ≤ L) (hM : ∀ (k : ℕ) ω, firstHit A ω = (k : WithTop ℕ) → Vs k ω ≤ M) (x : X)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet A (k + 1) →
      ∫ ω in G, Vs k ω ∂pathKernel P x ≤ ∫ ω in G, Vs (k + 1) ω ∂pathKernel P x) :
    ENNReal.ofReal ((v x - M) / (L - M)) ≤ pathKernel P x {ω | firstHit A ω = ⊤} := by
  have := isMarkovKernel_pathKernel P
  set μ := pathKernel P x with hμ
  have hv : Measurable v := by
    have : v = fun y => Vs 0 (fun _ => y) := funext fun y => (hV0 fun _ => y).symm
    rw [this]; exact (hVs 0).comp (measurable_pi_iff.2 fun _ => measurable_id)
  have hVint : ∀ k, Integrable (Vs k) μ := fun k =>
    Integrable.of_bound (hVs k).aestronglyMeasurable L (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn k ω)]; exact hL k ω)
  have hAm : ∀ k, MeasurableSet (avoidSet A k) := measurableSet_avoidSet hA
  set N : ℕ → (ℕ → X) → ℝ := fun k ω =>
    (avoidSet A k).indicator (Vs k) ω + (avoidSet A k)ᶜ.indicator (fun _ => M) ω with hNdef
  have hNint : ∀ k, Integrable (N k) μ := fun k =>
    ((hVint k).indicator (hAm k)).add ((integrable_const M).indicator (hAm k).compl)
  have hNint' : ∀ k, ∫ ω, N k ω ∂μ =
      ∫ ω in avoidSet A k, Vs k ω ∂μ + M * (μ (avoidSet A k)ᶜ).toReal := fun k => by
    rw [hNdef, integral_add ((hVint k).indicator (hAm k))
      ((integrable_const M).indicator (hAm k).compl), integral_indicator (hAm k),
      integral_indicator (hAm k).compl, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  -- `σ_A = k` on `{σ_A ≥ k} \ {σ_A ≥ k + 1}`
  have hhit : ∀ k (ω : ℕ → X), ω ∈ avoidSet A k → ω ∉ avoidSet A (k + 1) →
      firstHit A ω = k := by
    intro k ω h1 h2
    have hk : ω k ∈ A := by
      by_contra hk
      exact h2 fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact h1 i hi
        · rw [hi]; exact hk
    refine le_antisymm (hittingAfter_le_of_mem (Nat.zero_le k) hk) ?_
    exact (le_firstHit_iff A ω k).2 h1
  -- the submartingale inequality `E[Nₖ] ≤ E[N_{k+1}]`
  have hstep : ∀ k, ∫ ω, N k ω ∂μ ≤ ∫ ω, N (k + 1) ω ∂μ := by
    intro k
    have hpt : ∀ ω, N k ω ≤ (avoidSet A (k + 1)).indicator (Vs k) ω +
        (avoidSet A (k + 1))ᶜ.indicator (fun _ => M) ω := by
      intro ω
      by_cases h1 : ω ∈ avoidSet A (k + 1)
      · have h0 : ω ∈ avoidSet A k := avoidSet_succ_subset A k h1
        simp [hNdef, h0, h1]
      · by_cases h0 : ω ∈ avoidSet A k
        · simp only [hNdef, indicator_of_mem h0, indicator_of_notMem h1,
            indicator_of_mem (show ω ∈ (avoidSet A (k + 1))ᶜ from h1),
            indicator_of_notMem (show ω ∉ (avoidSet A k)ᶜ from fun h => h h0), add_zero,
            zero_add]
          exact hM k ω (hhit k ω h0 h1)
        · have h0' : ω ∈ (avoidSet A k)ᶜ := h0
          simp [hNdef, h0, h1, h0']
    have hint2 : Integrable (fun ω => (avoidSet A (k + 1)).indicator (Vs k) ω +
        (avoidSet A (k + 1))ᶜ.indicator (fun _ => M) ω) μ :=
      ((hVint k).indicator (hAm (k + 1))).add
        ((integrable_const M).indicator (hAm (k + 1)).compl)
    calc ∫ ω, N k ω ∂μ ≤ ∫ ω, ((avoidSet A (k + 1)).indicator (Vs k) ω +
          (avoidSet A (k + 1))ᶜ.indicator (fun _ => M) ω) ∂μ :=
          integral_mono (hNint k) hint2 hpt
      _ = ∫ ω in avoidSet A (k + 1), Vs k ω ∂μ + M * (μ (avoidSet A (k + 1))ᶜ).toReal := by
          rw [integral_add ((hVint k).indicator (hAm (k + 1)))
            ((integrable_const M).indicator (hAm (k + 1)).compl), integral_indicator (hAm (k + 1)),
            integral_indicator (hAm (k + 1)).compl, setIntegral_const, smul_eq_mul, mul_comm]
          rfl
      _ ≤ ∫ ω in avoidSet A (k + 1), Vs (k + 1) ω ∂μ + M * (μ (avoidSet A (k + 1))ᶜ).toReal :=
          add_le_add (hdrift k _ (measurableSet_natFilt_avoidSet hA le_rfl) subset_rfl) le_rfl
      _ = ∫ ω, N (k + 1) ω ∂μ := (hNint' (k + 1)).symm
  have hmono : ∀ n, ∫ ω, N 0 ω ∂μ ≤ ∫ ω, N n ω ∂μ := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact ih.trans (hstep n)
  have hN0 : ∫ ω, N 0 ω ∂μ = v x := by
    have h0 : ∀ ω, N 0 ω = v (ω 0) := fun ω => by
      have : ω ∈ avoidSet A 0 := fun i hi => absurd hi (Nat.not_lt_zero i)
      simp [hNdef, this, hV0]
    simp_rw [h0]
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hv.aestronglyMeasurable,
      pathKernel_map_zero, integral_dirac' _ _ hv.stronglyMeasurable]
  -- the upper bound `E[Nₙ] ≤ M + (L − M) P(σ_A ≥ n)`
  have hupper : ∀ n, ∫ ω, N n ω ∂μ ≤ M + (L - M) * (μ (avoidSet A n)).toReal := by
    intro n
    rw [hNint' n, prob_compl_eq_one_sub (hAm n), ENNReal.toReal_sub_of_le prob_le_one
      ENNReal.one_ne_top, ENNReal.toReal_one]
    have h1 : ∫ ω in avoidSet A n, Vs n ω ∂μ ≤ L * (μ (avoidSet A n)).toReal := by
      calc ∫ ω in avoidSet A n, Vs n ω ∂μ ≤ ∫ _ in avoidSet A n, L ∂μ :=
            setIntegral_mono (hVint n).integrableOn (integrable_const L).integrableOn (hL n)
        _ = L * (μ (avoidSet A n)).toReal := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
    linarith
  have hLM' : 0 < L - M := sub_pos.2 hLM
  have hq : ∀ n, (v x - M) / (L - M) ≤ (μ (avoidSet A n)).toReal := fun n => by
    rw [div_le_iff₀ hLM']
    have := (hN0.symm.le.trans (hmono n)).trans (hupper n)
    linarith
  have hiInter : {ω : ℕ → X | firstHit A ω = ⊤} = ⋂ n, avoidSet A n := by
    ext ω; simp only [mem_ofPred_eq, mem_iInter]; exact firstHit_eq_top_iff A ω
  rw [hiInter, Antitone.measure_iInter (antitone_nat_of_succ_le fun n => avoidSet_succ_subset A n)
    (fun n => (hAm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n => (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (hq n)

/-- **Theorem 19.2.5, transience** (MT p. 495): if (19.40) holds under every `P_x` and both `A`
and `{V₀ > M}` lie in `B⁺(X)`, the chain is transient. -/
theorem theorem_19_2_5_transient {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {Vs : ℕ → (ℕ → X) → ℝ} (hVs : ∀ k, Measurable (Vs k))
    {v : X → ℝ} (hV0 : ∀ ω, Vs 0 ω = v (ω 0)) {A : Set X} (hA : MeasurableSet A) {L M : ℝ}
    (hLM : M < L) (hnn : ∀ k ω, 0 ≤ Vs k ω) (hL : ∀ k ω, Vs k ω ≤ L)
    (hM : ∀ (k : ℕ) ω, firstHit A ω = (k : WithTop ℕ) → Vs k ω ≤ M)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G → G ⊆ avoidSet A (k + 1) →
      ∫ ω in G, Vs k ω ∂pathKernel P y ≤ ∫ ω in G, Vs (k + 1) ω ∂pathKernel P y)
    (hψA : 0 < ψ A) (hψv : 0 < ψ {x | M < v x}) : IsTransientChain P ψ := by
  have := isMarkovKernel_pathKernel P
  have hv : Measurable v := by
    have : v = fun y => Vs 0 (fun _ => y) := funext fun y => (hV0 fun _ => y).symm
    rw [this]; exact (hVs 0).comp (measurable_pi_iff.2 fun _ => measurable_id)
  refine (theorem_8_3_6_ii P hψ).2 ⟨A, {x | M < v x}, hA, measurableSet_lt measurable_const hv,
    hψA, hψv, fun x hx => ?_⟩
  have hb := theorem_19_2_5 P hVs hV0 hA hLM hnn hL hM x (hdrift x)
  have hpos : 0 < pathKernel P x {ω | firstHit A ω = ⊤} :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (div_pos (sub_pos.2 hx) (sub_pos.2 hLM))) hb
  have hEm : MeasurableSet {ω : ℕ → X | firstHit A ω = ⊤} := by
    have h := (measurableSet_ne_top (proposition_3_4_4 hA).2).compl
    convert h using 1
    ext ω; simp
  have hcompl : {ω : ℕ → X | firstHit A ω ≠ ⊤} = {ω | firstHit A ω = ⊤}ᶜ := by ext ω; simp
  calc hitProb P A x ≤ hitProbZero P A x := hitProb_le_hitProbZero P A x
    _ = 1 - pathKernel P x {ω | firstHit A ω = ⊤} := by
        rw [hitProbZero, hcompl, prob_compl_eq_one_sub hEm]
    _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'

/-! ### Theorem 19.2.3 -/

omit [MeasurableSpace X] in
/-- The arithmetic of the proof of Theorem 19.2.3 (MT p. 494): with `δ = ρ − λ`, `ε = δ/2` and
`c = 2L/δ + 1`, if `c ≤ w ≤ u` then `λu + L + ε(w + 1) ≤ ρu`. -/
theorem geomDrift_arith {lam ρ L w u : ℝ≥0∞} (hlr : lam ≤ ρ) (hδ : ρ - lam ≠ 0) (hρt : ρ ≠ ∞)
    (hcw : 2 * L * (ρ - lam)⁻¹ + 1 ≤ w) (hwu : w ≤ u) :
    lam * u + L + (ρ - lam) * 2⁻¹ * (w + 1) ≤ ρ * u := by
  set δ := ρ - lam with hδdef
  have hδt : δ ≠ ∞ := ENNReal.sub_ne_top hρt
  have hρ : ρ = lam + δ := (add_tsub_cancel_of_le hlr).symm
  have hεδ : δ * 2⁻¹ + δ * 2⁻¹ = δ := by
    rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  have hεL : δ * 2⁻¹ * (2 * L * δ⁻¹) = L := by
    calc δ * 2⁻¹ * (2 * L * δ⁻¹) = (δ * δ⁻¹) * (2⁻¹ * 2) * L := by ring
      _ = L := by
        rw [ENNReal.mul_inv_cancel hδ hδt, ENNReal.inv_mul_cancel two_ne_zero
          ENNReal.ofNat_ne_top, one_mul, one_mul]
  calc lam * u + L + δ * 2⁻¹ * (w + 1)
      = lam * u + δ * 2⁻¹ * (2 * L * δ⁻¹ + 1) + δ * 2⁻¹ * w := by
        rw [mul_add (δ * 2⁻¹) (2 * L * δ⁻¹), hεL]; ring
    _ ≤ lam * u + δ * 2⁻¹ * w + δ * 2⁻¹ * w :=
        add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hcw)) le_rfl
    _ = lam * u + δ * w := by rw [add_assoc, ← add_mul, hεδ]
    _ ≤ lam * u + δ * u := add_le_add le_rfl (mul_le_mul' le_rfl hwu)
    _ = ρ * u := by rw [hρ]; ring

/-- **The drift off `C`** in the proof of Theorem 19.2.3 (MT p. 494): if
`E[V_{k+1} | 𝓕ₖ^Φ] ≤ λVₖ + L` (19.37) and `Vₖ ≥ V(Φₖ) ≥ c` on `G`, then
`∫_G V_{k+1} + ε ∫_G f(Φₖ) ≤ ρ ∫_G Vₖ` with `f = V + 1`. -/
theorem setLIntegral_geomDrift_le (pr : Measure (ℕ → X)) {Vs : ℕ → (ℕ → X) → ℝ≥0∞}
    {V : X → ℝ≥0} (hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ Vs k ω) {lam ρ L : ℝ≥0∞} (hlr : lam ≤ ρ)
    (hδ : ρ - lam ≠ 0) (hρt : ρ ≠ ∞) {k : ℕ} {G : Set (ℕ → X)} (hGm : MeasurableSet G)
    (hG : ∀ ω ∈ G, 2 * L * (ρ - lam)⁻¹ + 1 ≤ V (ω k))
    (hdr : ∫⁻ ω in G, Vs (k + 1) ω ∂pr ≤ lam * ∫⁻ ω in G, Vs k ω ∂pr + L * pr G) :
    ∫⁻ ω in G, Vs (k + 1) ω ∂pr + (ρ - lam) * 2⁻¹ * ∫⁻ ω in G, ((V (ω k) : ℝ≥0∞) + 1) ∂pr ≤
      ρ * ∫⁻ ω in G, Vs k ω ∂pr := by
  have hlt : lam ≠ ∞ := ne_top_of_le_ne_top hρt hlr
  have hεt : (ρ - lam) * 2⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.sub_ne_top hρt) (ENNReal.inv_ne_top.2 two_ne_zero)
  calc ∫⁻ ω in G, Vs (k + 1) ω ∂pr + (ρ - lam) * 2⁻¹ * ∫⁻ ω in G, ((V (ω k) : ℝ≥0∞) + 1) ∂pr
      ≤ lam * ∫⁻ ω in G, Vs k ω ∂pr + L * pr G +
        (ρ - lam) * 2⁻¹ * ∫⁻ ω in G, ((V (ω k) : ℝ≥0∞) + 1) ∂pr := add_le_add hdr le_rfl
    _ = ∫⁻ ω in G, lam * Vs k ω ∂pr + ∫⁻ _ in G, L ∂pr +
        ∫⁻ ω in G, (ρ - lam) * 2⁻¹ * ((V (ω k) : ℝ≥0∞) + 1) ∂pr := by
        rw [lintegral_const_mul' _ _ hlt, lintegral_const_mul' _ _ hεt, setLIntegral_const]
    _ ≤ ∫⁻ ω in G, (lam * Vs k ω + L + (ρ - lam) * 2⁻¹ * ((V (ω k) : ℝ≥0∞) + 1)) ∂pr :=
        (add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ ω in G, ρ * Vs k ω ∂pr :=
        setLIntegral_mono' hGm fun ω hω => geomDrift_arith hlr hδ hρt (hG ω hω) (hVV k ω)
    _ = ρ * ∫⁻ ω in G, Vs k ω ∂pr := lintegral_const_mul' _ _ hρt

omit [MeasurableSpace X] in
/-- `Σ_{k<τ} Aₖ = A₀ + Σ_{1≤k<τ} Aₖ` when `τ ≥ 1`. -/
theorem sumBefore_eq_zero_add {τ : (ℕ → X) → WithTop ℕ} (A : ℕ → (ℕ → X) → ℝ≥0∞) {ω : ℕ → X}
    (hτ : (0 : WithTop ℕ) < τ ω) :
    sumBefore τ A ω = A 0 ω + sumBefore τ (fun k ω => if k = 0 then 0 else A k ω) ω := by
  have hsplit : sumBefore τ A ω = sumBefore τ (fun k ω => if k = 0 then A 0 ω else 0) ω +
      sumBefore τ (fun k ω => if k = 0 then 0 else A k ω) ω := by
    unfold sumBefore
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    by_cases hk : (k : WithTop ℕ) < τ ω
    · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
        indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
        indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk)]
      by_cases h0 : k = 0
      · subst h0; simp
      · simp [h0]
    · simp only [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk), add_zero]
  rw [hsplit]
  congr 1
  rw [sumBefore, tsum_eq_single 0 fun k hk => by simp [hk]]
  rw [indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : WithTop ℕ) < τ ω} from hτ)]
  simp

/-- **The comparison step of Theorem 19.2.3** (MT p. 494): under (19.37) for `P_x`, with
`C = {V ≤ 2L/(ρ − λ) + 1}`, `r = ρ⁻¹` and `f = V + 1`,
`E_x[Σ_{k<τ_C} f(Φₖ) rᵏ] ≤ f(x) + ε⁻¹ E_x[V₁]`. This is the book's Dynkin argument for
`Zₖ = rᵏ Vₖ`, started at time `1`. -/
theorem geomSum_le_of_genGeomDrift (P : Kernel X X) [IsMarkovKernel P]
    {Vs : ℕ → (ℕ → X) → ℝ≥0∞} (hVs : ∀ k, Measurable (Vs k)) {V : X → ℝ≥0} (hVm : Measurable V)
    (hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ Vs k ω) {lam ρ L : ℝ≥0∞} (hlr : lam ≤ ρ)
    (hδ : ρ - lam ≠ 0) (hρ0 : ρ ≠ 0) (hρt : ρ ≠ ∞) (x : X)
    (hdrift : ∀ k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P x ≤
        lam * ∫⁻ ω in G, Vs k ω ∂pathKernel P x + L * pathKernel P x G) :
    geomSum P {y | (V y : ℝ≥0∞) ≤ 2 * L * (ρ - lam)⁻¹ + 1} ρ⁻¹ (fun y => (V y : ℝ≥0∞) + 1) x ≤
      ((V x : ℝ≥0∞) + 1) + ((ρ - lam) * 2⁻¹)⁻¹ * ∫⁻ ω, Vs 1 ω ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  set c := 2 * L * (ρ - lam)⁻¹ + 1 with hc
  set C := {y | (V y : ℝ≥0∞) ≤ c} with hCdef
  have hCm : MeasurableSet C := measurableSet_le (measurable_coe_nnreal_ennreal.comp hVm)
    measurable_const
  set f : X → ℝ≥0∞ := fun y => (V y : ℝ≥0∞) + 1 with hfdef
  have hf : Measurable f := (measurable_coe_nnreal_ennreal.comp hVm).add measurable_const
  set r := ρ⁻¹ with hrdef
  have hr0 : r ≠ 0 := ENNReal.inv_ne_zero.2 hρt
  have hrt : r ≠ ∞ := ENNReal.inv_ne_top.2 hρ0
  have hrρ : r * ρ = 1 := ENNReal.inv_mul_cancel hρ0 hρt
  set ε := (ρ - lam) * 2⁻¹ with hεdef
  have hε0 : ε ≠ 0 := mul_ne_zero hδ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  have hεt : ε ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.sub_ne_top hρt) (ENNReal.inv_ne_top.2 two_ne_zero)
  set μ := pathKernel P x with hμ
  set τ := firstReturn C with hτdef
  have hτm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < τ ω} :=
    measurableSet_lt_firstReturn hCm
  set Z : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => if k = 0 then 0 else r ^ k * Vs k ω with hZ
  set F : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => if k = 0 then 0 else ε * r * (r ^ k * f (ω k))
    with hF
  set S : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => if k = 0 then r * Vs 1 ω else 0 with hS
  have hFm : ∀ k, Measurable (F k) := fun k => by
    by_cases hk : k = 0
    · simp only [hF, hk, ↓reduceIte]; exact measurable_const
    · simp only [hF, hk, ↓reduceIte]
      exact measurable_const.mul (measurable_const.mul (hf.comp (measurable_pi_apply k)))
  have hSm : ∀ k, Measurable (S k) := fun k => by
    by_cases hk : k = 0
    · simp only [hS, hk, ↓reduceIte]; exact measurable_const.mul (hVs 1)
    · simp only [hS, hk, ↓reduceIte]; exact measurable_const
  have hnot : ∀ (ω : ℕ → X) (k : ℕ), 1 ≤ k → (k : WithTop ℕ) < τ ω → ω k ∉ C := by
    intro ω k hk hlt
    exact (le_firstReturn_iff C ω (k + 1)).1 ((coe_lt_iff_succ_le k _).1 hlt) k hk
      (Nat.lt_succ_self k)
  have hstep : ∀ n : ℕ, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z (n + 1) ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ ≤
      ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z n ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, S n ω ∂μ := by
    intro n
    rcases n with _ | m
    · simp [hZ, hF, hS]
    · set G := {ω : ℕ → X | ((m + 1 : ℕ) : WithTop ℕ) < τ ω} with hGdef
      have hG : MeasurableSet[natFilt (X := X) (m + 1)] G :=
        measurableSet_lt_of_isStoppingTime (proposition_3_4_4 hCm).1 (m + 1)
      have hGm : MeasurableSet G := hτm (m + 1)
      have hGc : ∀ ω ∈ G, c ≤ V (ω (m + 1)) := fun ω hω => by
        have := hnot ω (m + 1) (by omega) hω
        simp only [hCdef, mem_ofPred_eq, not_le] at this
        exact this.le
      have hB := setLIntegral_geomDrift_le μ hVV hlr hδ hρt hGm hGc (hdrift (m + 1) G hG)
      have hZ1 : ∀ ω, Z (m + 1 + 1) ω = r ^ (m + 2) * Vs (m + 2) ω := fun ω => by simp [hZ]
      have hZ0 : ∀ ω, Z (m + 1) ω = r ^ (m + 1) * Vs (m + 1) ω := fun ω => by simp [hZ]
      have hF1 : ∀ ω, F (m + 1) ω = ε * r * (r ^ (m + 1) * f (ω (m + 1))) := fun ω => by
        simp [hF]
      have hS1 : ∀ ω, S (m + 1) ω = 0 := fun ω => by simp [hS]
      simp_rw [hZ1, hZ0, hF1, hS1, lintegral_zero, add_zero]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hrt),
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hεt hrt)]
      simp_rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hrt)]
      calc r ^ (m + 2) * ∫⁻ ω in G, Vs (m + 2) ω ∂μ +
            ε * r * (r ^ (m + 1) * ∫⁻ ω in G, f (ω (m + 1)) ∂μ)
          = r ^ (m + 2) * (∫⁻ ω in G, Vs (m + 1 + 1) ω ∂μ +
              ε * ∫⁻ ω in G, ((V (ω (m + 1)) : ℝ≥0∞) + 1) ∂μ) := by ring
        _ ≤ r ^ (m + 2) * (ρ * ∫⁻ ω in G, Vs (m + 1) ω ∂μ) := mul_le_mul' le_rfl hB
        _ = r ^ (m + 1) * ∫⁻ ω in G, Vs (m + 1) ω ∂μ := by
            rw [pow_succ, mul_assoc, ← mul_assoc r ρ, hrρ, one_mul]
  have hcomp := comparison_lintegral μ hτm hFm hSm hstep
  have hτ0 : ∀ ω : ℕ → X, (0 : WithTop ℕ) < τ ω := fun ω =>
    lt_of_lt_of_le (by norm_num) (one_le_firstReturn C ω)
  have hZ00 : ∫⁻ ω, Z 0 ω ∂μ = 0 := by simp [hZ]
  have hS0 : (fun k ω => if k = 0 then 0 else S k ω) = fun (_ : ℕ) (_ : ℕ → X) => 0 := by
    funext k ω; by_cases hk : k = 0 <;> simp [hS, hk]
  have hSsum : ∀ ω, sumBefore τ S ω = r * Vs 1 ω := fun ω => by
    rw [sumBefore_eq_zero_add S (hτ0 ω), hS0]
    simp [hS, sumBefore]
  set Rest : (ℕ → X) → ℝ≥0∞ :=
    sumBefore τ (fun k ω => if k = 0 then 0 else r ^ k * f (ω k)) with hRest
  have hFsum : ∀ ω, sumBefore τ F ω = ε * r * Rest ω := fun ω => by
    rw [hRest, ← sumBefore_const_mul]
    refine sumBefore_congr _ fun k _ => ?_
    by_cases hk : k = 0 <;> simp [hF, hk]
  have hRestm : Measurable Rest := measurable_sumBefore hτm fun k => by
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]; exact measurable_const
    · simp only [hk, ↓reduceIte]; exact measurable_const.mul (hf.comp (measurable_pi_apply k))
  simp_rw [hFsum, hSsum] at hcomp
  rw [hZ00, zero_add, lintegral_const_mul _ hRestm, lintegral_const_mul _ (hVs 1)] at hcomp
  have hcomp' : ε * ∫⁻ ω, Rest ω ∂μ ≤ ∫⁻ ω, Vs 1 ω ∂μ := by
    have h' : r * (ε * ∫⁻ ω, Rest ω ∂μ) ≤ r * ∫⁻ ω, Vs 1 ω ∂μ := by
      rw [← mul_assoc, mul_comm r ε]; exact hcomp
    exact (ENNReal.mul_le_mul_iff_right hr0 hrt).1 h'
  have hR : ∫⁻ ω, Rest ω ∂μ ≤ ε⁻¹ * ∫⁻ ω, Vs 1 ω ∂μ := by
    calc ∫⁻ ω, Rest ω ∂μ = ε⁻¹ * (ε * ∫⁻ ω, Rest ω ∂μ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hε0 hεt, one_mul]
      _ ≤ ε⁻¹ * ∫⁻ ω, Vs 1 ω ∂μ := mul_le_mul' le_rfl hcomp'
  calc geomSum P C r f x = ∫⁻ ω, (f (ω 0) + Rest ω) ∂μ := by
        rw [geomSum]
        refine lintegral_congr fun ω => ?_
        rw [sumBefore_eq_zero_add _ (hτ0 ω), pow_zero, one_mul]
    _ = f x + ∫⁻ ω, Rest ω ∂μ := by
        rw [lintegral_add_left (f := fun ω : ℕ → X => f (ω 0)) (hf.comp (measurable_pi_apply 0)),
          lintegral_coord_zero P x hf]
    _ ≤ f x + ε⁻¹ * ∫⁻ ω, Vs 1 ω ∂μ := add_le_add le_rfl hR

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.2.3** (MT p. 493): let the chain be a `ψ`-irreducible aperiodic T-chain and
`Vₖ` a coercive sequence (`Vₖ ≥ V(Φₖ)`, `V` coercive, (19.36)) with `V₀ = v(Φ₀)`, `v` bounded on
compact sets, satisfying the generalized geometric drift condition (19.37),
`E[V_{k+1} | 𝓕ₖ^Φ] ≤ λVₖ + L` with `λ < 1`, `L < ∞`, under every `P_y`. Then the chain is positive
and, with `f = V + 1`, every invariant probability `π` has `π(f) < ∞`, and for some `r > 1`,
`R < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R (V₀(x) + 1)` for every `x`.

The proof is the book's: `C = {V ≤ 2L/(ρ − λ) + 1}` (`ρ = (λ + 1)/2`) has compact closure, so it
is petite; the Dynkin argument (`geomSum_le_of_genGeomDrift`) makes it `f`-Kendall of rate
`ρ⁻¹`, and Theorem 15.4.1 gives the bound. -/
theorem theorem_19_2_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hT : IsTChain P)
    {Vs : ℕ → (ℕ → X) → ℝ≥0∞} (hVs : ∀ k, Measurable (Vs k)) {V : X → ℝ≥0} (hVm : Measurable V)
    (hV : IsCoercive V) (hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ Vs k ω) {v : X → ℝ≥0∞}
    (hV0 : ∀ ω, Vs 0 ω = v (ω 0))
    (hvc : ∀ K : Set X, IsCompact K → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ K, v x ≤ M)
    {lam L : ℝ≥0∞} (hlam : lam < 1) (hL : L ≠ ∞)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P y ≤
        lam * ∫⁻ ω in G, Vs k ω ∂pathKernel P y + L * pathKernel P y G) :
    IsPositive P ψ ∧ ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
      ∫⁻ x, ((V x : ℝ≥0∞) + 1) ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ n * fNorm (fun y => (V y : ℝ≥0∞) + 1) ((P ^ n : Kernel X X) x) π ≤
          R * (v x + 1) := by
  have := isMarkovKernel_pathKernel P
  have hv : Measurable v := by
    have : v = fun y => Vs 0 (fun _ => y) := funext fun y => (hV0 fun _ => y).symm
    rw [this]; exact (hVs 0).comp (measurable_pi_iff.2 fun _ => measurable_id)
  have hvfin : ∀ x, v x ≠ ∞ := fun x => by
    obtain ⟨M, hM, hb⟩ := hvc {x} isCompact_singleton
    exact ne_top_of_le_ne_top hM (hb x rfl)
  -- the constants
  have hlt : lam ≠ ∞ := ne_top_of_lt hlam
  set ρ := lam * 2⁻¹ + 2⁻¹ with hρdef
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have h2t : (2⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 two_ne_zero
  have hlh : lam * 2⁻¹ < 2⁻¹ := by
    calc lam * 2⁻¹ < 1 * 2⁻¹ := ENNReal.mul_lt_mul_left h2 h2t hlam
      _ = 2⁻¹ := one_mul _
  have hρ1 : ρ < 1 := by
    calc ρ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_right h2t hlh
      _ = 1 := ENNReal.inv_two_add_inv_two
  have hlρ : lam < ρ := by
    calc lam = lam * 2⁻¹ + lam * 2⁻¹ := by rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
      _ < lam * 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_left (ENNReal.mul_ne_top hlt h2t) hlh
  have hρt : ρ ≠ ∞ := ne_top_of_lt hρ1
  have hρ0 : ρ ≠ 0 := (lt_of_le_of_lt zero_le hlρ).ne'
  have hδ : ρ - lam ≠ 0 := (tsub_pos_iff_lt.2 hlρ).ne'
  set c := 2 * L * (ρ - lam)⁻¹ + 1 with hc
  have hct : c ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofNat_ne_top hL) (ENNReal.inv_ne_top.2 hδ), ENNReal.one_ne_top⟩
  set C := {y | (V y : ℝ≥0∞) ≤ c} with hCdef
  have hCm : MeasurableSet C := measurableSet_le (measurable_coe_nnreal_ennreal.comp hVm)
    measurable_const
  set f : X → ℝ≥0∞ := fun y => (V y : ℝ≥0∞) + 1 with hfdef
  have hf : Measurable f := (measurable_coe_nnreal_ennreal.comp hVm).add measurable_const
  have hf1 : ∀ y, 1 ≤ f y := fun y => le_add_self
  set r := ρ⁻¹ with hrdef
  have hr1 : 1 < r := ENNReal.one_lt_inv.2 hρ1
  have hrt : r ≠ ∞ := ENNReal.inv_ne_top.2 hρ0
  set ε := (ρ - lam) * 2⁻¹ with hεdef
  have hε0 : ε ≠ 0 := mul_ne_zero hδ h2
  have hεi : ε⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hε0
  -- the compact closure of `C`, petiteness, and the bound on `v`
  have hCset : C = {y | V y ≤ c.toNNReal} := by
    ext y
    simp only [hCdef, mem_ofPred_eq]
    nth_rewrite 1 [← ENNReal.coe_toNNReal hct]
    exact ENNReal.coe_le_coe
  have hK : IsCompact (closure C) := by rw [hCset]; exact hV c.toNNReal
  have hCpet : IsPetite P C := (theorem_6_2_5_ii hψ.2.1 hψ.1 hT hK).subset hCm subset_closure
  obtain ⟨MC, hMC, hvC⟩ := hvc _ hK
  -- the geometric sums
  have hgs : ∀ x, geomSum P C r f x ≤ f x + ε⁻¹ * (lam * v x + L) := fun x => by
    have h := geomSum_le_of_genGeomDrift P hVs hVm hVV hlρ.le hδ hρ0 hρt x (hdrift x)
    have h1 := hdrift x 0 univ MeasurableSet.univ
    simp only [Measure.restrict_univ, measure_univ, mul_one] at h1
    simp_rw [hV0] at h1
    rw [lintegral_coord_zero P x hv] at h1
    exact h.trans (add_le_add le_rfl (mul_le_mul' le_rfl h1))
  have hfC : ∀ y ∈ C, f y ≤ c + 1 := fun y hy => add_le_add hy le_rfl
  set Kb := (c + 1) + ε⁻¹ * (lam * MC + L) with hKb
  have hKbt : Kb ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩,
    ENNReal.mul_ne_top hεi (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hlt hMC, hL⟩)⟩
  have hgsC : ∀ y ∈ C, geomSum P C r f y ≤ Kb := fun y hy =>
    (hgs y).trans (add_le_add (hfC y hy) (mul_le_mul' le_rfl (add_le_add
      (mul_le_mul' le_rfl (hvC y (subset_closure hy))) le_rfl)))
  -- `C` is non-empty
  have hne : C.Nonempty := by
    obtain ⟨x₀⟩ : Nonempty X := by
      by_contra hX
      rw [not_nonempty_iff] at hX
      exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
    rw [nonempty_iff_ne_empty]
    intro hC0
    have hfin : geomSum P C r f x₀ ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩, ENNReal.mul_ne_top hεi
        (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hlt (hvfin x₀), hL⟩)⟩) (hgs x₀)
    apply hfin
    rw [geomSum, hC0]
    have htop : ∀ ω : ℕ → X, sumBefore (firstReturn (∅ : Set X)) (fun k ω => r ^ k * f (ω k)) ω
        = ∞ := fun ω => by
      have h : firstReturn (∅ : Set X) ω = ⊤ := by
        by_contra hne
        obtain ⟨k, -, hk⟩ := (firstReturn_ne_top_iff ∅ ω).1 hne
        exact notMem_empty _ hk
      rw [sumBefore_eq_of_eq (τ' := fun _ => (⊤ : WithTop ℕ)) h, sumBefore_top_eq]
      refine top_le_iff.1 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
      exact ENNReal.tsum_le_tsum fun k => one_le_mul (one_le_pow₀ hr1.le) (hf1 _)
    simp_rw [htop]
    simp
  -- `C` is `f`-Kendall, and Theorem 15.4.1 applies
  have hFK : IsFKendall P f C r := ⟨hCm, hr1, hrt, Kb, hKbt, hgsC⟩
  obtain ⟨-, -, hpos, hgeo⟩ := theorem_15_4_1 hψ hap hf hf1 hCpet hne hFK
  refine ⟨hpos, fun π _ hπ => ?_⟩
  obtain ⟨hπf, r', hr', R, hR, hbd⟩ := hgeo π hπ
  set a := 1 + ε⁻¹ * (lam + L) with ha
  have hat : a ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top hεi (ENNReal.add_ne_top.2 ⟨hlt, hL⟩)⟩
  set Mf := c + 1 with hMf
  set b := 1 + a + Mf + Mf * ((r - 1) * a) with hb
  have hbt : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, hat⟩, ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩⟩,
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩)
      (ENNReal.mul_ne_top (ENNReal.sub_ne_top hrt) hat)⟩
  refine ⟨hπf, r', hr', R * b, ENNReal.mul_ne_top hR hbt, fun x => (hbd x).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have hVv : (V x : ℝ≥0∞) ≤ v x := by have := hVV 0 (fun _ => x); rwa [hV0] at this
  have hfx : f x ≤ v x + 1 := add_le_add hVv le_rfl
  have h1v : 1 ≤ v x + 1 := le_add_self
  have hgsx : geomSum P C r f x ≤ a * (v x + 1) := by
    calc geomSum P C r f x ≤ f x + ε⁻¹ * (lam * v x + L) := hgs x
      _ ≤ (v x + 1) + ε⁻¹ * ((lam + L) * (v x + 1)) := by
          refine add_le_add hfx (mul_le_mul' le_rfl ?_)
          rw [add_mul]
          exact add_le_add (mul_le_mul' le_rfl le_self_add)
            (le_mul_of_one_le_right zero_le h1v)
      _ = a * (v x + 1) := by rw [ha]; ring
  calc geomG P C r f x ≤ f x + geomTaboo P C r f x := geomG_le P hCm r hf x
    _ ≤ f x + (geomSum P C r f x + Mf * kendallMoment P C r x) :=
        add_le_add le_rfl (geomTaboo_le_geomSum_add P hCm hr1 hf hfC x)
    _ ≤ (v x + 1) + (a * (v x + 1) + Mf * (1 + (r - 1) * (a * (v x + 1)))) :=
        add_le_add hfx (add_le_add hgsx (mul_le_mul' le_rfl
          ((kendallMoment_le_one_add P hCm hr1 hf1 x).trans
            (add_le_add le_rfl (mul_le_mul' le_rfl hgsx)))))
    _ ≤ (v x + 1) + (a * (v x + 1) + Mf * ((v x + 1) + (r - 1) * (a * (v x + 1)))) :=
        add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add h1v le_rfl)))
    _ = b * (v x + 1) := by rw [hb]; ring

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.2.3, the drift (V4) and the Harris property** (MT p. 493, with Theorem 15.2.4 and
Theorem 11.3.4): under the hypotheses of `theorem_19_2_3` (aperiodicity is not needed here), the
chain is positive Harris, and `W = G_C^{(ρ⁻¹)}(·, V + 1) ≥ V + 1`, finite everywhere with
`W ≤ B(V₀ + 1)`, satisfies (V4) for a petite set. This is the form in which the book's
"geometrically ergodic" feeds the limit theorems of Chapter 17 (Theorem 17.0.1). -/
theorem theorem_19_2_3_driftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P)
    {Vs : ℕ → (ℕ → X) → ℝ≥0∞} (hVs : ∀ k, Measurable (Vs k)) {V : X → ℝ≥0} (hVm : Measurable V)
    (hV : IsCoercive V) (hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ Vs k ω) {v : X → ℝ≥0∞}
    (hV0 : ∀ ω, Vs 0 ω = v (ω 0))
    (hvc : ∀ K : Set X, IsCompact K → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ K, v x ≤ M)
    {lam L : ℝ≥0∞} (hlam : lam < 1) (hL : L ≠ ∞)
    (hdrift : ∀ y k (G : Set (ℕ → X)), MeasurableSet[natFilt k] G →
      ∫⁻ ω in G, Vs (k + 1) ω ∂pathKernel P y ≤
        lam * ∫⁻ ω in G, Vs k ω ∂pathKernel P y + L * pathKernel P y G) :
    IsPositiveHarris P ψ ∧ ∃ W : X → ℝ≥0∞, Measurable W ∧ (∀ x, (V x : ℝ≥0∞) + 1 ≤ W x) ∧
      (∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x, W x ≤ B * (v x + 1)) ∧
      ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite P C ∧ DriftV4 P W ρ b C := by
  have := isMarkovKernel_pathKernel P
  have hv : Measurable v := by
    have : v = fun y => Vs 0 (fun _ => y) := funext fun y => (hV0 fun _ => y).symm
    rw [this]; exact (hVs 0).comp (measurable_pi_iff.2 fun _ => measurable_id)
  have hvfin : ∀ x, v x ≠ ∞ := fun x => by
    obtain ⟨M, hM, hb⟩ := hvc {x} isCompact_singleton
    exact ne_top_of_le_ne_top hM (hb x rfl)
  -- the constants
  have hlt : lam ≠ ∞ := ne_top_of_lt hlam
  set ρ := lam * 2⁻¹ + 2⁻¹ with hρdef
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have h2t : (2⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 two_ne_zero
  have hlh : lam * 2⁻¹ < 2⁻¹ := by
    calc lam * 2⁻¹ < 1 * 2⁻¹ := ENNReal.mul_lt_mul_left h2 h2t hlam
      _ = 2⁻¹ := one_mul _
  have hρ1 : ρ < 1 := by
    calc ρ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_right h2t hlh
      _ = 1 := ENNReal.inv_two_add_inv_two
  have hlρ : lam < ρ := by
    calc lam = lam * 2⁻¹ + lam * 2⁻¹ := by rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
      _ < lam * 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_left (ENNReal.mul_ne_top hlt h2t) hlh
  have hρt : ρ ≠ ∞ := ne_top_of_lt hρ1
  have hρ0 : ρ ≠ 0 := (lt_of_le_of_lt zero_le hlρ).ne'
  have hδ : ρ - lam ≠ 0 := (tsub_pos_iff_lt.2 hlρ).ne'
  set c := 2 * L * (ρ - lam)⁻¹ + 1 with hc
  have hct : c ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofNat_ne_top hL) (ENNReal.inv_ne_top.2 hδ), ENNReal.one_ne_top⟩
  set C := {y | (V y : ℝ≥0∞) ≤ c} with hCdef
  have hCm : MeasurableSet C := measurableSet_le (measurable_coe_nnreal_ennreal.comp hVm)
    measurable_const
  set f : X → ℝ≥0∞ := fun y => (V y : ℝ≥0∞) + 1 with hfdef
  have hf : Measurable f := (measurable_coe_nnreal_ennreal.comp hVm).add measurable_const
  have hf1 : ∀ y, 1 ≤ f y := fun y => le_add_self
  set r := ρ⁻¹ with hrdef
  have hr1 : 1 < r := ENNReal.one_lt_inv.2 hρ1
  have hrt : r ≠ ∞ := ENNReal.inv_ne_top.2 hρ0
  set ε := (ρ - lam) * 2⁻¹ with hεdef
  have hε0 : ε ≠ 0 := mul_ne_zero hδ h2
  have hεi : ε⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hε0
  -- the compact closure of `C`, petiteness, and the bound on `v`
  have hCset : C = {y | V y ≤ c.toNNReal} := by
    ext y
    simp only [hCdef, mem_ofPred_eq]
    nth_rewrite 1 [← ENNReal.coe_toNNReal hct]
    exact ENNReal.coe_le_coe
  have hK : IsCompact (closure C) := by rw [hCset]; exact hV c.toNNReal
  have hCpet : IsPetite P C := (theorem_6_2_5_ii hψ.2.1 hψ.1 hT hK).subset hCm subset_closure
  obtain ⟨MC, hMC, hvC⟩ := hvc _ hK
  -- the geometric sums
  have hgs : ∀ x, geomSum P C r f x ≤ f x + ε⁻¹ * (lam * v x + L) := fun x => by
    have h := geomSum_le_of_genGeomDrift P hVs hVm hVV hlρ.le hδ hρ0 hρt x (hdrift x)
    have h1 := hdrift x 0 univ MeasurableSet.univ
    simp only [Measure.restrict_univ, measure_univ, mul_one] at h1
    simp_rw [hV0] at h1
    rw [lintegral_coord_zero P x hv] at h1
    exact h.trans (add_le_add le_rfl (mul_le_mul' le_rfl h1))
  have hfC : ∀ y ∈ C, f y ≤ c + 1 := fun y hy => add_le_add hy le_rfl
  set Kb := (c + 1) + ε⁻¹ * (lam * MC + L) with hKb
  have hKbt : Kb ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩,
    ENNReal.mul_ne_top hεi (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hlt hMC, hL⟩)⟩
  have hgsC : ∀ y ∈ C, geomSum P C r f y ≤ Kb := fun y hy =>
    (hgs y).trans (add_le_add (hfC y hy) (mul_le_mul' le_rfl (add_le_add
      (mul_le_mul' le_rfl (hvC y (subset_closure hy))) le_rfl)))
  -- `C` is non-empty
  have hne : C.Nonempty := by
    obtain ⟨x₀⟩ : Nonempty X := by
      by_contra hX
      rw [not_nonempty_iff] at hX
      exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
    rw [nonempty_iff_ne_empty]
    intro hC0
    have hfin : geomSum P C r f x₀ ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩, ENNReal.mul_ne_top hεi
        (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hlt (hvfin x₀), hL⟩)⟩) (hgs x₀)
    apply hfin
    rw [geomSum, hC0]
    have htop : ∀ ω : ℕ → X, sumBefore (firstReturn (∅ : Set X)) (fun k ω => r ^ k * f (ω k)) ω
        = ∞ := fun ω => by
      have h : firstReturn (∅ : Set X) ω = ⊤ := by
        by_contra hne
        obtain ⟨k, -, hk⟩ := (firstReturn_ne_top_iff ∅ ω).1 hne
        exact notMem_empty _ hk
      rw [sumBefore_eq_of_eq (τ' := fun _ => (⊤ : WithTop ℕ)) h, sumBefore_top_eq]
      refine top_le_iff.1 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
      exact ENNReal.tsum_le_tsum fun k => one_le_mul (one_le_pow₀ hr1.le) (hf1 _)
    simp_rw [htop]
    simp
  -- `C` is `f`-Kendall, and Theorem 15.4.1 applies
  have hFK : IsFKendall P f C r := ⟨hCm, hr1, hrt, Kb, hKbt, hgsC⟩
  obtain ⟨M, hM, hdr, hfV, hVC⟩ := theorem_15_2_4 hf hf1 hFK
  set a := 1 + ε⁻¹ * (lam + L) with ha
  have hat : a ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top hεi (ENNReal.add_ne_top.2 ⟨hlt, hL⟩)⟩
  set Mf := c + 1 with hMf
  set b := 1 + a + Mf + Mf * ((r - 1) * a) with hb
  have hbt : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, hat⟩, ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩⟩,
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hct, ENNReal.one_ne_top⟩)
      (ENNReal.mul_ne_top (ENNReal.sub_ne_top hrt) hat)⟩
  have hW : ∀ x, geomG P C r f x ≤ b * (v x + 1) := fun x => by
    have hVv : (V x : ℝ≥0∞) ≤ v x := by have := hVV 0 (fun _ => x); rwa [hV0] at this
    have hfx : f x ≤ v x + 1 := add_le_add hVv le_rfl
    have h1v : 1 ≤ v x + 1 := le_add_self
    have hgsx : geomSum P C r f x ≤ a * (v x + 1) := by
      calc geomSum P C r f x ≤ f x + ε⁻¹ * (lam * v x + L) := hgs x
        _ ≤ (v x + 1) + ε⁻¹ * ((lam + L) * (v x + 1)) := by
            refine add_le_add hfx (mul_le_mul' le_rfl ?_)
            rw [add_mul]
            exact add_le_add (mul_le_mul' le_rfl le_self_add)
              (le_mul_of_one_le_right zero_le h1v)
        _ = a * (v x + 1) := by rw [ha]; ring
    calc geomG P C r f x ≤ f x + geomTaboo P C r f x := geomG_le P hCm r hf x
      _ ≤ f x + (geomSum P C r f x + Mf * kendallMoment P C r x) :=
          add_le_add le_rfl (geomTaboo_le_geomSum_add P hCm hr1 hf hfC x)
      _ ≤ (v x + 1) + (a * (v x + 1) + Mf * (1 + (r - 1) * (a * (v x + 1)))) :=
          add_le_add hfx (add_le_add hgsx (mul_le_mul' le_rfl
            ((kendallMoment_le_one_add P hCm hr1 hf1 x).trans
              (add_le_add le_rfl (mul_le_mul' le_rfl hgsx)))))
      _ ≤ (v x + 1) + (a * (v x + 1) + Mf * ((v x + 1) + (r - 1) * (a * (v x + 1)))) :=
          add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add h1v le_rfl)))
      _ = b * (v x + 1) := by rw [hb]; ring
  have hWm := measurable_geomG P hCm r hf
  have hWfin : ∀ x, geomG P C r f x ≠ ∞ := fun x => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hbt (ENNReal.add_ne_top.2 ⟨hvfin x, ENNReal.one_ne_top⟩)) (hW x)
  have hW1 : ∀ x, 1 ≤ geomG P C r f x := fun x => (hf1 x).trans (hfV x)
  have hκ : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr1
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr1).ne'
  have hb' : r⁻¹ * M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hr0) hM
  have hc : (1 - r⁻¹)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hκ).ne'
  have hph := theorem_11_3_4_positiveHarris hψ (hWm.const_mul _) (ENNReal.mul_ne_top hc hb')
    hCpet (hdr.driftV2_scaled hWm hW1 hκ) (fun x => ENNReal.mul_ne_top hc (hWfin x))
    (ENNReal.mul_ne_top hc hM) (fun x hx => mul_le_mul' le_rfl (hVC x hx))
  exact ⟨hph, geomG P C r f, hWm, hfV, ⟨b, hbt, hW⟩, r⁻¹, r⁻¹ * M, hκ, hb', C, hCpet, hdr⟩

end MeynTweedie.GeneralizedDrift
